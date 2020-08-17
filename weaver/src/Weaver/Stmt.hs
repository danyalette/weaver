{-# LANGUAGE
    ApplicativeDo,
    BlockArguments,
    DataKinds,
    FlexibleInstances,
    GADTs,
    ImplicitParams,
    MultiParamTypeClasses,
    RankNTypes,
    TypeFamilies,
    OverloadedLists,
    OverloadedStrings,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Weaver.Stmt (ThreadID (..), V, mkV, threadID, withThreadID, Stmt (..), isArtificial, artificial, assume, assign, atomic, indep, prove, isTriple, isIndep, straverse, straverse_) where

import qualified Prelude as P
import Prelude hiding (and, not, null, map)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.State (State, evalState, get, put)
import Data.Bifunctor (bimap)
import Data.Constraint (Dict (..))
import Data.Constraint.Compose (ComposeC)
import Data.Constraint.Extras (ArgDict (..))
import Data.Dependent.Sum (DSum (..))
import Data.Dependent.Map (DMap, empty, findWithDefault, foldrWithKey, fromList, insert, intersectionWithKey, null, map, mapWithKey, singleton, union, toList)
import Data.Foldable (traverse_)
import Data.Functor.Const (Const (..))
import Data.GADT.Compare (GEq (..), GCompare (..), GOrdering (..), gcompare, geq)
import Data.GADT.Show (GShow (..))
import Data.GADT.Compare (GEq (..), GCompare (..), GOrdering (..), gcompare, geq)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text, append, pack)
import Data.Type.Equality ((:~:) (..))
import Language.SMT.Expr (Expr, and, ebind, eq, emap, etraverse, etraverse_, not, var, imp)
import Language.SMT.SExpr (SExpr (..), SExpressible (..))
import Language.SMT.Solver (Solver, interpolate, isSatisfiable, isValid)
import Language.SMT.Var (Var (..), Sorts (..), Rank (..))
import Numeric.Natural (Natural)
import Weaver.Config

data ThreadID
  = Root
  | InAlt Int ThreadID
  | InSeq Int ThreadID
  | InPar Int ThreadID
  | InRep ThreadID
  | InDecl ThreadID
  | Symbolic Int
  deriving (Eq, Ord, Show)

data V a = V Text Natural ThreadID (Rank a)

instance Show (V a) where 
  show (V t n th _) = "V " ++ show t ++ show n ++ show th 
  
instance GShow V where gshowsPrec = showsPrec

instance SExpressible (V a) where
  toSExpr (V x _ t _) = case t of 
    Symbolic i -> Symbol (append x (pack ("_" ++ show i)))
    _ -> Symbol x 

mkV ∷ Text → ThreadID → Rank a → V a
mkV x t s = V x 0 t s

prime ∷ V a → V a
prime (V x i t s) = V x (i + 1) t s

unprime ∷ V a → V a
unprime (V x _ t s) = V x 0 t s

threadID ∷ V a → ThreadID
threadID (V _ _ t _) = t

withThreadID ∷ ThreadID → V a → V a
withThreadID t (V x i _ s) = V x i t s

instance GEq V where
  geq (V x₁ i₁ t₁ s₁) (V x₂ i₂ t₂ s₂)
    | (x₁, i₁, t₁) == (x₂, i₂, t₂) = geq s₁ s₂
    | otherwise                    = Nothing

instance GCompare V where
  gcompare (V x₁ i₁ t₁ s₁) (V x₂ i₂ t₂ s₂) =
    case compare (x₁, i₁, t₁) (x₂, i₂, t₂) of
      LT → GLT
      GT → GGT
      EQ → gcompare s₁ s₂

instance Var V where
  rank (V _ _ _ s) = s

newtype U a = U { toV ∷ V '( '[], a) }

instance ArgDict (ComposeC Eq (Expr V)) U where
  type ConstraintsFor U (ComposeC Eq (Expr V)) = ()
  argDict (U _) = Dict

instance ArgDict (ComposeC Ord (Expr V)) U where
  type ConstraintsFor U (ComposeC Ord (Expr V)) = ()
  argDict (U _) = Dict

-- instance EqTag U (Expr V) where
--   eqTagged (U _) (U _) = (==)

-- instance OrdTag U (Expr V) where
--   compareTagged (U _) (U _) = compare

instance GEq U where
  geq (U x₁) (U x₂) = do
    Refl ← geq x₁ x₂
    return Refl

instance GCompare U where
  gcompare (U x₁) (U x₂) =
    case gcompare x₁ x₂ of
      GLT → GLT
      GEQ → GEQ
      GGT → GGT

data Stmt = Stmt Bool [Expr V Bool] (DMap U (Expr V))
  deriving (Eq, Ord)

straverse ∷ Applicative f ⇒ (∀a. V a → f (V a)) → Stmt → f Stmt
straverse f (Stmt b φs xs) = do
  φs' ← traverse (etraverse f) φs
  xs' ← fromList <$> traverse (\(U k :=> v) → (:=>) <$> (U <$> f k) <*> etraverse f v) (toList xs)
  pure (Stmt b φs' xs')

straverse_ ∷ Applicative f ⇒ (∀a. V a → f b) → Stmt → f ()
straverse_ f (Stmt _ φs xs) =
  traverse_ (etraverse_ f) φs *>
  traverse_ (\(U k :=> v) → f k *> etraverse_ f v) (toList xs)

isArtificial ∷ Stmt → Bool
isArtificial (Stmt b _ _) = b

artificial ∷ Expr V Bool → Stmt
artificial φ = Stmt True [φ] empty

assume ∷ Expr V Bool → Stmt
assume φ = Stmt False [φ] empty

assign ∷ V '( '[], a) → Expr V a → Stmt
assign x e = Stmt False [] (singleton (U x) e)

atomic ∷ [Stmt] → Stmt
atomic [] = Stmt False [] empty
atomic (Stmt b φs xs : zs) =
  let Stmt c ψs ys = atomic zs
  in  Stmt (b || c) (φs ++ fmap (subst xs) ψs) (union (map (subst xs) ys) xs)

indep ∷ (?config ∷ Config) ⇒ Stmt → Stmt → Expr V Bool
indep stmt₁ stmt₂ =
  let Stmt _ φs₁ xs₁ = atomic [stmt₁, stmt₂]
      Stmt _ φs₂ xs₂ = atomic [stmt₂, stmt₁]
      xs₁' = union xs₁ (mapWithKey (\(U k) _ → var k ()) xs₂)
      xs₂' = union xs₂ (mapWithKey (\(U k) _ → var k ()) xs₁)
      eqs  = intersectionWithKey (\_ x₁ x₂ → Const (eq [x₁, x₂])) xs₁' xs₂'
      eqs' = foldrWithKey (\_ → (:) . getConst) [] eqs
      imp₁ = imp [and φs₁, and (φs₂ ++ eqs')]
      imp₂ = imp [and φs₂, and (φs₁ ++ eqs')]
  in if semi then imp₁ else and [imp₁, imp₂]

instance SExpressible Stmt where
  toSExpr (Stmt _ [φ] xs) | null xs = ["assume", toSExpr φ]
  toSExpr (Stmt _ [] (toList → [U k :=> v])) = ["set!", toSExpr k, toSExpr v]
  toSExpr (Stmt _ φs xs) = List ("group" : φs' ++ xs')
    where φs' = fmap (\φ → ["assume", toSExpr φ]) φs
          xs' = foldrWithKey (\(U k) v → (["set!", toSExpr k, toSExpr v]:)) [] xs

rename ∷ DMap U U → Expr V a → Expr V a
rename m = emap \x →
  case rank x of
    Rank SNil _ → toV (findWithDefault (U x) (U x) m)
    _           → x

interpret ∷ Stmt → State (DMap U U) (Expr V Bool)
interpret (Stmt _ φs xs) = do
  m ← get
  let φs' = fmap (rename m) φs
      (m', xs') = foldrWithKey
        (\(U k) v →
          let k' = prime (toV (findWithDefault (U k) (U k) m))
              v' = rename m v
          in bimap (insert (U k) (U k')) (eq [var k' (), v'] :))
        (m, []) xs
  put m'
  return (and (φs' ++ xs'))

shift ∷ Traversable f ⇒ f Stmt → f (Expr V Bool)
shift stmts = evalState (traverse interpret stmts) empty

subst ∷ DMap U (Expr V) → Expr V a → Expr V a
subst m = ebind \x → findWithDefault (var x ()) (U x) m

prove ∷ MonadIO m ⇒ Solver V → NonEmpty Stmt → m (Maybe [Expr V Bool])
prove solver = fmap (fmap (fmap (emap unprime))) . interpolate solver . shift

isTriple ∷ MonadIO m ⇒ Solver V → Expr V Bool → Stmt → Expr V Bool → m Bool
isTriple solver φ stmt ψ =
  P.not <$> isSatisfiable solver (and (shift [assume φ, stmt, assume (not ψ)]))

isIndep ∷ (MonadIO m, ?config ∷ Config) ⇒ Solver V → Expr V Bool → Stmt → Stmt → m Bool
isIndep solver φ stmt₁ stmt₂ = isValid solver (imp [φ, indep stmt₁ stmt₂])
