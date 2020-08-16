#!/usr/bin/env bash

DIR_DATE=$(date +"%F_%H.%M.%S")
SECONDS=0
IFS="," 

while [ "$1" != "" ]; do
    case $1 in
        -a | --algorithms )     shift
                                IFS=","
                                read -r -a ALGOS <<< "$1"
                                ;;
        -t | --templates )      shift
                                IFS=","
                                read -r -a TEMPLATES <<< "$1"
                                ;;
        -n | --thread-count )   shift
                                MAX_COUNT=$1
                                ;;
        * )                     usage
                                exit 1
    esac
    shift
done

TEMPLATES_DIR=./wvr-templates
WVR_DIR=./wvr/$DIR_DATE
RESULTS_DIR=./out/$DIR_DATE
OUTPUT_DIR=$RESULTS_DIR/output
WVR_DIR=$RESULTS_DIR/wvr-files
DATA_DIR=$RESULTS_DIR/data
REPORT_MD=$RESULTS_DIR/report.md
REPORT_FILE=$RESULTS_DIR/report.pdf

# create header of report markdown file 
mkdir -p "${REPORT_FILE%/*}" # make directory for report 
STR=$(cat <<-End
# Report 
Generated on $(date).

#### Algorithms
\`\`\`
${ALGOS[*]}
\`\`\`

#### Weaver Templates 
\`\`\`
${TEMPLATES[*]}
\`\`\`

#### Max Thread Count 
\`\`\`
$MAX_COUNT
\`\`\`


End)


printf "%s\n" $STR > "$REPORT_MD"


for TEMPLATE in ${TEMPLATES[@]}; do

TEMPLATE_TITLE=$(python -c "print '$TEMPLATE'.title()")

# files for csv data 
SIZE_DATA="$DATA_DIR/$TEMPLATE/size.csv"
ITER_DATA="$DATA_DIR/$TEMPLATE/iter.csv"
TIME_DATA="$DATA_DIR/$TEMPLATE/time.csv"
STATUS_DATA="$DATA_DIR/$TEMPLATE/status.csv"

# files for data graphs  
I_EXT="png"
SIZE_GRAPH="$DATA_DIR/$TEMPLATE/size.$I_EXT"
ITER_GRAPH="$DATA_DIR/$TEMPLATE/iter.$I_EXT"
TIME_GRAPH="$DATA_DIR/$TEMPLATE/time.$I_EXT"

# Weaver Algorithms 
# declare -a ALGOS=("non-symmetry" "symmetry-closed" "symmetry" "symmetry-canon")

OUTPUT_FILE="$OUTPUT_DIR/$TEMPLATE/$ALGO.txt"

mkdir -p "${SIZE_DATA%/*}" # make directory for data 
mkdir -p "${OUTPUT_FILE%/*}" # make directory for output

echo "threads,${ALGOS[*]}" > $SIZE_DATA  # add headings to size csv 
echo "threads,${ALGOS[*]}" > $ITER_DATA  # add headings to iter csv 
echo "threads,${ALGOS[*]}" > $TIME_DATA  # add headings to time csv 
echo "threads,${ALGOS[*]}" > $STATUS_DATA  # add headings to status csv 

for (( COUNT=1; COUNT<=$MAX_COUNT; COUNT++ ))
do
  
  # start newline for this thread count's data row with the thread count
  echo -n $COUNT >> $SIZE_DATA
  echo -n $COUNT >> $ITER_DATA
  echo -n $COUNT >> $TIME_DATA
  echo -n $COUNT >> $STATUS_DATA
  
  # file for wvr template with thread count subbed in
  WVR_FILE="$WVR_DIR/$TEMPLATE/$COUNT.wvr"
  mkdir -p "${WVR_FILE%/*}" # create dir for new wvr file 

  for ALGO in ${ALGOS[@]}; do
    
    OUTPUT=""
    
    # create wvr file and then run weaver on this file for current algo
    cat "$TEMPLATES_DIR/$TEMPLATE.wvr" | sed -e "s/\${n}/$COUNT/" > $WVR_FILE
    printf "%s\n" "-----------------------" "THREAD COUNT: $COUNT" "-----------------------" >> "$OUTPUT_DIR/$TEMPLATE/$ALGO.txt"
    printf "%s\n" "-----------------------" "THREAD COUNT: $COUNT" "-----------------------" >> "$OUTPUT_DIR/$TEMPLATE/$ALGO-complete.txt"
    OUTPUT=$(cabal new-run weaver -- "$WVR_DIR/$TEMPLATE/$COUNT.wvr" -m $ALGO -s mathsat -i 100  )
    RESULT=$(printf "%s" "$OUTPUT" | tail -n 5 )
    
    # determine status
    STATUS=$(printf "%s" "$RESULT" | sed '5q;d' )
    if [[ "$STATUS" != "SUCCESS" ]]
    then FAILOUT="$OUTPUT"; RESULT=""; fi 
    if [ "$STATUS" != "SUCCESS" ] && [ "$STATUS" != "FAILURE" ];
    then STATUS="ERROR"; fi 
    
    # get numerical data from output of running weaver 
    SIZE=$(printf "%s" "$RESULT" | sed '1q;d' | cut -d' ' -f4 )
    ITERS=$(printf "%s" "$RESULT" | sed '3q;d' | cut -d' ' -f2 )
    T=$(printf "%s" "$RESULT" | sed '4q;d' | cut -d' ' -f4 )
    TIME=${T%s}
    
    # add numerical data to csv files 
    echo -n ",$SIZE" >> $SIZE_DATA
    echo -n ",$ITERS" >> $ITER_DATA
    echo -n ",$TIME" >> $TIME_DATA
    echo -n ",$STATUS" >> $STATUS_DATA
    
    # write output to files
    if [[ "$STATUS" == "SUCCESS" ]]
    then printf "%s\n"  "$RESULT" >> "$OUTPUT_DIR/$TEMPLATE/$ALGO.txt"
    else printf "%s\n"  "$FAILOUT" >> "$OUTPUT_DIR/$TEMPLATE/$ALGO.txt"; fi 
    printf "%s\n"  "$OUTPUT" >> "$OUTPUT_DIR/$TEMPLATE/$ALGO-complete.txt"
      
  done
  
  # add newline after this thread's data row 
  echo "" >> $SIZE_DATA
  echo "" >> $ITER_DATA
  echo "" >> $TIME_DATA
  echo "" >> $STATUS_DATA
  
done

graph $SIZE_DATA --title "$TEMPLATE_TITLE: Size"   --ylabel ''  --marker '.' --fontsize 12 -o $SIZE_GRAPH
graph $ITER_DATA --title "$TEMPLATE_TITLE: Iterations"   --ylabel ''  --marker '.' --fontsize 12 -o $ITER_GRAPH
graph $TIME_DATA --title "$TEMPLATE_TITLE: Time"   --ylabel ''  --marker '.' --fontsize 12 -o $TIME_GRAPH


# generate report 
cat << End >> "$REPORT_MD"

## Weaver template: $TEMPLATE_TITLE

### Code 

\`\`\`
End

cat "$TEMPLATES_DIR/$TEMPLATE.wvr" >> $REPORT_MD

cat << End >> "$REPORT_MD"

\`\`\`

### Summary

#### Status 
|$(cat $STATUS_DATA | head -n 1 | sed 's/,/|/g')|
|$(cat $STATUS_DATA | head -n 1 | sed 's/,/|/g' | sed 's/[^|]/-/g')|
$(tail -n  +2  $STATUS_DATA | sed -e 's/$/|/' | sed -e 's/^/|/' | sed -e 's/,/|/g')

#### Time  
|$(cat $TIME_DATA | head -n 1 | sed 's/,/|/g')|
|$(cat $TIME_DATA | head -n 1 | sed 's/,/|/g' | sed 's/[^|]/-/g')|
$(tail -n  +2  $TIME_DATA | sed -e 's/$/|/' | sed -e 's/^/|/' | sed -e 's/,/|/g')

![time]($TIME_GRAPH)

#### Iterations  
|$(cat $ITER_DATA | head -n 1 | sed 's/,/|/g')|
|$(cat $ITER_DATA | head -n 1 | sed 's/,/|/g' | sed 's/[^|]/-/g')|
$(tail -n  +2  $ITER_DATA | sed -e 's/$/|/' | sed -e 's/^/|/' | sed -e 's/,/|/g')

![iterations]($ITER_GRAPH)

#### Proof Size  
|$(cat $SIZE_DATA | head -n 1 | sed 's/,/|/g')|
|$(cat $SIZE_DATA | head -n 1 | sed 's/,/|/g' | sed 's/[^|]/-/g')|
$(tail -n  +2  $SIZE_DATA | sed -e 's/$/|/' | sed -e 's/^/|/' | sed -e 's/,/|/g')

![proof size]($SIZE_GRAPH)

### Weaver Output 
End

# get string of each algo output 
for ALGO in ${ALGOS[@]}; do
   echo -e "#### $ALGO\n \`\`\`" >> $REPORT_MD
   cat "$OUTPUT_DIR/$TEMPLATE/$ALGO-complete.txt" >> $REPORT_MD
   echo -e "\n \`\`\`" >> $REPORT_MD
done 

done 

pandoc --toc "$REPORT_MD" -f gfm -t latex -o $REPORT_FILE
