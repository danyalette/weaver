# Generate A Report 
Use this bash script to automatically generate a performance report which compares the performance of Weaver across difference algorithms and different wvr files. 

## Usage
`./generate.sh -a <list,of,algos> -t <list,of,wvr,templates> -n <thread_count>`
E.g. `./generate.sh -a normal,partition,partition-progress -t replicate -n 5`

The generated report will be in `out/<current UTC datetime>/report.pdf`. 

## Weaver Templates 

Weaver template files are in `wvr-templates/`. If the file is called `<name>.wvr`, then the name supplied to `generate.sh`, for the `-t` parameter will be `<name>`. 

A weaver template file is a weaver file which includes the string `${n}`. This string will be replaced with an integer corresponding to thread count during report generation. 
E.g. in file `wvr-templates/replicate.wvr`, 
```
(var X Int)
(var assert Bool)
(set! assert true)
(replicate ${n}
  (declare (x Int)
      (set! x 5)
      (set! assert (and assert (= x 5)))
     ))
(assume (not assert))
```