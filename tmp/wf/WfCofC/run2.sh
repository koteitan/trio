#!/bin/bash
# worker: probeX (CAP $CAP, NMAX 4) on each file of list $1
W=/home/koteitan/proofs/trio/tmp/wf/WfCofC
while read f; do b=$(basename $(dirname $f))_$(basename $f .pkl); CAP=${CAP:-6000} nice -n 15 timeout 3000 python3 $W/probeX.py $W/out2/$b.json 4 $f > $W/out/$b.txt 2>&1; done < $1
