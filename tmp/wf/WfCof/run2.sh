#!/bin/bash
# worker: run fsprobe2 (CAP 20000, NMAX 5) on each file of list $1, outputs in out2/
cd /home/koteitan/proofs/trio/tmp/wf/WfCof
mkdir -p out2
while read f; do b=$(basename $(dirname $f))_$(basename $f .pkl); CAP=20000 nice -n 15 python3 fsprobe2.py out2/$b.json 5 $f > out2/$b.txt 2>&1; done < $1
