#!/bin/bash
# worker: probe2 (CAP $CAP, NMAX 4) on each file of list $1, outputs in out/
mkdir -p /home/koteitan/proofs/trio/tmp/wf/WfCofL/out
while read f; do b=$(basename $(dirname $f))_$(basename $f .pkl); CAP=${CAP:-3000} nice -n 15 python3 /home/koteitan/proofs/trio/tmp/wf/WfCofL/probe2.py /home/koteitan/proofs/trio/tmp/wf/WfCofL/out/$b.json 4 $f > /home/koteitan/proofs/trio/tmp/wf/WfCofL/out/$b.txt 2>&1; done < $1
