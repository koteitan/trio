#!/bin/bash
# worker: probeH (CAP $CAP, NMAX 4) on each file of list $1
while read f; do b=$(basename $(dirname $f))_$(basename $f .pkl); CAP=${CAP:-2000} nice -n 15 python3 /home/koteitan/proofs/trio/tmp/wf/WfCofH/probeH.py /home/koteitan/proofs/trio/tmp/wf/WfCofH/out/$b.json 4 $f > /home/koteitan/proofs/trio/tmp/wf/WfCofH/out/$b.txt 2>&1; done < $1
