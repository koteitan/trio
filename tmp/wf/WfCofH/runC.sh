#!/bin/bash
# worker: probeC (CAP $CAP, NMAX 4) on each file of list $1
while read f; do b=$(basename $(dirname $f))_$(basename $f .pkl); CAP=${CAP:-1000} nice -n 15 python3 /home/koteitan/proofs/trio/tmp/wf/WfCofH/probeC.py /home/koteitan/proofs/trio/tmp/wf/WfCofH/outC/$b.json 4 $f > /home/koteitan/proofs/trio/tmp/wf/WfCofH/outC/$b.txt 2>&1; done < $1
