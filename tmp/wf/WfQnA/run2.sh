#!/bin/bash
D=/home/koteitan/proofs/trio/tmp
W=$D/wf/WfQnA
nice -n 15 python3 $W/graftQ3.py $W/graftQ3.pkl 1500 3 >> $W/graft.log 2>&1
for f in $W/graftQ3.pkl $D/wf/WfQnE/graftQ1.pkl $D/wf/WfQnE/graftQ2.pkl $D/wf/WfInvA/graftA3.pkl $D/ytosk-handoff/sets/graftB.pkl $D/ytosk-handoff/sets/expP.pkl $D/ytosk-handoff/sets/ext1.pkl; do
  b=$(basename $f .pkl)
  nice -n 15 python3 $W/meas.py $f $W/m2_$b.json 3 >> $W/meas2.log 2>&1
done
echo DONE >> $W/meas2.log
