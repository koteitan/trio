#!/bin/bash
D=/home/koteitan/proofs/trio/tmp
for f in $D/wf/WfQnE/graftQ1.pkl $D/wf/WfQnE/graftQ2.pkl $D/wf/WfInvA/graftA2.pkl $D/ytosk-handoff/sets/graftA.pkl $D/wf/WfInvA/graftA3.pkl $D/ytosk-handoff/sets/graftB.pkl $D/ytosk-handoff/sets/expP.pkl $D/ytosk-handoff/sets/ext1.pkl; do
  b=$(basename $f .pkl)
  nice -n 15 python3 /home/koteitan/proofs/trio/tmp/wf/WfQnA/meas.py $f /home/koteitan/proofs/trio/tmp/wf/WfQnA/m_$b.json 3 >> /home/koteitan/proofs/trio/tmp/wf/WfQnA/meas.log 2>&1
done
echo DONE >> /home/koteitan/proofs/trio/tmp/wf/WfQnA/meas.log
