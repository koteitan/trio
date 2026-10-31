#!/bin/bash
# sequential runs, 3 processes each
D=/home/koteitan/proofs/trio/tmp
for f in $D/wf/WfQnE/graftQ1.pkl $D/wf/WfQnE/graftQ2.pkl $D/wf/WfDrE/graftE.pkl $D/wf/WfInvD/graftD.pkl $D/wf/WfCof/graftF.pkl $D/wf/WfCofL/graftG.pkl $D/wf/WfReM/graftM36.pkl $D/wf/WfReM/graftM36x.pkl $D/wf/WfAbsW/graft36c.pkl $D/wf/WfInvA/graftA1.pkl $D/wf/WfInvA/graftA2.pkl $D/ytosk-handoff/sets/graftA.pkl $D/ytosk-handoff/sets/graftB.pkl $D/ytosk-handoff/sets/ext1.pkl $D/ytosk-handoff/sets/expP.pkl $D/wf/WfInvA/graftA3.pkl; do
  b=$(basename $f .pkl)
  nice -n 15 python3 /home/koteitan/proofs/trio/tmp/wf/WfQnH/meas.py $f /home/koteitan/proofs/trio/tmp/wf/WfQnH/m_$b.json 3 >> /home/koteitan/proofs/trio/tmp/wf/WfQnH/meas.log 2>&1
done
echo DONE >> /home/koteitan/proofs/trio/tmp/wf/WfQnH/meas.log
