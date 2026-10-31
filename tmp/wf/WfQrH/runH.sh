#!/bin/bash
cd /home/koteitan/proofs/trio/tmp/wf/WfQrH
until [ -f runall.done ]; do sleep 20; done
nice -n 15 python3 graftH.py graftH.pkl 5 /home/koteitan/proofs/trio/tmp/wf/WfB2L/g36_2.pkl /home/koteitan/proofs/trio/tmp/wf/WfInvA/frames/graftM36x.pkl /home/koteitan/proofs/trio/tmp/wf/WfInvA/frames_g/graftA1.pkl /home/koteitan/proofs/trio/tmp/wf/WfInvA/frames/lift1.pkl > graftH.log 2>&1
nice -n 15 python3 mside.py 2 0 mside_H.jsonl graftH.pkl >> graftH.log 2>&1
CAP=4000 nice -n 15 python3 oframe.py 2 of_H.jsonl graftH.pkl >> graftH.log 2>&1
CAP=4000 nice -n 15 python3 compq2.py 2 3 cq_H.jsonl graftH.pkl >> graftH.log 2>&1
echo done > runH.done
