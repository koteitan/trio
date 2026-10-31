#!/bin/bash
# sequential measurement campaign (Pool(2) + parent = 3 processes)
cd /home/koteitan/proofs/trio/tmp/wf/WfQrH
S=$(cat sets1.txt)
nice -n 15 python3 mside.py 2 0 mside1.jsonl $S > mside1.log 2>&1
nice -n 15 python3 famframes.py famframes.pkl > famframes.log 2>&1
CAP=2000 nice -n 15 python3 oframe.py 2 of_all.jsonl $S famframes.pkl > of_all.log 2>&1
CAP=2000 nice -n 15 python3 compq2.py 2 3 cq_all.jsonl $S famframes.pkl > cq_all.log 2>&1
echo done > runall.done
