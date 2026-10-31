#!/bin/bash
# tpsrc on all frame sets, then runq (DQ vs true M[2], M[3]) with sample 1/100, then mfail on the rest
cd /home/koteitan/proofs/trio/tmp/wf/WfQrE
nice -n 15 python3 tpsrc.py 4 tpsrc.jsonl $(cat order.txt) > tpsrc.log 2>&1
nice -n 15 python3 runq.py 4 100 runq.jsonl $(cat order.txt) > runq.log 2>&1
nice -n 15 python3 mfail.py 4 mfail.jsonl $(cat rest.txt) > mfail2.log 2>&1
