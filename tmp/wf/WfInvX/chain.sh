#!/bin/bash
D=/home/koteitan/proofs/trio/tmp/wf/WfInvX

cd $D
nice -n 15 python3 $D/descent.py $D/descent.json 4 --prefixes > $D/descent.log 2>&1
nice -n 15 python3 $D/audit.py $D/sets.jsonl 4 $(cat $D/setlist.txt) > $D/sets.log 2>&1
echo CHAIN_DONE >> $D/sets.log
