#!/usr/bin/env bash
# Measure the drop inputs BumpAbsCB2 (ab) and the upgrade absorption (ua) on all 86 input sets.
set -u
cd /home/koteitan/proofs/trio
SETS=$(python3 -c "import json;print(' '.join(json.load(open('tmp/codex/inv3v3_inputs_sets_20261101.json'))))")
nice -n 15 python3 tmp/wf/WfSdH/abcb2.py 4 $SETS > tmp/claude/drop_ab_20261105.log 2>&1
nice -n 15 python3 tmp/wf/WfDrE/uaw2.py 4 $SETS > tmp/claude/drop_ua_20261105.log 2>&1
nice -n 15 python3 tmp/claude/measure_hardarg.py > tmp/claude/drop_hard_20261105.log 2>&1
