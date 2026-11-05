#!/usr/bin/env bash
# Audit Inv3V3 (all fields, incl. the HFrameV3 frame and leaf fields) on all 86 input sets (resumable).
set -u
cd /home/koteitan/proofs/trio
SETS=$(python3 -c "import json;print(' '.join(json.load(open('tmp/codex/inv3v3_inputs_sets_20261101.json'))))")
nice -n 15 python3 tmp/wf/WfExQ/audit3.py full tmp/claude/inv3v3_audit86_20261106.jsonl 4 $SETS > tmp/claude/inv3v3_audit86_20261106.log 2>&1
