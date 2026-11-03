#!/usr/bin/env bash
set -eu
cd /home/koteitan/proofs/trio
exec nice -n 15 python3 -u tmp/codex/seedfo_C_facts_20261104.py --workers 3 >> tmp/codex/seedfo_C_facts_20261104.log 2>&1
