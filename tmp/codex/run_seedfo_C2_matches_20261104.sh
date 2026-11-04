#!/usr/bin/env bash
set -eu
cd /home/koteitan/proofs/trio
exec nice -n 15 python3 -u tmp/codex/seedfo_C2_matches_20261104.py >> tmp/codex/seedfo_C2_matches_20261104.log 2>&1
