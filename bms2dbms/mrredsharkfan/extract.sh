#!/bin/bash
# MrredsharkFan/w-Y-global-lngi の conv.js から bmsToDbms / dbmsToBms の IIFE だけ抜く。
# 使い方: ./extract.sh ~/proofs/w-Y-global-lngi/conv.js > core.js
awk '/\(function\(\) *\{/ {s=NR; buf=""}
     s {buf = buf $0 "\n"}
     /window\.bmsToDbms/ {found=1}
     found && /^\}\)\(\);|^ *\}\)\(\);/ {printf "%s", buf; exit}' "$1"
