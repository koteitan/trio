#!/bin/bash
# r2_e8.pkl ができたら 9 列の全数を 4 分割で流す
D=/home/koteitan/proofs/dbms/bms2dbms/tools
until [ -f $D/r2_e8.pkl ] && grep -q "^saved" $D/r2gen8.log 2>/dev/null; do sleep 15; done
for i in 0 1 2 3; do
  timeout 7200 python3 $D/r2col9.py $i 4 > $D/r2_9_$i.log 2>&1 &
done
wait
echo ALL9DONE
