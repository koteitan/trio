S=/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets
for f in $S/graftBb2St.pkl $S/b2grow1.pkl $S/b2grow2.pkl $S/cbadext.pkl $S/ext2b2St.pkl $S/ext2b2.pkl $S/shapegrow.pkl /home/koteitan/proofs/trio/tmp/wf/WfB2S/graft4.pkl /home/koteitan/proofs/trio/tmp/wf/WfB2S/graft5.pkl $S/graftBb2St_g1.pkl $S/graftBb2St_x1.pkl $S/graftBb2.pkl; do
  nice -n 15 python3 probe_fail.py $f 4 | grep -v "^EX.*'o i=q"
done
