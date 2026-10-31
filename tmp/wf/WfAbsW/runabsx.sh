S=/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets
for f in graft36.pkl $S/graftBb2St.pkl $S/b2grow1.pkl $S/b2grow2.pkl $S/cbadext.pkl $S/ext2b2.pkl $S/shapegrow.pkl /home/koteitan/proofs/trio/tmp/wf/WfB2S/graft4.pkl /home/koteitan/proofs/trio/tmp/wf/WfB2S/graft5.pkl $S/graftBb2.pkl $S/Cprime.pkl; do
  nice -n 15 python3 probe_absx.py $f | cut -c1-600
done
