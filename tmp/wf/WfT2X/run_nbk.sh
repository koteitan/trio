A=/home/koteitan/proofs/trio/tmp/wf/WfAbsW; R=/home/koteitan/proofs/trio/tmp/wf/WfReM
for f in $A/graft36.pkl $A/graft36b.pkl $A/graft36c.pkl $R/graftM36.pkl $R/graftM36x.pkl; do
  nice -n 15 python3 /home/koteitan/proofs/trio/tmp/wf/WfT2X/probe_nbk.py $f
done
