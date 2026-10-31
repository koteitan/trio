"""Aggregate new.jsonl / full.jsonl / graftU.jsonl: per field cases / failures (and failures below SRO for new fields)."""
import json, collections, sys, os
D='/home/koteitan/proofs/trio/tmp/wf/WfExQ/'
for f in ['new.jsonl','full.jsonl','graftU.jsonl']:
    if not os.path.exists(D+f): continue
    c=collections.Counter(); sets=[]
    for l in open(D+f):
        r=json.loads(l); c.update(r['cnt']); sets.append(os.path.basename(r['set']))
    print('==',f,'inputs',c['input'],'sets',sorted(set(sets)))
    fields=sorted({k.rsplit('.',1)[0] for k in c if k.endswith('.cases')})
    for k in fields:
        print('  %-10s cases %9d fail %6d fmats %5d'%(k,c[k+'.cases'],c[k+'.fail'],c[k+'.fmats']))
    for k in c:
        if 'exception' in k or 'internal' in k or 'eval_failed' in k: print('  !!',k,c[k])
