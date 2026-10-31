"""Aggregate audit jsonl files into summary.json: per field cases / fail / mats / fmats, smallest standard witness
(bms -s = 1 among the kept smallest failing matrices). usage: summary.py OUT.json JSONL..."""
import sys,json,collections,subprocess
BMS='/home/koteitan/proofs/trio/bms'
def std(s):return subprocess.run([BMS,'-s',s],capture_output=True,text=True).stdout.strip()=='1'
GROUP={'SInv':['R0P','Z2','SibDec','Z1C','UAT','UAB','R12','BumpE2','R01','E00'],
 'SInvX':['R0P','R1S','Z2','R12','R01','E00','SibDec','Z1C','BumpE2','BumpLeaf'],'RowJ':['RowJ'],
 'Inv3V2':['cons','good','rank','vs','fc','fo','kd','td','ph','fc3','vra','ads','aus','tp1','tplos','tp1w','tplow','auwl','auw0','adw','trigs','tplon','adn','rootS','rootP']}
if __name__=='__main__':
    tot=collections.Counter();ex=collections.defaultdict(list);per=collections.defaultdict(collections.Counter);nmat=collections.Counter()
    for f in sys.argv[2:]:
        for l in open(f):
            r=json.loads(l);s=r['set'].split('/')[-1];nmat[s]+=r['n']
            tot.update(r['cnt']);per[s].update({k:v for k,v in r['cnt'].items() if k.endswith('.fail') or k.endswith('.cases')})
            for k,L in r['ex'].items():ex[k]+=[tuple(w) for w in L]
    fields=sorted({k.rsplit('.',1)[0] for k in tot if k.rsplit('.',1)[1] in('cases','fail','mats','fmats')})
    out={'matrices':sum(nmat.values()),'sets':dict(nmat),'other':{k:v for k,v in tot.items() if k.rsplit('.',1)[-1] not in('cases','fail','mats','fmats')},'fields':{}}
    for f in fields:
        d={k:tot.get(f+'.'+k,0) for k in('cases','fail','mats','fmats')}
        if d['fail']:
            L=sorted(set((w[0],w[1]) for w in ex.get(f,[])));d['witness']=None;d['nonstd_smaller']=0
            for n,s in L:
                if std(s):d['witness']=s;d['witness_len']=n;d['witness_info']=[w[2] for w in ex[f] if w[1]==s][0];break
                d['nonstd_smaller']+=1
            d['fail_by_set']={s:c[f+'.fail'] for s,c in per.items() if c.get(f+'.fail')}
        out['fields'][f]=d
    out['groups']={g:{'fail':sum(out['fields'].get(f,{}).get('fail',0) for f in fs)} for g,fs in GROUP.items()}
    json.dump(out,open(sys.argv[1],'w'),indent=1)
    for f,d in out['fields'].items():print(f,d['cases'],d['fail'],d['fmats'],d.get('witness_len',''))
