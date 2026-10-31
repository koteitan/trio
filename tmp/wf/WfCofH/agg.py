import json,glob,collections,sys
S=collections.Counter(); EX={}
for f in glob.glob(sys.argv[1]+'/*.json'):
    d=json.load(open(f))
    for k,v in d['stats'].items(): S[k]+=v
    for k,v in d['ex'].items():
        if k not in EX or len(v[0])<len(EX[k][0]): EX[k]=v
for k,v in sorted(S.items()): print(k,v)
for k,v in EX.items(): print('EX',k,v[1:],v[0][:300])
