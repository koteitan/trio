import json,collections,sys
t=collections.Counter();ex={}
for l in open(sys.argv[1]):
  d=json.loads(l);t.update(d['cnt'])
  for k,v in d['ex'].items():
    if k not in ex or v[0]<ex[k][0]:ex[k]=v
keys=sorted(t)
print({k:t[k] for k in keys})
for k,v in ex.items():print(k,str(v)[:300])
