import json,sys
for l in open(sys.argv[1]):
    d=json.loads(l);print(d['set'],d['n'],d['sec'],'measured',d['cnt'].get('n'))
    print('  ',{k:v for k,v in d['cnt'].items() if 'FAIL' in k or 'B2X' in k or 'exc' in k or 'side' in k or k=='ua.cases'})
    if len(sys.argv)>2:
        for k,v in d['ex'].items():print('   EX',k,v[0],v[1][-120:],v[2][:150])
