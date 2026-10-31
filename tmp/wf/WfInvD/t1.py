import sys,re,json;sys.path.insert(0,'.');import invd
for s in sys.argv[1:]:
    M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
    c,e=invd.probe(M);print(dict(c));print(json.dumps(e,indent=0))
