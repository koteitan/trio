import sys,json,re,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvX')
import audit as A
def P(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
res=json.load(open(sys.argv[1]));tag=sys.argv[2]
for k,m,info in res:
    if not k.startswith(tag):continue
    M=P(m);c,e=A.audit(M)
    fails={f[:-5]:v for f,v in c.items() if f.endswith('.fail')}
    print(len(M),k,info,'FAILS',fails,{x:c[x] for x in c if 'internal' in x or 'exception' in x or 'eval' in x})
    print('  ',m)
