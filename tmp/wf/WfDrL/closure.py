"""WfDrL: import closure of PV-mentioning files below given targets (2026-10-31)."""
import re,os,sys
D='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/'
imp={};pv={};ln={}
for f in os.listdir(D):
    if not f.endswith('.lean'):continue
    n=f[:-5];s=open(D+f).read()
    imp[n]=re.findall(r'^import Ytosk\.(\w+)',s,re.M)
    code=re.sub(r'/-.*?-/','',s,flags=re.S);code=re.sub(r'--.*','',code)
    pv[n]=bool(re.search(r'\bPV\b|\bPV\.|WCSP|WeakCS\b',code));ln[n]=s.count('\n')
def clo(t,seen):
    if t in seen or t not in imp:return
    seen.add(t)
    for i in imp[t]:clo(i,seen)
for t in sys.argv[1:]:
    s=set();clo(t,s)
    c=sorted(x for x in s if pv[x])
    print(t,len(c),sum(ln[x] for x in c),c)
