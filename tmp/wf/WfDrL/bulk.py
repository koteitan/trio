"""WfDrL: bulk PV2 copies of the live PV consumers (2026-10-31).
Selects every live constant whose type mentions PV (pvdeps.out), minus the drop lemma itself (producers),
structure projections/constructors, and what WfDrL1/2 already cover; orders modules topologically.
usage: python3 bulk.py > body.lean   (also writes bulk_list.txt)"""
import re,os,sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrL')
from extract import blocks
D='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/';W='/home/koteitan/proofs/trio/tmp/wf/WfDrL/'
PROD={'V3DropMain','V3DropStrong','V3BumpDrop','V3BumpDropB','V3DropH','V3DropR','V3DropResHB'}
SKIP={'PV.le','PV.eq_1','WCSP.wcs','T2AbsNWeak.weak_of_drop_failure','PO.zero_of_strong','PO.zero_of_ne','po_lhd_or_weak','lhd_t0_of','lhd_or_weak_t0','t1_drop_of_fields','g0_drop_rel','qr_dropSeed','StepCtxB.hdrop','hdrop_of_U','t2_drop_ctx'}
DONE2={'PO.zero_of_strong','PO.zero_of_ne','po_lhd_or_weak','lhd_t0_of','lhd_or_weak_t0','s1_core_weak','t0_S1W'}
live=[]
for l in open(W+'pvdeps.out'):
    if not l.startswith('PVLIVE'):continue
    _,m,n,t,r=l.split()
    m=m.replace('Ytosk.','');n=n.replace('Ytosk.','',1)
    if m in PROD or n in SKIP or n.endswith('.mk') or t!='type=true':continue
    live.append((m,n))
imp={}
for f in os.listdir(D):
    if f.endswith('.lean'):imp[f[:-5]]=re.findall(r'^import Ytosk\.(\w+)',open(D+f).read(),re.M)
order=[];seen=set()
def topo(m):
    if m in seen:return
    seen.add(m)
    for i in imp.get(m,[]):topo(i)
    order.append(m)
for m,_ in live:topo(m)
mods=[m for m in order if any(mm==m for mm,_ in live)]
names=[n for _,n in live]
ren={n:n+'2' for n in names+sorted(DONE2)}
out=[];miss=[]
for m in mods:
    B={}
    for n,c,t in blocks(D+m+'.lean'):B[n]=(c,t)
    ns=[n for mm,n in live if mm==m]
    # keep file order
    fo=[n for n,_,_ in blocks(D+m+'.lean')]
    ns.sort(key=lambda n:fo.index(n.split('.')[-1]) if n.split('.')[-1] in fo else (fo.index(n) if n in fo else 10**6))
    for n in ns:
        key=n if n in B else (n.split('.',1)[1] if '.' in n and n.split('.',1)[1] in B else None)
        if key is None:miss.append((m,n));continue
        c,t=B[key]
        txt='section\n'+'\n'.join(c)+'\n'+t+'\nend\n'
        for a,b in sorted(ren.items(),key=lambda p:-len(p[0])):
            short=a.split('.')[-1] if a.startswith(('T2UpgAbs.','T0UpgAbs.','T2AbsNWeak.','T0SeedOutside.','WfH7W.','G.')) else a
            if short!=a:txt=re.sub(r'(?<![\w])'+re.escape(a)+r'(?![\w\'])',b,txt)
            txt=re.sub(r'(?<![\w.])'+re.escape(short)+r'(?![\w\'])',b.split('.')[-1] if short!=a else b,txt)
        txt=re.sub(r'\bPV (?=[MN_(])','PV2 ',txt)
        txt=re.sub(r'\bPV\.le\b','PV2.le',txt)
        ns_=re.search(r'^namespace Ytosk\.(\w+)',open(D+m+'.lean').read(),re.M)
        if ns_:txt='namespace %s\nopen T\n'%ns_.group(1)+txt+'end %s\n'%ns_.group(1)
        out.append('-- copied from %s.%s\n'%(m,n)+txt)
open(W+'bulk_list.txt','w').write('\n'.join('%s %s'%x for x in live)+'\nMISSING '+repr(miss)+'\n')
print('\n'.join(out))
