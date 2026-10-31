"""WfDrL: generate rewired copies (2026-10-31). usage: python3 gen.py GROUP > out"""
import re,sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrL')
from extract import blocks
D='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/'
G={
 'nc':[('V3StrictR',['arg0_take','new_rewrite_same_v','o_strict_frame','v_strict_bump']),
       ('V3MainT1F',['dep_strict0','o_r_strict0']),
       ('V3DropPres',['cl_take_vals','good3_take','rewrite_take']),
       ('V3VSRAllDrop',['frame_take_rw']),
       ('V3T1VSRAll',['frameMapT1_takeG','frameMapT1_take'])],
 'w2':[('V3MainT1D',['PO.zero_of_ne','PO.zero_of_strong']),
       ('V3T0Weak',['s1_core_weak','po_lhd_or_weak','lhd_t0_of','lhd_or_weak_t0','t0_S1W'])],
}
grp=sys.argv[1];suf={'nc':'NC','w2':'2'}[grp]
names=[n for _,ns in G[grp] for n in ns]
ren={n:n+suf for n in names}
out=[]
for f,ns in G[grp]:
    B={n:(c,t) for n,c,t in blocks(D+f+'.lean')}
    for n in ns:
        c,t=B[n]
        txt='section\n'+'\n'.join(c)+'\n'+t+'\nend\n'
        for a,b in sorted(ren.items(),key=lambda p:-len(p[0])):
            txt=re.sub(r'(?<![\w.])'+re.escape(a)+r'(?![\w\'])',b,txt)
        if grp=='nc':
            txt=re.sub(r'\bPV (?=[MN_(])','PVnc ',txt)
        else:
            txt=re.sub(r'\bPV (?=[MN_(])','PV2 ',txt)
            txt=re.sub(r'\bWCS (?=[(a-zA-Z_])','WCS2 ',txt)
        out.append('-- copied from %s.%s\n'%(f,n)+txt)
print('\n'.join(out))
