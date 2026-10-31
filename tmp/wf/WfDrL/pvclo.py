import re,sys
E={};mod={}
for l in open('/home/koteitan/proofs/trio/tmp/wf/WfDrL/pvedges.out'):
    if not l.startswith('E '):continue
    _,m,n,rest=l.split(' ',3)
    E[n]=re.findall(r'[\w.\']+',rest);mod[n]=m
def clo(t,s):
    if t in s:return
    s.add(t)
    for d in E.get(t,[]):clo(d,s)
for t in sys.argv[1:]:
    s=set();clo('Ytosk.'+t,s)
    print(t,len(s));
    for n in sorted(s,key=lambda n:(mod.get(n,''),n)):print('   ',mod.get(n),n)
