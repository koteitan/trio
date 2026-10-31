"""Build the derived set: every family member M, M[2], M[3] (tools/trio.expand), and all their prefixes (len >= 2), deduped.
usage: fam.py OUT.pkl  (counts only with --count)"""
import sys,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
W='/home/koteitan/proofs/trio/tmp/wf/'
FAMS=['WfReM/graftM36.pkl','WfReM/graftM36x.pkl','WfB2L/lift1.pkl','WfB2L/lift2.pkl','WfB2L/g36_1.pkl','WfB2L/g36_2.pkl',
 'WfSib/hunt_found.pkl','WfAbsW/graft36.pkl','WfAbsW/graft36b.pkl','WfAbsW/graft36c.pkl','WfAbsW/cex36.pkl',
 'WfB2S/graft4.pkl','WfB2S/graft5.pkl','WfH7W2/graft2.pkl','WfH7W2/graft3.pkl']
if __name__=='__main__':
    members=set();exp=set();allp=set();st=collections.Counter()
    for f in FAMS:
        for M in pickle.load(open(W+f,'rb')):members.add(tuple(tuple(c) for c in M))
    for M in members:
        for n in (2,3):
            try:N=tuple(tuple(c) for c in trio.expand([list(c) for c in M],n))
            except Exception as e:st['expand_err']+=1;continue
            exp.add(N)
    for N in members|exp:
        for j in range(2,len(N)+1):allp.add(N[:j])
    allp-=members
    st.update(members=len(members),expansions=len(exp),prefixes_new=len(allp),
              cols=sum(len(N) for N in allp),maxlen=max(len(N) for N in allp))
    print(dict(st))
    if sys.argv[1]!='--count':
        pickle.dump(sorted(allp,key=lambda N:(len(N),N)),open(sys.argv[1],'wb'))
