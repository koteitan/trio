"""graft family around cex36: insert one column at any position >= 20 (keep x), plus append one column after any prefix >= 28.
Standard by bms -s. Output graft36.pkl"""
import re,pickle,subprocess,sys
from multiprocessing import Pool
B=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',open('/home/koteitan/proofs/trio/tmp/wf/WfSrcC3/cex36.txt').read())]
def mt(M): return ''.join('(%d,%d,%d)'%c for c in M)
def std(M):
    return subprocess.run(['/home/koteitan/proofs/trio/bms','-s',mt(M)],capture_output=True,text=True).stdout.strip()=='1'
cands=set()
cols=[(a,b,c) for a in range(1,16) for b in range(0,5) for c in range(0,3)]
for p in range(20,len(B)):
    for col in cols: cands.add(tuple(B[:p]+[col]+B[p:]))
for L in range(28,len(B)+1):
    for col in cols:
        if col[2]: cands.add(tuple(B[:L]+[col]))
cands=[M for M in cands if M[-1][2]!=0]
def f(M): return M if std(list(M)) else None
if __name__=='__main__':
    print(len(cands),flush=True)
    with Pool(4) as P: out=[M for M in P.map(f,cands,chunksize=64) if M]
    print(len(out))
    pickle.dump(out,open('/home/koteitan/proofs/trio/tmp/wf/WfAbsW/graft36.pkl','wb'))
