import sys,re,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
import pickle
for M in pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfQnE/seeds0.pkl','rb')):
    c,e=A.scope(list(M),(2,3,4))
    if c: print(len(M),dict(c),{k:v[1:] for k,v in e.items()})
