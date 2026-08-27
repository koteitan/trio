import sys, time, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms/h1')
import importlib
from h7agree import agree
name=sys.argv[1]; lim=int(sys.argv[2])
mod = importlib.import_module('rows3' if name=='base' else 'rows3'+name)
t0=time.time(); S=agree(mod.b2d3, lim=lim)
pickle.dump(S, open('/tmp/h1work/ag_%s_%d.pkl'%(name,lim),'wb'))
print('%s lim=%d: |一致| = %d  (%.0fs)'%(name,lim,len(S),time.time()-t0))
