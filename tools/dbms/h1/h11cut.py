import sys, time, pickle, os
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms/h1')
import importlib
from h7agree import agree
tag=sys.argv[1]; lim=int(sys.argv[2]); mod=importlib.import_module(sys.argv[3])
t0=time.time(); S=agree(mod.b2d3, lim=lim)
pickle.dump(S, open('/tmp/h1work/ag_%s_%d.pkl'%(tag,lim),'wb'))
print('%s (SBFLAGS=%s) lim=%d: |一致| = %d  (%.0fs)'%(tag,os.environ.get('SBFLAGS',''),lim,len(S),time.time()-t0))
