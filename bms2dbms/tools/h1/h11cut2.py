import sys, time, pickle, os
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
import importlib
from h7agree import agree
tag=sys.argv[1]; lim=int(sys.argv[2]); mod=importlib.import_module(sys.argv[3])
nm=int(sys.argv[4]); mm=int(sys.argv[5])
t0=time.time(); S=agree(mod.b2d3, lim=lim, nmax=nm, mmax=mm)
pickle.dump(S, open('/tmp/h1work/ag2_%s.pkl'%tag,'wb'))
print('%s lim=%d n<=%d m<=%d: |一致| = %d  (%.0fs)'%(tag,lim,nm,mm,len(S),time.time()-t0))
