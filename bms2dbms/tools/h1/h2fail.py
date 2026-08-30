import sys, pickle, time
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, inv3, imgfast
lim=int(sys.argv[1]); mm=int(sys.argv[2]); jobs=int(sys.argv[3]) if len(sys.argv)>3 else 4
A=sorted(rows3.gen3('BMS',lim,zcap=1), key=rows3.key)
t0=time.time()
ok,tot,bad = imgfast.imgclosed_fast(rows3.b2d3, A, mm, inv3.d2b3, jobs=jobs)
print('lim=%d m<=%d  逆像あり %d/%d  破れた A %d 個  %.0fs' % (lim,mm,ok,tot,len(bad),time.time()-t0))
pickle.dump(sorted(bad, key=rows3.key), open('/tmp/h1work/fail%d_%d.pkl'%(lim,mm),'wb'))
