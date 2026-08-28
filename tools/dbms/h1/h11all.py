import sys, os, time
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import importlib
mod = importlib.import_module(sys.argv[1])
what = sys.argv[2]
import rows3
if what == 'dohyo':
    lim = int(sys.argv[3])
    A = sorted(rows3.gen3('BMS', lim, zcap=1), key=rows3.key)
    print('lim=%d %d 個' % (lim, len(A)))
    rows3.check(mod.b2d3, A, imgc=3)
elif what == 'onto':
    import onto
    onto.score(int(sys.argv[3]), f=mod.b2d3)
elif what == 'sheet':
    import sheet3
    sheet3.score(mod.b2d3, show_n=0)
