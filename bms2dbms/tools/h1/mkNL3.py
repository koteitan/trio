"""H10 (2b): 番兵を「写しの本当の次の柱」に置きかえる。

`pre` の長さは `1+len(A)+len(U)` で `na` に依らない（copy_shift はブロックを
1 対 1 に写す）ので、写しの終わりの次の柱は `na` を決める前に読める:
    _L = 1 + len(A) + len(U)
    na_real = Aq[_L] if _L < len(Aq) else (Bq[0] if Bq else nx)
これは行列だけから読めるので**写しに同変**。
"""
src=open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src=src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
old="            for na in (q, NOTLAST):\n"
assert src.count(old)==1
DEF=("            _L = 1 + len(A) + len(U)\n"
     "            _nr = (Aq[_L] if _L < len(Aq)\n"
     "                   else (Bq[0] if Bq else nx))\n")
open('/tmp/h1work/rows3n3.py','w').write(
    src.replace(old, DEF+"            for na in ((q, _nr) if _nr is not None else (q, NOTLAST)):\n",1))
open('/tmp/h1work/rows3n4.py','w').write(
    src.replace(old, DEF+"            for na in ((_nr,) if _nr is not None else (q,)):\n",1))
open('/tmp/h1work/rows3n5.py','w').write(
    src.replace(old, DEF+"            for na in ((q, _nr, NOTLAST) if _nr is not None else (q, NOTLAST)):\n",1))
print('ok')
