"""H10 (2): 番兵 NOTLAST を落とした写し rows3n1.py と、
   本当の次の柱に置きかえた写し rows3n2.py。"""
src=open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src=src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
old="            for na in (q, NOTLAST):\n"
assert src.count(old)==1
# n1: 番兵を落とす
open('/tmp/h1work/rows3n1.py','w').write(src.replace(old,"            for na in (q,):\n",1))
# n2: 番兵のかわりに「q の木の後ろの柱」（行列から読める・写しに同変）
n2=src.replace(old,"            for na in (q, (Bq[0] if Bq else (nx if nx is not None else q))):\n",1)
open('/tmp/h1work/rows3n2.py','w').write(n2)
print('ok')
