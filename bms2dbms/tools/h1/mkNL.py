"""H10 (2): 縮約が番兵 NOTLAST を選んだ場所を記録する写し rows3N.py。"""
src=open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src=src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src=src.replace("V12 = {","NLREC = []\n\n\nV12 = {",1)
old="            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数\n"
new=("            _real = (rest2[0] if rest2 else (Bq[0] if Bq else nx))\n"
     "            NLREC.append(dict(off=off, sent=(na == NOTLAST), na=tuple(na),\n"
     "                              real=(tuple(_real) if _real is not None else None),\n"
     "                              rest=bool(rest2), e=e,\n"
     "                              cu_na=closes_unit(na),\n"
     "                              cu_real=closes_unit(_real),\n"
     "                              br_na=is_branch(na),\n"
     "                              br_real=is_branch(_real) if _real else None,\n"
     "                              w_na=is_w_col(na),\n"
     "                              w_real=is_w_col(_real) if _real else None))\n"
     + old)
assert src.count(old)==1
src=src.replace(old,new,1)
src+='''

def b2d3N(M):
    del NLREC[:]
    st={'ST':(),'prev':None,'dmap':[],'Mo':tuple(M),'nc':0,'rec':{}}
    out=tuple(conv3(list(M), st=st))
    return out, list(NLREC)
'''
open('/tmp/h1work/rows3N.py','w').write(src)
print('ok')
