"""縮約を lad0 から切り離して試せる写し rows3i.py。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", """GX = {
    'nolad0': False,     # lad0 が立たなくても縮約を試す
    'nolad0_v': False,   # 同上、ただし v == ps[0] + 1 のときだけ（first だけ外す）
    'nolad0_f': False,   # 同上、ただし first のときだけ（v の条件だけ外す）
}
CTRN2 = {'n': 0}


V12 = {""", 1)
old = "    if lad0:\n        for e in (0, 1):"
new = """    _try = lad0
    if not _try:
        if GX['nolad0']:
            _try = True
        elif GX['nolad0_v'] and v == ps[0] + 1:
            _try = True
        elif GX['nolad0_f'] and first:
            _try = True
    if _try:
        for e in (0, 1):"""
assert src.count(old)==1, src.count(old)
src = src.replace(old,new,1)
src = src.replace("            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数",
                  "            CTRN2['n'] += 1\n            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数",1)
open('/tmp/h1work/rows3i.py','w').write(src)
print('ok')
