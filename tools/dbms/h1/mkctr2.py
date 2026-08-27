"""縮約を止めたり数えたりできる rows3 の写し（rows3c.py）。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", """CX = {
    'noctr': False,       # 縮約を全部止める
    'no_res': False,      # 残余ありの縮約だけ止める
    'no_rf': False,       # 残余なしの縮約だけ止める
    'max1': False,        # 縮約は 1 行列につき 1 回まで
}
CTRN = {'all': 0, 'res': 0, 'rf': 0}   # 発火の内訳（b2d3c が数える）


V12 = {""", 1)
old = """        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])"""
new = """        for e in (0, 1):
            if CX['noctr']:
                break
            if CX['max1'] and st.get('nc', 0) >= 1:
                break
            qlab = (ps[0] + e, ps[1])"""
assert src.count(old)==1
src = src.replace(old,new,1)

old = """            elif e == 0 or not deep_end:"""
new = """            if rest2 and CX['no_res']:
                continue
            if (not rest2) and CX['no_rf']:
                continue
            if False:
                pass
            elif e == 0 or not deep_end:"""
assert src.count(old)==1
src = src.replace(old,new,1)
# rest2 の判定より前に置くと未定義になるので、if rest2: ... の直後に入れ直す
src = src.replace("""            if rest2 and CX['no_res']:
                continue
            if (not rest2) and CX['no_rf']:
                continue
            if False:
                pass
            elif e == 0 or not deep_end:""",
"""            if rest2 and CX['no_res']:
                continue
            if (not rest2) and CX['no_rf']:
                continue
            if rest2:
                pass
            elif e == 0 or not deep_end:""", 1)
# もとの `if rest2:` ブロックはそのまま残っているので、二重にならないよう確認
old = """            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数"""
new = """            CTRN['all'] += 1
            CTRN['res' if rest2 else 'rf'] += 1
            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数"""
assert src.count(old)==1
src = src.replace(old,new,1)
src += '''

def b2d3c(M):
    """(像, 縮約の内訳) — CTRN を 0 に戻してから走らせる。"""
    CTRN['all'] = CTRN['res'] = CTRN['rf'] = 0
    out = b2d3(M)
    return out, dict(CTRN)
'''
open('/tmp/h1work/rows3c.py','w').write(src)
print('ok')
