"""prev==0 の枝を `term_top(Mo, off+1)` に置き換える写し rows3m.py（課題 H6）。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", '''MX = {'tt': False, 'tt2': False}


def p0_shallow(Mo, off):
    """`prev == 0` の枝: 浅く綴るか。**次の柱が「行 1 の加算項の頭」なら浅い。**

    課題 H6。教師データ（シート ＋ ImgClosedT の目標、`prev == 0` の枝 6480 本）で
    **食い違い 0**。ホールドアウト検定（半分で当てはめ、もう半分で測る）でも
    正例 1257/1257、負例 1972 本に誤発火 0。
    """
    if off + 1 >= len(Mo) or term_top(Mo, off + 1):
        return True
    if MX['tt2'] and not any(copy_head(Mo, t) for t in range(off)):
        return True          # 写しの頭が前に 1 つも無いなら浅い（課題 H7）
    return False


V12 = {''', 1)
old = """                if cw:
                    shallow = True
                elif st['prev'] == 0 and not closes_unit(nxt):
                    _w0 = p0deep_ok(Mo, off, p, nxt)
                    shallow = not _w0"""
new = """                if (MX['tt'] or MX['tt2']) and st['prev'] == 0:
                    _w0 = not p0_shallow(Mo, off)
                    shallow = not _w0
                elif cw:
                    shallow = True
                elif st['prev'] == 0 and not closes_unit(nxt):
                    _w0 = p0deep_ok(Mo, off, p, nxt)
                    shallow = not _w0"""
assert src.count(old)==1, src.count(old)
src = src.replace(old,new,1)
open('/tmp/h1work/rows3o.py','w').write(src)
print('ok')
