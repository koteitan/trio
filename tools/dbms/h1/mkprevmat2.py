"""st['prev'] を行列から導く値に置き換えられる写し rows3s2.py（課題 H9）。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", '''PM = {'prevmat': False}


def _prev_of(Mo, off, memo):
    """`off` より前の**同じ項の中の**直前の分岐列の綴り（0=浅い / 1=深い）。
    項の頭 `term_top` に当たったら None。位置についての整礎な再帰。"""
    for j in range(off - 1, -1, -1):
        if Mo[j][0] == 0:
            return None                  # v12 newterm と同じ切り方
        if is_branch(Mo[j]):
            sp = _spell(Mo, j, memo)
            if sp is None:
                continue                 # tie の柱は prev を書き換えない
            return 0 if sp else 1
    return None


def _spell(Mo, off, memo):
    """分岐列 Mo[off] を浅く綴るか。行列と位置だけで決まる（`nxt` は Mo[off+1]）。"""
    if off in memo:
        return memo[off]
    memo[off] = True                     # 再入の保険
    tie = memo.get('tie')
    if tie is not None and off in tie:
        memo[off] = None
        return None
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    nxt = g(off + 1); pv = g(off - 1); pv2 = g(off - 2)
    prev = _prev_of(Mo, off, memo)
    shallow = (prev == 0) or closes_unit(nxt)
    hi = hi_block2(Mo, off) if V14['h1'] else hi_block(Mo, off)
    if V14['h1']:
        if closes_top(Mo, off, nxt):
            shallow = True
        elif prev == 0:
            shallow = p0_shallow(Mo, off)
    if prev == 1 and is_w_col(pv) and closes_unit(nxt):
        pnt = off > 0 and par0(Mo, off - 1) == 0
        shallow = not (hi and not pnt)
    elif V13['wchain'] and prev == 1 and closes_unit(nxt):
        j = wchain_head(Mo, off)
        if j is not None and V14['h1'] and copy_head(Mo, j):
            j = None
        if j is not None:
            shallow = not (hi and not (par0(Mo, j) == 0))
    if closes_hi_unit(p, nxt, pv, pv2, hi, is_repeat(Mo, off)):
        shallow = True
    memo[off] = shallow
    return shallow


V12 = {''', 1)
old = """            st['rec'][off] = st['prev']
            shallow = (st['prev'] == 0) or closes_unit(nxt)"""
new = """            st['rec'][off] = st['prev']
            if PM['prevmat']:
                st['prev'] = _prev_of(Mo0, off, st.setdefault('spmemo', {}))
            shallow = (st['prev'] == 0) or closes_unit(nxt)"""
assert src.count(old)==1
src = src.replace(old,new,1)
# Mo は下で定義されるので、先に別名を用意する
src = src.replace("""            st['rec'][off] = st['prev']
            if PM['prevmat']:""",
"""            Mo0 = st['Mo']
            st['rec'][off] = st['prev']
            if PM['prevmat']:""", 1)
open('/tmp/h1work/rows3t2.py','w').write(src)
print('ok')
