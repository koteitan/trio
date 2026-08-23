"""深さ規則の例外節を探す。

「末尾列（nxt=None）は浅い」「それ以外は深い」の 2 分岐に例外を足す候補を
小さな文法から並べ、まず「深さビットが変わる行数」で粗く篩い、
少数しか動かさないものだけシート全体で測る。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
import rule as R

DS = {Y: [x for x in load() if x[3] == Y] for Y in (1, 2, 3)}


def ctx(m, x):
    c = m[x]
    return (c,
            m[x + 1] if x + 1 < len(m) else None,
            m[x - 1] if x > 0 else None)


def is_w(c):        # 「×w」の列 (k,0,0), k>=1
    return c is not None and len(c) > 1 and c[1] == 0 and c[0] >= 1


def full_anchor(c):  # (1,1,1) のようにすべての行が 1
    return c is not None and len(c) > 2 and c[0] == 1 and c[1] == 1 and c[2] == 1


def hi_block(m, x):
    """x の属するブロック（直前のアンカー以降）に行 2 を使う列があるか。
    W_(w^2) 系の regime にいるかどうかの目印。"""
    b = max([q for q in range(x)
             if len(m[q]) > 1 and m[q][0] == m[q][1] and m[q][0] >= 1], default=0)
    return any(len(m[z]) > 2 and m[z][2] > 0 for z in range(b + 1, x))


E1 = {   # nxt=None のとき深くする条件
    'なし': lambda c, nx, pv, pr, m=None, x=None: False,
    'prev=1 & 前が(k,0,0)': lambda c, nx, pv, pr, m=None, x=None: pr == 1 and is_w(pv),
    '前が(k,0,0)': lambda c, nx, pv, pr, m=None, x=None: is_w(pv),
    'prev=1': lambda c, nx, pv, pr, m=None, x=None: pr == 1,
    'prev=1 & 前が(k,0,0) & c=(2,1,0)': lambda c, nx, pv, pr, m=None, x=None: pr == 1 and is_w(pv) and c[0] == 2,
    'prev=1 & 高ブロック': lambda c, nx, pv, pr, m=None, x=None: pr == 1 and hi_block(m, x),
    '高ブロック': lambda c, nx, pv, pr, m=None, x=None: hi_block(m, x),
    'prev=1 & 前が(k,0,0) & 高ブロック': lambda c, nx, pv, pr, m=None, x=None: pr == 1 and is_w(pv) and hi_block(m, x),
}
E2 = {   # ふつう深いところを浅くする条件
    'なし': lambda c, nx, pv, pr, m=None, x=None: False,
    '次が(1,1,1)': lambda c, nx, pv, pr, m=None, x=None: full_anchor(nx),
    '次が(1,1,1) & 前が(k,2,0)': lambda c, nx, pv, pr, m=None, x=None: full_anchor(nx) and pv is not None and len(pv) > 2 and pv[1] == 2 and pv[2] == 0,
    '次が(1,1,1) & 前が(c0,2,0)': lambda c, nx, pv, pr, m=None, x=None: full_anchor(nx) and pv is not None and len(pv) > 2 and pv[1] == 2 and pv[2] == 0 and pv[0] == c[0],
    '次が(1,1,1) & prev=1': lambda c, nx, pv, pr, m=None, x=None: full_anchor(nx) and pr == 1,
    '次が(1,1,1) & 高ブロック': lambda c, nx, pv, pr, m=None, x=None: full_anchor(nx) and hi_block(m, x),
    '次が(1,1,1) & 高ブロック & 前が(c0,2,0)': lambda c, nx, pv, pr, m=None, x=None: full_anchor(nx) and hi_block(m, x) and pv is not None and len(pv) > 2 and pv[1] == 2 and pv[2] == 0 and pv[0] == c[0],
}


def depths(m, e1, e2):
    """e1/e2 は (c, nxt, pv, prev, m, x) を受ける"""
    prev = [None]; out = []
    for x, c in enumerate(m):
        if R.is_anchor1(c):
            prev[0] = 0
        if not R.is_branching(c):
            out.append(None); continue
        nx, pv = ctx(m, x)[1], ctx(m, x)[2]
        pr = prev[0]
        if pr == 0:
            v = 0
        elif nx is None:
            v = 1 if e1(c, nx, pv, pr, m, x) else 0
        elif R.is_anchor1(nx):
            v = 0
        elif pr is None and pv is not None and len(pv) > 1 and pv[1] == 0 and pv[0] >= 1:
            v = 0
        else:
            v = 0 if e2(c, nx, pv, pr, m, x) else 1
        prev[0] = v; out.append(v)
    return out


def conv(m, Y, e1, e2):
    m2, n = R.strip_lift(m)
    if n and m2 and R.is_branching(m2[-1]):
        return R.dedup(R._stair(m2, Y, lambda x, c: 1 if R.is_branching(c) else 0,
                                relay=False))
    ds = depths(m, e1, e2)
    return R.dedup(R._stair(m, Y, lambda x, c: ds[x] or 0))


def moved(e1, e2):
    base = (E1['なし'], E2['なし'])
    n = 0
    for r, mb, md, _ in DS[3]:
        if depths(mb, e1, e2) != depths(mb, *base):
            n += 1
    return n


if __name__ == '__main__':
    PICK1 = ['なし', 'prev=1 & 高ブロック', '高ブロック', 'prev=1 & 前が(k,0,0) & 高ブロック']
    PICK2 = ['なし', '次が(1,1,1) & 高ブロック', '次が(1,1,1) & 高ブロック & 前が(c0,2,0)']
    for n1 in PICK1:
        e1 = E1[n1]
        for n2 in PICK2:
            e2 = E2[n2]
            if n1 == 'なし' and n2 == 'なし':
                continue
            mv = moved(e1, e2)
            if mv > 60:
                print('%-32s %-28s 動く行 %d (多すぎ、測定省略)' % (n1, n2, mv)); continue
            tot = okall = 0; res = []
            for Y in (1, 2, 3):
                ok = sum(1 for r, mb, md, _ in DS[Y] if conv(mb, Y, e1, e2) == md)
                tot += len(DS[Y]); okall += ok; res.append('Y%d %d/%d' % (Y, ok, len(DS[Y])))
            print('%-32s %-28s 動く行 %-4d %s 合計 %d/%d' % (n1, n2, mv, ' '.join(res), okall, tot))
