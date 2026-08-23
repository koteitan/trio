"""深さ規則の変種を総当たりで測る調査スクリプト。

depth_rule の各分岐（末尾列の扱い／アンカー判定の緩さ）を差し替えて、
BM4-Analysis シートに対する一致数を比べる。
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
import rule as R

DS = {Y: [x for x in load() if x[3] == Y] for Y in (1, 2, 3)}


def make(tail, loose):
    """tail: 末尾列の深さ (0 / 'prev')   loose: 次列のアンカー判定を緩めるか"""
    def anch(c):
        if loose:
            return len(c) > 1 and c[0] == 1 and c[1] == 1
        return R.is_anchor1(c)

    def rule(c, nxt, prev, pv):
        if not R.is_branching(c):
            return 0
        if prev == 0:
            return 0
        if nxt is None:
            return 0 if tail == 0 else (1 if prev == 1 else 0)
        if anch(nxt):
            return 0
        if prev is None and pv is not None and len(pv) > 1 and pv[1] == 0 and pv[0] >= 1:
            return 0
        return 1

    def f(m, Y):
        m2, n = R.strip_lift(m)
        if n and m2 and R.is_branching(m2[-1]):
            return R.dedup(R._stair(m2, Y, lambda x, c: 1 if R.is_branching(c) else 0,
                                    relay=False))
        prev = [None]

        def dep(x, c):
            if R.is_anchor1(c):
                prev[0] = 0
            if not R.is_branching(c):
                return 0
            v = rule(c, m[x + 1] if x + 1 < len(m) else None, prev[0],
                     m[x - 1] if x > 0 else None)
            prev[0] = v
            return v
        return R.dedup(R._stair(m, Y, dep))
    return f


if __name__ == '__main__':
    for tail, loose in itertools.product((0, 'prev'), (False, True)):
        f = make(tail, loose)
        tot = okall = 0; res = []
        for Y in (1, 2, 3):
            ok = sum(1 for r, mb, md, _ in DS[Y] if f(mb, Y) == md)
            tot += len(DS[Y]); okall += ok; res.append('Y%d %d/%d' % (Y, ok, len(DS[Y])))
        print('末尾=%-5s 緩アンカー=%-5s %s 合計 %d/%d'
              % (tail, loose, ' '.join(res), okall, tot))
