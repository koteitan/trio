"""深さ規則の述語を 1 つずつ外したり緩めたりして、本当に要るものを見る。

各変種でシートとの一致数を測る。落ちなければその述語は不要（か、もっと緩くてよい）。
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
import rule as R

DS = {Y: [x for x in load() if x[3] == Y] for Y in (1, 2, 3)}
NAMES = ['closes_unit', 'tail_of_hi_unit', 'ladder_spent', 'fresh_after_w',
         'closes_hi_unit']


def make(off=(), gen=()):
    """off: 外す述語名。gen: 緩める指定 (名前, 版)。"""
    def rule(c, nxt, prev, pv, hi, pv2, rep, spent):
        if not R.is_branching(c):
            return 0
        if prev == 0:
            return 0
        if 'closes_unit' not in off and R.closes_unit(nxt):
            if not ('tail_of_hi_unit' not in off
                    and R.tail_of_hi_unit(nxt, pv, hi, prev)):
                return 0
        if 'ladder_spent' not in off:
            if ('ladder_spent_loose' in gen):
                if (spent and nxt is not None and len(nxt) > 2
                        and nxt[0] <= c[0] + 1 and nxt[1] <= 1 and nxt[2] == 0):
                    return 0
            elif R.ladder_spent(c, nxt, pv, spent):
                return 0
        if 'fresh_after_w' not in off and R.fresh_after_w(prev, pv):
            return 0
        if 'closes_hi_unit' not in off:
            if 'closes_hi_unit_loose' in gen:
                if (hi and not rep and nxt is not None and len(nxt) > 2
                        and nxt[:3] == (1, 1, 1) and R.is_lv2_col(pv)):
                    return 0
            elif R.closes_hi_unit(c, nxt, pv, pv2, hi, rep):
                return 0
        return 1

    def depths(m):
        prev = [None]; out = []
        for x, c in enumerate(m):
            if R.is_anchor1(c):
                prev[0] = 0
            if not R.is_branching(c):
                out.append(0); continue
            v = rule(c, m[x + 1] if x + 1 < len(m) else None, prev[0],
                     m[x - 1] if x > 0 else None, R.hi_block(m, x),
                     m[x - 2] if x > 1 else None, R.is_repeat(m, x),
                     R.spent_level(m, x, c[1] + 1))
            prev[0] = v; out.append(v)
        return out

    def conv(m, Y):
        m2, n = R.strip_lift(m)
        if n and m2 and R.is_branching(m2[-1]):
            return R.dedup(R._stair(m2, Y, lambda x, c: 1 if R.is_branching(c) else 0,
                                    relay=False))
        ds = depths(m)
        return R.dedup(R._stair(m, Y, lambda x, c: ds[x]))
    return conv


def score(conv):
    tot = ok = 0
    for Y in (1, 2, 3):
        for r, mb, md, _ in DS[Y]:
            tot += 1
            try:
                ok += (conv(mb, Y) == md)
            except Exception:
                pass
    return ok, tot


if __name__ == '__main__':
    base = score(make())
    print('基準（全部あり） %d/%d' % base)
    print()
    print('--- 1 つ外す ---')
    for n in NAMES:
        s = score(make(off=(n,)))
        print('  %-16s なし -> %d/%d  (%+d)' % (n, s[0], s[1], s[0] - base[0]))
    print()
    print('--- 緩める ---')
    for g in ('ladder_spent_loose', 'closes_hi_unit_loose'):
        s = score(make(gen=(g,)))
        print('  %-24s -> %d/%d  (%+d)' % (g, s[0], s[1], s[0] - base[0]))
    print()
    print('--- 2 つ外す（減らなかった組だけ）---')
    for a, b in itertools.combinations(NAMES, 2):
        s = score(make(off=(a, b)))
        if s[0] >= base[0]:
            print('  %s + %s なし -> %d/%d' % (a, b, s[0], s[1]))


def make2(variant='unified'):
    """「×w の直後」を 1 本にまとめた版を試す。"""
    def rule(c, nxt, prev, pv, hi, pv2, rep, spent):
        if not R.is_branching(c):
            return 0
        if prev == 0:
            return 0
        if variant == 'unified' and R.is_w_col(pv):
            # ×w は段を上げない。ただし W_(w^2) 系では ×w が段の上に乗るので段は残る。
            return 1 if hi else 0
        if variant == 'unified2' and R.is_w_col(pv) and (prev is None or nxt is None):
            return 1 if hi else 0
        if R.closes_unit(nxt):
            return 0
        if R.ladder_spent(c, nxt, pv, spent):
            return 0
        if R.closes_hi_unit(c, nxt, pv, pv2, hi, rep):
            return 0
        return 1

    def depths(m):
        prev = [None]; out = []
        for x, c in enumerate(m):
            if R.is_anchor1(c):
                prev[0] = 0
            if not R.is_branching(c):
                out.append(0); continue
            v = rule(c, m[x + 1] if x + 1 < len(m) else None, prev[0],
                     m[x - 1] if x > 0 else None, R.hi_block(m, x),
                     m[x - 2] if x > 1 else None, R.is_repeat(m, x),
                     R.spent_level(m, x, c[1] + 1))
            prev[0] = v; out.append(v)
        return out

    def conv(m, Y):
        m2, n = R.strip_lift(m)
        if n and m2 and R.is_branching(m2[-1]):
            return R.dedup(R._stair(m2, Y, lambda x, c: 1 if R.is_branching(c) else 0,
                                    relay=False))
        ds = depths(m)
        return R.dedup(R._stair(m, Y, lambda x, c: ds[x]))
    return conv
