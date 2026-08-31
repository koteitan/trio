"""深さ 1 ビットの「正解ラベル」を集める。

いまの規則はシート全 1621 行を再現するので、その深さ割り当ては正解の一つ。
各分岐列のビットを 1 つずつ反転して出力が真値から外れるかを見れば、
その地点が「1 でなければならない / 0 でなければならない / どちらでもよい」の
どれかが分かる。強制されている地点だけを学習データにする。
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
from core import pim, show
import rule as R


def features(m, x, ds):
    """分岐列 x の文脈を、意味のある名前つきの特徴に落とす。"""
    c = m[x]
    nxt = m[x + 1] if x + 1 < len(m) else None
    pv = m[x - 1] if x > 0 else None
    pv2 = m[x - 2] if x > 1 else None
    P = pim(m)

    def rel(a):
        if a is None:
            return 'なし'
        if a[0] == c[0] + 1:
            return '+1'
        if a[0] == c[0]:
            return '同'
        if a[0] > c[0] + 1:
            return '飛び'
        return '戻り'

    def lv(a):
        if a is None:
            return -1
        return a[1] + (10 if len(a) > 2 and a[2] > 0 else 0)

    prevd = None
    for q in range(x - 1, -1, -1):
        if R.is_anchor1(m[q]):
            prevd = 0
            break
        if R.is_branching(m[q]):
            prevd = ds[q]
            break
    return {
        'nxt_rel': rel(nxt),
        'nxt_lv': lv(nxt),
        'nxt_anchor1': nxt is not None and R.is_anchor1(nxt),
        'nxt_full': nxt is not None and len(nxt) > 2 and nxt[:3] == (1, 1, 1),
        'nxt_base': nxt is not None and len(nxt) > 2 and nxt[0] <= 1 and nxt[2] == 0,
        'pv_rel': rel(pv),
        'pv_lv': lv(pv),
        'pv2_rel': rel(pv2),
        'pv2_lv': lv(pv2),
        'prev': prevd,
        'hi': R.hi_block(m, x),
        'spent': R.spent_level(m, x, c[1] + 1),
        'rep': R.is_repeat(m, x),
        'p1_root': P[x][1] == 0,
        'first_br': not any(R.is_branching(m[q]) for q in range(x)),
    }


def collect(Y=3):
    out = []
    for r, mb, md, y in load():
        if y != Y:
            continue
        ds = R.depths(mb)
        if R.dedup(R._stair(mb, Y, lambda x, c: ds[x])) != md:
            continue          # 規則の経路が違う行（strip_lift 等）は除く
        br = [x for x, c in enumerate(mb) if R.is_branching(c)]
        for i in br:
            e = list(ds); e[i] ^= 1
            try:
                W = R.dedup(R._stair(mb, Y, lambda x, c, e=e: e[x]))
            except Exception:
                W = None
            forced = (W != md)
            out.append({'row': r['row'], 'x': i, 'depth': ds[i],
                        'forced': forced, **features(mb, i, ds)})
    return out


if __name__ == '__main__':
    import collections
    D = collect(3) + collect(2) + collect(1)
    print('地点 %d、うち強制 %d' % (len(D), sum(1 for d in D if d['forced'])))
    F = [d for d in D if d['forced']]
    print('強制のうち 深い %d / 浅い %d'
          % (sum(1 for d in F if d['depth'] == 1), sum(1 for d in F if d['depth'] == 0)))
    json.dump(D, open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   'depth_data.json'), 'w'))
    # 単独の特徴でどれだけ分かれるか
    for k in ('nxt_rel', 'nxt_lv', 'nxt_anchor1', 'nxt_full', 'nxt_base',
              'pv_rel', 'pv_lv', 'prev', 'hi', 'spent', 'rep', 'p1_root', 'first_br'):
        t = collections.Counter((d[k], d['depth']) for d in F)
        keys = sorted({a for a, b in t}, key=str)
        line = '  '.join('%s:%d/%d' % (a, t[(a, 1)], t[(a, 0)]) for a in keys)
        print('%-12s %s' % (k, line))
