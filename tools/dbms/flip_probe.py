"""flip_data.json（後始末が出した正解ラベル）に新しい特徴を足して分離条件を探す。

flip_learn.py が行列ごと保存しているので、特徴を思いつくたびに
パイプラインを回さずにその場で採点できる。
"""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import pim, show
import rule as R

DUMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'flip_data.json')


def openers(m, x):
    """x より前の regime 開き列 (a,1,1) 型の位置（直前のアンカー以降）。"""
    b = max([q for q in range(x) if R.is_anchor1(m[q])], default=0)
    return [q for q in range(b, x)
            if len(m[q]) > 2 and m[q][2] >= 1 and m[q][1] <= m[q][2]]


def extra(d):
    m = tuple(tuple(c) for c in d['m'])
    x = d['x']
    c = m[x]
    ops = openers(m, x)
    op = ops[-1] if ops else None
    P = pim(m)
    bb = R.block_base(m, x)
    out = {
        'nest': len(ops),
        'op_a': m[op][0] if op is not None else -1,
        'c0_minus_op': (c[0] - m[op][0]) if op is not None else -99,
        'hi_bb': any(len(m[z]) > 2 and m[z][2] > 0 for z in range(bb + 1, x)),
        'bb_is_op': op is not None and bb == op,
        'br_since_op': (sum(1 for q in range(op, x) if R.is_branching(m[q]))
                        if op is not None else -1),
        'lv2_since_op': (sum(1 for q in range(op, x)
                             if len(m[q]) > 2 and m[q][1] == 2 and m[q][2] == 0)
                         if op is not None else -1),
        'nxt2_lv': (m[x + 2][1] + (10 if len(m[x + 2]) > 2 and m[x + 2][2] else 0)
                    if x + 2 < len(m) else -1),
        'p0_is_prev': P[x][0] == x - 1,
        'p1_gap': x - P[x][1] if P[x][1] >= 0 else -1,
        'tail_gap': len(m) - 1 - x,
    }
    return out


def main():
    d = json.load(open(DUMP))
    pos, neg = d['pos'], d['neg']
    print('正例 %d、負例 %d' % (len(pos), len(neg)))
    for z in pos + neg:
        z.update(extra(z))
    keys = [k for k in pos[0] if k not in ('depth', 'm', 'x')]
    atoms = []
    for k in keys:
        vs = {z[k] for z in pos} | {z[k] for z in neg}
        if len(vs) > 30:
            continue
        for v in sorted(vs, key=str):
            atoms.append((k, v))
    print('条件のかけら %d 個' % len(atoms))
    best = []
    for L in (1, 2, 3):
        for cond in itertools.combinations(atoms, L):
            if len({k for k, v in cond}) != L:
                continue
            np_ = sum(1 for z in pos if all(z[k] == v for k, v in cond))
            if np_ < 30:
                continue
            nn = sum(1 for z in neg if all(z[k] == v for k, v in cond))
            best.append((np_ / (np_ + nn), np_, nn, cond))
        if any(b[2] == 0 for b in best):
            break
    best.sort(reverse=True)
    print('純度の高い条件:')
    for pu, np_, nn, cond in best[:15]:
        print('  純度 %.3f  正 %4d / 負 %4d   %s'
              % (pu, np_, nn, ' かつ '.join('%s=%s' % kv for kv in cond)))


if __name__ == '__main__':
    main()
