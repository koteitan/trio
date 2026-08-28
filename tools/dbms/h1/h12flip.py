# -*- coding: utf-8 -*-
"""H12: 証人 B = d2b3(T) が要求する「浅い／深い」を site ごとに逆算する。

conv3(B) != T のとき、分岐 site を 1 つずつ（足りなければ 2 つまで）ひっくり返し、
T にぴったり当たる組み合わせを探す。当たったら
    (B, off) -> 正しい shallow    が教師データ 1 行になる。
"""
import sys, pickle, itertools
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3v, inv3
from core import expand, show, isstd

bad = sorted(pickle.load(open('/tmp/h1work/img54p.pkl', 'rb')),
             key=lambda e: (len(e[0]), e[0], e[1]))
FIX, c = [], Counter()
seen = set()
for A, m, Tg in bad:
    Tg = tuple(map(tuple, Tg))
    B = inv3.d2b3([list(x) for x in Tg])
    if B is None:
        continue
    Bt = tuple(tuple(x) for x in B)
    if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
        continue
    if (Bt, Tg) in seen:
        continue
    seen.add((Bt, Tg))
    C0, S0 = rows3v.b2d3v(list(Bt))
    if C0 == Tg:
        c['素で当たる'] += 1
        continue
    br = [s for s in S0 if not s[5]]
    ties = [s for s in S0 if s[5] and s[4] != s[3]]   # base_sd で選択肢が生まれる tie
    cand = [(s[0], not s[1]) for s in br] + [(s[0], 'sd') for s in ties]
    hit = None
    for off, val in cand:
        if rows3v.b2d3v(list(Bt), {off: val})[0] == Tg:
            hit = [(off, val)]
            break
    if hit is None and len(cand) <= 14:
        for a, b in itertools.combinations(cand, 2):
            if a[0] == b[0]:
                continue
            if rows3v.b2d3v(list(Bt), dict([a, b]))[0] == Tg:
                hit = [a, b]
                break
    if hit is None:
        c['1〜2 個の反転では当たらない'] += 1
        continue
    c['%d 個の反転で当たる' % len(hit)] += 1
    for off, val in hit:
        FIX.append((Bt, off, val))
print('証人 %d 件:' % len(seen))
for k, v in c.most_common():
    print('   %-30s %d' % (k, v))
print()
print('正しい決定が分かった site %d（相異なる %d）'
      % (len(FIX), len(set((b, o) for b, o, _ in FIX))))
print('  内訳:', Counter(v for _, _, v in FIX).most_common())
pickle.dump(FIX, open('/tmp/h1work/h12fix.pkl', 'wb'))
