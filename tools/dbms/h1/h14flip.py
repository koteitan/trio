# -*- coding: utf-8 -*-
"""H14 (2): 残る 18 個の証人が要求する「浅い／深い」を site ごとに逆算する。"""
import sys, pickle, itertools
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, rows3v, provc, inv3
from core import expand, show, isstd

cof = set(tuple(map(tuple, A)) for A in
          pickle.load(open('/tmp/h1work/cof6.pkl', 'rb')))
bad = [e for e in pickle.load(open('/tmp/h1work/img54p.pkl', 'rb'))
       if tuple(map(tuple, e[0])) in cof]
FIX, c = [], Counter()
seen = set()
for A, m, Tg in bad:
    Tg = tuple(map(tuple, Tg))
    B = inv3.d2b3([list(x) for x in Tg])
    if B is None:
        continue
    Bt = tuple(tuple(x) for x in B)
    if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt) or (Bt, Tg) in seen:
        continue
    seen.add((Bt, Tg))
    C0, S0 = rows3v.b2d3v(list(Bt))
    if C0 == Tg:
        c['素で当たる'] += 1
        continue
    C, PR = provc.b2d3p(list(Bt))
    whyof = {}
    for e in PR:
        if e[2]:
            whyof[e[1]] = str(e[2])
    br = [s for s in S0 if not s[5]]
    ties = [s for s in S0 if s[5] and s[4] != s[3]]
    cand = [(s[0], not s[1]) for s in br] + [(s[0], 'sd') for s in ties]
    hit = None
    for off, val in cand:
        if rows3v.b2d3v(list(Bt), {off: val})[0] == Tg:
            hit = [(off, val)]
            break
    if hit is None and len(cand) <= 16:
        for a, b in itertools.combinations(cand, 2):
            if a[0] != b[0] and rows3v.b2d3v(list(Bt), dict([a, b]))[0] == Tg:
                hit = [a, b]
                break
    if hit is None:
        c['1〜2 個の反転では当たらない'] += 1
        continue
    c['当たる（反転 %d 個）' % len(hit)] += 1
    for off, val in hit:
        FIX.append((Bt, off, val))
        c['反転すべき site の条項: %s' % whyof.get(off, 'tie/なし')] += 1
print('証人 %d 件（ImgCofinalT の破れ 18 個から）:' % len(seen))
for k, v in c.most_common():
    print('   %-34s %d' % (k, v))
print('正しい決定が分かった site %d（相異なる %d） 内訳 %s'
      % (len(FIX), len(set((b, o) for b, o, _ in FIX)),
         Counter(v for _, _, v in FIX).most_common()))
pickle.dump(FIX, open('/tmp/h1work/h14fix.pkl', 'wb'))
