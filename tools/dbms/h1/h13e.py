# -*- coding: utf-8 -*-
"""H13 (2): `after_w` の当たり外れを測り直す（v16(2) の後、母数は ImgCofinalT の 27）。

`after_w` が決めた site だけを取り出して
  正例（**反転すべき**）= 証人 d2b3(T) が要求する場所（ImgCofinalT の破れ 27 個から）
  負例（反転してはいけない）= シート 1354 行 ＋ lim=7 の一致を壊す場所
"""
import sys, os, pickle, itertools
from collections import Counter
os.environ.setdefault('RFLAGS', '')
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, rows3v, provc, inv3, sheet3, core
from rows3 import gen3, key
from core import expand, show, isstd


def aw_sites(M):
    """`after_w` / `wchain` が決めた site の集合（provc の why から）。"""
    C, PR = provc.b2d3p(list(M))
    return set(e[1] for e in PR if e[2] and str(e[2]).startswith('after_w')), \
        set(e[1] for e in PR if e[2] and str(e[2]).startswith('wchain'))


# ---- 1. 発火の頻度と決定の内訳
for lim in (6, 7):
    c = Counter()
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    for i, M in enumerate(A):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        S = tuple(map(tuple, M))
        C, PR = provc.b2d3p(list(S))
        for e in PR:
            w = str(e[2])
            if w.startswith('after_w'):
                c['after_w/' + w.split('/')[-1]] += 1
            elif w.startswith('wchain'):
                c['wchain/' + w.split('/')[-1]] += 1
            if e[2]:
                c['_決定した柱'] += 1
    print('lim=%d: 決定した柱 %d  %s'
          % (lim, c['_決定した柱'],
             {k: v for k, v in sorted(c.items()) if not k.startswith('_')}))

# ---- 2. 証人が反転を要求する after_w の site
cof = set(tuple(map(tuple, A)) for A in
          pickle.load(open('/tmp/h1work/cof6.pkl', 'rb')))
bad = [e for e in pickle.load(open('/tmp/h1work/img54p.pkl', 'rb'))
       if tuple(map(tuple, e[0])) in cof]
POS, cc = [], Counter()
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
        continue
    aw, wc = aw_sites(Bt)
    br = [s for s in S0 if not s[5]]
    cand = [(s[0], not s[1]) for s in br]
    hit = [x for x in cand if rows3v.b2d3v(list(Bt), {x[0]: x[1]})[0] == Tg]
    if not hit:
        for a, b in itertools.combinations(cand, 2):
            if a[0] != b[0] and rows3v.b2d3v(list(Bt), dict([a, b]))[0] == Tg:
                hit = [a, b]
                break
    if not hit:
        cc['1〜2 個の反転では当たらない'] += 1
        continue
    cc['当たる（反転 %d 個）' % len(hit)] += 1
    for off, val in hit:
        tag = ('after_w' if off in aw else ('wchain' if off in wc else 'ほか'))
        cc['反転すべき site の条項: %s' % tag] += 1
        if tag == 'after_w':
            POS.append((Bt, off, val))
print()
print('証人 %d 件（ImgCofinalT の破れ 27 個から）:' % len(seen))
for k, v in cc.most_common():
    print('   %-34s %d' % (k, v))
print('after_w の正例 %d（相異なる %d）'
      % (len(POS), len(set((b, o) for b, o, _ in POS))))
pickle.dump(POS, open('/tmp/h1work/h13awpos.pkl', 'wb'))
