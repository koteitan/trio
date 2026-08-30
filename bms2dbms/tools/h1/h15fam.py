# -*- coding: utf-8 -*-
"""H15 (3): 残る 17 個を族に分ける。

軸:
  W  証人 B = d2b3(T) が BMS 標準形で取れるか
  X  B が「すでに一致している対」にも現れ、そこでは**別の像**を要求されるか
     （＝ conv3 は関数なので**両立不能**。直すなら conv3(A) 自身の綴り）
  F  B が分岐列の反転 1〜2 個で直るか / `sbody_w` で直るか
  P  `d2b3` の当たりの並び（`O` が続くか）
"""
import sys, os, pickle, itertools
from collections import Counter, defaultdict
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3v, rows3b, provc, inv3, cofinal
from core import expand, show, isstd

AG = pickle.load(open('/tmp/h1work/ag_v18_7.pkl', 'rb'))
# すでに一致している対から「この行列はこの像でなければならない」表を作る
need = {}
for A, n, m in AG:
    E = tuple(tuple(x) for x in expand(A, n))
    fA = tuple(map(tuple, rows3.b2d3(list(A))))
    need.setdefault(E, set()).add(tuple(expand(fA, m)))

cof = [tuple(map(tuple, A)) for A in pickle.load(open('/tmp/h1work/cof6.pkl', 'rb'))]
bad = defaultdict(list)
for A, m, T in pickle.load(open('/tmp/h1work/img54p.pkl', 'rb')):
    a = tuple(map(tuple, A))
    if a in set(cof):
        bad[a].append((m, tuple(map(tuple, T))))

rows = []
for A in cof:
    pat = cofinal.hits(A, 8)
    ent = dict(A=A, pat=pat, ms=[], cls=None)
    kinds = Counter()
    for m, T in sorted(bad[A]):
        B = inv3.d2b3([list(x) for x in T])
        if not B:
            kinds['証人なし'] += 1
            continue
        Bt = tuple(tuple(x) for x in B)
        if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
            kinds['証人が標準形でない'] += 1
            continue
        # X: 証人がすでに別の像を約束しているか
        if Bt in need and T not in need[Bt]:
            kinds['**衝突**（証人は別の像を約束ずみ）'] += 1
            continue
        C0, S0 = rows3v.b2d3v(list(Bt))
        if C0 == T:
            kinds['素で当たる'] += 1
            continue
        br = [s for s in S0 if not s[5]]
        ties = [s for s in S0 if s[5] and s[4] != s[3]]
        cand = [(s[0], not s[1]) for s in br] + [(s[0], 'sd') for s in ties]
        hit = [x for x in cand if rows3v.b2d3v(list(Bt), {x[0]: x[1]})[0] == T]
        if not hit and len(cand) <= 14:
            for a2, b2 in itertools.combinations(cand, 2):
                if a2[0] != b2[0] and rows3v.b2d3v(list(Bt), dict([a2, b2]))[0] == T:
                    hit = [a2, b2]
                    break
        if hit:
            kinds['分岐の反転で直る'] += 1
            continue
        if rows3b.b2d3b(list(Bt))[0] == T:
            kinds['sbody_w で直る'] += 1
            continue
        kinds['どれでも直らない'] += 1
    ent['kinds'] = kinds
    rows.append(ent)

print('ImgCofinalT で破れている A: %d 個' % len(rows))
big = Counter()
for e in rows:
    k = e['kinds'].most_common(1)[0][0] if e['kinds'] else '対が無い'
    e['cls'] = k
    big[k] += 1
print()
print('族の分類（各 A で最も多い型）:')
for k, v in big.most_common():
    print('   %-38s %d' % (k, v))
print()
for e in sorted(rows, key=lambda x: (x['cls'], len(x['A']))):
    print('   %-30s %-14s %s  %s'
          % (show(list(e['A'])), e['pat'][:8], e['cls'], dict(e['kinds'])))
pickle.dump(rows, open('/tmp/h1work/h15fam.pkl', 'wb'))
