# -*- coding: utf-8 -*-
"""**H43-b —— (b)「行 1 に印つき」と「復活」は同じ難所の 2 つの顔か。**

`M` のバッドルート `r0`、悪い部分 `blk = M[r0 : |M|-1]`（幅 b）について

    列 j が行 1 で上がる  ⟺  t >= 2 かつ `is_ancestor(M, 1, r0, j)`   （上昇行列 A_xy）
    （t = srow(M, |M|-1)。行 0 は t >= 1 なら全列上がる）

「印つき」= 上がる列と上がらない列が混在する。
「復活」= `M⟦2⟧` のバッドルートが**新しい段の外**にある。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import r66, trio, h41, h42
import wcert as wc
from collections import Counter

T = r66.load_ladder()


def feats(M):
    M = [tuple(c) for c in M]
    n = len(M) - 1
    t = h42.srow(M, n)
    r0 = trio.parent(M, t, n)
    if r0 is None:
        return None
    blk = M[r0:n]
    b = len(blk)
    mask = [1 if (t >= 2 and trio.is_ancestor(M, 1, r0, r0 + i)) else 0
            for i in range(b)]
    E2 = [tuple(c) for c in trio.expand(list(M), 2)]
    r1 = trio.parent(E2, h42.srow(E2, len(E2) - 1), len(E2) - 1)
    # r1 の居場所（M⟦2⟧ = M[:r0] ++ blk ++ lift(blk)）
    if r1 is None:
        loc, off = '孤児', None
    elif r1 < r0:
        loc, off = '固定接頭辞', r1
    elif r1 < r0 + b:
        loc, off = '**段 0（前の段）**', r1 - r0
    else:
        loc, off = '段 1（新しい段）', r1 - r0 - b
    return dict(t=t, r0=r0, b=b, mask=tuple(mask), loc=loc, off=off,
                nz=sum(1 for x in mask if x == 0), a=r0,
                lastmask=mask[-1] if mask else None)


rows = []
for row, M, ocf in T:
    f = feats(M)
    if f is None:
        continue
    kd = h41.classify(M, 6)[0]
    esc = f['loc'] != '段 1（新しい段）'
    rows.append((row, M, ocf, kd, f, esc))
print('母集団 %d 行（バッドルートがある行）' % len(rows))
print()

print('**1. 「印つき」と「復活」は同じ列か**')
print('   `M⟦2⟧` のバッドルートの居場所 x 印（行 1 が上がらない列の有無）')
c = Counter()
for row, M, ocf, kd, f, esc in rows:
    c[('印つき' if 0 < f['nz'] < f['b'] else
       ('全列上がらない' if f['nz'] == f['b'] else '全列上がる'), f['loc'])] += 1
for k, v in sorted(c.items(), key=lambda t: -t[1]):
    print('   %-40s %5d' % (str(k), v))
print()
print('   逃げ先が**段 0 の中**のとき、その列の印は?')
c2 = Counter()
for row, M, ocf, kd, f, esc in rows:
    if f['loc'] != '**段 0（前の段）**':
        continue
    c2[('印 0（行 1 が上がらない）' if f['mask'][f['off']] == 0
        else '印 1（上がる）', 'off=%d/%d' % (f['off'], f['b']))] += 1
for k, v in sorted(c2.items(), key=lambda t: -t[1])[:8]:
    print('      %-44s %5d' % (str(k), v))
print()

print('**2. (b) かつ逃げない 312 件と (b) かつ逃げる 244 件で何が違うか**')
B = [r for r in rows if r[3] == 'b']
print('   (b) は %d 件（逃げる %d / 逃げない %d）'
      % (len(B), sum(1 for r in B if r[5]), sum(1 for r in B if not r[5])))
for nm, g in (('末尾列の `srow` t', lambda f: f['t']),
              ('段の幅 b', lambda f: min(f['b'], 6)),
              ('印 0 の本数', lambda f: min(f['nz'], 4)),
              ('段の**最後**の列の印', lambda f: f['lastmask']),
              ('固定接頭辞の長さ a', lambda f: min(f['a'], 4))):
    cc = Counter()
    for row, M, ocf, kd, f, esc in B:
        cc[(g(f), '逃げる' if esc else '逃げない')] += 1
    keys = sorted({k for k, _ in cc})
    line = '   %-22s ' % nm
    for k in keys:
        e, s = cc[(k, '逃げる')], cc[(k, '逃げない')]
        line += '%s:%d/%d  ' % (k, e, e + s)
    print(line + '  （逃げる/合計）')
print()

print('**3. (a) かつ逃げる 333 件に共通の形はあるか**')
A = [r for r in rows if r[3] == 'a']
Ae = [r for r in A if r[5]]
print('   (a) は %d 件（逃げる %d）' % (len(A), len(Ae)))
for nm, g in (('末尾列の `srow` t', lambda f: f['t']),
              ('段の幅 b', lambda f: min(f['b'], 6)),
              ('印 0 の本数', lambda f: min(f['nz'], 4)),
              ('段の最後の列の印', lambda f: f['lastmask'])):
    cc = Counter()
    for row, M, ocf, kd, f, esc in A:
        cc[(g(f), '逃げる' if esc else '逃げない')] += 1
    keys = sorted({k for k, _ in cc})
    line = '   %-22s ' % nm
    for k in keys:
        e, s = cc[(k, '逃げる')], cc[(k, '逃げない')]
        line += '%s:%d/%d  ' % (k, e, e + s)
    print(line + '  （逃げる/合計）')
print()

print('**★ 段の最後の列の印 x 逃げる（全行）**')
cc = Counter()
for row, M, ocf, kd, f, esc in rows:
    cc[(f['lastmask'], '逃げる' if esc else '逃げない')] += 1
for k in sorted({k for k, _ in cc}, key=lambda x: (x is None, x)):
    e, s = cc[(k, '逃げる')], cc[(k, '逃げない')]
    print('   印=%-5s 逃げる %5d / %5d (%.1f%%)' % (k, e, e + s,
                                                 100.0 * e / max(1, e + s)))
print()
print('**退化検査**')
f_ = lambda r: r[5]
for nm, tv in (('「段の最後の列の印 = 0」', lambda r: r[4]['lastmask'] == 0),
               ('「b = 1」', lambda r: r[4]['b'] == 1),
               ('「t <= 1」', lambda r: r[4]['t'] <= 1)):
    wc.audit(rows, f_, tv, '「逃げる」 vs ' + nm)
