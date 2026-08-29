# -*- coding: utf-8 -*-
"""**H44-a/b/c —— 判別子の精密化と「復活の回数」の上限。**"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import r66, trio, h41, h42, h43b
import wcert as wc
from collections import Counter

T = r66.load_ladder()
rows = []
for row, M, ocf in T:
    f = h43b.feats(M)
    if f is None:
        continue
    f['trail0'] = 0
    for x in reversed(f['mask']):
        if x == 0:
            f['trail0'] += 1
        else:
            break
    f['lead1'] = 0
    for x in f['mask']:
        if x == 1:
            f['lead1'] += 1
        else:
            break
    rows.append((row, M, ocf, h41.classify(M, 6)[0], f,
                 f['loc'] != '段 1（新しい段）'))
print('母集団 %d 行' % len(rows))
print()

# ---- H44-a 例外 13 件を潰せるか -------------------------------------
print('**H44-a 判別子を「段の末尾から何本 0 が続くか」(`trail0`) に直す**')
R = [r for r in rows if r[4]['b'] >= 2 and r[4]['t'] == 2]
print('   母数: `b>=2` かつ `t=2` の %d 行' % len(R))
cc = Counter()
for row, M, ocf, kd, f, e in R:
    cc[(min(f['trail0'], 4), e)] += 1
print('   | `trail0` | 逃げる / 合計 |')
for k in sorted({k for k, _ in cc}):
    a, b = cc[(k, True)], cc[(k, False)]
    print('   | %s | **%d / %d (%.1f%%)** |'
          % ('4+' if k == 4 else k, a, a + b, 100.0 * a / max(1, a + b)))
print()
print('   `trail0` を閾値にしたときの食い違い:')
best = None
for th in range(0, 6):
    bad = sum(1 for r in R if (r[4]['trail0'] >= th) != r[5])
    print('      `trail0 >= %d`  食い違い **%d / %d**' % (th, bad, len(R)))
    if best is None or bad < best[1]:
        best = (th, bad)
print('   ⟹ 最良は `trail0 >= %d` で食い違い **%d**（元の判別子は 13）'
      % best)
ex = [r for r in R if (r[4]['trail0'] >= best[0]) != r[5]]
print('   残る例外 %d 件:' % len(ex))
for row, M, ocf, kd, f, e in sorted(ex, key=lambda r: r[0])[:6]:
    print('      行 %-5d %-30s 印=%s trail0=%d 逃げる=%s'
          % (row, ocf[:30], f['mask'], f['trail0'], e))
print()

# ---- H44-b t ごとの判別子 -------------------------------------------
print('**H44-b `t` ごとの判別子**')
for t in (0, 1, 2):
    Rt = [r for r in rows if r[4]['t'] == t and r[4]['b'] >= 2]
    if not Rt:
        continue
    ne = sum(1 for r in Rt if r[5])
    print('   ** t = %d : %d 行、逃げる %d (%.1f%%)**'
          % (t, len(Rt), ne, 100.0 * ne / len(Rt)))
    cand = (('段の最後の列の印', lambda f: f['lastmask']),
            ('`trail0`', lambda f: min(f['trail0'], 3)),
            ('段の最後の列が行 0 で上がるか', lambda f: 1 if t >= 1 else 0),
            ('段の最後の列の `lev`', lambda f: None),
            ('段の幅 b', lambda f: min(f['b'], 6)),
            ('固定接頭辞 a = 0 か', lambda f: f['a'] == 0))
    for nm, g in cand:
        if g(Rt[0][4]) is None:
            continue
        c2 = Counter()
        for row, M, ocf, kd, f, e in Rt:
            c2[(g(f), e)] += 1
        ks = sorted({k for k, _ in c2}, key=str)
        line = '      %-26s ' % nm
        for k in ks:
            a, b = c2[(k, True)], c2[(k, False)]
            line += '%s:%d/%d  ' % (k, a, a + b)
        print(line)
    # t<2 のときの追加の候補: 段の最後の列が悪い列か / 段が M の接尾辞か
    if t < 2:
        c3 = Counter()
        for row, M, ocf, kd, f, e in Rt:
            blkfirst = M[f['r0']]
            c3[(('段の先頭が全体で最浅' if all(blkfirst[0] <= q[0] for q in M)
                 else '段の先頭より浅い列が外にある'), e)] += 1
        for k in sorted({k for k, _ in c3}):
            a, b = c3[(k, True)], c3[(k, False)]
            print('      %-26s %s: **%d / %d (%.1f%%)**'
                  % ('段の先頭の深さ', k, a, a + b, 100.0 * a / max(1, a + b)))
print()

# ---- H44-c 復活の回数 -----------------------------------------------
print('**H44-c 復活を繰り返すと何回で止まるか**')
MAXL = 3000
cnt = Counter()
worst = []
for row, M, ocf, kd, f, e in rows:
    X = [tuple(c) for c in M]
    k = 0
    while k < 12:
        g = h43b.feats(X)
        if g is None or g['loc'] == '段 1（新しい段）':
            break
        k += 1
        X = [tuple(c) for c in trio.expand(list(X), 2)]
        if len(X) > MAXL:
            k = '長さ切れ'
            break
    cnt[k] += 1
    if k != '長さ切れ' and isinstance(k, int) and k >= 2:
        worst.append((row, M, ocf, k))
tot = sum(cnt.values())
print('   連続して復活する回数（`X -> X⟦2⟧` を繰り返す）')
for k in sorted(cnt, key=lambda x: (isinstance(x, str), x)):
    print('      %-8s %5d (%.2f%%)' % (k, cnt[k], 100.0 * cnt[k] / tot))
mx = max(k for k in cnt if isinstance(k, int))
print('   ⟹ **上限 %d 回**（長さ切れ %d 件）' % (mx, cnt.get('長さ切れ', 0)))
print('   2 回以上復活する行 %d 件。最小のもの:' % len(worst))
for row, M, ocf, k in sorted(worst, key=lambda r: r[0])[:5]:
    print('      行 %-5d %-34s %d 回' % (row, ocf[:34], k))
print()
print('**退化検査**')
wc.audit(R, lambda r: r[5], lambda r: r[4]['trail0'] >= best[0],
         '「逃げる」 vs 「trail0 >= %d」' % best[0])
wc.audit(rows, lambda r: r[5], lambda r: r[4]['t'] < 2, '「逃げる」 vs 「t < 2」')
