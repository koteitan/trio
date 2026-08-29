# -*- coding: utf-8 -*-
"""**課題 H46 —— 復活 3 回の 46 件／残核の前提を全数で。**"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import r66, h41, h42, h43b
import trio, ladder
import wcert as wc
from collections import Counter

T = r66.load_ladder()
print('母集団: **%d 行**（`r66.load_ladder()`。R1 と同一）' % len(T))
print()


def blkinfo(M):
    M = [tuple(c) for c in M]
    n = len(M) - 1
    t = h42.srow(M, n)
    r0 = trio.parent(M, t, n)
    if r0 is None:
        return None
    return t, r0, M[r0:n]


def revives(M):
    """連続して復活する回数と、各段での特徴。"""
    X = [tuple(c) for c in M]
    out = []
    for _ in range(12):
        f = h43b.feats(X)
        if f is None or f['loc'] == '段 1（新しい段）':
            break
        bi = blkinfo(X)
        out.append((bi[0], len(bi[2]), tuple(bi[2][-1])) if bi else None)
        X = [tuple(c) for c in trio.expand(list(X), 2)]
        if len(X) > 4000:
            break
    return out


# ---- H46-a --------------------------------------------------------
print('**H46-a 復活の回数 `k` は何で決まるか**')
data = []
for row, M, ocf in T:
    rv = revives(M)
    bi = blkinfo(M)
    if bi is None:
        continue
    t, r0, blk = bi
    data.append((row, [tuple(c) for c in M], ocf, len(rv), t, r0, blk, rv))
c = Counter(d[3] for d in data)
print('   `k` の分布: %s' % dict(sorted(c.items())))
print()
print('   **`k` ごとの最小の行**')
for k in sorted(c):
    ds = sorted([d for d in data if d[3] == k], key=lambda d: d[0])
    d = ds[0]
    print('      k=%d  行 %-5d %-36s |M|=%d t=%d b=%d'
          % (k, d[0], d[2][:36], len(d[1]), d[4], len(d[6])))
print()
print('   **`k` と各量の関係**')
for nm, g in (('`t`（末尾列の srow）', lambda d: d[4]),
              ('`lev`（末尾列）', lambda d: min(2 * d[1][-1][1] + d[1][-1][2], 6)),
              ('`|M|`', lambda d: min(len(d[1]), 8)),
              ('段の幅 `b`', lambda d: min(len(d[6]), 6)),
              ('行 2 に 1 がある列の本数', lambda d: min(sum(1 for q in d[1] if q[2] > 0), 4)),
              ('**段の最後の列の `lev`**', lambda d: min(2 * d[6][-1][1] + d[6][-1][2], 6))):
    cc = Counter((g(d), d[3]) for d in data)
    ks = sorted({k for k, _ in cc})
    print('   %-28s' % nm)
    for k in ks:
        line = '      %-4s : ' % k
        for kk in sorted({v for _, v in cc}):
            if cc[(k, kk)]:
                line += 'k=%d:%d  ' % (kk, cc[(k, kk)])
        print(line)
print()
print('   **k=3 の 46 件を直に見る**')
d3 = sorted([d for d in data if d[3] == 3], key=lambda d: d[0])
print('      `t` の分布: %s' % dict(Counter(d[4] for d in d3)))
print('      `|M|` の分布: %s' % dict(Counter(len(d[1]) for d in d3)))
print('      段の幅 `b`: %s' % dict(Counter(len(d[6]) for d in d3)))
print('      段の最後の列: %s' % dict(Counter(d[6][-1] for d in d3).most_common(5)))
print('      各段での `t` の並び: %s'
      % dict(Counter(tuple(x[0] for x in d[7]) for d in d3).most_common(5)))
for d in d3[:5]:
    print('      行 %-5d %-30s M=%s' % (d[0], d[2][:30],
                                        ''.join('(%d,%d,%d)' % q for q in d[1])))
print()

# ---- H46-b --------------------------------------------------------
print('**H46-b 残核 `Subst1gReviveSelf` の 9 前提をシート全数で**')
print('   塔の 1 段を substitution として書く:')
print('      `S = M⟦1⟧`,  `p = |S|-1`,  `C = [S[p]] ++ B_1`,  `R = S.dropLast ++ C = M⟦2⟧`')
print('   （こう置くと前提 5「lev C 0 <= lev S p」と 6「entry C 0 0 = entry S 0 p」は**自動**）')
print()
C6 = ladder.Cert(('TOW', 'LTOW', 'MTOW'))
cnt = Counter()
tot = 0
for row, M, ocf in T:
    E1 = [tuple(c) for c in trio.expand(list(M), 1)]
    E2 = [tuple(c) for c in trio.expand(list(M), 2)]
    if len(E2) <= len(E1) or E2[:len(E1)] != E1:
        cnt['塔にならない'] += 1
        continue
    S = E1
    p = len(S) - 1
    Bn = E2[len(E1):]
    Cb = [S[p]] + list(Bn)
    R = list(S[:p]) + Cb
    tot += 1
    if R != E2:
        cnt['R != M⟦2⟧（対応が崩れる）'] += 1
        continue
    cnt['2. p < |S|'] += 1
    cnt['3. C != []'] += (len(Cb) > 0)
    cnt['5. lev C 0 <= lev S p'] += (wc.lev(Cb[0]) <= wc.lev(S[p]))
    cnt['6. entry C 0 0 = entry S 0 p'] += (Cb[0][0] == S[p][0])
    cnt['**7. C の全列が S[p] 以上の深さ**'] += all(S[p][0] <= q[0] for q in Cb)
    cnt['**8. R の末尾は R で親を持つ**'] += wc.has_parent(R, len(R) - 1)
    tail = S[p + 1:]
    d9 = (not wc.has_parent(Cb, len(Cb) - 1)) if not tail else \
         (not wc.has_parent(tail, len(tail) - 1))
    cnt['**9. 選言（自分のブロック内では孤児）**'] += d9
    cnt['**10. R.dropLast に行 2 > 0**'] += any(q[2] > 0 for q in R[:-1])
    cnt['1. S に証明書（`ladder.Cert`）'] += bool(C6(tuple(S), 80))
    cnt['4. C に証明書（`ladder.Cert`）'] += bool(C6(tuple(Cb), 80))
print('   母数 **%d 件**（塔にならない %d / 対応が崩れる %d）'
      % (tot, cnt['塔にならない'], cnt['R != M⟦2⟧（対応が崩れる）']))
tot2 = cnt['2. p < |S|']
print('   | 前提 | 成り立つ |')
print('   |---|--:|')
for k in ('2. p < |S|', '3. C != []', '5. lev C 0 <= lev S p',
          '6. entry C 0 0 = entry S 0 p',
          '**7. C の全列が S[p] 以上の深さ**',
          '**8. R の末尾は R で親を持つ**',
          '**9. 選言（自分のブロック内では孤児）**',
          '**10. R.dropLast に行 2 > 0**',
          '1. S に証明書（`ladder.Cert`）', '4. C に証明書（`ladder.Cert`）'):
    print('   | %s | **%d / %d (%.1f%%)** |'
          % (k, cnt[k], tot2, 100.0 * cnt[k] / max(1, tot2)))
