# -*- coding: utf-8 -*-
"""**課題 H47-a/b/c ＋ H48 —— `TowerOK` の場面をシートで作り、`TieFree` を測る。**

`TowerOK`（`lean/Wset.lean:4365`）の場面は

    R           `argOK R`（全列の行 0 が > 0）、`R != []`
    根          `(0, v, z)`、`z <= 1`
    `∃ m, domT R m`   `lev R (|R|-1) > 0` かつ **`R` の中で末尾が孤児**
    `hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|`   根を付けると親ができる

シートの行 `M` で `M[0] = (0,v,z)` かつ `argOK (M[1:])` なら、
`R = M[1:]`、`(0,v,z) :: R = M` なので **`X = M⟦n⟧` がそのまま塔**になる。

`coneV` / `le1` / `TieFree` は `tools/probe_tiefree_tower.py` の実装を再利用
（`assert` で `coneV_of_le1`（無条件のはずの包含）を毎回検算している）。
"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import r66
import trio
import probe_tiefree_tower as PT
import wcert as wc
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
T = r66.load_ladder()


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def has_parent(S, j):
    return trio.parent([tuple(c) for c in S], srow(S, j), j) is not None


sites = []
skip = Counter()
for row, M, ocf in T:
    M = [tuple(c) for c in M]
    if len(M) < 2:
        skip['|M| < 2'] += 1
        continue
    if M[0][0] != 0:
        skip['根の行 0 が 0 でない'] += 1
        continue
    R = M[1:]
    if not all(p[0] > 0 for p in R):
        skip['**argOK が破れる**'] += 1
        continue
    j = len(R) - 1
    if 2 * R[j][1] + R[j][2] == 0:
        skip['domT: lev = 0'] += 1
        continue
    if has_parent(R, j):
        skip['domT: R の中で末尾に親がある'] += 1
        continue
    if not has_parent(M, len(R)):
        skip['根を付けても親ができない'] += 1
        continue
    sites.append((row, M, ocf, M[0][1], M[0][2], R, srow(R, j)))

print('母集団: シート **%d 行**' % len(T))
print()
print('**H47-a `TowerOK` の場面がシートに何件あるか**')
print('| 落ちた条件 | 件数 |')
print('|---|--:|')
for k, v in skip.most_common():
    print('| %s | %d |' % (k, v))
print('| **`TowerOK` の場面** | **%d** |' % len(sites))
print()
c = Counter(s[6] for s in sites)
print('   **`srow R (|R|-1)` の内訳**')
for k in sorted(c):
    print('      `srow` = %d : **%d (%.1f%%)**%s'
          % (k, c[k], 100.0 * c[k] / len(sites),
             '  ⟸ **`TowerOK2`（唯一の核）**' if k == 2 else ''))
print()

# H47-b: srow=2 のとき「z=0 かつ行 1 の祖先」の列が R に無いか
print('**H47-b `srow = 2` で「根を付けると親ができる」条件の構造**')
S2 = [s for s in sites if s[6] == 2]
cc = Counter()
for row, M, ocf, v, z, R, sr in S2:
    j = len(R) - 1
    # R の中の「z=0 かつ 行 1 で j の祖先」の列
    cand = [i for i in range(j) if R[i][2] == 0 and trio.is_ancestor(R, 1, i, j)]
    cc[(len(cand) == 0, z)] += 1
print('   | `R` に「z=0 かつ行 1 で末尾の祖先」の列が | 根の `z` | 件数 |')
print('   |---|--:|--:|')
for k, vv in sorted(cc.items()):
    print('   | %s | %d | %d |' % ('**無い**' if k[0] else 'ある', k[1], vv))
none0 = sum(vv for k, vv in cc.items() if k[0])
print('   ⟹ **`R` にその列が無いのが %d / %d (%.1f%%)**'
      % (none0, len(S2), 100.0 * none0 / max(1, len(S2))))
print()

# H47-c 持ち上げ量 w - v
print('**H47-c 持ち上げ量 `w - v` の同定**')
ok = bad = 0
exw = []
for row, M, ocf, v, z, R, sr in S2:
    w = R[-1][1]
    d1 = w - v
    X1 = [tuple(c) for c in trio.expand(list(M), 1)]
    X2 = [tuple(c) for c in trio.expand(list(M), 2)]
    if len(X2) < 2 * len(X1) or X2[:len(X1)] != X1:
        continue
    C = PT.cone(X1)
    pred = [(c[0], c[1] + (d1 if i in C else 0), c[2]) for i, c in enumerate(X1)]
    seg = X2[len(X1):len(X1) + len(X1)]
    if len(seg) == len(pred):
        if [q[1] - p[1] for p, q in zip(X1, seg)] == \
           [d1 if i in C else 0 for i in range(len(X1))]:
            ok += 1
        else:
            bad += 1
            if len(exw) < 3:
                exw.append((row, ocf, v, w))
print('   `w = entry R 1 (|R|-1)`（`R` の末尾の行 1）、`d1 = w - v` と置いて')
print('   `X⟦2⟧` の 2 段目が `Lift1(X⟦1⟧, d1)` と一致するか: **%d / %d**'
      % (ok, ok + bad))
if exw:
    print('   食い違いの例:')
    for row, ocf, v, w in exw:
        print('      行 %-5d %-30s v=%d w=%d' % (row, ocf[:30], v, w))
print('   `w - v` の分布: %s'
      % dict(Counter(min(s[5][-1][1] - s[3], 6) for s in S2)))
print()

# ---- H48 ----------------------------------------------------------
print('**H48 `TowerOK2` の場面で `TieFree (((0,v,z)::R)⟦n⟧)` が立つ割合**')
print('   母数: **%d 件**' % len(S2))
res = {}
for n in range(1, N + 1):
    okn = badn = und = 0
    ex = []
    for row, M, ocf, v, z, R, sr in S2:
        X = [tuple(c) for c in trio.expand(list(M), n)]
        if not X or len(X) > 400:
            und += 1
            continue
        try:
            t = PT.tiefree(X)
        except AssertionError:
            und += 1
            continue
        if t:
            okn += 1
        else:
            badn += 1
            if len(ex) < 4:
                v0 = X[0][1]
                C1 = PT.cone(X)
                js = [j for j in range(len(X))
                      if PT.amin(X, j) >= v0 and j not in C1]
                ex.append((row, ocf, v, z, js[:3], [X[j] for j in js[:3]]))
    res[n] = (okn, badn, und, ex)
    print('   n=%-2d  `TieFree` 成立 **%4d / %4d (%.1f%%)**  未判定 %d'
          % (n, okn, okn + badn, 100.0 * okn / max(1, okn + badn), und))
print()
print('**破れる例（n=1）の最小のもの**')
for row, ocf, v, z, js, cols in sorted(res[1][3], key=lambda e: e[0])[:4]:
    print('   行 %-5d %-32s v=%d z=%d  破れる列 j=%s 値=%s'
          % (row, ocf[:32], v, z, js, cols))
print()
print('**退化検査**')
pop = S2
f = lambda s: PT.tiefree([tuple(c) for c in trio.expand(list(s[1]), 1)])
for nm, tv in (('「`z` = 0」', lambda s: s[4] == 0),
               ('「`v` = 0」', lambda s: s[3] == 0),
               ('「`|R|` <= 3」', lambda s: len(s[5]) <= 3),
               ('「`R` に行 1 = `v` の列が無い」',
                lambda s: all(p[1] != s[3] for p in s[5]))):
    wc.audit(pop, f, tv, '`TieFree(X_1)` vs ' + nm)
