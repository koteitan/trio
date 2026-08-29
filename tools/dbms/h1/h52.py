# -*- coding: utf-8 -*-
"""**課題 H51 —— 「狭義」版（`∀ p ∈ R, v < p.2.1`）で測り直す。**

    無タイ   `∀ p ∈ R, p.2.1 != v`
    **狭義**  `∀ p ∈ R, v < p.2.1`      ← `liftStage_of_window` の `hw` そのもの

`v = 0` では同値。`v >= 1` では狭義のほうが真に強い。
母集団は H49-0 / H50 と同じ正しい作り方。
"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h51
import trio
import probe_tiefree_tower as PT
from collections import Counter

rng = random.Random(20260829)
scenes = h51.scenes
notie = h51.notie
strict = [s for s in scenes if all(s[3] < p[1] for p in s[2])]
mid = [s for s in notie if not all(s[3] < p[1] for p in s[2])]
print('母集団: 場面 **%d 件**' % len(scenes))
print('   無タイ  **%d (%.1f%%)**' % (len(notie), 100.0 * len(notie) / len(scenes)))
print('   **狭義  %d (%.1f%%)**' % (len(strict), 100.0 * len(strict) / len(scenes)))
print('   無タイだが狭義でない **%d (%.1f%%)**'
      % (len(mid), 100.0 * len(mid) / len(scenes)))
print()

# ---- H51-a ---------------------------------------------------------
print('**H51-a `v` 別の内訳**')
print('| `v` | 場面 | 無タイ | **狭義** | 狭義 / 場面 |')
print('|--:|--:|--:|--:|--:|')
cs = Counter(s[3] for s in scenes)
cn = Counter(s[3] for s in notie)
ct = Counter(s[3] for s in strict)
for v in sorted(cs):
    print('| %d | %d | %d (%.1f%%) | **%d** | **%.1f%%** |'
          % (v, cs[v], cn[v], 100.0 * cn[v] / cs[v], ct[v],
             100.0 * ct[v] / cs[v]))
print()

# ---- H51-b ---------------------------------------------------------
S = strict if len(strict) <= 20000 else rng.sample(strict, 20000)
print('**H51-b ★ 狭義の伝播**（標本 %d 件）' % len(S))
print('| `n` | `argOK R_n` | **狭義が保たれる** |')
print('|--:|--:|--:|')
exb = []
for n in list(range(1, 6)) + [6, 8, 10, 12]:
    a = b = tot = 0
    SS = S if n <= 5 else (S if len(S) <= 3000 else rng.sample(S, 3000))
    for M, j, R, v in SS:
        X = [(0, v, 0)] + R
        Y = [tuple(c) for c in trio.expand(list(X), n + 1)]
        if not Y or len(Y) > 2000:
            continue
        Rn = list(Y[1:])
        tot += 1
        a += all(p[0] > 0 for p in Rn)
        ok = all(v < p[1] for p in Rn)
        b += ok
        if not ok and len(exb) < 3:
            exb.append((M, j, R, v, n,
                        [(i, p) for i, p in enumerate(Rn) if p[1] <= v][:2]))
    print('| %d | %d / %d (%.2f%%) | **%d / %d (%.2f%%)** |'
          % (n, a, tot, 100.0 * a / max(1, tot), b, tot, 100.0 * b / max(1, tot)))
print()
if exb:
    print('   **破れる最小の例**')
    for M, j, R, v, n, bad in exb:
        print('      n=%d v=%d R=%s  破れる列 %s'
              % (n, v, ''.join('(%d,%d,%d)' % q for q in R), bad))
else:
    print('   **破れる例は 1 件も無い。**')
print()

# ---- 対照 -----------------------------------------------------------
print('**対照（H50 と同じ形）**')
T = scenes if len(scenes) <= 6000 else rng.sample(scenes, 6000)
nsx = [s for s in T if not all(s[3] < p[1] for p in s[2])]
a = tot = 0
for M, j, R, v in nsx:
    X = [(0, v, 0)] + R
    Y = [tuple(c) for c in trio.expand(list(X), 2)]
    if not Y or len(Y) > 500:
        continue
    tot += 1
    a += all(v < p[1] for p in Y[1:])
print('   狭義でない場面で狭義の伝播を測る: **%d / %d (%.1f%%)**'
      % (a, tot, 100.0 * a / max(1, tot)))
S4 = rng.sample(strict, min(4000, len(strict)))
for dt in (-1, 0, 1):
    ok = tot = 0
    for M, j, R, v in S4:
        X = [(0, v, 0)] + R
        t = R[-1][1] - v + dt
        if t < 0:
            continue
        A = [tuple(c) for c in trio.expand(list(X), 1)]
        pred = [(0, v, 0)] + PT.graft(list(R), PT.Lift1(A, t))
        B = [tuple(c) for c in trio.expand(list(X), 2)]
        tot += 1
        ok += ([tuple(c) for c in pred] == B)
    print('   持ち上げ量 `t %+d`: `hstep` 成立 **%d / %d (%.1f%%)**'
          % (dt, ok, tot, 100.0 * ok / max(1, tot)))
print()

# ---- H51-c ---------------------------------------------------------
print('**H51-c 無タイだが狭義でない %d 件はどうなるか**' % len(mid))
MD = mid if len(mid) <= 8000 else rng.sample(mid, 8000)
for n in (1, 2, 3, 5):
    a = b = tot = 0
    for M, j, R, v in MD:
        X = [(0, v, 0)] + R
        Y = [tuple(c) for c in trio.expand(list(X), n + 1)]
        if not Y or len(Y) > 1000:
            continue
        Rn = list(Y[1:])
        tot += 1
        a += all(p[1] != v for p in Rn)          # 無タイは保たれるか
        b += all(v < p[1] for p in Rn)           # 狭義になることはあるか
    print('   n=%-2d 無タイが保たれる **%d / %d (%.1f%%)**   狭義になる %d (%.1f%%)'
          % (n, a, tot, 100.0 * a / max(1, tot), b, 100.0 * b / max(1, tot)))
print()
print('   **`R` の中で行 1 が `v` 未満の列**')
c1 = Counter(sum(1 for p in R if p[1] < v) for M, j, R, v in mid)
print('      本数の分布: %s' % dict(sorted(c1.items())))
c2 = Counter()
for M, j, R, v in mid:
    idx = [i for i, p in enumerate(R) if p[1] < v]
    c2['先頭' if idx[0] == 0 else ('末尾' if idx[-1] == len(R) - 1 else '中')] += 1
print('      位置: %s' % dict(c2))
c3 = Counter(p[1] for M, j, R, v in mid for p in R if p[1] < v)
print('      その列の行 1 の値: %s' % dict(sorted(c3.items())))
print('      `v` の分布: %s' % dict(sorted(Counter(s[3] for s in mid).items())))
