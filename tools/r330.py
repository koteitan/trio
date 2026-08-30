# -*- coding: utf-8 -*-
"""**(R-C9) —— 本線の `R` で「末尾列が `R` の中で行 0 最浅」は起こるか。**

## ⚠ 定義（逐語）

    `Wset.lean:61`  def domT (M : TrioSeq) (m : ℕ) : Prop :=
                      **lev M (M.length - 1) = m + 1** ∧
                      **¬ hasParent M (srow M (M.length - 1)) (M.length - 1)**
    `Wset.lean:1314` def argOK (R : TrioSeq) : Prop := **∀ p ∈ R, 0 < p.1**
    `Wset.lean:57`  def lev (M : TrioSeq) (j : ℕ) : ℕ := 2 * entry M 1 j + entry M 2 j

## ★★★★★ 先に算術で分かること（測るまでもない部分）

    `lev M (末尾) = m + 1 > 0` ⟹ **`srow(末尾) >= 1`**（行 1 か行 2 が正）
    ★ **「末尾が行 0 で弱く最浅」⟹ `nextrel0` が末尾に入れない**
      （`nextrel0 R j0 j1` は **`entry R 0 j0 < entry R 0 j1`（狭義）** を要求）
      ⟹ `le0 R j0 (末尾)` は `j0 = 末尾` だけ ⟹ `nextrel1`/`nextrel2` は `j0 < 末尾` も要るので**不可能**
      ⟹ ⟹ ★★★ **末尾は必ず孤児** ⟹ **`domT` の第 2 連言は自動で成立**
    ⟹ ⛔ **ですから `domT` は「末尾が最浅」を禁じません。むしろ自動で許します。**
    ⟹ ★ **測るべきは「本線でそういう `R` が実際に現れるか」だけ**です。

## ⚠ 母集団（本線の `R` の作り方）

    本線: `(0,v,z) :: R` が塔の土台 ⟹ **`R := M.drop 1`**（`M` は根が `(0,*,*)` の本線の行列）
    (i) ★ **Reach**（`D_v` を実際に `expand` して出る行列）… いちばん本線に近い
    (ii) ★ **シート**（`psiI.json` ＝ `BM4-Analysis-2021.4.27.xlsx` を落としたもの、**本物の標準形**）
    (iii) ⚠ **窓（`W_drop`/`W_take`）由来** … 本線とは限らないので**別に集計**
    (iv) ⛔ **人工の対照**
    条件: **`argOK R`**（全列の行 0 > 0）∧ **`∃ m, domT R m`**（`lev(末尾) > 0` ∧ 末尾が孤児）
    測る述語: **`min` 判定 := `∀ r, entry R 0 (|R|-1) <= entry R 0 r`**（末尾が行 0 で弱く最浅）
"""
import sys, itertools, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
from r315 import windows

pct = lambda a, b: 100.0 * a / b if b else float('nan')
lev = lambda S, j: 2 * S[j][1] + S[j][2]
argOK = lambda R: all(p[0] > 0 for p in R)


def domT(R):
    j = len(R) - 1
    return lev(R, j) > 0 and trio.parent(R, srow(R, j), j) is None


def shallowest(R):
    return all(R[-1][0] <= p[0] for p in R)


def scan(MS, tag, drop1=True):
    c = Counter(); ex = []
    for M in MS:
        R = list(M)[1:] if drop1 else list(M)
        if len(R) < 1: continue
        c['候補'] += 1
        if not argOK(R): c['⛔ argOK 破れ'] += 1; continue
        c['argOK'] += 1
        if not domT(R): c['⛔ domT 破れ'] += 1; continue
        c['★ 本線の R（argOK ∧ domT）'] += 1
        s = shallowest(R)
        c['★★ 末尾が行 0 で最浅'] += s
        c['  うち |R| = 1'] += (s and len(R) == 1)
        c['  うち |R| >= 2'] += (s and len(R) >= 2)
        if s and len(R) >= 2 and len(ex) < 4: ex.append(R)
    n = c['★ 本線の R（argOK ∧ domT）']
    print('  [%s]' % tag)
    print('     候補 %d ／ argOK %d ／ ★ 本線の R（argOK ∧ domT）**%d**' % (c['候補'], c['argOK'], n))
    print('     ★★ 末尾が行 0 で最浅: **%d 件 = %.4f%%**（うち `|R|=1` %d 件、`|R|>=2` %d 件）'
          % (c['★★ 末尾が行 0 で最浅'], pct(c['★★ 末尾が行 0 で最浅'], n),
             c['  うち |R| = 1'], c['  うち |R| >= 2'])) if n else None
    for R in ex:
        print('     ★ 例（`|R|>=2`）: %s' % ' '.join('(%d,%d,%d)' % q for q in R))
    return c


t0 = time.time()
print('== (i) Reach（`D_v` の実際の展開）==')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6),
                      ((1, 2, 3, 4, 5, 6, 7, 8), (1, 2), 6)):
    RC |= reach(vs, ns, depth)
RCb = [list(x) for x in RC if x and x[0][0] == 0]
scan(RCb, 'Reach、根が (0,*,*) の元 %d 本 ⟹ R = M.drop 1' % len(RCb))

print('== (ii) シート（`psiI.json` ＝ BM4-Analysis の落とし）==')
SH = [[tuple(v) for v in M] for M in load()]
SHb = [M for M in SH if M and M[0][0] == 0]
scan(SHb, 'シート、根が (0,*,*) の行列 %d 本 ⟹ R = M.drop 1' % len(SHb))
print('   ＋ シートの全接頭辞版:')
PRE = []
seen = set()
for M in SH:
    for k in range(2, len(M) + 1):
        if tuple(M[:k]) not in seen: seen.add(tuple(M[:k])); PRE.append(M[:k])
scan([M for M in PRE if M[0][0] == 0], 'シートの接頭辞 %d 本' % len(PRE))

print('== (iii) ⚠ 窓由来（本線とは限らない。別集計）==')
WN = list(windows(SH, cap=60000)) + list(windows([list(x) for x in RC], cap=60000))
scan(WN, '窓 %d 本 ⟹ R = 窓そのもの（根も含む）' % len(WN), drop1=False)

print('== (iv) ⛔ 人工の対照 ==')
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
ART = [list(t) for L in (1, 2, 3) for t in itertools.product(COL, repeat=L)]
scan(ART, '人工 %d 本（`R` を直接作る）' % len(ART), drop1=False)
print('（%.1f 秒）' % (time.time() - t0))
