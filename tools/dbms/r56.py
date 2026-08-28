# -*- coding: utf-8 -*-
"""課題 R33-1 改め: **`(TOW)` の所属側の地図**（反証型は原理的に届かないので、§R33-0）。

## 見つけた還元（Lean の既存の補題 2 本だけで出る）

    `mem_Wself_iff` (`Wtower2.lean:2991`, 証明ずみ):
        **M ∈ W u  ↔  M ∈ Wself ∧ lev M 0 ≤ u**      （段は lev M 0 しか運んでいない）
    `zeroRow2_mem_Wself` (`:2985`, 証明ずみ):
        **(∀ p ∈ M, p.2.2 = 0) → M ∈ Wself**

そして `shTower Q e n = flatMap (k => shiftr01 (k*e) 0 Q)` は
**行 2 を変えない**（`shiftr01` は行 0 と行 1 しか動かさない）し、
**第 0 列も変えない**（k=0 の写しは持ち上げ 0）。⟹ `lev (shTower Q e n) 0 = lev Q 0`。

### ⟹ (a) **`(TOW)` は行 2 ≡ 0 の Q では定理**（側条件すら要らない）

    Q ∈ W u, 行 2 ≡ 0
      ⟹ shTower Q e n も行 2 ≡ 0        （shiftr01 は行 2 を保つ）
      ⟹ shTower Q e n ∈ Wself           （zeroRow2_mem_Wself）
      ⟹ lev (shTower Q e n) 0 = lev Q 0 ≤ u   （lev_root_le_of_mem_W）
      ⟹ shTower Q e n ∈ W u             （mem_Wself_iff の逆向き）  ∎

### ⟹ (b) **一般の `(TOW)` は u の要らない文に還元できる**

    (TOW) ⟺ ∀ Q e n, Q ∈ Wself → (根が最浅) → **shTower Q e n ∈ Wself**

    `Q ∈ W u` から `lev Q 0 ≤ u` が出て、結論側の lev も同じなので u が消える。

⟹ **難所は「行 2 に 1 を含む Q」だけ**（`PROOF-STATUS §2` と一致）。
ここではその難所がどれだけ残るかと、既存の証明書で届く範囲を測る。
"""
import sys, time, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r49 import Wlo, has_parent


def lev0(Q):
    return 2 * Q[0][1] + Q[0][2] if Q else 0


def shTower(Q, e, n):
    return tuple((p[0] + k * e, p[1], p[2]) for k in range(n) for p in Q)


def zero2(Q):
    return all(p[2] == 0 for p in Q)


def root_shallowest(Q):
    return all(Q[0][0] <= p[0] for p in Q)


CAP = int(sys.argv[1]); EMAX = int(sys.argv[2]); NMAX = int(sys.argv[3])
rng = random.Random(20260829)
COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
P = set()
while len(P) < CAP:
    P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 6))))
P = list(P)

# --- 検算: shTower は行 2 と第 0 列（したがって lev 0）を保つか
c = Counter()
for Q in P:
    for e in range(EMAX + 1):
        for n in range(1, NMAX + 1):
            T = shTower(Q, e, n)
            c['行 2 の並びが保たれる' if [p[2] for p in T] ==
              [p[2] for p in Q] * n else '**行 2 が変わった**'] += 1
            c['lev 0 が保たれる' if lev0(T) == lev0(Q) else '**lev 0 が変わった**'] += 1
            c['行 2 ≡ 0 が保たれる'] += 1 if zero2(Q) == zero2(T) else 0
print('== 検算（母数 %d 個の Q × e=0..%d × n=1..%d）' % (len(P), EMAX, NMAX))
for k in sorted(c, key=str):
    print('   %-28s %d' % (k, c[k]))

# --- (TOW) の事例空間のうち、どれだけが「定理として片づく」か
d = Counter(); hard = []
for Q in P:
    if not root_shallowest(Q):
        continue
    d['側条件（根が最浅）を満たす Q'] += 1
    if zero2(Q):
        d['  **行 2 ≡ 0 ⟹ (TOW) は定理**'] += 1
    else:
        d['  行 2 に 1 がある（難所）'] += 1
        if Wlo(Q):
            d['    Q は孤児の塔でもある'] += 1
        if len(hard) < 2000:
            hard.append(Q)
print('== (TOW) の事例空間')
for k in sorted(d, key=str):
    print('   %-38s %d' % (k, d[k]))

# --- 難所: shTower が既存の証明書（Wlo）で届くか
e2 = Counter(); ex = []
for Q in hard:
    for e in range(EMAX + 1):
        for n in range(2, NMAX + 1):
            T = shTower(Q, e, n)
            if Wlo(T):
                e2['**shTower も孤児の塔 ⟹ 証明できる**'] += 1
            else:
                e2['証明書が届かない'] += 1
                if len(ex) < 6 and Wlo(Q):
                    ex.append((Q, e, n))
print('== 難所（行 2 に 1 がある Q %d 個）で既存の証明書が届く範囲' % len(hard))
for k in sorted(e2, key=str):
    print('   %-38s %d' % (k, e2[k]))
for Q, e, n in ex:
    print('   届かない例（Q は孤児の塔）Q=%s e=%d n=%d -> %s'
          % (''.join(map(str, Q)), e, n, ''.join(map(str, shTower(Q, e, n)))))
