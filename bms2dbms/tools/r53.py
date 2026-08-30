# -*- coding: utf-8 -*-
"""課題 R33-1: **`(TOW)` = `ShiftTowerClosed`** を健全な反証器で測り直す。

`lean/Wtower2.lean:1763`:

    ShiftTowerClosed : ∀ (u e n : ℕ) (Q : TrioSeq),
      Q ∈ W u → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) → **shTower Q e n ∈ W u**

    ShiftTowerClosedS (:1771) は側条件が**狭義**:
      (∀ j, 1 ≤ j → j < |Q| → entry Q 0 0 < entry Q 0 j)

    shTower Q e n = (range n).flatMap (k => shiftr01 (k*e) 0 Q)
                  = **Q の写しを n 個、k 番目は行 0 を k*e だけ沈めて並べる**

`PROOF-STATUS §4` の 1642293 例は `inW` の退化（教訓 12）で**空虚**。ここが
`WSnoc` の証明が循環する先でもある（team-lead / L2 が確定）。

## 入力の証明書（`Q ∈ W u` が**確定**している Q だけを使う）

    (i)  **行 2 ≡ 0**  ⟹ `zeroRow2_mem_Wself`（`Wtower2.lean:2985`、**証明ずみ**）で
         `Q ∈ W (lev Q 0)`。さらに `W_mono` で `u >= lev Q 0` すべて。
    (ii) **孤児の塔**（`r49.Wlo`）⟹ 任意の u で `Q ∈ W u`。

## 出力の反証（**健全**）

    refute(shTower Q e n, u) = True   ⟹ `shTower Q e n ∉ W u` が**証明された**
    Wup(shTower Q e n, u)    = False  ⟹ 同上（独立な計器）
    ⟹ **どちらが出ても `(TOW)` の本物の反例**

## 陽性対照（教訓 12）

`Q ∈ W u` を**満たさない** Q（`u < lev Q 0` かつ孤児の塔でもない）で
`refute(shTower Q e n, u)` が True を返す例が実在するか。
出ないなら、この出力の形では反証器に判別力が無い。
"""
import sys, time, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from refute import refute
from r49 import Wlo, Wup


def lev0(Q):
    return 2 * Q[0][1] + Q[0][2] if Q else 0


def shTower(Q, e, n):
    return tuple((p[0] + k * e, p[1], p[2]) for k in range(n) for p in Q)


def root_shallowest(Q):
    return all(Q[0][0] <= p[0] for p in Q)


def root_strict(Q):
    return all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))


def gen_Q(cap, lmax, amax, bmax, seed=20260829, zero2=True):
    """行 2 ≡ 0（`zeroRow2_mem_Wself` の族）の Q を乱択で作る。"""
    rng = random.Random(seed)
    COLS = [(a, b, 0 if zero2 else c)
            for a in range(amax) for b in range(bmax) for c in range(2)]
    out = set()
    while len(out) < cap:
        out.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, lmax))))
    return list(out)


if __name__ == '__main__':
    CAP = int(sys.argv[1]); EMAX = int(sys.argv[2]); NMAX = int(sys.argv[3])
    DEP = int(sys.argv[4]); NS = int(sys.argv[5])
    UEX = int(sys.argv[6]) if len(sys.argv) > 6 else 2   # u を lev0 から何段上まで
    Q0 = gen_Q(CAP, 5, 6, 5)
    # ---- まず数えるだけ（今日の規則）
    c = Counter()
    for Q in Q0:
        c['行 2 ≡ 0 の Q'] += 1
        if root_shallowest(Q): c['  側条件（弱、根が最浅）を満たす'] += 1
        if root_strict(Q):     c['  側条件（強、狭義最浅）を満たす'] += 1
        if Wlo(Q):             c['  孤児の塔でもある'] += 1
    for k in sorted(c, key=str):
        print('  %-34s %d' % (k, c[k]))
    QW = [Q for Q in Q0 if root_shallowest(Q)]
    QS = [Q for Q in Q0 if root_strict(Q)]
    print('前提を満たす (Q,e,n,u) の組: 弱 %d  強 %d  (e=0..%d, n=2..%d, u は lev0..lev0+%d)'
          % (len(QW) * (EMAX + 1) * (NMAX - 1) * (UEX + 1),
             len(QS) * (EMAX + 1) * (NMAX - 1) * (UEX + 1), EMAX, NMAX, UEX),
          flush=True)

    # ---- 陽性対照: Q ∈ W u を**満たさない** Q で反証器が鳴るか
    print('== 陽性対照（教訓 12）: `Q ∈ W u` を満たさない Q で反証器が鳴るか', flush=True)
    mc = {}; cc = Counter()
    for Q in Q0[:600]:
        u = lev0(Q) - 1                       # **証明書の外**（W_mono も効かない）
        if u < 0 or Wlo(Q):
            continue
        for e in range(EMAX + 1):
            for n in range(2, NMAX + 1):
                T = shTower(Q, e, n)
                r = refute(T, u, DEP, mc, NS)
                cc['refute が鳴った' if r is True else
                   ('所属側' if r is False else '不明')] += 1
    print('   %s' % dict(cc), flush=True)
    if cc['refute が鳴った'] == 0:
        print('   ⚠ **鳴らない ⟹ この出力の形では判別力が無い**', flush=True)

    # ---- 本番
    for nm, QQ in [('弱（根が最浅）', QW), ('強（狭義最浅）', QS)]:
        c = Counter(); bad = []; memo = {}; t0 = time.time()
        for Q in QQ:
            if time.time() - t0 > 600:
                c['**時間切れ**'] += 1; break
            if len(memo) > 1500000: memo.clear()
            base = 0 if Wlo(Q) else lev0(Q)   # 孤児の塔なら任意の u で証明書がある
            for u in range(base, base + UEX + 1):
                for e in range(EMAX + 1):
                    for n in range(2, NMAX + 1):
                        T = shTower(Q, e, n)
                        r = refute(T, u, DEP, memo, NS)
                        w = Wup(T, u, DEP, memo.setdefault('_w', {}), NS, 40) \
                            if not isinstance(memo.get('_w'), type(None)) else None
                        if r is True:
                            c['**(TOW) の反例（refute）**'] += 1
                            if len(bad) < 8: bad.append((Q, e, n, u))
                        elif r is False:
                            c['所属側'] += 1
                        else:
                            c['不明'] += 1
        print('== `(TOW)` %s  (%.0fs)' % (nm, time.time() - t0))
        for k in sorted(c, key=str):
            print('   %-34s %d' % (k, c[k]))
        for Q, e, n, u in bad:
            print('   反例 Q=%s e=%d n=%d u=%d  ->  %s'
                  % (''.join(map(str, Q)), e, n, u,
                     ''.join(map(str, shTower(Q, e, n)))))
