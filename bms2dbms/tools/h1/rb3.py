# -*- coding: utf-8 -*-
"""**(R-D0) —— 弱い 3 本（`Inj3` / `OrderReindexT3` / `SandwichUReindexT3`）は真か。**

## ⚠ 定義（`lean/Dbms3.lean` 逐語）

    `Dbms3:2156`  def Inj3 (conv3) := ∀ {M N}, ST_TS M → ST_TS N → conv3 M = conv3 N → M = N

    `Dbms3:2189`  def OrderReindexT3 (conv3) :=
      ∀ {A B}, ST_TS A → ST_TS B → ∀ {n m}, 1 <= n → n + 1 <= m →
        **(conv3 A)⟦m⟧ = conv3 B** →
          (seqlex (conv3 (A⟦n⟧)) (conv3 B) → translate (A⟦n⟧) <o translate B) ∧
          (seqlex (conv3 B) (conv3 A) → translate B <o translate A)

    `Dbms3:2216`  def SandwichUReindexT3 (conv3) :=
      ∀ {A B}, ST_TS A → 1 < A.length → ST_TS B → ∀ {n m},
        1 <= n → n + 1 <= m → **(conv3 A)⟦m⟧ = conv3 B** → sle3 (conv3 (A⟦n⟧)) (conv3 B)

    `Seqlex:22`   collt p q := p.1<q.1 ∨ (p.1=q.1 ∧ (p.2.1<q.2.1 ∨ (p.2.1=q.2.1 ∧ p.2.2<q.2.2)))
    `Seqlex:25`   seqlex [] N := N ≠ [] ／ seqlex (_::_) [] := False
                  seqlex (p::M) (q::N) := collt p q ∨ (p = q ∧ seqlex M N)
    `Dbms3:1994`  sle3 M N := M = N ∨ seqlex M N

## ★★★★★ 順序が組合せに落ちます（`Seqlex:717` 逐語）

    theorem olt_ST_iff_seqlex (hM : ST_TS M) (hN : ST_TS N) (hne : M ≠ N) :
      **(translate M <o translate N ↔ seqlex M N)**
    ⟹ ★ `ST_TS` 上では **`<o` は `seqlex`（BMS 側）そのもの** ⟹ **順序数を計算せずに測れます**
    ⚠ `M = N` のときは両辺とも偽なので、そのまま使えます。

## ⚠ 母集団（規則 9）—— **「相手は像の展開の逆像に限る」の意味**

    ★ **`B` は `conv3 B = (conv3 A)⟦m⟧` を満たすものだけ** ⟹ **`B` は自由に動けません**
    ⟹ ★ 作り方: `Y := (conv3 A)⟦m⟧` ⟹ `B := inv3.d2b3(Y)` ⟹ **`conv3 B == Y` を検算してから使う**
    `A`: `rows3.gen3('BMS', lim, 1)` の標準形。`m ∈ [2, mmax]`、`n ∈ [1, m-1]`。
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, inv3
from collections import Counter
from core import expand

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def seqlex(M, N):
    """`Seqlex:25` 逐語（`collt` はタプルの辞書式と一致）。"""
    for p, q in zip(M, N):
        if p != q: return p < q
    return len(M) < len(N)


def sle3(M, N): return M == N or seqlex(M, N)
def T(M): return tuple(map(tuple, M))


def run(lim, mmax, tag):
    t0 = time.time()
    MS = [M for M in rows3.gen3('BMS', lim, 1) if len(M) >= 2]
    c = Counter(); exO = []; exU = []
    # ---- Inj3 ----
    img = {}
    for M in MS:
        try: f = T(rows3.b2d3(list(M)))
        except Exception: c['⛔ conv3 が落ちる'] += 1; continue
        c['Inj3 分母'] += 1
        if f in img:
            c['⛔ Inj3 の破れ'] += 1
            if len(exO) < 2: exO.append(('Inj3', img[f], M))
        else: img[f] = M
    # ---- Reindex 2 本 ----
    for A in MS:
        try: fA = T(rows3.b2d3(list(A)))
        except Exception: continue
        for m in range(2, mmax + 1):
            Y = T(expand(fA, m))
            try: B = T(inv3.d2b3(Y))
            except Exception: c['逆像なし'] += 1; continue
            if not B: c['逆像なし'] += 1; continue
            try: fB = T(rows3.b2d3(list(B)))
            except Exception: c['逆像なし'] += 1; continue
            if fB != Y: c['⛔ 逆像の検算が合わない（除外）'] += 1; continue
            c['★ (A,B,m) の組'] += 1
            for n in range(1, m):
                An = T(expand(T(A), n))
                try: fAn = T(rows3.b2d3([list(x) for x in An]))
                except Exception: continue
                c['★ (A,B,n,m) の組（分母）'] += 1
                # OrderReindexT3
                o1 = (not seqlex(fAn, fB)) or seqlex(An, B)
                o2 = (not seqlex(fB, fA)) or seqlex(B, A)
                c['★ OrderReindexT3 (1)'] += o1
                c['★ OrderReindexT3 (2)'] += o2
                c['★★ OrderReindexT3 両方'] += (o1 and o2)
                if not (o1 and o2) and len(exO) < 4:
                    exO.append(('Order', A, B, n, m, o1, o2))
                # SandwichUReindexT3（`1 < |A|` が前提）
                if len(A) > 1:
                    u = sle3(fAn, fB)
                    c['SandwichU 分母'] += 1
                    c['★ SandwichUReindexT3'] += u
                    if not u and len(exU) < 4: exU.append((A, B, n, m))
    n1 = c['Inj3 分母']; n2 = c['★ (A,B,n,m) の組（分母）']; n3 = c['SandwichU 分母']
    print('  [%s] 標準形 %d 個（%.1f 秒）' % (tag, len(MS), time.time() - t0))
    print('     ★ Inj3: 分母 %d ／ ⛔ 破れ %d = %.4f%%' % (n1, c['⛔ Inj3 の破れ'], pct(c['⛔ Inj3 の破れ'], n1)))
    print('     ★ (A,B,m) の組 %d ／ 逆像なし %d ／ ⛔ 検算不一致 %d'
          % (c['★ (A,B,m) の組'], c['逆像なし'], c['⛔ 逆像の検算が合わない（除外）']))
    if n2:
        print('     ★★ OrderReindexT3: 分母 %d ／ (1) %.4f%% ／ (2) %.4f%% ／ **両方 %.4f%%**（⛔ 破れ %d）'
              % (n2, pct(c['★ OrderReindexT3 (1)'], n2), pct(c['★ OrderReindexT3 (2)'], n2),
                 pct(c['★★ OrderReindexT3 両方'], n2), n2 - c['★★ OrderReindexT3 両方']))
    if n3:
        print('     ★★ SandwichUReindexT3: 分母 %d ／ **%.4f%%**（⛔ 破れ %d）'
              % (n3, pct(c['★ SandwichUReindexT3'], n3), n3 - c['★ SandwichUReindexT3']))
    for e in exO[:3]: print('     ⛔ Order の破れ:', e)
    for e in exU[:3]: print('     ⛔ SandwichU の破れ:', e)
    if n2 and c['★★ OrderReindexT3 両方'] == n2 and n3 and c['★ SandwichUReindexT3'] == n3:
        print('     ★★★★★ **3 本とも破れ 0**')
    return c


import sys as _s
for lim, mmax in ((int(_s.argv[1]), int(_s.argv[2])),):
    run(lim, mmax, 'lim=%d, m<=%d' % (lim, mmax))
