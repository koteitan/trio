# -*- coding: utf-8 -*-
"""課題 R7: `SeqEmbT3` を **`ST_TS` 展開閉包**で測る。

`seqlex` は Python のタプルの自然順序とまったく同じ:

    seqlex [] N            = (N ≠ [])            ⟺  () < N
    seqlex (p::M) []       = False               ⟺  ¬((p,..) < ())
    seqlex (p::M) (q::N)   = collt p q ∨ (p=q ∧ seqlex M N)
                                                 ⟺  タプルの辞書式

しかも `seqlex` は**狭義全順序**（三分律が成り立つ）なので、
「全対で `seqlex M N ↔ seqlex (f M) (f N)`」は

    `M` の昇順に並べたとき、像も**狭義単調増加**

と同値である（推移律で隣どうしだけ見ればよい）。⟹ 母数の 2 乗は要らない。
"""
import sys, os, time, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, trio
from rows3 import b2d3


def stts_pool(vmax=None, maxlen=10, ns=None):
    """**`tools/dbms/stts.py` の `stts` に一本化した**（課題 R26, 2026-08-29）。

    既定引数 2 つ（`ns=(1,2,3)` / `vmax=5`）が `ST_TS` の定義を狭めていたので
    直した。完全性の証明と、古い既定が何を落としていたかは `stts.py` の
    docstring にある（`|S⟦n⟧| >= n` より `ns=1..maxlen` で完全、
    `diagSeqT 0 v` は `v+1` 列なので `vmax=maxlen-1` で完全）。

    古い挙動が要るときだけ `ns=(1, 2, 3)`（と `vmax=5`）を明示的に渡すこと。
    """
    from stts import stts as _stts
    return _stts(maxlen, vmax=vmax, ns=ns)


def adj(seq):
    """隣どうしの (増 / 等 / 減) を数える。"""
    up = eq = dn = 0
    bad = []
    for i in range(len(seq) - 1):
        a, b = seq[i], seq[i + 1]
        if a < b:
            up += 1
        elif a == b:
            eq += 1
            if len(bad) < 5:
                bad.append(('eq', i))
        else:
            dn += 1
            if len(bad) < 5:
                bad.append(('dn', i))
    return up, eq, dn, bad


def run(vmax, maxlen, verbose=3):
    t0 = time.time()
    P = stts_pool(vmax, maxlen)
    print('母集団: ST_TS 展開閉包 v<=%d len<=%d  **%d 個**  (%.1fs)'
          % (vmax, maxlen, len(P), time.time() - t0))
    from collections import Counter
    print('  長さ分布', sorted(Counter(len(m) for m in P).items()))

    t0 = time.time(); IM = []
    for i, M in enumerate(P):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        IM.append(tuple(tuple(c) for c in b2d3(list(M))))
    print('  像を計算 %.1fs' % (time.time() - t0))

    # ---- 本番: M の昇順で像が狭義単調増加か（両向きを別々に）
    order = sorted(range(len(P)), key=lambda i: P[i])
    img_by_M = [IM[i] for i in order]
    up, eq, dn, bad = adj(img_by_M)
    n = len(P) - 1
    print()
    print('== (→) seqlex M N → seqlex (f M) (f N)   隣 %d 対' % n)
    print('   増 %d / **等 %d（＝ 像の重複）** / **減 %d（＝ 逆転）**' % (up, eq, dn))
    print('   ⟹ 破れ **%d**' % (eq + dn))
    for k, i in bad[:verbose]:
        print('   例 %s: M1=%s' % (k, ''.join(str(c).replace(' ', '')
                                              for c in P[order[i]])))
        print('        M2=%s' % ''.join(str(c).replace(' ', '')
                                        for c in P[order[i + 1]]))
        print('        f M1=%s' % ''.join(str(c).replace(' ', '')
                                          for c in img_by_M[i]))
        print('        f M2=%s' % ''.join(str(c).replace(' ', '')
                                          for c in img_by_M[i + 1]))

    order2 = sorted(range(len(P)), key=lambda i: IM[i])
    M_by_img = [P[i] for i in order2]
    up2, eq2, dn2, bad2 = adj(M_by_img)
    print('== (←) seqlex (f M) (f N) → seqlex M N   隣 %d 対' % n)
    print('   増 %d / 等 %d / **減 %d（＝ 逆転）**' % (up2, eq2, dn2))
    print('   ⟹ 破れ **%d**' % (eq2 + dn2))

    # ---- 陽性対照
    print()
    print('== 陽性対照（どれも「ほぼ全部破れる」はず）')
    print('   P1 向きを逆（像が狭義**減少**を要求）: 破れ %d / %d' % (up + eq, n))
    im3 = [IM[i][:-1] for i in order]
    u3, e3, d3, _ = adj(im3)
    print('   P2 像の末尾 1 柱を落とす: 破れ %d / %d' % (e3 + d3, n))
    im4 = [P[order[i]] for i in range(len(order))]   # f = 恒等（負の対照）
    u4, e4, d4, _ = adj(im4)
    print('   P3 f = 恒等（**負**の対照。0 になるはず）: 破れ %d / %d' % (e4 + d4, n))
    im5 = [tuple(reversed(x)) for x in img_by_M]
    u5, e5, d5, _ = adj(im5)
    print('   P4 像を逆順に並べ替える: 破れ %d / %d' % (e5 + d5, n))
    # ---- 隣どうしで十分なことの裏取り: 無作為の非隣接対を直に判定
    import random
    random.seed(7)
    nchk = bad2 = 0
    for _ in range(200000):
        i, j = random.randrange(len(P)), random.randrange(len(P))
        if i == j:
            continue
        nchk += 1
        if (P[i] < P[j]) != (IM[i] < IM[j]):
            bad2 += 1
    print('   裏取り: 無作為の非隣接対 %d 個を直に判定 -> 破れ %d' % (nchk, bad2))
    return P, IM, order


if __name__ == '__main__':
    v = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    run(v, L)
