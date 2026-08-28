# -*- coding: utf-8 -*-
"""**測定 (N')**（課題 L46、L2 の依頼）—— `ResidHeadT` と `Dm11` が同時に片づくか。

    (N')  convResid の呼び出し点で rest2 != [] のとき
          **|st.dmap| == rest2[0][0]**       ← 「<=」ではなく **等号**

真なら `ResidHeadT`（`rest2.head.1 <= |dmap|`）はその系で、さらに `DmOK` と `DmST`
から `Dm11` が新しい不変量なしで出る（L2 の解析）。

陽性対照（必ず鳴るはず）: `== rest2[0][0] + 1` と `== rest2[0][0] - 1`。

弱い版 (M) も同時に測る:

    (M)  ∀ k < j < |dmap|,  dmap[k] <= dmap[j] + 1      （+1 までの非狭義単調性）
    陽性対照: `<= dmap[j]`（狭義単調は偽と記録ずみ ⟹ **必ず鳴る**）と `<= dmap[j] - 1`

使い方: python3 tools/dbms/residhead.py [gen3 の列数] [ST_TS の列数]
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core
from rows3 import b2d3, gen3

G = int(sys.argv[1]) if len(sys.argv) > 1 else 8
L = int(sys.argv[2]) if len(sys.argv) > 2 else 0


def run(pool, tag):
    eq = hi = lo = other = 0
    nn_ok = nn_c1 = nn_c2 = nonempty = 0
    m_ok = m_eq = m_lo = tot_m = 0
    ex = []
    t0 = time.time()
    for i, M in enumerate(pool):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        rows3._RESID_TRACE = []
        b2d3(list(M))
        for n, h, p0, dm in rows3._RESID_TRACE:
            if n == h:
                eq += 1
            elif n == h + 1:
                hi += 1
            elif n == h - 1:
                lo += 1
            else:
                other += 1
            if h <= n + 1: nn_ok += 1
            if h <= n:     nn_c1 += 1
            if h <= n - 1: nn_c2 += 1
            if dm:         nonempty += 1
            if len(ex) < 4 and n != h:
                ex.append((M, n, h, p0, dm))
            for j in range(len(dm)):
                for k in range(j):
                    tot_m += 1
                    if dm[k] <= dm[j] + 1: m_ok += 1
                    if dm[k] <= dm[j]:     m_eq += 1
                    if dm[k] <= dm[j] - 1: m_lo += 1
        rows3._RESID_TRACE = None
    tot = eq + hi + lo + other
    print('=== %s  呼び出し点 **%d 件**  (%.0fs)' % (tag, tot, time.time() - t0), flush=True)
    if tot:
        print('  **(N\') |dmap| == rest2[0][0]  : %d / %d（%.2f%%）**'
              % (eq, tot, 100.0 * eq / tot), flush=True)
        print('  陽性対照 == +1 : %d / == -1 : %d / その他 : %d'
              % (hi, lo, other), flush=True)
        print('  ⟹ (N\') は %s' % ('**真**' if eq == tot else '**偽**'), flush=True)
        print('  **(N\'\') h <= |dmap| + 1 : %d / %d（%.2f%%）**'
              % (nn_ok, tot, 100.0 * nn_ok / tot), flush=True)
        print('  陽性対照 h <= |dmap|     : %d（破れ **%d**）' % (nn_c1, tot - nn_c1), flush=True)
        print('  陽性対照 h <= |dmap| - 1 : %d（破れ **%d**）' % (nn_c2, tot - nn_c2), flush=True)
        print('  **stU.dmap != [] : %d / %d（%.2f%%）**'
              % (nonempty, tot, 100.0 * nonempty / tot), flush=True)
        print('  ⟹ (N\'\') は %s / 対照は %s'
              % ('**真**' if nn_ok == tot else '**偽**',
                 '**鳴っている**' if tot - nn_c1 > 0 else '**鳴っていない**'), flush=True)
    if tot_m:
        print('  **(M) dmap[k] <= dmap[j] + 1 : %d / %d（%.2f%%）**'
              % (m_ok, tot_m, 100.0 * m_ok / tot_m), flush=True)
        print('  陽性対照 <= dmap[j] : %d（%.2f%%）/ <= dmap[j]-1 : %d（%.2f%%）'
              % (m_eq, 100.0 * m_eq / tot_m, m_lo, 100.0 * m_lo / tot_m), flush=True)
        print('  ⟹ (M) は %s' % ('**真**' if m_ok == tot_m else '**偽**'), flush=True)
    for M, n, h, p0, dm in ex:
        print('   反例 |dmap|=%d rest2[0][0]=%d p[0]=%d dmap=%s'
              % (n, h, p0, list(dm)), flush=True)
        print('        M=%s' % ''.join('(%d,%d,%d)' % c for c in M), flush=True)


t0 = time.time()
P = gen3('BMS', G, zcap=1)
print('母集団 gen3(BMS, <=%d, zcap=1) = ST_TS ∩ {len<=%d}  **%d 個**  (%.0fs)'
      % (G, G, len(P), time.time() - t0), flush=True)
run(P, 'gen3 <=%d' % G)
if L:
    import r7
    Q = r7.stts_pool(maxlen=L)
    print(flush=True)
    print('母集団 ST_TS 展開閉包 len<=%d  **%d 個**' % (L, len(Q)), flush=True)
    run(Q, 'ST_TS len<=%d' % L)
