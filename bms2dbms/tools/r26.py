# -*- coding: utf-8 -*-
"""課題 R13（差し替え）: (D0') を**正しい呼び方**で測る。

(D0')  `dmap[k] := dd` を書くとき、書く前の `dmap` に `k' > k` があって
       `dmap[k'] <= dd` なら **違反**（もとの深さ `k` と `k'` が像で潰れる）。

⚠ `b2d3` には**タプルのリスト**を渡すこと（`list(M)`）。
   `[list(c) for c in M]` にすると `conv3` のタプル比較が外れ、
   **縮約が一度も発火しない**（シート 1354 -> 1021、像が変わる行 334/1358）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from collections import Counter


def d0(M):
    """(D0') の違反 [(off, k, dd, ぶつかる段…)] と像を返す。"""
    rows3._DMAP_TRACE = []
    img = tuple(tuple(c) for c in b2d3(list(M)))      # ← タプルのリスト
    out = []
    for off, k, dd, old in rows3._DMAP_TRACE:
        cl = tuple(kk for kk in range(k + 1, len(old)) if old[kk] <= dd)
        if cl:
            out.append((off, k, dd, cl))
    rows3._DMAP_TRACE = None
    return img, out


def run(v, L, order=True, verbose=4):
    t0 = time.time()
    P = r7.stts_pool(v, L)
    print('母集団 ST_TS v<=%d len<=%d  **%d 個**  (%.0fs)'
          % (v, L, len(P), time.time() - t0), flush=True)
    t0 = time.time()
    IM = []; bad = []
    c = Counter()
    for i, M in enumerate(P):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        img, vs = d0(M)
        IM.append(img)
        if vs:
            c['**(D0\') 違反を持つ行列**'] += 1
            bad.append(i)
            for off, k, dd, cl in vs:
                c['違反の署名 (k=%d, dd=%d, ぶつかる段=%s)' % (k, dd, cl)] += 1
        else:
            c["(D0') 違反なし"] += 1
    print('  (D0\') を測った %.0fs' % (time.time() - t0), flush=True)
    for k in sorted(c, key=str):
        print('   %-46s %d' % (k, c[k]))
    if not order:
        return
    S = set(bad)
    dn = [i for i in range(len(P) - 1) if IM[i] > IM[i + 1]]
    print('  順序 (→) の破れ **%d**' % len(dn))
    cov = sum(1 for i in dn if i in S or (i + 1) in S)
    print('  そのうち **どちらかに (D0\') 違反があるもの: %d / %d**' % (cov, len(dn)))
    print('  (D0\') 違反を持つ行列 %d 個のうち、順序の破れに関わるのは %d 個'
          % (len(bad), len(set([i for i in dn] + [i + 1 for i in dn]) & S)))
    for i in dn[:verbose]:
        print('   ### 破れ  M1 に違反 %s / M2 に違反 %s'
              % (i in S, (i + 1) in S))
        print('      M1 = %s' % ''.join(str(x).replace(' ', '') for x in P[i]))
        print('      M2 = %s' % ''.join(str(x).replace(' ', '') for x in P[i + 1]))


if __name__ == '__main__':
    v = int(sys.argv[1]); L = int(sys.argv[2])
    run(v, L, order=(len(sys.argv) < 4 or sys.argv[3] != 'noorder'))
