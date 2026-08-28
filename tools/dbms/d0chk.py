# -*- coding: utf-8 -*-
"""(D0') —— **行列 1 本だけ**で柱単調性の破れを予告する計器。

`dmap[k] := dd` を書くとき、書く前の `dmap` に `k' > k` があって
`dmap[k'] <= dd` なら **違反**。もとの深さ `k` と `k'` が像で潰れる、
つまり「同じ状態から `k` を選んだ枝」と「`k'` を選んだ枝」で
seqlex の向きが逆転しうる。

使い方: python3 tools/dbms/d0chk.py [v] [len]
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3

v = int(sys.argv[1]) if len(sys.argv) > 1 else 5
L = int(sys.argv[2]) if len(sys.argv) > 2 else 11

t0 = time.time()
P = r7.stts_pool(v, L)
print('母集団 ST_TS v<=%d len<=%d  %d 個  (%.0fs)' % (v, L, len(P), time.time() - t0),
      flush=True)


def viol(M):
    """(D0') の違反を (off, k, dd, ぶつかる段) で返す。"""
    rows3._DMAP_TRACE = []
    img = tuple(tuple(c) for c in b2d3(list(M)))
    out = []
    for off, k, dd, old in rows3._DMAP_TRACE:
        cl = [kk for kk in range(k + 1, len(old)) if old[kk] <= dd]
        if cl:
            out.append((off, k, dd, tuple(cl)))
    rows3._DMAP_TRACE = None
    return img, out


t0 = time.time()
IM = []
nv = 0
sig = {}
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    img, vs = viol(M)
    IM.append((img, bool(vs)))
    if vs:
        nv += 1
        for _, k, dd, cl in vs:
            sig[(k, dd, cl)] = sig.get((k, dd, cl), 0) + 1
print('(D0\') 違反を持つ行列 **%d / %d**  (%.0fs)' % (nv, len(P), time.time() - t0),
      flush=True)
print('  署名 (もとの深さ k, 像の深さ dd, ぶつかる段) 上位:', flush=True)
for s, c in sorted(sig.items(), key=lambda x: -x[1])[:10]:
    print('    k=%d dd=%d ぶつかる=%s : %d 件' % (s[0], s[1], list(s[2]), c), flush=True)

# --- 順序の破れと突き合わせる
t0 = time.time()
brk = []
for i in range(len(P) - 1):
    if IM[i][0] >= IM[i + 1][0]:
        brk.append(i)
print('順序 (→) の破れ %d 件  (%.0fs)' % (len(brk), time.time() - t0), flush=True)
cov = sum(1 for i in brk if IM[i][1] or IM[i + 1][1])
print('  そのうち (D0\') 違反が**どちらかに**ある: **%d / %d**' % (cov, len(brk)), flush=True)
covL = sum(1 for i in brk if IM[i][1])
print('  深いほう (M1) に違反がある: **%d / %d**' % (covL, len(brk)), flush=True)
print('  ＝ (D0\') は %s' % ('**十分条件の候補**（違反ゼロなら破れゼロ）'
                            if cov == len(brk) else '**破れを覆いきれない**'), flush=True)
