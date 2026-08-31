# -*- coding: utf-8 -*-
"""課題 R9 の続き: 綴りが**浅くなる 41 か所**を、条項ごと切らずに潰せるか。

観測: 41 件のうち 34 件は「その分岐列が `M1` の**末尾の列**」で、`tie_sd` が
末尾で深く綴るために起きる。そこで `tie_sd` / `aw_flip` に

    「行列の末尾の列では発火しない」

という門を足して（`rows3.py` は触らず monkeypatch）、順序とシート点を測る。
"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3

MODE = sys.argv[1] if len(sys.argv) > 1 else 'tie'
_tie, _aw = rows3.tie_sd, rows3.aw_flip


def tie_end(Mo, off):
    if off == len(Mo) - 1:
        return False
    return _tie(Mo, off)


def aw_end(Mo, off):
    if off == len(Mo) - 1:
        return False
    return _aw(Mo, off)


if MODE in ('tie', 'both'):
    rows3.tie_sd = tie_end
if MODE in ('aw', 'both'):
    rows3.aw_flip = aw_end

v, L = int(sys.argv[2]), int(sys.argv[3])
P = r7.stts_pool(v, L)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
dn = sum(1 for i in range(len(o) - 1) if IM[o[i]] > IM[o[i + 1]])
eq = sum(1 for i in range(len(o) - 1) if IM[o[i]] == IM[o[i + 1]])
ns = sum(1 for B in IM if not core.isstd(B, 'DBMS'))
import sheet3
ok, tot = 0, 0
for row, b, d in sheet3.load(1):
    tot += 1
    if tuple(b2d3(b)) == d:
        ok += 1
print('門 %-5s  ST_TS v<=%d len<=%d %d 個  **順序の破れ %d**（逆転 %d / 重複 %d）'
      '  非標準の像 %d  **シート %d/%d**'
      % (MODE, v, L, len(P), dn + eq, dn, eq, ns, ok, tot))
