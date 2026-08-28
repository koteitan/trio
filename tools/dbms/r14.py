# -*- coding: utf-8 -*-
"""課題 R10: 3 条項の発火のうち「減を作る発火」は何割か。

`tie_sd` / `aw_flip` を包んで発火を数え、末尾かどうかで分ける。
`rows3.py` は無改変（monkeypatch）。
"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from collections import Counter

C = Counter()
_tie, _aw = rows3.tie_sd, rows3.aw_flip


def tie_probe(Mo, off):
    r = _tie(Mo, off)
    C['tie_sd 呼び出し'] += 1
    if r:
        C['tie_sd **発火**'] += 1
        C['tie_sd 発火（末尾の列）' if off == len(Mo) - 1
          else 'tie_sd 発火（末尾でない）'] += 1
    return r


def aw_probe(Mo, off):
    r = _aw(Mo, off)
    C['aw_flip 呼び出し'] += 1
    if r:
        C['aw_flip **発火**'] += 1
        C['aw_flip 発火（末尾の列）' if off == len(Mo) - 1
          else 'aw_flip 発火（末尾でない）'] += 1
    return r


rows3.tie_sd = tie_probe
rows3.aw_flip = aw_probe

v, L = int(sys.argv[1]), int(sys.argv[2])
P = r7.stts_pool(v, L)
t0 = time.time()
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
V = [(o[i], o[i + 1]) for i in range(len(o) - 1) if IM[o[i]] > IM[o[i + 1]]]
print('ST_TS v<=%d len<=%d  %d 個  %.0fs' % (v, L, len(P), time.time() - t0))
for k in sorted(C, key=str):
    print('   %-26s %d' % (k, C[k]))
print('   **減（順序の破れ）**            %d' % len(V))
print()
print('比率: tie_sd の発火 %d 回のうち、減を作るのは **34 回**（門の実験で確定）= %.4f%%'
      % (C['tie_sd **発火**'], 100.0 * 34 / max(1, C['tie_sd **発火**'])))
print('      aw_flip の発火 %d 回のうち 3〜4 回 = %.4f%%'
      % (C['aw_flip **発火**'], 100.0 * 4 / max(1, C['aw_flip **発火**'])))
