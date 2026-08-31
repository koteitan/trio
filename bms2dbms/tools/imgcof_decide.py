# -*- coding: utf-8 -*-
"""**`ImgCofinalT3` の真偽を決める全数探索。**

⚠⚠ **この計器の前提は誤りだった**（課題 R29 / R1、2026-08-29）。**使わないこと。**

書いたときの前提: 「`conv3` は 1 列につき 1 柱以上出すので `|conv3 B| >= |B|`、
つまり `conv3 B = T` なら `|B| <= |T|`。だから `|T| <= 11` なら全数探索で確定する。」

**これは偽。** `conv3` は**縮約で縮む**。R1 が `gen3(BMS,<=7,zcap=1)` 全数で測った:

    |B|            1   2   3   4   5   6   7
    min |conv3 B|  1   2   3   4   4   5   5

**`min |conv3 B|` は `|B|` のおよそ半分の速さでしか伸びない。**
⟹ `|T| = 16` の `T` の逆像 `B` は **`|B| = 30` くらいでもありうる**。
表を 9 列に伸ばしても上限が 16 -> 18 になるだけで、必要な 30 列には**絶対に届かない**。

⟹ **像の表による全数判定は `ImgCofinalT` に原理的に使えない。**
決着させるには **`T` の形から `|B|` の上界を出す構文的な補題**が要る。
**数値実験では進まない**（教訓 13: 母数を増やしても届かない形の失敗）。

使い方: python3 bms2dbms/tools/imgcof_decide.py
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import expand, isstd


def parse(s):
    out = []
    for t in s.replace(' ', '').split(')'):
        t = t.strip('(')
        if t:
            out.append(tuple(int(x) for x in t.split(',')))
    return tuple(out)


def sh(M):
    return ''.join('(%d,%d,%d)' % tuple(c) for c in M)


t0 = time.time()
P = r7.stts_pool(5, 11)
img = {}
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    img[tuple(map(tuple, b2d3(list(M))))] = M
print('母集団 ST_TS v<=5 len<=11  %d 個 / 像の表 %d 通り  (%.0fs)'
      % (len(P), len(img), time.time() - t0), flush=True)
Pset = set(P)

CASES = [
    ('外れ続ける 1', '(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)(3,1,0)'),
    ('外れ続ける 2', '(0,0,0)(1,1,1)(1,1,1)(1,0,0)(2,1,1)(2,1,0)(3,2,1)'),
    ('外れ続ける 3', '(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)'),
    ('陽性対照',     '(0,0,0)(1,1,1)(2,2,1)(2,2,0)'),
]
print(flush=True)
for tag, s in CASES:
    A = parse(s)
    print('=== %s  A=%s   ST_TS=%s' % (tag, sh(A), A in Pset), flush=True)
    fA = tuple(map(tuple, b2d3(list(A))))
    for m in range(2, 13):
        T = tuple(map(tuple, expand(fA, m)))
        if not T:
            break
        if len(T) > 11:
            print('   m=%-2d |T|=%-3d  **母集団の外（|B| <= |T| が 11 を超える）**'
                  % (m, len(T)), flush=True)
            continue
        B = img.get(T)
        print('   m=%-2d |T|=%-3d DBMS標準形=%-5s **全数探索の逆像=%s**'
              % (m, len(T), isstd(T, 'DBMS'), sh(B) if B else '**無し（確定）**'),
              flush=True)
