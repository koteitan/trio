# -*- coding: utf-8 -*-
"""H13 (2)(3): `conv_resid` のループが 2 周する入力があるか / `rest2` は単一の木か。"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
from rows3 import gen3, key
from core import expand, show

C = Counter()
EX = []
_orig = rows3.conv_resid


def wrapped(rest, rd, Lr, ps, pw, st, nx, off):
    r, n = list(rest), 0
    while r:
        m0 = r[0][0]
        i = 1
        while i < len(r) and r[i][0] >= m0:
            i += 1
        n += 1
        r = r[i:]
    C['木の本数 %d' % n] += 1
    C['_呼び出し'] += 1
    if n >= 2 and len(EX) < 6:
        EX.append((tuple(st['Mo']), tuple(map(tuple, rest)), off))
    if rest:
        # rest2[0][0] は最小か（＝ conv_resid の切り方で 1 本になるか）
        C['先頭が最小' if rest[0][0] == min(x[0] for x in rest)
          else '**先頭が最小でない**'] += 1
    return _orig(rest, rd, Lr, ps, pw, st, nx, off)


rows3.conv_resid = wrapped
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 7
nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 0
t0 = time.time()
A = sorted(gen3('BMS', lim, zcap=1), key=key)
Ms = [tuple(map(tuple, M)) for M in A]
if nmax:
    for M in list(Ms):
        for n in range(1, nmax + 1):
            x = [tuple(y) for y in expand(M, n)]
            if x:
                Ms.append(tuple(x))
for i, M in enumerate(Ms):
    if i % 20000 == 0:
        import core
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    rows3.b2d3(list(M))
print('lim=%d 展開 n<=%d: 行列 %d 個  (%.0fs)' % (lim, nmax, len(Ms), time.time() - t0))
for k, v in sorted(C.items(), key=str):
    print('   %-22s %d' % (k, v))
for Mo, rest, off in EX:
    print('   例 %s  off=%d rest=%s' % (show([list(x) for x in Mo]), off,
                                        show([list(x) for x in rest])))
