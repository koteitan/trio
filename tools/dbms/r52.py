# -*- coding: utf-8 -*-
"""`tools/refute.py`（L47）と `tools/dbms/r49.py` の `Wup` の突き合わせ。

どちらも「`M not in W u`」を健全に主張する道具だが、作りが違う:

    refute(M,u) = True   … (W3) の対偶。底は `lev M[0] > u`
    Wup(M,u)    = False  … 節 1/2/3 を三値で展開。節 3 は `dropLast` に緩める

**両方とも健全なので、片方が「非所属」と言い、もう片方が「所属（True）」と
言ったら、どちらかにバグがある。**それを探す。
"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import refute as R
from r49 import Wup, Wlo, has_parent, towers, towers_deep

U = int(sys.argv[1]); N = int(sys.argv[2]); DEP = int(sys.argv[3])
CAP = int(sys.argv[4]); DEEP = len(sys.argv) > 5 and sys.argv[5] == 'deep'
COLS = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
T = towers_deep(COLS, 4, 12, CAP) if DEEP else towers(COLS, 6, CAP)
print('u=%d  n=1..%d  depth=%d  C %d 個  長さ %s'
      % (U, N, DEP, len(T), dict(sorted(Counter(len(C) for C in T).items()))),
      flush=True)

c = Counter(); bad = []; m1 = {}; m2 = {}; t0 = time.time()
for i, C in enumerate(T):
    if time.time() - t0 > 900:
        c['**時間切れ（C %d / %d）**' % (i, len(T))] += 1; break
    if len(m1) > 1500000: m1.clear()
    if len(m2) > 1500000: m2.clear()
    for p in [q for q in COLS if has_parent(C + (q,), len(C))]:
        S = C + (p,)
        a = R.refute(S, U, DEP, m1, N)         # True なら S not in W U
        b = Wup(S, U, DEP, m2, N, 26)          # False なら S not in W U
        if a is True and b is True:
            c['**矛盾: refute は非所属、Wup は所属**'] += 1
            if len(bad) < 6: bad.append((S, 'refute=True, Wup=True'))
        elif a is True and b is False:
            c['両方とも非所属（一致）'] += 1
        elif a is True and b is None:
            c['refute だけが非所属を証明'] += 1
        elif b is False and a is not True:
            c['Wup だけが非所属を証明'] += 1
        elif b is True:
            c['Wup は所属、refute は不明'] += 1
        else:
            c['どちらも不明'] += 1
print('--- 結果 (%.0fs)' % (time.time() - t0))
for k in sorted(c, key=str):
    print('    %-42s %d' % (k, c[k]))
for e in bad:
    print('    ', ''.join(map(str, e[0])), e[1])
