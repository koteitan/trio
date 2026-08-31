# -*- coding: utf-8 -*-
"""課題 R42: **`B` を最小で切る再帰は何段で底に着くか。**

§R39 の残り 6930 件のうち 42% は「切った左片 `A ++ B1` がまた届かない」だった。
`B1` は毎回**真に短くなる**ので有限段で底に着く。**底で何が起きるか**を測る。

    A ++ B  ->  (A ++ B1) ++ B2   （B1 = B.take s, B2 = B.drop s, s = 最初の最小の位置）
    s = 0 なら **B の根は既に B 内で最浅** ⟹ 切っても進まない ＝ **底**
    左片 `A ++ B1` が届かなければ `B1` をさらに切る

底に着いたとき残るのは **`rsum` が `A` 側に対して破れている**ことだけ。
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from r60 import why2, lev0, wadd_ok
from r61 import cat_direct


def argmin0(B):
    mn = min(p[0] for p in B)
    return next(j for j, p in enumerate(B) if p[0] == mn)


def solve(A, B, trace):
    """段数を数えながら再帰。戻り値 (理由, 段数, **底での (A,B)**)。"""
    for step in range(0, 60):
        trace[:] = [A, B]                 # **底での状態**を記録（原因の診断に使う）
        if cat_direct(A, B):
            return ('解決', step, A, B)
        if len(B) < 2:
            return ('底: |B| < 2', step, A, B)
        s = argmin0(B)
        if s == 0:
            return ('底: B の根が既に B 内で最浅', step, A, B)
        B1, B2 = B[:s], B[s:]
        if why2(B1) is None:
            return ('底: 左片 B1 に証明書が無い', step, A, B)
        if why2(B2) is None:
            return ('底: 右片 B2 に証明書が無い', step, A, B)
        if lev0(B1) > lev0(A):
            return ('底: lev B1 0 > lev A 0', step, A, B)
        # 左片が届くなら、右片を継ぐ問題に進む
        if cat_direct(A, B1):
            T1 = A + B1
            if lev0(B2) <= lev0(T1) and wadd_ok(T1, B2):
                return ('解決（W_add で右片を継げた）', step + 1, A, B)
            A, B = T1, B2                 # 右片の問題に進む
        else:
            B = B1                        # 左片がまだ届かない ⟹ B1 をさらに切る
        trace.append(len(B))
    return ('60 段で打ち切り', 60, A, B)


CAP = int(sys.argv[1]); PAIRS = int(sys.argv[2])
rng = random.Random(20260829)
COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
P = set()
while len(P) < CAP:
    P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 6))))
OK = [M for M in P if why2(M) is not None]
c = Counter(); dep = Counter(); n = 0; bot = []
while n < PAIRS:
    A = rng.choice(OK); B = rng.choice(OK)
    if A == B or lev0(B) > lev0(A):
        continue
    n += 1
    if cat_direct(A, B):
        continue
    tr = []
    r = solve(A, B, tr)
    c[r[0]] += 1
    dep['段数 %d' % r[1]] += 1
    if r[0].startswith('底') and len(bot) < 4000:
        bot.append((r[2], r[3], r[0]))       # **底での (A,B)**
print('== `B` を最小で切る再帰の行き先（A != B、母数 %d 組、届かないものだけ）' % PAIRS)
for k in sorted(c, key=str):
    print('   %-44s %d' % (k, c[k]))
print('== 段数の分布')
for k in sorted(dep, key=lambda s: int(s.split()[1])):
    print('   %-12s %d' % (k, dep[k]))
print('== 底に着いた事例で `rsum` が破れる原因')
f = Counter()
for A, B, why in bot:
    mnB = min(p[0] for p in B); mnA = min(p[0] for p in A)
    f['**A に B の最浅より浅い列がある**' if mnA < mnB else 'A は全部 B の最浅以上'] += 1
    f['  lev B 0 > lev A 0（段が合わない）' if lev0(B) > lev0(A) else '  段は合う'] += 1
    f['  B の根 = B の最浅' if B[0][0] == mnB else '  B の根 != B の最浅'] += 1
    f['  [%s]' % why] += 1
for k in sorted(f, key=str):
    print('   %-44s %d' % (k, f[k]))
