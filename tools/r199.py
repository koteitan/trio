# -*- coding: utf-8 -*-
"""(z1a)(z1b) 理由 (A)(D)(B) ごとの `V` の構造。

(A) = 孤児の列 `j` に対し「`V` の中で行 2 が `V[j]` より小さい列が 1 本も無い」。
断片では `V[j][2] = 1` なので **`V[0..j-1]` の行 2 が全部 1**。
**⟹ team-lead の問い: `V` **全体**の行 2 も全部 1 か。**
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r195 import h2cone
from r196 import why


def run(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter(); tries = 0
    while c['Q'] < nsamp and tries < nsamp * 300:
        tries += 1
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), rnd.randrange(2))] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if h2cone(Q): continue
        c['Q'] += 1
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j0 in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j0 + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None: continue
                V = [tuple(x) for x in S[par:last]]
                if len(V) < 2: continue
                for j in h2cone(V):
                    r = why(V, j)[:3]
                    c[('理由', r)] += 1
                    allone = all(p[2] == 1 for p in V)
                    if allone: c[('理由 ∧ V の行2が全部1', r)] += 1
                    c[('理由 ∧ 行2が1の列の割合', r, round(
                        10 * sum(p[2] for p in V) / len(V)))] += 1
                    # 孤児より後ろに行 2 = 0 の列があるか
                    if any(V[i][2] == 0 for i in range(j + 1, len(V))):
                        c[('理由 ∧ 後ろに行2=0 がある', r)] += 1
    print(f'### 値域<{E} |Q|∈{LS}  Q {c["Q"]}')
    print(f'    {"理由":6s} {"孤児の本数":>10s} {"V の行2が全部1":>16s} {"後ろに行2=0 がある":>20s}')
    for r in ['(A)', '(B)', '(C)', '(D)', '(E)', '(F)']:
        t = c[('理由', r)]
        if not t: continue
        print(f'    {r:6s} {t:10d} {c[("理由 ∧ V の行2が全部1", r)]:9d} '
              f'({100*c[("理由 ∧ V の行2が全部1", r)]/t:6.2f}%) '
              f'{c[("理由 ∧ 後ろに行2=0 がある", r)]:9d} '
              f'({100*c[("理由 ∧ 後ろに行2=0 がある", r)]/t:6.2f}%)')
    print('    (A) の「行 2 が 1 の列の割合」の分布（10 分位）: ',
          dict(sorted((k[2], c[k]) for k in c
                      if isinstance(k, tuple) and len(k) == 3 and k[1] == '(A)')))
    print()


if __name__ == '__main__':
    run(6, (3,4,5,6,8), (1,2,3,4), range(6), 3000, 321)
    run(9, (4,6,8,10),  (1,2,3,4), range(9), 2500, 323)
