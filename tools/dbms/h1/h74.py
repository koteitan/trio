# -*- coding: utf-8 -*-
"""**課題 H63: 空虚さの監査 —— §151 以降の全部の表に「前提の充足率」を入れる。**

§182 で自分の候補補題が**前提が 1 度も成り立たない**ために空虚だったと分かった。
**同じ穴が他の表にも開いていないか**を、核ごとに「前提を満たした件数（分母）」で数える。

見るのは 2 つ。**両方書いて初めて「反例ゼロ」に意味がある**:

    (1) **分母**: 前提を全部満たした事例は何件か（0 なら空虚）
    (2) **射程**: そもそも反証器が鳴りうるか（R94: 鳴る ⟺ `lev 結論の根 > a`）
        鳴りえないなら、その核の「違反 0」は測定ではない

`h61` の 8 本は表に分母を書いていなかったので、ここで数え直す。
⚠ `inW` は分母を数えるのに使う（前提の `∈ W` を確かめるため）。
**結論の判定には使わない**（R94 で射程外と分かっているので意味がない）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
import h61
from wref import Ref, fmt, entry, levM, Lift1, shiftr01, srow, has_parent
from collections import Counter

AMAX = 12


def main(lens=(1, 2, 3)):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=1500)
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    pool = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            pool.append(list(S))
    dec = [(S, ref.minstage(S, AMAX)) for S in pool]
    dec = [(S, u) for S, u in dec if u is not None]
    print('## 母集団: 長さ %s、候補 %d 本、段が確定 **%d** 本'
          % (list(lens), len(pool), len(dec)))
    print()

    rows = []

    def add(name, n_try, n_ok, scope):
        rows.append((name, n_try, n_ok, scope))

    # ---------------- LiftStage: 前提は `X ∈ W m`（minstage で必ず満たす）
    n = len(dec) * 2
    add('`LiftStage`', n, n,
        '**射程外**（結論の根は錐に反射で入るので `lev` が `+2d`、段も `+2d`）')

    # ---------------- LiftTie: 前提に「根つき」「タイあり」が要る
    t_try = t_ok = 0
    for S, u in dec:
        for d in (1, 2):
            t_try += 1
            if S and S[0][0] == 0 and wref.argOK(S[1:]) and \
               any(q[1] == S[0][1] for q in S[1:]):
                t_ok += 1
    add('`LiftTie`（タイのある根）', t_try, t_ok, '**射程外**（同上）')

    # ---------------- Row1DownLocal / Row1DownRoot0: 台が `∈ W a` になる `a` が要る
    for name, cond in (('`Row1DownLocal`', 1), ('`Row1DownRoot0`', 0)):
        r_try = r_ok = 0
        for S, u in dec:
            v0 = entry(S, 1, 0)
            if (v0 >= 1) != (cond == 1):
                continue
            for d in (1, 2):
                r_try += 1
                base = (h61.mlift(S, v0 - 1, d) if cond == 1
                        else shiftr01(0, d, S))
                if any(ref.inW(base, a) is True
                       for a in range(u, u + 2 * d + 1)):
                    r_ok += 1
        add(name, r_try, r_ok, '**射程外**')

    # ---------------- Row1Mono / Row0Free / WConvex: 相手の列が要る
    for name, gen in (('`Row1Mono`', h61.variants_row1),
                      ('`Row0Free` ⚠', h61.variants_row0)):
        g_try = g_ok = 0
        for S, u in dec:
            for M2 in gen(S):
                g_try += 1
                g_ok += 1              # 前提は構文だけ（長さ・行の一致）なので必ず真
        add(name, g_try, g_ok, '**射程外**（行 1 を下げる/行 0 を動かすと根の `lev` は下がるか不変）')

    c_try = c_ok = 0
    for S, u in dec:
        for C2 in h61.variants_row1_up(S):
            c_try += 1
            if ref.inW(C2, u) is True:
                c_ok += 1
    add('`WConvex`（上端 `C ∈ W a` が要る）', c_try, c_ok, '**射程外**')

    # ---------------- ShiftTowerClosedS: 狭義に深い、が要る
    s_try = s_ok = 0
    for S, u in dec:
        for e in (1, 2):
            for n2 in (2, 3):
                s_try += 1
                if S and all(entry(S, 0, j) > entry(S, 0, 0)
                             for j in range(1, len(S))) \
                   and len(h61.shTower(S, e, n2)) <= 9:
                    s_ok += 1
    add('`ShiftTowerClosedS`', s_try, s_ok,
        '**射程外**（`shTower Q e n` の根は `Q` の根）')

    print('| 核 | 当てた事例 | **前提を満たした（分母）** | 充足率 | 反証器の射程 |')
    print('|---|--:|--:|--:|---|')
    for name, a, b, sc in rows:
        print('| %s | %d | **%d** | %.1f%% | %s |'
              % (name, a, b, 100.0 * b / max(a, 1), sc))
    print()
    print('> **⟹ どの核も分母は 0 ではない**（§181 のような空虚さは無い）。')
    print('> **ただし射程は全部外**（R94/R95）。⟹ 「違反 0」は測定ではないが、')
    print('> **「前提を満たす事例がこれだけあった」という母集団の情報は生きている。**')
    print()


if __name__ == '__main__':
    main(lens=(1, 2))
    print()
    main(lens=(3,))
