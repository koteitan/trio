# -*- coding: utf-8 -*-
"""**R98 の続き —— `LiftTie` が `towerOK2_of_clause3` の中で実際に受け取る `R` は何か。**

`L53Subst.lean:2444-2466` の証明本体を読むと、`LiftTie` は

    `exact W_mono hfits (liftStage_cons hlt (argOK_graft hRne hR _) ih)`

の 1 か所でしか使われず、`liftStage_cons` に渡る `R` は **`ih` の主語**、すなわち

    **`R' := graft R (Lift1 ((((0,v,z)::R)⟦k⟧)) (entry R 1 (|R|-1) - v))`**

（`v, z` は外側と同じ）。⟹ **`LiftTie` が実際に見る `R` はこの形だけ。**

⟹ 母集団問題 (p1) の本当の答え:

    `LiftTieCore` を**独立した仮定**として置くなら債務は `∀ argOK R` 全部（＝ 構成的一様）
    `towerOK2_of_clause3` を通すのに**必要な分だけ**なら、この `graft` 形だけ

後者で残核が消えるなら、**`LiftTie` を特殊化するだけで `TowerGraft2` が閉じる**。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean
from r102 import classify, srow, lev


def graft(M, y):
    dd = M[-1][0] if M else 0
    return M[:-1] + [(p[0] + dd, p[1], p[2]) for p in y]


def Lift1(X, d):
    return [(c[0], c[1] + (d if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def run(DS, BS, CS, VS, ZS, LS, KS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    cls = Counter(); n = 0; ex = {}; tie = Counter()
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None:
                continue                                  # domT の ¬hasParent + srow=2
            if lev(R[j]) - 1 < 0:
                continue
            for v in VS:
                for z in ZS:
                    if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                        continue                          # 根が復活させる
                    D1 = R[j][1] - v
                    for k in KS:
                        T = oper_lean([(0, v, z)] + R, k) if k >= 1 else []
                        Rp = graft(R, Lift1(list(T), D1))
                        if not Rp:
                            cls['R\' が空（k=0 で |R|=1）'] += 1
                            continue
                        if any(p[0] < 1 for p in Rp):
                            cls['**argOK が破れる**'] += 1
                            ex.setdefault('argOK 破れ', (R, v, z, k, Rp))
                            continue
                        n += 1
                        c = classify(Rp, v, z)
                        cls[c] += 1
                        tie['タイあり' if any(p[1] == v for p in Rp)
                            else 'タイなし'] += 1
                        if c.startswith('5'):
                            ex.setdefault('核の例', (R, v, z, k, Rp))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  母数 **{n}**')
    for k in sorted(cls):
        pct = f'  ({100*cls[k]/n:5.2f}%)' if n and not k.startswith('R\'') and not k.startswith('**arg') else ''
        print(f'  {k:34s} {cls[k]:10d}{pct}')
    print('  -- タイの有無 --')
    for k in sorted(tie):
        print(f'     {k:12s} {tie[k]:10d}  ({100*tie[k]/max(n,1):5.2f}%)')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2, 3), (0, 1, 2), (0, 1, 2, 3), (0, 1),
        tuple(range(1, a.L + 1)), (0, 1, 2, 3, 4),
        f'R98-b `LiftTie` が実際に受け取る `R\' = graft R (Lift1 T_k D1)` |R|<={a.L}')
