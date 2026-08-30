# -*- coding: utf-8 -*-
"""**課題 R117 —— L3 の対応「ブロック外の祖先 ＝ `X` の末尾列の行 0 祖先の像」を測る。**

L3 の `tower_anc0_not_blocker`（`L105Cap.lean` §63、緑）:
    塔の場面で **`X = (0,v,z) :: R` の末尾列の（根以外の）行 0 祖先はすべて `v < 行 1`**

L3 の対応: ブロック `k` の根（行 0 = `k*d`）は「`X` の末尾列（行 0 = `d`）を
ブロック `k-1` の座標系に置いたもの」（`k*d = d + (k-1)*d`）。

★ **測る前に書く予想**: `k = 1` では完全一致するが、**`k >= 2` では一致しない**はず。
   ブロック `k` の根の鎖は**ブロック `k-1` を通り抜けてブロック `k-2`, …, 0 まで続く**ので、
   「ブロック外の祖先」は `X` の像**より真に大きい**（像はブロック `k-1` の部分だけ）。
   ⟹ **正しい対応は「ブロック `k-1` に制限したもの」であって「ブロック外の全部」ではない**はず。

  (e1) 対応の一致率（`k=1` / `k>=2` を分けて）。分母・単位・箱・サンプリングを明記
  (e2) 一致しない最小の事例
  (e3) ⚠ **反例の形を先に書いて、母集団に何件入っているかを数える**（教訓 45）:
       「ブロック外の祖先で `X` の末尾列の行 0 祖先の像ではないもの」
  (e4) `|R|` / `n` / 箱の行 2 の範囲を振る（教訓 21 / 27）
"""
import sys, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r113 import operTower, scene_gen


def anc0(S, j):
    out = [j]
    while True:
        p = trio.parent(S, 0, out[-1])
        if p is None:
            break
        out.append(p)
    return out


def run(COL, VS, ZS, Ls, NS, label, sample_from=9, sample=40000):
    c = Counter(); ex = {}
    for Q, d, e, hb in scene_gen(COL, VS, ZS, Ls, sample_from, sample):
        L = len(Q); v = Q[0][1]
        X = list(Q) + [(d, 0, 0)]          # `nextrel0` は行 0 しか見ないので行 1,2 は任意
        chX = set(anc0(X, L)) - {L}        # X の末尾列の行 0 祖先（自分を除く）＝ Q の添字
        for n in NS:
            T = operTower(Q, d, e, n)
            for k in range(1, n):
                ch = set(anc0(T, k * L)) - {k * L}
                outb = {y for y in ch if y // L != k}
                img = {(k - 1) * L + j for j in chX}      # L3 の像
                inb1 = {y for y in outb if y // L == k - 1}
                c[f'k={"1" if k == 1 else ">=2"} / ブロック外の全部 = 像/' +
                  ('ok' if outb == img else '**不一致**')] += 1
                c[f'k={"1" if k == 1 else ">=2"} / ブロック k-1 に制限 = 像/' +
                  ('ok' if inb1 == img else '**不一致**')] += 1
                # (e3) 像でないブロック外の祖先
                extra = outb - img
                c[f'k={"1" if k == 1 else ">=2"} / 像でない外部祖先 ' +
                  ('あり' if extra else 'なし')] += 1
                if extra and 'extra' not in ex:
                    ex['像でない外部祖先'] = (Q, d, e, n, k, sorted(extra),
                                             sorted(img), sorted(outb))
                # 像でない外部祖先はブロッカーか
                for y in extra:
                    c['  像でない外部祖先が ' +
                      ('**ブロッカー**' if T[y][1] <= v else 'ブロッカーでない')] += 1
                if inb1 != img and 'inb' not in ex:
                    ex['ブロック k-1 制限の不一致'] = (Q, d, e, n, k,
                                                     sorted(inb1), sorted(img))
    print(f'### {label}')
    for k in sorted(c):
        print(f'  {k:46s} {c[k]:10d}')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    ap.add_argument('--n', type=int, default=5)
    a = ap.parse_args()
    Ls = tuple(range(2, a.L + 1)); NS = tuple(range(2, a.n + 1))
    run([(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)],
        (0, 1, 2), (0, 1), Ls, NS,
        f'R117 (a) H12 の箱（行2<=1）|R|<={a.L}, n=2..{a.n}／単位: (事例,n,k)／全数')
    run([(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1, 2)],
        (0, 1, 2, 3), (0, 1), (2, 3), (2, 3, 4),
        'R117 (b) 広い箱（行0<=3,行1<=3,**行2<=2**,v<=3）|R|<=3, n=2..4／全数')
