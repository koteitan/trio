#!/usr/bin/env python3
"""課題 L1 の突き合わせ集合を作る（Lean `Conv3.b2d3` vs Python `rows3.b2d3`）。

`tools/dbms/lean_v13_check.py`（課題 G4）の集合の作り方を、v14 の h1 ＋ wterm に
合わせて広げたもの。**`tools/dbms/*.py` は読むだけ**なので、この file は
`lean/` に置いてある（旗は実行時に `rows3.V12` / `rows3.V14` を書き換えて切る。
file は 1 バイトも触らない）。

    python3 l1_sets.py 6 <out.txt>     # <=6 列 全数（8387）
    python3 l1_sets.py 7 <out.txt>     # 7 列: 縮約発火 ∪ 旗で像が変わる ∪ 無作為
    python3 l1_sets.py 8 <out.txt>     # 8 列: 同上（無作為は少なめ）

出力は 1 行 1 行列（`x,y,z x,y,z ...`）。
"""
import random
import sys

TOOLS = '/home/koteitan/proofs/dbms/tools/dbms'
sys.path.insert(0, TOOLS)
import rows3                                                   # noqa: E402


def enc(M):
    return ' '.join('%d,%d,%d' % tuple(c) for c in M)


def imgs(G):
    return [rows3.b2d3(M) for M in G]


def flip(sel, G, base, name, setter, unsetter):
    """旗を落として像が変わる行列を全部拾う。"""
    setter()
    other = imgs(G)
    unsetter()
    d = {M for M, a, b in zip(G, base, other) if a != b}
    print(name, 'changes', len(d), flush=True)
    sel |= d
    return d


def main(lim, out):
    rnd = random.Random(12345)
    if lim <= 6:
        sel = set(rows3.gen3('BMS', lim, zcap=1))
    else:
        G = [M for M in rows3.gen3('BMS', lim, zcap=1) if len(M) == lim]
        print('gen', lim, len(G), flush=True)
        base = imgs(G)
        sel = {M for M in G if rows3.b2d3n(M)[1] > 0}
        print('contraction', len(sel), flush=True)
        flip(sel, G, base, 'h1',
             lambda: rows3.V14.__setitem__('h1', False),
             lambda: rows3.V14.__setitem__('h1', True))
        flip(sel, G, base, 'wterm',
             lambda: rows3.V14.__setitem__('wterm', False),
             lambda: rows3.V14.__setitem__('wterm', True))
        flip(sel, G, base, 'mark',
             lambda: rows3.V12.__setitem__('mark', False),
             lambda: rows3.V12.__setitem__('mark', True))
        n = 5000 if lim == 7 else 3000
        sel |= set(rnd.sample(G, min(n, len(G))))
    S = sorted(sel)
    with open(out, 'w') as f:
        for M in S:
            f.write(enc(M) + '\n')
    print('wrote', len(S), 'to', out)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2])
