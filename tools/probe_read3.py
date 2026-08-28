"""課題 L14: `read3` の設計を測る。

`OrderT3` は `ReadT3`（読みの保存）＋ `ImgDokT3` ＋ `ReadLexT3` から出る
（`Dbms3.OrderT3_of_read`、**証明ずみ・3 行**）。律速は読み `read3` の設計。

## 2 行との違い（設計の出発点）

2 行の `readD`（`Dbms.lean:131`）は段を**そのまま**読む:

    readD (p :: r) first plev =
      if first ∧ p.2 = plev ∧ r.headI = p + (1,1) then readD r true plev   -- 影
      else P p.2 (readD 子 true p.2) (readD 兄弟 false p.2)

これで済むのは `convD` が本体の柱に BMS の段 `p.2` を**そのまま書く**からである。
3 行の `conv3` は

    e2 = s2          行 2 は**そのまま**
    e1 = 梯子の表から計算  行 1 は**そのままではない**

なので、像の行 1 は BMS の添字ではなく**行 1 の木の中での順位**になる。
実際、最小の反例が対角にある:

    M   = (0,0,0)(1,1,1)            translate M = P 0 0 (P 1 1 Z Z) Z
    像  = (0,0,0)(1,0,0)(2,1,0)(3,2,1)
    像の (行1,行2) は (0,0) (0,0) (1,0) (2,1) で、**(1,1) がどこにも無い**

⟹ **`readD` の逐語版は 3 行では原理的に不可能。**

## 測る設計

    survivors : 影を 2 種類の節で捨てる（`readD` と同じ再帰、`first` / `plev` つき）
      行 1 の影 … first ∧ (p の段) = plev ∧ 次 = p + (1,1,0)
      行 2 の影 … first ∧ p の行 2 = plev の行 2 ∧ 次 = p + (1,1,1)
    rankify   : 生き残った行列の (行 0, 行 1, 行 2) を**その行の木での順位**に置き換える

    (INV)  rankify (survivors (conv3 M)) = M        for ST_TS M

(INV) が真なら `read3 := translate ∘ rankify ∘ survivors` が `ReadT3` を与える
（BMS 標準形では `rankify` が恒等なので）。
"""
import sys

sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3                                                   # noqa: E402
import trio                                                    # noqa: E402


def survivors(l, first, plev, out):
    """`readD` と同じ再帰で影を捨て、生き残った柱を `out` に積む。"""
    if not l:
        return
    p = l[0]
    r = l[1:]
    if first and (p[1], p[2]) == plev and r and \
            tuple(r[0]) == (p[0] + 1, p[1] + 1, p[2]):
        return survivors(r, True, plev, out)          # 行 1 の影
    if first and p[2] == plev[1] and r and \
            tuple(r[0]) == (p[0] + 1, p[1] + 1, p[2] + 1):
        return survivors(r, True, plev, out)          # 行 2 の影
    out.append(p)
    ch, i = [], 0
    while i < len(r) and r[i][0] > p[0]:
        ch.append(r[i])
        i += 1
    lev = (p[1], p[2])
    survivors(ch, True, lev, out)
    survivors(r[i:], False, lev, out)


def rankify(S):
    """各行の値を「その行の木での順位」に置き換える。"""
    S = [tuple(c) for c in S]
    r = [[0] * len(S) for _ in range(3)]
    for y in range(3):
        for j in range(len(S)):
            pp = trio.parent(S, y, j)
            r[y][j] = 0 if pp is None else r[y][pp] + 1
    return tuple((r[0][j], r[1][j], r[2][j]) for j in range(len(S)))


def stts_pool(vmax, maxlen, ns=(1, 2, 3)):
    """対角からの展開閉包（`ST_TS`）。"""
    seen, frontier = set(), []
    for v in range(vmax + 1):
        S = tuple(tuple(c) for c in trio.diag(3, v, zcap=1))
        if S not in seen:
            seen.add(S)
            frontier.append(S)
    while frontier:
        S = frontier.pop()
        for n in ns:
            T = tuple(tuple(c) for c in trio.expand(list(S), n))
            if T and len(T) <= maxlen and T not in seen:
                seen.add(T)
                frontier.append(T)
    return sorted(seen, key=rows3.key)


def run(vmax, maxlen, ctrl=0):
    P = stts_pool(vmax, maxlen)
    ok = bad = lenb = 0
    ex = []
    for M in P:
        B = [tuple(c) for c in rows3.b2d3(M)]
        out = []
        survivors(B, True, (0, 0), out)
        if ctrl == 1:                     # 陽性対照 1: 影を捨てない
            out = B
        if ctrl == 2:                     # 陽性対照 2: 順位に直さない
            R = tuple(out)
        else:
            R = rankify(out)
        if len(out) != len(M):
            lenb += 1
        if R == tuple(M):
            ok += 1
        else:
            bad += 1
            if len(ex) < 3:
                ex.append((M, B, out, R))
    tag = {0: '本番', 1: '陽性対照(影を捨てない)', 2: '陽性対照(順位に直さない)'}[ctrl]
    print(f"[{tag}] ST_TS v<={vmax} len<={maxlen}: 母数 {len(P)}  "
          f"一致 {ok}  **破れ {bad}**  （うち長さ違い {lenb}）")
    for M, B, out, R in ex:
        print("  M  ", ' '.join('%d,%d,%d' % c for c in M))
        print("  img", ' '.join('%d,%d,%d' % c for c in B))
        print("  srv", ' '.join('%d,%d,%d' % c for c in out))
        print("  R  ", ' '.join('%d,%d,%d' % c for c in R))
    return bad


if __name__ == '__main__':
    vmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    mx = int(sys.argv[2]) if len(sys.argv) > 2 else 11
    run(vmax, mx, 0)
    run(vmax, mx, 1)
    run(vmax, mx, 2)
