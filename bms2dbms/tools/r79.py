# -*- coding: utf-8 -*-
"""課題 R79: **`rsum (M.take j0) (M.drop j0)`**（`j0` ＝ `oper` のバッドルート）。

今日 3 回出てきた同じ形:
    §49  `snoc_flat_root` の「親が根」＝ `take j0` が空
    §96  `split_lastMin` の切れ目が `R.dropLast` の中に落ちる（95.6%）
    §109 `srow=0` 枝で要るのは `rsum (C.take j0) (C.drop j0)`

`rsum A P : ∀ p ∈ A ++ P, entry P 0 0 ≤ p.1` で `A = M.take j0`, `P = M.drop j0` なので

    **`rsum` ⟺ `M[j0].行0` が `M` の全列の行 0 以下 ＝ バッドルートが大域最小の深さにいる**

⚠ 探索も打ち切りも使わない**直接計算**なので、教訓 18（打ち切り依存）は該当しない。
"""
import sys
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from wcert import srow, has_parent


def badroot(M):
    """`oper` のバッドルート `j0`（無ければ None）。"""
    j1 = len(M) - 1
    if j1 < 1 or tuple(M[j1]) == (0, 0, 0) or not has_parent(M, j1):
        return None
    return trio.parent([tuple(p) for p in M], srow(M, j1), j1)


def audit(P, name):
    c = Counter(); N = 0
    for M in P:
        M = tuple(map(tuple, M))
        j0 = badroot(M)
        if j0 is None:
            continue
        N += 1
        if j0 == 0:
            c['**j0 = 0（take が空 ⟹ 自動で無料）**'] += 1
            continue
        d = M[j0][0]
        sh = [j for j, p in enumerate(M[:j0]) if p[0] < d]
        if not sh:
            c['**j0 > 0 かつ `rsum` が立つ**'] += 1
        else:
            c['**j0 > 0 かつ `rsum` が破れる（芯）**'] += 1
            c['   浅い列 %s 本' % ('1' if len(sh) == 1 else
                                   ('2' if len(sh) == 2 else '3 以上'))] += 1
            c['   **接頭辞にまとまる**' if sh == list(range(len(sh)))
              else '   飛び飛び'] += 1
            c['   j0 が前半' if j0 * 2 < len(M) else '   j0 が後半'] += 1
    print('== %s（バッドルートがある %d 件）' % (name, N), flush=True)
    for k in sorted(c, key=str):
        print('   %-44s %d (%.1f%%)' % (k, c[k], 100.0 * c[k] / N), flush=True)
    return N


if __name__ == '__main__':
    from rows3 import gen3
    from book import load_book
    audit([b for *_, b, _ in load_book()], 'ブックのラダー（20415 行、最大 44 列）')
    for L in (6, 8):
        audit(gen3('BMS', L, zcap=1), '`ST_TS` 標準形 len<=%d' % L)
