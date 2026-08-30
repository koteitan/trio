# -*- coding: utf-8 -*-
"""課題 R28: **BMS 3 行標準形 ∧ z<2 ⟺ ST_TS** を、**経路を構成して**決める。

BFS の枝刈り問題を避けるため、**`isstd` が内部で使っている `reach` の歩みを
そのまま取り出す**。`core._isstd_raw` は

    b が対角の接頭辞でなければ  s = (対角の接頭辞) ++ (1 か所だけ b に合わせた柱)
    を作り  reach(s, b)  で基本列を降りて b に到達できるかを見る

`s` 自身も標準形なので**再帰**すれば、**完全な対角から `b` までの経路**が構成できる。
その経路の途中がすべて z<2 で、しかも **z 頭打ち対角 `diagSeqT 0 v`** を通れば、
`b ∈ ST_TS` が**構成的に**言える（`CLAUDE.md`: z 頭打ち対角は完全な対角の展開）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import core, trio
from core import rows, diagcol, expand, cmpmat, fsindex, isstd
from rows3 import gen3, key
from collections import Counter


def start_of(b, ver='BMS'):
    """`_isstd_raw` と同じ `s`。`b` が対角の接頭辞なら None。"""
    Y = rows(b)
    for x in range(len(b)):
        dc = diagcol(ver, x, Y)
        for y in range(Y):
            v = b[x][y]
            if v > dc[y]:
                return False            # 標準形でない
            if v < dc[y]:
                return tuple(list(b[:x]) +
                             [tuple(list(dc[:y]) + [v + 1] + [0] * (Y - y - 1))])
    return None                          # 対角の接頭辞そのもの


def walk(a, b, limit=4000):
    """`reach` と同じ歩み。通った行列の列を返す（`a` を含み `b` で終わる）。"""
    out = [a]
    for _ in range(limit):
        c = cmpmat(a, b)
        if c == 0:
            return out
        if c < 0:
            return None
        n = fsindex(a, b)
        if n is None:
            return None
        a = expand(a, n)
        out.append(a)
    return None


def path_from_diag(b, depth=0):
    """完全な対角から `b` までの経路（行列の列）。無ければ None。"""
    if depth > 40:
        return None
    s = start_of(b)
    if s is False:
        return None
    if s is None:
        return [tuple(map(tuple, b))]     # b は対角の接頭辞
    pre = path_from_diag(s, depth + 1)
    if pre is None:
        return None
    w = walk(tuple(map(tuple, s)), tuple(map(tuple, b)))
    if w is None:
        return None
    return [tuple(map(tuple, x)) for x in pre[:-1]] + \
           [tuple(map(tuple, x)) for x in w]


def zcapdiag(M):
    """`M` が z 頭打ち対角 `diagSeqT 0 v` か。"""
    return all(c == (j, j, min(j, 1)) for j, c in enumerate(M))


if __name__ == '__main__':
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    G = [tuple(map(tuple, M)) for M in gen3('BMS', LIM, zcap=1)]
    print('gen3(BMS, <=%d, zcap=1) = **%d 個**' % (LIM, len(G)), flush=True)
    c = Counter(); ex = []
    t0 = time.time()
    for i, b in enumerate(G):
        if i % 2000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        p = path_from_diag(b)
        if p is None:
            c['**経路が作れない**'] += 1
            if len(ex) < 4:
                ex.append(('経路なし', b, None))
            continue
        # z 頭打ち対角を通るか、そこから先が全部 z<2 か
        k = next((j for j, M in enumerate(p) if zcapdiag(M)), None)
        if k is None:
            c['z 頭打ち対角を通らない'] += 1
            if len(ex) < 4:
                ex.append(('z 対角を通らない', b, p[0]))
            continue
        if all(all(col[2] <= 1 for col in M) for M in p[k:]):
            c['**ST_TS（構成的に確定）**'] += 1
        else:
            c['z 対角の後に z>=2 が出る'] += 1
            if len(ex) < 4:
                ex.append(('z>=2 が途中に', b, None))
    print('  %.0fs' % (time.time() - t0))
    for k2 in sorted(c, key=str):
        print('   %-32s %d' % (k2, c[k2]))
    for tag, b, s in ex:
        print('   ### %s' % tag)
        print('      b = %s' % ''.join(str(x).replace(' ', '') for x in b))
        if s:
            print('      経路の先頭 = %s' % ''.join(str(x).replace(' ', '') for x in s))
