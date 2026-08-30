"""**教師つきデータ**: 写しの中での「正しい綴り」を ImgClosedT の目標から読む。

シートは長い展開を 1 行も含まないので、「写しの中で分岐列をどう綴るか」を
シートからは決められない。しかし ImgClosedT の目標

    T = (conv3 A)<m>          （DBMS の展開だけで決まる。conv3 の意見は入らない）
    U = conv3(A<m+1>)         （conv3 の答え）

は、`len(T) == len(U)` のとき柱ごとに整列できる。ずれた柱の**正しい値がそのまま
読める**ので、これが教師になる。整列した柱のうち一致しているものは
**負例**（いまの綴りで正しい）として同じくらい大事である。

出典の対応づけには `g2/provc.py`（柱ごとに (kind, off, why, ctx) を記録する
conv3 の写し）を使う。`why` は分岐列の綴りを決めた条項の名前。

使い方
------
    python3 teach.py 6            <=6 列 x m<=3 で表を作る
    python3 teach.py 6 out.pkl    pickle に落とす

出力 1 件 = 1 本の柱:
    ok      目標と一致したか
    off     A<m+1> の何列目の柱か / src その柱
    why     conv3 がその綴りを決めた条項（分岐列でなければ None）
    ctx     縮約の中のどの再帰か
    got     conv3 が出した像の柱 / want 目標の柱
    feat    行列から直に読める特徴（下の `features`）
"""
import sys, os, pickle, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'g2'))
import rows3
from rows3 import (is_branch, is_w_col, closes_unit, par0, hi_block,
                   is_repeat, wchain_head, ANCHOR)
from core import expand, show
import provc


def run_prov(M):
    provc.PROV.clear()
    provc.CTX.clear()
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(provc.conv3(list(M), st=st))
    return out, list(provc.PROV)


def unit_head(Mo, off):
    """`off` の柱が属する行 1 のユニットの頭。
    頭 = 行 0 が 0 の柱 / 行 1 も行 2 も 0 の柱（x w）/ アンカー (1,1,0)。"""
    for j in range(off, -1, -1):
        c = Mo[j]
        if c[0] == 0 or (c[1] == 0 and c[2] == 0) or tuple(c) == ANCHOR:
            return j
    return 0


def features(Mo, off):
    """その柱について**行列から直に読める**量だけを並べる（状態を使わない）。
    学習した規則が写しに同変であるためには、これだけで決まる必要がある。"""
    p = Mo[off]
    nxt = Mo[off + 1] if off + 1 < len(Mo) else None
    pv = Mo[off - 1] if off >= 1 else None
    pv2 = Mo[off - 2] if off >= 2 else None
    uh = unit_head(Mo, off)
    j = wchain_head(Mo, off)
    return {
        'col': tuple(p),
        'br': is_branch(p),
        'nxt': tuple(nxt) if nxt else None,
        'pv': tuple(pv) if pv else None,
        'pv2': tuple(pv2) if pv2 else None,
        'closes': closes_unit(nxt),
        'hi': hi_block(Mo, off),
        'rep': is_repeat(Mo, off),
        'wjs': None if j is None else off - j,      # wchain の頭までの距離
        'wpar0': None if j is None else par0(Mo, j),
        'par0': par0(Mo, off),
        'uh': off - uh,                              # ユニットの頭からの距離
        'uhcol': tuple(Mo[uh]),
        # ユニットの中で自分より前にある分岐列の本数（G1 が見つけた指紋）
        'nbr': sum(1 for t in range(uh, off) if is_branch(Mo[t])),
        # ユニットの中で自分より前にある「x w」柱の本数
        'nw': sum(1 for t in range(uh, off) if is_w_col(Mo[t])),
        'pvw': bool(pv) and is_w_col(pv),
    }


def collect(lim=6, mmax=3, zcap=1, verbose=1):
    rows = []
    A = sorted(rows3.gen3('BMS', lim, zcap=zcap), key=rows3.key)
    t0 = time.time()
    nal = nmis = 0
    for k, M in enumerate(A):
        if len(M) < 2:
            continue
        fM = rows3.b2d3(list(M))
        for m in range(1, mmax + 1):
            T = tuple(expand(tuple(map(tuple, fM)), m))
            E = [tuple(c) for c in expand(tuple(map(tuple, M)), m + 1)]
            U, pr = run_prov(E)
            if len(U) != len(T):
                nmis += 1
                continue
            nal += 1
            for i, (c, want, p) in enumerate(zip(U, T, pr)):
                if p[0] != 'body':
                    continue
                src = E[p[1]]
                if not is_branch(src):
                    continue
                rows.append(dict(A=tuple(map(tuple, M)), m=m, i=i,
                                 off=p[1], src=tuple(src), why=p[2],
                                 ctx=''.join(p[3]),
                                 got=tuple(c), want=tuple(want),
                                 ok=tuple(c) == tuple(want),
                                 feat=features(E, p[1])))
        if verbose and (k + 1) % 500 == 0:
            print('  %d/%d  柱 %d  整列 %d / 不一致 %d  %.0fs'
                  % (k + 1, len(A), len(rows), nal, nmis, time.time() - t0),
                  flush=True)
    if verbose:
        print('整列できた対 %d / 長さが違う対 %d   分岐列の柱 %d 本  %.0fs'
              % (nal, nmis, len(rows), time.time() - t0))
    return rows


def report(rows):
    from collections import Counter
    bad = [r for r in rows if not r['ok']]
    print('分岐列の柱 %d 本   うち目標とずれ %d 本 (%.3f%%)'
          % (len(rows), len(bad), 100.0 * len(bad) / max(1, len(rows))))
    print('ずれの向き（目標 - conv3）:',
          dict(Counter(tuple(r['want'][j] - r['got'][j] for j in range(3))
                       for r in bad)))
    print('ずれた柱を出した条項:', dict(Counter(r['why'] for r in bad)))
    print('正しい柱を出した条項:', dict(Counter(r['why'] for r in rows if r['ok'])))
    print()
    print('=== 特徴ごとの「深くすべきか」の食い違い ===')
    key = lambda r: (r['feat']['nbr'], r['feat']['closes'], r['feat']['hi'],
                     r['feat']['pvw'], r['feat']['wjs'] is not None)
    tab = {}
    for r in rows:
        tab.setdefault(key(r), [0, 0])[0 if r['ok'] else 1] += 1
    print('%-32s %8s %8s' % ('(nbr,closes,hi,pvw,wch)', '一致', 'ずれ'))
    for k in sorted(tab, key=lambda k: -tab[k][1]):
        if tab[k][1]:
            print('%-32s %8d %8d' % (str(k), tab[k][0], tab[k][1]))


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    rows = collect(lim)
    report(rows)
    if len(sys.argv) > 2:
        pickle.dump(rows, open(sys.argv[2], 'wb'))
        print('書いた', sys.argv[2])
