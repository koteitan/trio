# -*- coding: utf-8 -*-
"""課題 R7 の続き: `SeqEmbT3` を破る 41 対で、**どの条項が綴りを決めたか**を読む。

`g2/provc.py` の `PROV`（柱ごとに `(kind, off, why, ctx)`）から、
最初にずれる柱の `why`（分岐列の綴りを決めた条項）を集計する。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc, r7
from rows3 import b2d3
from collections import Counter


def main(vmax=5, maxlen=10, verbose=6):
    t0 = time.time()
    P = r7.stts_pool(vmax, maxlen)
    print('母集団 ST_TS v<=%d len<=%d: %d 個 (%.1fs)'
          % (vmax, maxlen, len(P), time.time() - t0))
    IM = []
    for i, M in enumerate(P):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        IM.append(tuple(tuple(c) for c in b2d3(list(M))))
    o = sorted(range(len(P)), key=lambda i: P[i])
    V = [(o[i], o[i + 1]) for i in range(len(o) - 1)
         if not (IM[o[i]] < IM[o[i + 1]])]
    print('(→) の破れ（隣接）: %d' % len(V))

    # provc が rows3 と同じ像を返すことをこの母集団で確かめる
    nd = 0
    for a, b in V:
        for M in (P[a], P[b]):
            C, _ = provc.b2d3p(list(M))
            if tuple(tuple(c) for c in C) != tuple(tuple(c) for c in b2d3(list(M))):
                nd += 1
    print('provc と rows3 の像の差（破れ %d 対 x 2）: %d' % (len(V), nd))

    c = Counter(); ex = []
    for a, b in V:
        A, B = P[a], P[b]
        _, PA = provc.b2d3p(list(A))
        _, PB = provc.b2d3p(list(B))
        fa, fb = IM[a], IM[b]
        j = 0
        while j < len(fa) and j < len(fb) and fa[j] == fb[j]:
            j += 1
        ea = PA[j] if j < len(PA) else None
        eb = PB[j] if j < len(PB) else None
        c['ずれ始め: 左 kind=%s why=%s' % (ea[0], ea[2]) if ea else '左なし'] += 1
        c['ずれ始め: 右 kind=%s why=%s' % (eb[0], eb[2]) if eb else '右なし'] += 1
        c['左が縮約の中: %s' % (bool(ea[3]) if ea else '?')] += 1
        c['ずれ始めの入力列 左=末尾から %s'
          % ((len(A) - 1 - ea[1]) if ea else '?')] += 1
        c['ずれ始めの入力列 右=末尾から %s'
          % ((len(B) - 1 - eb[1]) if eb else '?')] += 1
        if len(ex) < verbose:
            ex.append((A, B, fa, fb, j, ea, eb))
    for k in sorted(c, key=str):
        print('   %-44s %d' % (k, c[k]))
    print()
    for A, B, fa, fb, j, ea, eb in ex[:verbose]:
        print(' M1 =', ''.join(str(x).replace(' ', '') for x in A))
        print(' M2 =', ''.join(str(x).replace(' ', '') for x in B))
        print('   j=%d  fM1[j]=%s PROV=%s' % (j, fa[j] if j < len(fa) else None, ea))
        print('         fM2[j]=%s PROV=%s' % (fb[j] if j < len(fb) else None, eb))
    return V


if __name__ == '__main__':
    v = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    main(v, L)
