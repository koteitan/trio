# -*- coding: utf-8 -*-
"""H10 (1): 行 1 の梯子 `L` が写しに同変か。写しの頭ごとに `L` を比べる。"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3L
from rows3 import copy_head
from core import expand, show

def L_at(rec, off):
    """off の柱を処理した呼び出しの L / F（最初に off が先頭になった呼び出し）。"""
    for r in rec:
        if r['off'] == off:
            return r
    return None

def run(lim=6, nmax=4, verbose=1):
    A = sorted(rows3.gen3('BMS', lim, zcap=1), key=rows3.key)
    c = Counter(); ex = {}
    for M in A:
        Mt = tuple(map(tuple, M))
        for n in range(1, nmax + 1):
            E = [tuple(x) for x in expand(Mt, n)]
            ch = [t for t in range(len(E)) if copy_head(E, t)]
            if len(ch) < 2: continue
            out, rec = rows3L.b2d3L(list(E))
            rs = [L_at(rec, t) for t in ch]
            for k in range(len(ch) - 1):
                a, b = rs[k], rs[k+1]
                if a is None or b is None:
                    c['呼び出しが無い'] += 1; continue
                same_L = a['L'] == b['L']
                same_F = a['F'] == b['F']
                same_ps = a['ps'] == b['ps']
                same_pw = a['pw'] == b['pw']
                c[('L' if same_L else '**L がちがう**',
                   'F' if same_F else '**F がちがう**')] += 1
                if not same_L:
                    ex.setdefault('L', (tuple(E), ch[k], ch[k+1], a, b))
                if not same_F:
                    ex.setdefault('F', (tuple(E), ch[k], ch[k+1], a, b))
    return c, ex

if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv)>1 else 6
    nm  = int(sys.argv[2]) if len(sys.argv)>2 else 4
    c, ex = run(lim, nm)
    print('写しの頭の隣り合う対 %d 組' % sum(c.values()))
    for k in sorted(c, key=str): print('   %-34s %d' % (str(k), c[k]))
    for kind, (E, t1, t2, a, b) in ex.items():
        print()
        print('=== %s のちがう例（写しの頭 %d と %d）' % (kind, t1, t2))
        print('   %s' % show([list(x) for x in E]))
        print('   写しの頭 %d: L=%s F=%s d=%s ps=%s pw=%s' % (t1, a['L'], a['F'], a['d'], a['ps'], a['pw']))
        print('   写しの頭 %d: L=%s F=%s d=%s ps=%s pw=%s' % (t2, b['L'], b['F'], b['d'], b['ps'], b['pw']))
