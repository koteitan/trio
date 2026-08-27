# -*- coding: utf-8 -*-
"""族 β の構造を測る: 長さが揃わない対で T が U の部分列になっているか。"""
import sys, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3
from core import expand

def subseq_pos(T, U):
    """T が U の部分列なら、貪欲に左から取った位置の並びを返す。無ければ None。"""
    pos, j = [], 0
    for t in T:
        while j < len(U) and U[j] != t:
            j += 1
        if j == len(U):
            return None
        pos.append(j); j += 1
    return pos

def run(lim=6, mmax=3):
    A = sorted(rows3.gen3('BMS', lim, zcap=1), key=rows3.key)
    c = Counter(); ex = {}
    t0=time.time()
    for M in A:
        if len(M) < 2: continue
        fM = tuple(map(tuple, rows3.b2d3(list(M))))
        Mt = tuple(map(tuple, M))
        for m in range(1, mmax+1):
            T = tuple(expand(fM, m))
            E = [tuple(x) for x in expand(Mt, m+1)]
            U = tuple(rows3.b2d3(E))
            if U == T:
                c['一致'] += 1; continue
            if len(U) == len(T):
                c['同長ちがい'] += 1
                ex.setdefault('同長ちがい', (Mt,m)); continue
            if len(U) > len(T):
                p = subseq_pos(T, U)
                if p is not None:
                    c['U>T 部分列 ok'] += 1
                    c['  抜く本数 %d' % (len(U)-len(T))] += 1
                    ex.setdefault('sub', (Mt,m))
                else:
                    c['U>T 部分列でない'] += 1
                    ex.setdefault('nosub', (Mt,m))
            else:
                p = subseq_pos(U, T)
                c['U<T ' + ('部分列 ok' if p is not None else '部分列でない')] += 1
                ex.setdefault('U<T', (Mt,m))
    print('lim=%d mmax=%d  %.0fs' % (lim, mmax, time.time()-t0))
    for k in sorted(c): print('   %-24s %d' % (k, c[k]))
    return c, ex

if __name__ == '__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 6, int(sys.argv[2]) if len(sys.argv)>2 else 3)
