# -*- coding: utf-8 -*-
"""H6 (1): 分岐列の柱ぜんぶについて、目標の行 1 が base_s / deep / どれでもない
   のどれかを数える（今までの教師データは「どれでもない」を捨てていた）。"""
import sys, pickle, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, provh
from rows3 import is_branch
from core import expand, show

def collect(lim=6, mmax=6, zcap=1, verbose=1):
    A = sorted(rows3.gen3('BMS', lim, zcap=zcap), key=rows3.key)
    c = Counter(); rows = []
    t0 = time.time()
    for i, M in enumerate(A):
        if len(M) < 2: continue
        fM = tuple(map(tuple, rows3.b2d3(list(M))))
        Mt = tuple(map(tuple, M))
        for m in range(1, mmax + 1):
            T = tuple(expand(fM, m))
            E = tuple(tuple(x) for x in expand(Mt, m + 1))
            U, pr = provh.b2d3p(list(E))
            if len(U) != len(T):
                continue
            for q, w, pe in zip(U, T, pr):
                k, off, why, ctx, d = pe
                if k != 'body' or d is None or d.get('why') == 'tie': continue
                if not is_branch(E[off]): continue
                wv = w[1]
                tags = []
                if wv == d['base_s']: tags.append('base_s')
                if wv == d['deep']: tags.append('deep')
                if wv == d['base_d']: tags.append('base_d')
                if wv == d['base_sd']: tags.append('base_sd')
                lab = '+'.join(sorted(set(tags))) if tags else 'NEITHER'
                c[lab] += 1
                if lab == 'NEITHER':
                    rows.append(dict(A=E, off=off, want=tuple(w), got=tuple(q),
                                     dec=d, base=(d['base_s'], d['deep'],
                                                  d['base_d'], d['base_sd']),
                                     src=(Mt, m)))
        if verbose and (i+1) % 2000 == 0:
            print('  %d/%d  %.0fs' % (i+1, len(A), time.time()-t0), flush=True)
    return c, rows

if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv)>1 else 6
    mm  = int(sys.argv[2]) if len(sys.argv)>2 else 6
    c, rows = collect(lim, mm)
    tot = sum(c.values())
    print('分岐列の柱 %d 本（lim=%d, m<=%d、長さが揃った対だけ）' % (tot, lim, mm))
    for k in sorted(c, key=lambda x: -c[x]):
        print('   %-24s %6d  (%.2f%%)' % (k, c[k], 100.0*c[k]/tot))
    pickle.dump(rows, open('/tmp/h1work/neither%d_%d.pkl' % (lim, mm), 'wb'))
    print()
    print('**どれとも違う** %d 本' % len(rows))
    seen = set()
    for r in rows[:30]:
        key = (r['base'], r['want'][1])
        print('   want[1]=%s  (base_s,deep,base_d,base_sd)=%s  why=%s  p=%s'
              % (r['want'][1], r['base'], r['dec']['why'], r['A'][r['off']]))
