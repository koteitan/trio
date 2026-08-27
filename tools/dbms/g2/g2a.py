"""G2 段 1: <=6 列の破れ 88 個を集めて、安い指紋（A の末尾 2 柱 / 破れる m）で数える。"""
import sys, os, collections, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, imgfast, core
from core import expand, show, isstd

SC = '/home/koteitan/proofs/dbms/tools/dbms/g2/'


def ctype(c):
    """柱の型（分類の指紋の素）。"""
    if c is None:
        return '-'
    a, b, z = c
    if a == 0:
        return 'root'                       # (0,0,0)
    if (a, b, z) == (1, 1, 0):
        return 'anch'                       # アンカー (1,1,0)
    if a == b:
        return 'diag%d' % z                 # 対角列 (a,a,z), a>=2 か (1,1,1)
    if b == 0:
        return 'w'                          # x w の柱 (k,0,0)
    if b == 1 and z == 0:
        return 'br'                         # 分岐列 (a,1,0), a>=2
    if z == 0:
        return 'lo0'                        # (a,b,0) その他
    return 'lo1'                            # (a,b,1) その他


def tail2(A):
    return '%s,%s' % (ctype(A[-2] if len(A) > 1 else None), ctype(A[-1]))


def main(lim=6):
    r = imgfast.score(rows3.b2d3, lim=lim, mmax=3, zcap=1, verbose=0,
                      fallback=False)
    bad = list(r.badpairs)
    ms = collections.defaultdict(set)
    for A, m, T in bad:
        ms[tuple(A)].add(m)
    print('破れ A %d 個 / 対 %d' % (len(ms), len(bad)))
    pickle.dump(bad, open(SC + 'bad%d.pkl' % lim, 'wb'))
    c1 = collections.Counter(tail2(A) for A in ms)
    print('\n-- A の末尾 2 柱の型 --')
    for k, v in c1.most_common():
        print('  %-14s %3d' % (k, v))
    c2 = collections.Counter(tuple(sorted(v)) for v in ms.values())
    print('\n-- 破れる m の集合 --')
    for k, v in c2.most_common():
        print('  %-10s %3d' % (str(k), v))
    c3 = collections.Counter((tail2(A), tuple(sorted(v))) for A, v in ms.items())
    print('\n-- 交差 --')
    for k, v in c3.most_common():
        print('  %-14s %-10s %3d' % (k[0], str(k[1]), v))
    print('\n-- 列数別 --', sorted(collections.Counter(len(A) for A in ms).items()))
    return ms


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
