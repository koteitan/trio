# -*- coding: utf-8 -*-
"""課題 R7 (4): `conv3` の**接頭辞単調でなさ**の構造を見る。

`b2d3(M[:k])` が `b2d3(M)` の接頭辞にならないとき、
どこが・どれだけ・なぜずれるかを数える。`rows3.py` は読むだけ。
"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc
from rows3 import gen3, key, b2d3n
from collections import Counter


def imgp(M):
    """(像, PROV, 縮約の回数)。"""
    C, PR = provc.b2d3p(list(M))
    return tuple(tuple(c) for c in C), PR


def run(pop, name, verbose=4):
    c = Counter(); ex = {}
    t0 = time.time()
    for i, M in enumerate(pop):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear()
            core._flat_memo.clear()
        bad_m = [False]
        Bi, PRi = imgp(M)
        nc_full = sum(1 for e in PRi if e[3])       # 縮約の中の柱があるか
        for k in range(1, len(M)):
            Pk = M[:k]
            Bk, PRk = imgp(Pk)
            c['_対'] += 1
            if Bi[:len(Bk)] == Bk:
                c['接頭辞になる'] += 1
                continue
            c['**破れ**'] += 1
            # 最初にずれる位置
            j = 0
            while j < len(Bk) and j < len(Bi) and Bk[j] == Bi[j]:
                j += 1
            tail = len(Bk) - j          # 短いほうの「末尾から何柱ずれるか」
            c['ずれるのは末尾 %d 柱' % tail] += 1
            c['ずれ始めの柱の種類 %s' % (PRk[j][0] if j < len(PRk) else '長さ')] += 1
            if j < len(PRk):
                off = PRk[j][1]
                c['ずれ始めの入力列は末尾から %d 本目' % (k - 1 - off)] += 1
            c['ずれ始めは像の末尾か %s'
              % ('はい' if j == len(Bk) - 1 else 'いいえ')] += 1
            bad_m[0] = True
            c['ずれ始めが縮約の中 %s'
              % ('はい' if (j < len(PRk) and PRk[j][3]) else 'いいえ')] += 1
            c['像の長さ %s' % ('短い' if len(Bk) > len(Bi) else '足りる')] += 1
            # 分岐列の綴りが変わったか（行 1 の値だけ違う）
            if j < len(Bk) and j < len(Bi):
                a, b = Bk[j], Bi[j]
                if a[0] == b[0] and a[2] == b[2] and a[1] != b[1]:
                    c['ずれの型: 行 1 だけ違う'] += 1
                elif a[0] != b[0]:
                    c['ずれの型: 深さが違う'] += 1
                else:
                    c['ずれの型: その他'] += 1
            else:
                c['ずれの型: 片方が尽きた'] += 1
            kk = (tail, PRk[j][0] if j < len(PRk) else '長さ')
            if kk not in ex:
                ex[kk] = (M, k, Bk, Bi, j)
        if bad_m[0]:
            c['_破れる行列'] += 1
    print('   破れる行列 %d / %d' % (c['_破れる行列'], len(pop)))
    print('== %s  母数（行列 %d、(M,k) の対 %d）  %.1fs'
          % (name, len(pop), c['_対'], time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-34s %d' % (k, c[k]))
    for kk, e in list(ex.items())[:verbose]:
        M, k, Bk, Bi, j = e
        print('   例 %s' % str(kk))
        print('      M      = %s' % ''.join(str(x).replace(' ', '') for x in M))
        print('      M[:%d]  = %s' % (k, ''.join(str(x).replace(' ', '')
                                                for x in M[:k])))
        print('      f(M[:k])= %s' % ''.join(str(x).replace(' ', '') for x in Bk))
        print('      f(M)    = %s' % ''.join(str(x).replace(' ', '') for x in Bi))
        print('      最初にずれる位置 j = %d' % j)
    return c


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    P = [tuple(map(tuple, M)) for M in sorted(gen3('BMS', lim, zcap=1), key=key)]
    run(P, 'gen3 <=%d' % lim)
