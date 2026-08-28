# -*- coding: utf-8 -*-
"""課題 R9: 分岐列の綴りは**接頭辞 `Mo[:off+1]` の関数**か。

site を「接頭辞 `Mo[:off+1]`」で束ね（接頭辞の長さが `off+1` なので `off` は決まる）、
同じ束の中で

  (A) その列が出した柱（絶対座標）が食い違うか   … 強い版
  (B) 浅い／深いのラベルが食い違うか             … 弱い版（門が開いた柱だけ）

を数える。分岐列 `(a,1,0)`（`a>=2`）だけを見る。
"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc
from rows3 import is_branch
from collections import Counter


def scan(pop, name, verbose=4):
    A = {}      # 接頭辞 -> 出した柱の組
    B = {}      # 接頭辞 -> ラベルの集合
    cA = Counter(); cB = Counter(); exA = []; exB = []
    t0 = time.time()
    for i, M in enumerate(pop):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        C, PR = provc.b2d3p(list(M))
        C = tuple(tuple(c) for c in C)
        # 列ごとに出した柱を集める
        bycol = {}
        for idx, (kind, off, why, ctx) in enumerate(PR):
            bycol.setdefault(off, []).append((kind, C[idx]))
        for off, items in bycol.items():
            if off >= len(M) or not is_branch(M[off]):
                continue
            pre = tuple(M[:off + 1])
            val = tuple(items)
            if pre in A:
                cA['_判定'] += 1
                if A[pre] != val:
                    cA['**柱が食い違う**'] += 1
                    if len(exA) < 6:
                        exA.append((pre, A[pre], val))
                else:
                    cA['柱が一致'] += 1
            else:
                A[pre] = val
            why = next((w for k, o, w, c in PR
                        if o == off and w and ('/' in w)), None)
            if why:
                lab = why.split('/')[-1]
                s = B.setdefault(pre, set())
                if s and lab not in s:
                    cB['**ラベルが割れる**'] += 1
                    if len(exB) < 6:
                        exB.append((pre, sorted(s), lab))
                s.add(lab)
                cB['_判定'] += 1
    print('== %s  母数 %d 行列  %.1fs' % (name, len(pop), time.time() - t0))
    print('   分岐列の site（接頭辞の束）: %d 個 / 比較 %d 回'
          % (len(A), cA['_判定']))
    for k in sorted(cA, key=str):
        if not k.startswith('_'):
            print('     %-22s %d' % (k, cA[k]))
    print('   ラベルつき site: %d 個 / 判定 %d 回' % (len(B), cB['_判定']))
    for k in sorted(cB, key=str):
        if not k.startswith('_'):
            print('     %-22s %d' % (k, cB[k]))
    for pre, a, b in exA[:verbose]:
        print('   ### 柱が食い違う例')
        print('      接頭辞 = %s' % ''.join(str(c).replace(' ', '') for c in pre))
        print('      一方 = %s' % str(a))
        print('      他方 = %s' % str(b))
    for pre, s, lab in exB[:verbose]:
        print('   ### ラベルが割れる例')
        print('      接頭辞 = %s' % ''.join(str(c).replace(' ', '') for c in pre))
        print('      既出 = %s  新 = %s' % (s, lab))
    return A, B, cA, cB


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'sheet'
    if what == 'sheet':
        import sheet3
        D = sheet3.load(1)
        P = [tuple(tuple(c) for c in b) for _, b, _ in D]
        nm = 'シート 3 行 z<=1 の %d 行' % len(P)
    else:
        import r7
        v, L = int(sys.argv[2]), int(sys.argv[3])
        P = r7.stts_pool(v, L)
        nm = 'ST_TS v<=%d len<=%d' % (v, L)
    scan(P, nm)
