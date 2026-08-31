# -*- coding: utf-8 -*-
"""**(R-D1) 続き —— 「`T` は `U` の部分列」は族 β 全体で成り立つか。抜き方に規則はあるか。**

## ⚠ 母集団（規則 9）

    BMS 3 行 `z <= 1` の標準形、**2..6 列**（`imgfast.py` と同じ作り方）、`m ∈ {2,3,4}`。
    ★ **長さが揃わない対（族 β）だけ**を集める。**分母を必ず出す**。
"""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3
from collections import Counter
from core import expand

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def sub_align(T, U):
    keep = []; i = 0
    for k, u in enumerate(U):
        if i < len(T) and tuple(T[i]) == tuple(u):
            keep.append(k); i += 1
    return (i == len(T)), keep


def gaps(keep, n):
    s = set(keep); out = []; st = None
    for k in range(n):
        if k not in s:
            if st is None: st = k
        else:
            if st is not None: out.append((st, k - st)); st = None
    if st is not None: out.append((st, n - st))
    return out


def gen(lim=6, zcap=1):
    """`rows3.gen3('BMS', lim, zcap)` そのもの（`imgfast.py` と同じ作り方）。"""
    return [M for M in rows3.gen3('BMS', lim, zcap) if len(M) >= 2]


t0 = time.time()
MS = gen(6)
print('BMS 3 行 z<=1 標準形（2..6 列）: %d 個（%.1f 秒）' % (len(MS), time.time() - t0))
c = Counter(); pats = Counter(); ex = []
for M in MS:
    try: fM = tuple(map(tuple, rows3.b2d3(list(M))))
    except Exception: c['⛔ conv3 が落ちる'] += 1; continue
    for m in (2, 3, 4):
        try:
            T = tuple(map(tuple, expand(fM, m)))
            E = tuple(map(tuple, expand(M, m + 1)))
            U = tuple(map(tuple, rows3.b2d3([list(x) for x in E])))
        except Exception:
            c['⛔ 展開が落ちる'] += 1; continue
        c['対（分母）'] += 1
        if len(T) == len(U):
            c['★ 族 α（長さ一致）'] += 1
            c['　うち 完全一致'] += (T == U)
            continue
        c['⛔ 族 β（長さ不一致）'] += 1
        c['　うち |T| < |U|'] += (len(T) < len(U))
        c['　うち ⛔ |T| > |U|'] += (len(T) > len(U))
        if len(T) > len(U): 
            if len(ex) < 3: ex.append(('⛔ |T| > |U|', M, m, len(T), len(U)))
            continue
        ok, keep = sub_align(T, U)
        c['　　★ T は U の部分列'] += ok
        c['　　⛔ 部分列でない'] += (not ok)
        if ok:
            g = gaps(keep, len(U))
            LF = len(fM)
            starts = [s for (s, l) in g]
            lens = [l for (s, l) in g]
            pats['区間の個数 %s' % (len(g) if len(g) <= 3 else '>=4')] += 1
            pats['★ 開始位置が等差 |f(A)|=%s' % ('はい' if len(starts) < 2 or
                 all(starts[i + 1] - starts[i] == LF for i in range(len(starts) - 1)) else 'いいえ')] += 1
            pats['★ 最後以外の長さが全部同じ %s' % ('はい' if len(lens) < 2 or
                 len(set(lens[:-1])) == 1 else 'いいえ')] += 1
        elif len(ex) < 3:
            ex.append(('⛔ 部分列でない', M, m, len(T), len(U)))
n = c['対（分母）']
print()
print('== 結果（分母 %d 対）==' % n)
for k in ('★ 族 α（長さ一致）', '　うち 完全一致', '⛔ 族 β（長さ不一致）', '　うち |T| < |U|',
          '　うち ⛔ |T| > |U|', '　　★ T は U の部分列', '　　⛔ 部分列でない', '⛔ conv3 が落ちる', '⛔ 展開が落ちる'):
    if c[k] or k.startswith('　　') or k.startswith('⛔'):
        print('   %-26s %8d  %8.4f%%' % (k, c[k], pct(c[k], n)))
b = c['⛔ 族 β（長さ不一致）']
print('   ⟹ ★ 族 β の中で「T は U の部分列」: %.4f%%（%d / %d）'
      % (pct(c['　　★ T は U の部分列'], b), c['　　★ T は U の部分列'], b))
print()
print('== 抜き方の規則（部分列だった %d 件）==' % c['　　★ T は U の部分列'])
for k in sorted(pats): print('   %-34s %8d  %8.4f%%' % (k, pats[k], pct(pats[k], c['　　★ T は U の部分列'])))
for e in ex: print('   ⛔ 例:', e[0], ' '.join('(%d,%d,%d)' % q for q in e[1]), 'm=%d |T|=%d |U|=%d' % e[2:])
print('（%.1f 秒）' % (time.time() - t0))
