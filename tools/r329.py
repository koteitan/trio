# -*- coding: utf-8 -*-
"""**(R-C8) —— 再帰を 10 段まわして、`d <= 段差` が何段続くか。**

## ⚠ 状態遷移（`oper` の中身から。`Trio.lean:106-114` 逐語）

    `T := mTower Q d e n ++ [第 n ブロックの根]`、`t := |T|-1`、`sr := srow T t`、`c := parent T sr t`
    ⟹ `c is None` なら **孤児 ⟹ そこで終わり（`snoc_orphan_W` で無料）**
    ⟹ **窓 `V := T[c:t]`**
    ⟹ **`d' := entry T 0 t - entry T 0 c`（`0 < sr` のとき、でなければ 0）**
    ⟹ **`e' := entry T 1 t - entry T 1 c`（`1 < sr` のとき、でなければ 0）**
    次の段: `Q <- V`、`d <- d'`、`e <- e'`、`n <- k`（`k` は選ぶ）

    ★ **段差(Q) := min_{i>=1}(entry Q 0 i - entry Q 0 0)**

## ⚠ 母集団

    (i) いちばん硬い 2 列の残核 3 本 ／ (ii) Reach の窓から 20 本 ／ (iii) ⛔ 人工の対照 20 本
    `n0, k ∈ {1,2,3}`、`d0 <= 4`（規則 8）、**`d0 <= 段差(Q0)` を課す**。10 段。
    **所属の判定はしません**（列の計算だけ）。

## ⚠ 測る前の見積もり

    ★ `V` ＝ ブロック `n-1` ＝ `Lift1 (shiftr01 (d(n-1)) 0 Q) (e(n-1))`。
      **`shiftr01` は行 0 を一様にずらすだけ**、**`Lift1` は行 0 に触らない**
      ⟹ ⛔ **行 0 の差は不変 ⟹ 段差も不変**。そして `d' = d` なら **`d <= 段差` は永遠**。
    ⟹ ★ 私の予想は「**永遠に続く（真の輪）**」です。⟹ ⛔ 外れてほしいところ。
"""
import sys, itertools, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, sh, mTower
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')
span = lambda Q: min(Q[i][0] - Q[0][0] for i in range(1, len(Q))) if len(Q) >= 2 else 0


def step(Q, d, e, n):
    """1 段。返り値 (状態 or None, ラベル)。"""
    T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
    t = len(T) - 1
    sr = srow(T, t)
    c = trio.parent(T, sr, t)
    if c is None: return None, '孤児（無料）', sr, None
    V = T[c:t]
    if len(V) < 2: return None, '窓が 1 列以下', sr, c
    d2 = (T[t][0] - T[c][0]) if sr > 0 else 0
    e2 = (T[t][1] - T[c][1]) if sr > 1 else 0
    return (V, d2, e2), 'ok', sr, c


def chain(Q0, d0, e0, n0, k, steps=10, verbose=False):
    Q, d, e, n = Q0, d0, e0, n0
    rec = []
    for i in range(steps):
        sp = span(Q)
        rec.append(dict(i=i, L=len(Q), d=d, e=e, sp=sp, ok=(d <= sp),
                        root=Q[0], based=(Q[0][0] == 0)))
        if verbose:
            print('      段%2d: |Q|=%d d=%d e=%d 段差=%d %s 根=%s  Q=%s'
                  % (i, len(Q), d, e, sp, '★d<=段差' if d <= sp else '⛔d>段差', Q[0],
                     ' '.join('(%d,%d,%d)' % q for q in Q[:6])))
        st, lab, sr, c = step(Q, d, e, n)
        if st is None:
            rec.append(dict(i=i, stop=lab, srow=sr)); return rec
        Q, d, e = st
        n = k
    return rec


t0 = time.time()
print('== ★ (i) いちばん硬い 2 列の残核 3 本（逐語で 10 段）==')
for Q0 in ([(3, 2, 1), (4, 1, 0)], [(7, 7, 1), (8, 7, 0)], [(5, 4, 0), (6, 3, 1)]):
    for (d0, e0, n0, k) in ((1, 1, 2, 2), (1, 0, 2, 2), (1, 1, 3, 3)):
        if d0 > span(Q0): continue
        print('  ★ Q0=%s d0=%d e0=%d n0=%d k=%d（段差=%d）'
              % (' '.join('(%d,%d,%d)' % q for q in Q0), d0, e0, n0, k, span(Q0)))
        rec = chain(Q0, d0, e0, n0, k, steps=10, verbose=True)
        last = rec[-1]
        if 'stop' in last: print('      ⟹ 段%d で終了: %s（srow=%s）' % (last['i'], last['stop'], last['srow']))
        else: print('      ⟹ ⛔ 10 段まわしても終わりません')

print()
print('== ★ (ii)(iii) 大きい箱で「`d <= 段差` は何段続くか」==')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS)
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
ART = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
random.shuffle(ART)
for tag, L in (('Reach の窓 40 本', QS[:40]), ('⛔ 負の対照: 人工 3 列 40 本', ART[:40])):
    c = Counter(); firstbreak = Counter()
    for Q0 in L:
        sp0 = span(Q0)
        for d0 in range(1, min(sp0, 4) + 1):
            for e0 in (0, 1, 2):
                for n0 in (1, 2, 3):
                    for k in (1, 2, 3):
                        rec = chain(Q0, d0, e0, n0, k, steps=10)
                        c['鎖'] += 1
                        stop = [r for r in rec if 'stop' in r]
                        if stop:
                            c['★ 途中で終わった（孤児など）'] += 1
                            firstbreak['終了 段%d' % min(stop[0]['i'], 9)] += 1
                            continue
                        st = [r for r in rec if 'stop' not in r]
                        bad = [r['i'] for r in st if not r['ok']]
                        if bad:
                            c['★★ `d > 段差` になった'] += 1
                            firstbreak['`d>段差` 段%d' % min(bad[0], 9)] += 1
                        else:
                            c['⛔ 10 段ずっと `d <= 段差`'] += 1
                        # 状態が一定か
                        if all((r['L'], r['d'], r['e']) == (st[0]['L'], st[0]['d'], st[0]['e']) for r in st):
                            c['⛔ (|Q|,d,e) が 10 段ずっと一定'] += 1
                        if all(r['sp'] == st[0]['sp'] for r in st): c['段差が一定'] += 1
                        c['based が保たれた'] += all(r['based'] for r in st)
    n = c['鎖']
    print('  [%s] 鎖 %d 本' % (tag, n))
    for kk in ('★ 途中で終わった（孤児など）', '★★ `d > 段差` になった', '⛔ 10 段ずっと `d <= 段差`',
               '⛔ (|Q|,d,e) が 10 段ずっと一定', '段差が一定', 'based が保たれた'):
        print('     %-30s %7d  %8.4f%%' % (kk, c[kk], pct(c[kk], n)))
    for kk in sorted(firstbreak): print('        %s: %d' % (kk, firstbreak[kk]))
print('（%.1f 秒）' % (time.time() - t0))
