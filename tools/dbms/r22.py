# -*- coding: utf-8 -*-
"""課題 R13 (1): 柱単調性 (CM) の破れを **(状態, 柱の対)** の署名に畳む。

隣接する破れ (M1, M2) から
    p       = 入力の共通接頭辞の長さ
    c1, c2  = M1[p], M2[p]              （c1 < c2）
    q       = 像の最初に食い違う番号
    h1, h2  = f(M1)[q], f(M2)[q]
    状態    = 第 p 列を処理する瞬間の conv3 の入力（d / ST / prev / dmap / L / ps / pw
              / first / force）。M1 と M2 で一致するはず（接頭辞が同じなので）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from collections import Counter

_c3 = rows3.conv3
TARGET = [None]
SNAP = [None]


def probe(*a, **kw):
    M = a[0] if a else kw.get('M')
    off = a[10] if len(a) > 10 else kw.get('off', 0)
    if M and off == TARGET[0] and SNAP[0] is None:
        st = a[8] if len(a) > 8 else kw.get('st')
        SNAP[0] = (a[1] if len(a) > 1 else kw.get('d', 0),
                   tuple(st['ST']), st['prev'], tuple(st['dmap']),
                   tuple(a[2] if len(a) > 2 else ()),
                   tuple(a[4] if len(a) > 4 else (0, 0)),
                   tuple(a[5] if len(a) > 5 else (0, 0)),
                   a[6] if len(a) > 6 else True,
                   a[7] if len(a) > 7 else False)
    return _c3(*a, **kw)


rows3.conv3 = probe


def state_at(M, p):
    TARGET[0] = p; SNAP[0] = None
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    rows3.conv3(list(M), st=st)
    return SNAP[0]


v, L = int(sys.argv[1]), int(sys.argv[2])
P = r7.stts_pool(v, L)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    TARGET[0] = None
    IM.append(tuple(tuple(x) for x in b2d3(list(M))))
V = [(i, i + 1) for i in range(len(P) - 1) if IM[i] > IM[i + 1]]
print('ST_TS v<=%d len<=%d  %d 個  **減 %d**' % (v, L, len(P), len(V)), flush=True)

sig = Counter(); same = 0; ex = {}
for a, b in V:
    A, B = P[a], P[b]
    p = 0
    while p < len(A) and p < len(B) and A[p] == B[p]:
        p += 1
    fa, fb = IM[a], IM[b]
    q = 0
    while q < len(fa) and q < len(fb) and fa[q] == fb[q]:
        q += 1
    sA, sB = state_at(A, p), state_at(B, p)
    if sA == sB:
        same += 1
    s = (sA, A[p], B[p], fa[q], fb[q])
    sig[s] += 1
    if s not in ex:
        ex[s] = (A, B, p, q)
print('  M1 と M2 の第 p 列での状態が一致: %d / %d' % (same, len(V)))
print('  **署名の種類: %d**' % len(sig))
for k, (s, n) in enumerate(sorted(sig.items(), key=lambda t: -t[1])):
    A, B, p, q = ex[s]
    st, c1, c2, h1, h2 = s
    print()
    print(' 署名 %d（%d 件）' % (k + 1, n))
    print('   p=%d  c1=%s -> h1=%s   c2=%s -> h2=%s' % (p, c1, h1, c2, h2))
    print('   状態: d=%s prev=%s ST=%s dmap=%s ps=%s pw=%s first=%s'
          % (st[0], st[2], st[1], st[3], st[5], st[6], st[7]))
    print('   例 M1 = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print('      M2 = %s' % ''.join(str(x).replace(' ', '') for x in B))
