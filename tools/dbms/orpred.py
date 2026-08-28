# -*- coding: utf-8 -*-
"""`Inj3` と `OrderReindexT3` / `SandwichUReindexT3` を**述語として直に**測る。

課題 L28-L31 で Lean の仮定が弱まった:

    ReindexT1_of_cofinal'' : ImgCofinalT3 ＋ **Inj3** ＋ **OrderReindexT3**
                             ＋ **SandwichUReindexT3** ＋ ImgBlockT3 ＋ ImgLenT3

弱い 3 本はどれも「相手 `B` は `(conv3 A)⟦m⟧ = conv3 B` を満たすものに限る」形。
だから母数は **そういう `(A, m, B)` の三つ組だけ**で、行列の全対より桁で小さい。

    Inj3                : conv3 M = conv3 N かつ M, N ∈ ST_TS  ならば  M = N
    OrderReindexT3      : (1) conv3 (A⟦n⟧) = conv3 B  ならば  A⟦n⟧ = B
                          (2) seqlex (conv3 (A⟦n⟧)) (conv3 B)  ならば  seqlex (A⟦n⟧) B
                          (3) seqlex (conv3 B) (conv3 A)        ならば  seqlex B A
    SandwichUReindexT3  : sle3 (conv3 (A⟦n⟧)) (conv3 B)

`translate _ <o translate _` は `ST_TS` 上で `seqlex` と同値（`olt_ST_iff_seqlex`）。

使い方: python3 tools/dbms/orpred.py [vA] [lenA] [lenB] [mmax]
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import expand

vA = int(sys.argv[1]) if len(sys.argv) > 1 else 5
LA = int(sys.argv[2]) if len(sys.argv) > 2 else 8
LB = int(sys.argv[3]) if len(sys.argv) > 3 else 11
MM = int(sys.argv[4]) if len(sys.argv) > 4 else 6

t0 = time.time()
PB = r7.stts_pool(vA, LB)
PA = [M for M in PB if len(M) <= LA and len(M) > 1]
print('母集団 B 側 ST_TS v<=%d len<=%d  %d 個 / A 側 len<=%d  %d 個  (%.0fs)'
      % (vA, LB, len(PB), LA, len(PA), time.time() - t0), flush=True)

# --- 像の表（同時に Inj3 を測る）
t0 = time.time()
img = {}
dup = 0
ex_dup = []
for i, M in enumerate(PB):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    T = tuple(tuple(c) for c in b2d3(list(M)))
    if T in img:
        dup += 1
        if len(ex_dup) < 3:
            ex_dup.append((img[T], M))
    else:
        img[T] = M
print('像の表 %d 通り  (%.0fs)' % (len(img), time.time() - t0), flush=True)
print('=== **Inj3**: 像がぶつかる行列 **%d / %d**  %s'
      % (dup, len(PB), '⟹ **単射（この母数で）**' if dup == 0 else '⟹ **単射でない**'),
      flush=True)
for a, b in ex_dup:
    f = lambda M: ''.join('(%d,%d,%d)' % c for c in M)
    print('     %s' % f(a), flush=True)
    print('     %s' % f(b), flush=True)

# --- (A, m, B) の三つ組を集める
t0 = time.time()
tri = []
for A in PA:
    fA = tuple(tuple(c) for c in b2d3(list(A)))
    for m in range(2, MM + 1):
        T = tuple(map(tuple, expand(fA, m)))
        if not T:
            break
        B = img.get(T)
        if B is not None:
            tri.append((A, m, B, fA, T))
print('三つ組 (A, m, B) で (conv3 A)⟦m⟧ = conv3 B なるもの **%d 組**  (%.0fs)'
      % (len(tri), time.time() - t0), flush=True)
if not tri:
    print('  ⟹ **母数 0。範囲を広げること**（測定になっていない）', flush=True)
    sys.exit(0)

# --- 3 本を判定
t0 = time.time()
n1 = n2 = n3 = nS = 0
tot = 0
ex = []
for A, m, B, fA, T in tri:
    for n in range(1, m):
        An = tuple(map(tuple, expand(A, n)))
        if not An:
            continue
        fAn = tuple(tuple(c) for c in b2d3(list(An)))
        tot += 1
        if fAn == T and An != B:
            n1 += 1
            if len(ex) < 3: ex.append(('Inj', A, n, B))
        if fAn < T and not (An < B):
            n2 += 1
            if len(ex) < 3: ex.append(('(2)', A, n, B))
        if T < fA and not (B < A):
            n3 += 1
            if len(ex) < 3: ex.append(('(3)', A, n, B))
        if not (fAn <= T):
            nS += 1
            if len(ex) < 3: ex.append(('SandU', A, n, B))
print('判定 %d 回  (%.0fs)' % (tot, time.time() - t0), flush=True)
print('=== **OrderReindexT3**', flush=True)
print('  (1) 単射性の枝   破れ **%d**' % n1, flush=True)
print('  (2) (←) A⟦n⟧ vs B 破れ **%d**' % n2, flush=True)
print('  (3) (←) B vs A    破れ **%d**' % n3, flush=True)
print('=== **SandwichUReindexT3**  破れ **%d**' % nS, flush=True)
print('  ⟹ %s' % ('**この母数では全部真**' if n1 + n2 + n3 + nS == 0 else '**偽**'),
      flush=True)
for k, A, n, B in ex:
    f = lambda M: ''.join('(%d,%d,%d)' % c for c in M)
    print('   %s n=%d A=%s' % (k, n, f(A)), flush=True)
    print('        B=%s' % f(B), flush=True)
