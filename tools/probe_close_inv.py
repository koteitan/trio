# -*- coding: utf-8 -*-
"""Inv3 を展開で閉じさせる追加の不変条件 P を探す。

  python3 probe_close_inv.py collect <seed0> <seed1> <out.pkl>   # 構造＋Inv3 を満たす非標準形の土台と、M[n]（n ≤ 3）の壊れ方
  python3 probe_close_inv.py test <std1.pkl,std2.pkl,...> <bases.pkl>  # 候補 P: Std で真か、P の土台で閉じるか

候補（Std で真、A∪B∪C の 183372 個で例外 0）:
- S1: 兄弟の部分木（列の並び）が辞書式で増えない。
- S2: z = 1 の列には、それより前に行 1 が以下の z = 1 の列がある（(1,1,1) 自身を除く）。
- S3: 行 1 は行 0 の親より高々 1 しか上がらない。
- S4: z = 1 の列 c、q = P_1(c)、d = q の子で c の祖先: d ≠ c なら d は z = 1 で、d と c の間の列の行 1 は c より大きい。
- PH2: B ≠ 0 の書き換えの枠では PreHi（hi(y) = B ∧ lo(y) ≠ 0）。ただし c の部分木と [i, c) の両方に z = 1 の列があり
  e1(c) ≥ 1 の枠は除く。
- PH4: PH2 に、除いた枠のうち PreHi でなく B が y の先頭部分でもない枠では
  (B = Ω_σ ∧ 頭(y) = Ω_τ ∧ σ < τ) ∨ (B ≠ Ω ∧ 頭(y) ≠ Ω ∧ σ_B ≥ σ_頭) を足したもの。
"""
import sys, os, pickle, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from multiprocessing import Pool
import trio, ytosk_eval2 as Y2
from probe_dropres_single import structok, inv3_fails

def kids(M):
    e = Y2.Ev2(M); return e
def subtree_end(e, c):
    # c's subtree = c .. last descendant (row 0)
    n = len(e.M); k = c + 1
    while k < n:
        p = k
        while p is not None and p > c: p = e.par(0, p)
        if p != c: break
        k += 1
    return k

def S1(M):
    """sibling subtrees lexicographically non-increasing"""
import sys, os, pickle, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from multiprocessing import Pool
import trio, ytosk_eval2 as Y2
from probe_dropres_single import structok, inv3_fails, rand_mat, std

def subtree_end(e, c):
    # c's subtree = c .. last descendant (row 0)
    n = len(e.M); k = c + 1
    while k < n:
        p = k
        while p is not None and p > c: p = e.par(0, p)
        if p != c: break
        k += 1
    return k

def S1(M):
    """sibling subtrees lexicographically non-increasing"""
    e = Y2.Ev2(M)
    for p in range(len(M)):
        ch = e.children[p]
        for a, b in zip(ch, ch[1:]):
            A = M[a:subtree_end(e, a)]; B = M[b:subtree_end(e, b)]
            if B > A: return False
    return True

def S2(M):
    """z = 1 column needs an earlier z = 1 column with row 1 <= its row 1 (or is (1,1,1))"""
    for c in range(len(M)):
        if M[c][2] == 1:
            if M[c] == (1, 1, 1): continue
            if not any(M[d][2] == 1 and M[d][1] <= M[c][1] for d in range(c)): return False
    return True

from probe_inv3_prefix import Ctx, spa, sumN, split, succ, lt, Z, summ

def sub_end_C(C, c):
    n = len(C.M); k = c + 1
    while k < n:
        p = k
        while p is not None and p > c: p = C.e.par(0, p)
        if p != c: break
        k += 1
    return k

def frame_ok(M, which):
    C = Ctx(M)
    if not C.ok: return False
    for i in range(len(M)):
        cl = C.CL(i); vi = C.v(i)
        for idx, c in enumerate(cl):
            B = spa(vi, sumN([C.o(d) for d in cl[:idx]]))
            s, y, _ = C.o(c)
            if not (lt(B, y) and lt((vi, Z, Z), (s, y, Z))): continue
            zc = any(M[k][2] == 1 for k in range(c, sub_end_C(C, c)))
            zb = any(M[k][2] == 1 for k in range(i, c))
            hi, lo = split(y, (succ(s), Z, Z))
            if zc and zb and ('2' not in which or M[c][1] >= 1):
                if '4' in which and B != Z and not (hi == B and lo != Z):
                    sb, sy = summ(B), summ(y)
                    pre = len(sb) < len(sy) and sy[:len(sb)] == sb
                    h = sy[0]; bo = (not B[2] and B[1] == Z); ho = (h[1] == Z)
                    if not pre and not ((bo and ho and lt(B[0], h[0])) or (not bo and not ho and not lt(B[0], h[0]))):
                        return False
                continue
            if B != Z and 'H' in which:
                if not (hi == B and lo != Z): return False
            if B == Z and 'F' in which and vi == s:
                if not (hi == Z and lo != Z): return False
    return True

def S3(M):
    e = Y2.Ev2(M)
    for c in range(len(M)):
        p = e.par(0, c)
        if p is not None and M[c][1] > M[p][1] + 1: return False
    return True

def S4(M):
    e = Y2.Ev2(M)
    for c in range(len(M)):
        if M[c][2] != 1: continue
        q = e.par(1, c)
        if q is None: continue
        path = []; a = c
        while a is not None and a != q: path.append(a); a = e.par(0, a)
        if a != q: continue
        d = path[-1]
        if d == c: continue
        if M[d][2] != 1: return False
        if any(M[t][1] <= M[c][1] for t in path[1:-1]): return False
    return True

def PH(M): return frame_ok(M, 'H')
def PH2(M): return frame_ok(M, 'H2')
def PH4(M): return frame_ok(M, 'H24')

CANDS = {'S1..S4+PH2': lambda M: S1(M) and S2(M) and S3(M) and S4(M) and PH2(M),
         'S1..S4+PH4': lambda M: S1(M) and S2(M) and S3(M) and S4(M) and PH4(M)}

def std_check(M):
    M = list(M); return {k: f(M) for k, f in CANDS.items()}

def close_check(item):
    M, res = item; M = list(M)
    out = {}
    for k, f in CANDS.items():
        if not f(M): out[k] = 'P false on base'; continue
        st = 'closed'
        for n in (1, 2, 3):
            N = trio.expand(M, n)
            if not N or len(N) < 2: continue
            try:
                if not structok(N) or inv3_fails(N): st = 'BROKEN(struct/Inv3)'; break
                if not f(N): st = 'BROKEN(P)'; break
            except Exception: st = 'EXC'; break
        out[k] = st
    return M, any(b for _, b in res), out


def collect_go(seed):
    """構造＋Inv3 を満たす非標準形の乱択の土台と、M[n]（n = 1..3）で壊れた欄。"""
    rng = random.Random(seed); out = []
    for _ in range(400):
        M = rand_mat(rng)
        if M[-1] == (0, 0, 0): continue
        try:
            if not structok(M) or inv3_fails(M): continue
        except Exception: continue
        if std(M): continue
        res = []
        for n in (1, 2, 3):
            try:
                N = trio.expand(M, n)
                if not N or len(N) < 2: continue
                if not structok(N): res.append((n, ['STRUCT'])); continue
                bad = inv3_fails(N)
            except Exception:
                res.append((n, ['EXC'])); continue
            res.append((n, sorted(bad)))
        out.append((tuple(M), res))
    return out

def main_collect(a, b, path):
    seen = {}
    with Pool(24) as p:
        for o in p.imap_unordered(collect_go, range(a, b)):
            for M, res in o: seen[M] = res
    broken = {M: r for M, r in seen.items() if any(bad for _, bad in r)}
    print('bases', len(seen), 'broken', len(broken))
    print(Counter(t for r in broken.values() for _, bad in r for t in bad))
    pickle.dump(seen, open(path, 'wb'))

def main_test(stdfiles, bases):
    c = Counter(); mats = []
    for f in stdfiles: mats += pickle.load(open(f, 'rb'))
    with Pool(24) as p:
        for r in p.imap_unordered(std_check, mats, chunksize=200):
            for k, v in r.items(): c[('Std', k, v)] += 1
    d = pickle.load(open(bases, 'rb')); ex = {}
    with Pool(24) as p:
        for M, br, out in p.imap_unordered(close_check, list(d.items()), chunksize=20):
            for k, v in out.items():
                c[('base', k, 'broken' if br else 'ok', v)] += 1
                if v.startswith('BROKEN') and len(ex.setdefault((k, v), [])) < 3: ex[(k, v)].append(M)
    for k in sorted(c, key=str): print(k, c[k])
    for k, v in ex.items():
        for M in v: print('EX', k, ''.join('(%d,%d,%d)' % t for t in M))

if __name__ == '__main__':
    if sys.argv[1] == 'collect': main_collect(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    else: main_test(sys.argv[2].split(','), sys.argv[3])
