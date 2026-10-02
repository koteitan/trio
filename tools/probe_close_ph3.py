# -*- coding: utf-8 -*-
"""Inv3 を展開で閉じさせる追加の不変条件 P = S1 ∧ S2 ∧ S3 ∧ S4 ∧ PH3s の実測。

PH3s（値の PreHi の 3 行版）: 列 i の数える子 c の枠で、B = spa(v(i), 前の数える子の o の和) ≠ 0、
o(c) = ψ_s(y)、書き換えが起きる（B < y かつ v(i) < ψ_s(y)）とき、hi・lo = y を Ω_{s+1} で分けたものとして
次のどれか:
  (eq)     hi = B かつ lo ≠ 0（2 行の PreHi）
  (pre)    B は hi の真の先頭部分（和として）
  (shadow) s ≠ 0、B = X + b0、hi = X + h0 + R（X は共通の先頭部分、b0 は B の最後の項）で、
           b0 = h0[π := Ω_s]。π は h0 の右端の背骨（各段で最後の項、添字か引数に入る）の上の位置で、
           そこにある項（後ろの項なし）は ψ_k(γ)、k ≥ s。

  python3 probe_close_ph3.py std <mats.pkl>               # P が標準形の集合で真か
  python3 probe_close_ph3.py bases <bases.pkl>            # 既存の非標準形の土台で閉じるか（n = 1..3 と 1 列落とし）
  python3 probe_close_ph3.py perturb <C.pkl> <seed0> <seed1>  # 標準形の接頭辞に乱択の列を足した非標準形の土台で、
                                                          # 閉じるかと、P の世界の中の乱択の展開の歩み
  python3 probe_close_ph3.py deep <seed0> <seed1> <out.pkl>  # SRO からの長い乱択の展開の鎖と接頭辞の閉包で P
"""
import sys, os, pickle, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from multiprocessing import Pool
import trio
from probe_dropres_single import structok, inv3_fails, std
from probe_close_inv import S1, S2, S3, S4
from probe_inv3_prefix import Ctx, spa, sumN, split, succ, lt, le, Z, summ

def S(M): return ''.join('(%d,%d,%d)' % t for t in M)

def frames(M):
    """書き換えが起きる B ≠ 0 の数える子の枠 (i, c, B, hi, lo, s)。評価がなければ None。"""
    C = Ctx(M)
    if not C.ok: return None
    out = []
    for i in range(len(M)):
        cl = C.CL(i); vi = C.v(i)
        for idx, c in enumerate(cl):
            B = spa(vi, sumN([C.o(d) for d in cl[:idx]]))
            s, y, _ = C.o(c)
            if B == Z or not (lt(B, y) and lt((vi, Z, Z), (s, y, Z))): continue
            hi, lo = split(y, (succ(s), Z, Z))
            out.append((i, c, B, hi, lo, s))
    return out

def spine(h, s):
    """h の右端の背骨の上の ψ_k(γ)（k ≥ s、後ろの項なし）を Ω_s に置き換えた項の集合。"""
    out = set()
    if not h: return out
    a, x, c = h
    if c:
        for t in spine(c, s): out.add((a, x, t))
        return out
    if le(s, a): out.add((s, Z, Z))
    for t in spine(a, s): out.add((t, x, Z))
    for t in spine(x, s): out.add((a, t, Z))
    return out

def ph3s_kind(B, hi, lo, s):
    if hi == B: return 'eq' if lo != Z else None
    sb, sh = summ(B), summ(hi)
    if len(sb) < len(sh) and sh[:len(sb)] == sb: return 'pre'
    if s == Z: return None
    k = 0
    while k < min(len(sb), len(sh)) and sb[k] == sh[k]: k += 1
    if k != len(sb) - 1 or k >= len(sh): return None
    return 'shadow' if sb[k] in spine(sh[k], s) else None

def cuts(h, s):
    """h の位置 π（ψ_k(γ) + 後ろ、k ≥ s）を Ω_s に替え、π より右（項の順序: 添字 → 引数 → 後ろ）をすべて落とした項。"""
    out = set()
    if not h: return out
    a, x, c = h
    if le(s, a): out.add((s, Z, Z))
    for t in cuts(a, s): out.add((t, Z, Z))
    for t in cuts(x, s): out.add((a, t, Z))
    for t in cuts(c, s): out.add((a, x, t))
    return out

def ph3c_kind(B, hi, lo, s):
    if hi == B: return 'eq' if lo != Z else None
    sb, sh = summ(B), summ(hi)
    if len(sb) < len(sh) and sh[:len(sb)] == sb: return 'pre'
    if s == Z: return None
    return 'cut' if B in cuts(hi, s) else None

def PH3c(M):
    f = frames(list(M))
    if f is None: return False
    return all(ph3c_kind(B, hi, lo, s) for i, c, B, hi, lo, s in f)

def PH3s(M):
    f = frames(list(M))
    if f is None: return False
    return all(ph3s_kind(B, hi, lo, s) for i, c, B, hi, lo, s in f)

PH = os.environ.get('PH', 'c')   # c: PH3c（既定）、s: PH3s
def P(M):
    M = list(M)
    return S1(M) and S2(M) and S3(M) and S4(M) and (PH3c(M) if PH == 'c' else PH3s(M))

RELAX = os.environ.get('RELAX', '0') != '0'   # 1: 穴の欄を非厳密版に、2: さらに AbsDW・TPLoW を外す（標準形で偽）
def world(M):
    """構造 ∧ Inv3 ∧ P。壊れた欄の名前（空なら成立）。"""
    M = list(M)
    try:
        if not structok(M): return 'struct'
        b = inv3_fails_relaxed(M) if RELAX else inv3_fails(M)
        if b: return 'Inv3:' + ','.join(sorted(b))
        if not P(M): return 'P'
    except Exception as e:
        return 'EXC'
    return ''

STAR = os.environ.get('STAR') == '1'
def world_star(M):
    """すべての接頭辞（長さ ≥ 2）で world。STAR=1 のとき閉性の判定に使う。"""
    for k in range(2, len(M) + 1):
        w = world(M[:k])
        if w: return ('pre%d:' % k if k < len(M) else '') + w
    return ''
def W(M): return world_star(M) if STAR else world(M)

def succs(M):
    """M[n]（n = 1..3）と 1 列落とし。"""
    out = []
    if len(M) >= 2: out.append(('drop', list(M[:-1])))
    if M[-1] != (0, 0, 0):
        for n in (1, 2, 3):
            N = trio.expand(list(M), n)
            if N and len(N) >= 2: out.append(('n%d' % n, N))
    return out

def close_one(M):
    for tag, N in succs(M):
        w = W(N)
        if w: return tag + ':' + w, N
    return 'closed', None

# ---- std ----
def main_std(path):
    mats = pickle.load(open(path, 'rb'))
    if isinstance(mats, dict): mats = list(mats)
    with Pool(24) as p: r = p.map(P, mats, chunksize=300)
    bad = [S(M) for M, ok in zip(mats, r) if not ok]
    print('std', len(mats), 'P false', len(bad))
    for m in sorted(bad, key=len)[:10]: print('  ', m)

# ---- bases ----
def bases_go(M):
    M = list(M)
    if not P(M): return 'Pfalse', M, None
    st, N = close_one(M)
    return st, M, N

def main_bases(path):
    d = pickle.load(open(path, 'rb')); c = Counter(); ex = {}
    with Pool(24) as p:
        for st, M, N in p.imap_unordered(bases_go, list(d), chunksize=20):
            c[st] += 1
            if st not in ('Pfalse', 'closed') and len(ex.setdefault(st, [])) < 4: ex[st].append((M, N))
    for k in sorted(c): print(k, c[k])
    for k, v in ex.items():
        for M, N in v: print('EX', k, S(M), '->', S(N))

# ---- perturb ----
def rand_col(rng, M):
    p = rng.randrange(len(M))
    if rng.random() < 0.08: return (0, 0, 0)
    a = M[p][0] + 1; b = rng.randint(0, M[p][1] + 1); cc = rng.randint(0, 1) if b > 0 else 0
    return (a, b, cc)

CMATS = None
def perturb_go(seed):
    rng = random.Random(seed); cnt = Counter(); ex = []
    for _ in range(60):
        Sm = list(rng.choice(CMATS))
        k = rng.randint(1, len(Sm))
        M = Sm[:k]
        for _ in range(rng.randint(1, 3)): M.append(rand_col(rng, M))
        if M[-1] == (0, 0, 0) or len(M) > 30: continue
        if W(M): continue
        if std(M): cnt['std(skip)'] += 1; continue
        cnt['base'] += 1
        st, N = close_one(M)
        cnt['close:' + st.split(':')[0] + ('' if st == 'closed' else ':' + st.split(':', 1)[1])] += 1
        if st != 'closed': ex.append((st, S(M), S(N))); continue
        # P の世界の中の乱択の歩み
        cur = M
        for step in range(12):
            nx = succs(cur)
            nx = [(t, N) for t, N in nx if len(N) <= 40]
            if not nx: break
            t, N = rng.choice(nx)
            w = W(N)
            if w:
                cnt['walk:BROKEN'] += 1; ex.append(('walk ' + t + ':' + w, S(cur), S(N))); break
            cur = N
            cnt['walk:step'] += 1
    return cnt, ex

def init_pool(path):
    global CMATS
    CMATS = pickle.load(open(path, 'rb'))

def main_perturb(path, a, b):
    c = Counter(); ex = []
    with Pool(24, initializer=init_pool, initargs=(path,)) as p:
        for cnt, e in p.imap_unordered(perturb_go, range(a, b)):
            c.update(cnt); ex += e
    for k in sorted(c): print(k, c[k])
    ex.sort(key=lambda t: len(t[1]))
    for e in ex[:20]: print('EX', *e)

# ---- deep ----
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]   # Ytosk BMS.lean の SRO。Std = SRO から展開で届く

def deep_go(seed):
    rng = random.Random(seed); out = set()
    for _ in range(20):
        M = list(SRO)
        for step in range(rng.randint(10, 60)):
            if M[-1] == (0, 0, 0): M = M[:-1]
            if len(M) < 2: break
            n = rng.choice((1, 2, 2, 3, 3, 4)) if len(M) < 30 else 1
            N = trio.expand(M, n)
            if not N or len(N) < 2: break
            M = N
            for k in range(2, len(M) + 1): out.add(tuple(M[:k]))
    return out

def main_deep(a, b, path):
    allm = set()
    with Pool(24) as p:
        for o in p.imap_unordered(deep_go, range(a, b)): allm |= o
    allm = [m for m in allm if len(m) <= 34]
    print('deep mats', len(allm))
    pickle.dump(allm, open(path, 'wb'))
    with Pool(24) as p: r = p.map(P, allm, chunksize=200)
    bad = [m for m, ok in zip(allm, r) if not ok]
    print('P false', len(bad))
    for m in sorted(bad, key=len)[:5]: print('  ', S(m), 'bms -s', std(list(m)))

# ---- 穴の欄の非厳密版（AbsDW・TPLoW は標準形で等号の場合に偽、2026-10-02 実測）----
from probe_inv3_prefix import (inv_fields, Ctx as _Ctx, ohole, holelev, fsD, cof, etaOm, notNode, isSucc,
                               last, ONE, summ as _summ)
HOLE = {'TP1', 'TP1W', 'AbsD', 'AbsDW', 'AbsDN', 'AbsU', 'AbsUW', 'TPLo', 'TPLoW', 'TPLoN'}
def hole_relaxed(C, note):
    """穴の欄を ≤（AbsD/AbsU/TP1 系）と fsD ≥ s（TPLo 系）で評価する。"""
    M = C.M
    for i in range(len(M)):
        vi = C.v(i); chs = C.ch(i)
        for idx, c in enumerate(chs):
            P_ = C.pre(i, chs[:idx]); s, y, _ = C.o(c)
            if not (lt(P_, y) and lt((vi, Z, Z), (s, y, Z))): continue
            if ohole(y):
                note('TP1', le(P_, fsD(y, (holelev(y), ONE, Z))))
                if cof(y)[0] == 'omega': note('TP1W', le(P_, fsD(y, ONE)))
        if C.e12(i):
            Wt = C.bumpW(i)
            if ohole(Wt):
                qs = [q for q in _summ(C.vOpt1(i)) if lt(q, Wt)]
                note('AbsD', all(le(q, fsD(Wt, etaOm(holelev(Wt)))) for q in qs))
                if cof(Wt)[0] == 'omega':
                    note('AbsDW', all(le(q, fsD(Wt, (holelev(Wt), ONE, Z))) for q in qs))
                    if notNode(Wt): note('AbsDN', all(le(q, fsD(Wt, ONE)) for q in qs))
        k = C.upg(i)
        if k is not None:
            lv = last(C.v(k))
            if ohole(lv):
                qs = [q for q in _summ(C.vOpt1(i)) if lt(q, lv)]
                note('AbsU', all(le(q, fsD(lv, etaOm(holelev(lv)))) for q in qs))
                if cof(lv)[0] == 'omega': note('AbsUW', all(le(q, fsD(lv, ONE)) for q in qs))
        s, y, _ = C.o(i)
        if y and split(y, (succ(s), Z, Z))[1] == Z:
            l = last(y)
            if not l[1]:
                a = l[0]
                if not isSucc(a) and ohole(a):
                    th = (s, Z, Z)
                    note('TPLo', not lt((fsD(a, etaOm(holelev(y))), Z, Z), th))
                    if cof(a)[0] == 'omega':
                        note('TPLoW', not lt((fsD(a, (holelev(y), ONE, Z)), Z, Z), th))
                        if notNode(a): note('TPLoN', not lt((fsD(a, ONE), Z, Z), th))

def inv3_fails_relaxed(M):
    C = _Ctx(list(M))
    if not C.ok: return {'noval'}
    bad = set()
    inv_fields(C, lambda f, g, info: bad.add(f) if g is False and f not in HOLE else None)
    drop = {'AbsDW', 'TPLoW'} if os.environ.get('RELAX') == '2' else set()
    hole_relaxed(C, lambda f, g: bad.add(f + "'") if not g and f not in drop else None)
    return bad

def main_relaxed(path):
    mats = pickle.load(open(path, 'rb'))
    if isinstance(mats, (dict, set)): mats = list(mats)
    c = Counter(); ex = {}
    with Pool(24) as p:
        for M, b in zip(mats, p.imap(inv3_fails_relaxed, mats, chunksize=300)):
            for f in b:
                c[f] += 1; ex.setdefault(f, []).append(S(M))
    print(len(mats), dict(c))
    for f, v in ex.items(): print(f, sorted(v, key=len)[:3])

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'std': main_std(sys.argv[2])
    elif cmd == 'bases': main_bases(sys.argv[2])
    elif cmd == 'perturb': main_perturb(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
    elif cmd == 'deep': main_deep(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif cmd == 'relaxed': main_relaxed(sys.argv[2])
