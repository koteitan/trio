# -*- coding: utf-8 -*-
"""DropRes の各項目（argT・VSmallNew・BumpWeakSrc・UpgAbsX・BumpAbsC）を、1 つの行列とその評価だけで述べた
条件から出す案を測る。あわせて、その条件が展開 M → M[n]（n = 1..3）で保たれるかを測る。

  python3 probe_dropres_single.py imply <mats.pkl>...     # 案の条件が成り立つか、DropRes を導くか
  python3 probe_dropres_single.py pres  <mats.pkl>...     # Std の M で、案の条件が M[n] に保たれるか
  python3 probe_dropres_single.py close <seed> <count>    # 非標準形（構造と Inv3 の値の不変条件を満たす乱択）で保存
  python3 probe_dropres_single.py trv   <mats.pkl>...     # VSmallV の DRelV での受け渡し（順序数だけの補題）

案（x = 最後の列、Dx = M.take x で値が変わりうる呼び出し。Dx は構造だけで決まる: 右辺の形が変わる呼び出しから、
依存の辺を逆にたどった閉包）:
- LocA（構造）: take で数える子をもつ i について v(i) ∉ Dx、最後の数える子より前の数える子 d で o(d) ∉ Dx。
  argT ⟸ Good3(M.take x) ∧ LocA（M.take x は Std。枠の後の状態の ψ が標準形 ⟺ argT の比較）。
- VSmallNew ⟸ VSmallF(M.take x) の前半 ∧ LocA ∧ VSmallF(M) の後半 ∧ TrV（VSmallV v ∧ DRelV v' v → VSmallV v'）。
- BumpWeakSrc: Lean の文は偽（drop1 は範囲外の x で o' = ψ_0(0) を返すので k = x で発火する。また k = x−1 が
  upg を失うときなど、o(k) が ◁ で変わる所でも発火する）。BWS'（k < x かつ ◁ でない変化、または k = x が唯一の子）
  なら成り立つ。BWS' ⟸ CollShape ∧ LocWeak:
  CollShape（値、最後の列を使う）: 段の子 j の子が k だけで o(k) = ψ_w(0)（w ≠ 0）、k = x か o(k) ∈ Wk なら
    children i = [j] ∧ CS(v(P_1 i))。Wk = 崩れの枠（段の子の子が x だけ、v(x) ≠ 0）の v から、弱い変化が伝わる
    辺（o ← o(子) を除き、o ← v(自分) は数える子がないときだけ）でたどった o 節点。
  LocWeak: o(k) が ◁ でなく変わる（k < x）なら o(k) ∈ Wk かつ k は唯一の子（ドロップ補題の帰納法で運ぶ形）。
  （FirstKidShape・LocWS は Std で偽。比較のため残す。）
- UpgAbsL（値）: upg i = k で k < i か k が葉なら UpgAbs の主張。UpgAbsX ⟸ UpgAbsL（x−1 の upg の的は x か祖先）。
- BumpAbsC: それ自身が 1 つの行列の条件（最後の列を使う）。
"""
import sys, os, pickle, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_inv3_prefix import *

def deps_all(C, upto):
    d = {}
    for i in range(upto): d.update(rhs_deps(C, i))
    return d

def Dx(C, T):
    """M.take x で値が変わりうる呼び出し（構造だけ）。"""
    x = len(C.M) - 1
    dM = deps_all(C, x + 1); dT = deps_all(T, x)
    rev = {}
    for nd, ds in dT.items():
        for d, _ in ds: rev.setdefault(d, []).append(nd)
    out = set(); todo = []
    for nd in dT:
        if sorted(dM[nd]) != sorted(dT[nd]) or (nd[0] == 's' and C.ch(nd[1]) != T.ch(nd[1])):
            out.add(nd); todo.append(nd)
    while todo:
        nd = todo.pop()
        for nx in rev.get(nd, []):
            if nx not in out: out.add(nx); todo.append(nx)
    return out

def CLT(T, i): return [d for d in T.ch(i) if T.counted(i, d)]

# ---- 案の条件 ----
def locA(C, T, D, bad):
    x = len(C.M) - 1
    for i in range(x):
        cl = CLT(T, i)
        if not cl: continue
        if ('v', i) in D: bad('LocA', ('v', i))
        for d in cl[:-1]:
            if ('o', d) in D: bad('LocA', ('o', d, 'under', i))

def bumpKids(C):
    for i in range(len(C.M)):
        if not C.e12(i): continue
        for j in C.ch(i):
            if C.M[j] == C.e.bump(i):
                for idx, k in enumerate(C.ch(j)): yield i, j, idx, k

def weak(t): return t[1] == Z and t[2] == Z and t[0] != Z

def firstKidShape(C, bad):
    for i, j, idx, k in bumpKids(C):
        if idx == 0 and weak(C.o(k)):
            V = C.vOpt1(i)
            if not (C.ch(i) == [j] and all(lt(g, OM1) for g in comps(Z, V))): bad('FirstKidShape', (i, j, k))

def locWS(C, T, D, bad):
    for i, j, idx, k in bumpKids(C):
        if k < len(C.M) - 1 and weak(C.o(k)) and ('o', k) in D and idx != 0: bad('LocWS', (i, j, k))

def weakClosure(C):
    """崩れの枠（段の子 j' の子が最後の列 x だけで v(x) ≠ 0 の i'）の v から、弱い変化が伝わりうる辺だけで
    たどった o 節点。o ← o(子) は通さない（そこでは ◁ になる）。o ← v(自分) は数える子がないときだけ通す。"""
    M = C.M; x = len(M) - 1
    src = [('v', i) for i in range(len(M)) if C.e12(i) and C.v(x) != Z and
           any(M[j] == C.e.bump(i) and C.ch(j) == [x] for j in C.ch(i))]
    rev = {}
    for i in range(len(M)):
        for nd, ds in rhs_deps(C, i).items():
            for d, k in ds:
                if k == 'o<-o(child)': continue
                if k == 'o<-v(self)' and C.CL(nd[1]): continue
                rev.setdefault(d, []).append(nd)
    out = set(src); todo = list(src)
    while todo:
        nd = todo.pop()
        for nx in rev.get(nd, []):
            if nx not in out: out.add(nx); todo.append(nx)
    return set(i for (t, i) in out if t == 'o')

def collShape(C, bad):
    x = len(C.M) - 1; Wk = weakClosure(C)
    for i, j, idx, k in bumpKids(C):
        if C.ch(j) == [k] and weak(C.o(k)) and (k == x or k in Wk):
            V = C.vOpt1(i)
            if not (C.ch(i) == [j] and all(lt(g, OM1) for g in comps(Z, V))): bad('CollShape', (i, j, k))

def locWeak(C, T, bad):
    """ドロップで o(k) が ◁ でなく変わる（k < x）なら o(k) ∈ Wk かつ k は段の子 j のただ 1 つの子。"""
    x = len(C.M) - 1; Wk = weakClosure(C)
    for i, j, idx, k in bumpKids(C):
        if k < x and weak(C.o(k)) and T.o(k) != C.o(k) and not lhd(T.o(k), C.o(k)):
            if not (k in Wk and C.ch(j) == [k]): bad('LocWeak', (i, j, k))

def bumpWeakSrcVariants(C, T, res, note, M):
    """BumpWeakSrc の 3 つの版。Lean: k = x では drop1 の値は範囲外の ψ_0(0) = 1。"""
    x = len(C.M) - 1
    for v in ('BWS(Lean)', 'BWS(k<x)', "BWS'(k<x,not lhd)"): res[v] = True
    for i, j, idx, k in bumpKids(C):
        ok_ = C.o(k)
        if not weak(ok_): continue
        V = C.vOpt1(i)
        shape = C.ch(i) == [j] and idx == 0 and all(lt(g, OM1) for g in comps(Z, V))
        if shape: continue
        o2 = T.o(k) if k < x else ONE
        only = k == x and C.ch(j) == [x]
        for v, fire in (('BWS(Lean)', only or o2 != ok_),
                        ('BWS(k<x)', only or (k < x and o2 != ok_)),
                        ("BWS'(k<x,not lhd)", only or (k < x and o2 != ok_ and not lhd(o2, ok_)))):
            if fire: res[v] = False; note((v, 'FAIL'), (M, (i, j, k)))

def upgAbsGen(C, bad, name, sel):
    for i in range(len(C.M)):
        k = C.upg(i)
        if k is None or not sel(i, k): continue
        vk = C.v(k); V = C.vOpt1(i); sl = summ(vk)
        for st in range(len(sl)):
            Wt = Z
            for q in reversed(sl[st:]): Wt = (q[0], q[1], Wt)
            if Wt == Z or Y.add(V, Wt) != vk: continue
            for r in summ(V):
                if lt(r, Wt) and not lhd(r, Wt): bad(name, (i, k, Y.tstr(r), Y.tstr(Wt)))

def upgAbsL(C, bad): upgAbsGen(C, bad, 'UpgAbsL', lambda i, k: k < i or not C.ch(k))
def upgAbsX(C, bad):
    x = len(C.M) - 1; upgAbsGen(C, bad, 'UpgAbsX', lambda i, k: i + 1 == x)

def bumpAbsC(C, bad):
    M = C.M; x = len(M) - 1
    for i in range(len(M)):
        if not C.e12(i): continue
        if any(M[j] == C.e.bump(i) and C.ch(j) == [x] and C.v(x) != Z for j in C.ch(i)): continue
        V = C.vOpt1(i); W = C.bumpW(i)
        for r in summ(V):
            if not lt(r, W2) and lt(r, W) and not lhd(r, W): bad('BumpAbsC', (i, Y.tstr(r), Y.tstr(W)))

VALUE_P = [('FirstKidShape', firstKidShape), ('CollShape', collShape), ('UpgAbsL', upgAbsL), ('UpgAbsX', upgAbsX), ('BumpAbsC', bumpAbsC)]

def eval_all(M, cnt, note, with_drop=True):
    """M の上で案の条件（と、確かめのため DropRes の各項目と Dx の健全性）を測る。"""
    C = Ctx(M)
    if not C.ok: cnt['noval'] += 1; return None
    res = {}
    def mk(name):
        def bad(_n, info):
            res[name] = False; note((name, 'FAIL'), (M, info))
        return bad
    for name, f in VALUE_P:
        res[name] = True; f(C, mk(name))
    if with_drop and len(M) >= 2 and M[-1] != (0, 0, 0):
        T = Ctx(M[:-1])
        if T.ok:
            D = Dx(C, T); x = len(M) - 1
            sound = all(nd in D for i in range(x) for nd, a, b in
                        ((('o', i), C.o(i), T.o(i)), (('v', i), C.v(i), T.v(i))) if a != b)
            res['Dx sound'] = sound
            if not sound: note(('Dx sound', 'FAIL'), (M, ()))
            res['LocA'] = True; locA(C, T, D, mk('LocA'))
            res['LocWS'] = True; locWS(C, T, D, mk('LocWS'))
            res['LocWeak'] = True; locWeak(C, T, mk('LocWeak'))
            bumpWeakSrcVariants(C, T, res, note, M)
            dr = Counter()
            def dnote(f, ok, info):
                if not ok: res[f] = False; note((f, 'FAIL'), (M, info))
            for f in DFIELDS: res[f] = True
            drop_fields(C, T, dnote)
    return res

def go_imply(M):
    M = list(M); cnt = Counter(); ex = {}
    def note(k, info):
        if len(ex.setdefault(k, [])) < 2: ex[k].append(info)
    res = eval_all(M, cnt, note)
    if res:
        for k, v in res.items(): cnt[(k, v)] += 1
        # 導出の確かめ: 案が成り立つ所で DropRes が成り立つか
        if 'LocA' in res:
            cnt[('argT <= LocA', res['LocA'] <= res['argT'])] += 1
            cnt[("BWS' <= CollShape&LocWeak", (res['CollShape'] and res['LocWeak']) <= res["BWS'(k<x,not lhd)"])] += 1
            cnt[('UpgAbsX <= UpgAbsL', res['UpgAbsL'] <= res['UpgAbsX'])] += 1
    return cnt, ex

def t_of(M):
    c = M[-1]; return 2 if c[2] else (1 if c[1] else 0)

PRES = ['CollShape', 'LocWeak', 'FirstKidShape', 'UpgAbsL', 'UpgAbsX', 'BumpAbsC', 'LocA', 'LocWS', 'Dx sound']

def go_pres(M):
    M = list(M); cnt = Counter(); ex = {}
    def note(k, info):
        if len(ex.setdefault(k, [])) < 2: ex[k].append(info)
    if len(M) < 2 or M[-1] == (0, 0, 0): return cnt, ex
    r0 = eval_all(M, cnt, lambda k, i: None)
    if not r0: return cnt, ex
    for n in (1, 2, 3):
        N = trio.expand(M, n)
        if not N or len(N) < 2: continue
        r1 = eval_all(N, cnt, lambda k, i: None)
        if not r1: cnt['N noval'] += 1; continue
        for p in PRES:
            if p in r0 and p in r1 and r0[p]:
                cnt[(p, 't%d' % t_of(M), 'kept' if r1[p] else 'BROKEN')] += 1
                if not r1[p]: note((p, 'BROKEN'), (M, n, N))
    return cnt, ex

# ---- 非標準形での閉包 ----
def structok(M):
    e = Y2.Ev2(M)
    if e.value() is None: return False
    n = len(M)
    if M[0] != (0, 0, 0): return False
    for c in range(n):
        p = e.par(0, c)
        if p is not None and M[c][0] != M[p][0] + 1: return False
        if M[c][2] > 1: return False
        if M[c][1] == 0 and M[c][2] != 0: return False
        if M[c][0] == 0 and M[c][1] != 0: return False
    for p in range(n):
        ch = e.children[p]
        for a, b in zip(ch, ch[1:]):
            if not (M[b] <= M[a]): return False
        for c in ch:
            if M[p][2] == 1 and M[c][1] > M[p][1]: return False
            if M[c] == e.bump(p) and M[p][2] != 1: return False
    for i in range(n):
        k = e._upg[i]
        if k is None or k == i + 1: continue
        if e.topped(k): return False
        a = i
        while a is not None and a != k:
            if a in [j for j in e.children[k] if M[j] == e.bump(k)]: return False
            a = e.par(0, a)
    return True

def inv3_ok(M):
    C = Ctx(M)
    if not C.ok: return False
    ok = [True]
    def note(f, good, info):
        if not good: ok[0] = False
    inv_fields(C, note)
    return ok[0]

def rand_mat(rng):
    L = rng.randint(3, 10); M = [(0, 0, 0)]
    for _ in range(L - 1):
        p = rng.randrange(len(M))
        if rng.random() < 0.85:
            a = M[p][0] + 1; b = rng.randint(0, M[p][1] + 1); cc = rng.randint(0, 1) if b > 0 else 0
        else: a, b, cc = 0, 0, 0
        M.append((a, b, cc))
    return M

def inv3_fails(M):
    C = Ctx(M)
    if not C.ok: return {'noval'}
    bad = set()
    inv_fields(C, lambda f, good, info: bad.add(f) if not good else None)
    return bad

def go_close(seed):
    """構造の不変条件と Inv3 の値の不変条件を満たす非標準形 M から M[n] へ。案の条件の保存（N の Inv3 が
    保たれたかで分けて数える）と、N で壊れた Inv3 の欄。"""
    rng = random.Random(seed); cnt = Counter(); ex = {}
    def note(k, info):
        if len(ex.setdefault(k, [])) < 2: ex[k].append(info)
    for _ in range(400):
        M = rand_mat(rng)
        if M[-1] == (0, 0, 0): continue
        try:
            if not structok(M) or inv3_fails(M): continue
        except Exception: continue
        if std(M): cnt['std (skipped)'] += 1; continue
        r0 = eval_all(M, cnt, lambda k, i: None)
        if not r0: continue
        cnt['nonstd base'] += 1
        for n in (1, 2, 3):
            try:
                N = trio.expand(M, n)
            except Exception: continue
            if not N or len(N) < 2: continue
            try:
                if not structok(N): cnt['N struct broken'] += 1; continue
                bad = inv3_fails(N)
                for f in bad:
                    cnt[('N Inv3 broken', f)] += 1; note(('N Inv3 broken', f), (M, n, N))
                tag = 'N Inv3 ok' if not bad else 'N Inv3 broken'
                r1 = eval_all(N, cnt, lambda k, i: None)
            except Exception: continue
            if not r1: continue
            for p in PRES:
                if p in r0 and p in r1 and r0[p]:
                    cnt[(p, tag, 'kept' if r1[p] else 'BROKEN')] += 1
                    if not r1[p]: note((p, tag, 'BROKEN'), (M, n, N))
    return cnt, ex

# ---- TrV: VSmallV の受け渡し ----
def CSv(t): return all(lt(g, OM1) for g in comps(Z, t))
def go_trv(M):
    M = list(M); cnt = Counter(); ex = {}
    C = Ctx(M)
    if not C.ok: return cnt, ex
    seen = set()
    for i in range(len(M)):
        v = C.v(i)
        if v in seen or not vsmallV(v): continue
        seen.add(v)
        front = [v]
        for depth in range(3):
            nxt = []
            for t in front:
                cf = cof(t)
                if cf[0] == 'zero': continue
                etas = [Z] if cf[0] == 'succ' else ([mulT(ONE, 1), mulT(ONE, 2), mulT(ONE, 3)] if cf[0] == 'omega'
                                                    else [Z, ONE, (cf[1], ONE, Z), (cf[1], (succ(cf[1]), Z, Z), Z)])
                for eta in etas:
                    t2 = fs(t, eta)
                    if t2 == t: continue
                    nxt.append(t2)
                    rel = 'lhd' if lhd(t2, v) else ('wkv' if lt(t2, v) and CSv(t2) and le(ONE, t2) else None)
                    if rel is None: continue
                    ok = vsmallV(t2)
                    cnt[('TrV', rel, ok)] += 1
                    if not ok and len(ex.setdefault(('TrV', rel), [])) < 3:
                        ex[('TrV', rel)].append((M, Y.tstr(v), Y.tstr(t2)))
            front = nxt
    return cnt, ex

def run(fn, items, nproc=16):
    tot = Counter(); exs = {}
    with Pool(nproc) as p:
        for c, ex in p.imap_unordered(fn, items, chunksize=20):
            tot.update(c)
            for k, v in ex.items():
                if len(exs.setdefault(k, [])) < 2: exs[k].extend(v[:2 - len(exs[k])])
    for k in sorted(tot, key=str): print(k, tot[k])
    for k, v in exs.items():
        for e in v:
            M = e[0]
            print('EX', k, 'std' if std(M) else 'nonstd', ''.join('(%d,%d,%d)' % c for c in M), e[1:])

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode in ('imply', 'pres', 'trv'):
        mats = []
        for f in sys.argv[2:]: mats += pickle.load(open(f, 'rb'))
        run({'imply': go_imply, 'pres': go_pres, 'trv': go_trv}[mode], mats)
    elif mode == 'close':
        seed, count = int(sys.argv[2]), int(sys.argv[3])
        run(go_close, [seed * 100000 + k for k in range(count)])
