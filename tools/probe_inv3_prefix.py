# -*- coding: utf-8 -*-
"""Inv3 の値の不変条件を「すべての接頭辞」で、DropRes を「すべての接頭辞の 1 列落とし」で測る。
あわせて M[n-1] -> M[n]（ブロックを 1 個足す）で値が変わる列の位置を分類する。

使い方: python3 probe_inv3_prefix.py <mats.pkl> [nproc]
  mats.pkl は列の組のタプルのリスト（SRO からの乱択の展開と、その接頭辞すべて）。
  標準形の判定は ~/code/yaBMS/c/bms -s。

定義は Ytosk/lean/Ytosk の Lean の定義をそのまま写したもの（fs・fsD・OHole・holeLev・cof は Lean と同じ形）。
◁（Lhd z b a）は (b, a] を a の基本列の数項で標本にとる近似（偽の失敗は出ないが、失敗を見落としうる）。
"""
import sys, os, pickle, subprocess
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trio, ytosk_eval as Y, ytosk_eval2 as Y2

Z = (); ONE = (Z, Z, Z); TWO = (Z, Z, ONE); OM1 = (ONE, Z, Z); W2 = (Z, TWO, Z)
lt = Y.lt
BMS = os.path.expanduser('~/code/yaBMS/c/bms')

# ---- terms (Lean と同じ形) ----
def le(x, y): return x == y or lt(x, y)
def init(t):
    if not t: return Z
    a, b, c = t
    return Z if not c else (a, b, init(c))
def last(t):
    while t and t[2]: t = t[2]
    return t if not t else (t[0], t[1], Z)
def isSucc(t): return last(t) == ONE
def count(t):
    n = 0
    while t: n += 1; t = t[2]
    return n
def app(x, y): return y if not x else (x[0], x[1], app(x[2], y))
def succ(t): return app(t, ONE)
def summ(t):
    out = []
    while t: out.append((t[0], t[1], Z)); t = t[2]
    return out
def mulT(t, n): return Z if n == 0 else app(t, mulT(t, n - 1))
def cof(t):
    if not t: return ('zero',)
    a, b, c = t
    if c: return cof(c)
    if not b:
        if not a: return ('succ',)
        if isSucc(a): return ('big', init(a))
        return cof(a)
    if isSucc(b): return ('omega',)
    cb = cof(b)
    if cb[0] == 'big': return cb if lt(cb[1], a) else ('omega',)
    return cb
def fs(t, eta):
    if not t: return Z
    a, b, c = t
    if c: return (a, b, fs(c, eta))
    if not b:
        if not a: return Z
        if isSucc(a): return eta
        return (fs(a, eta), Z, Z)
    if isSucc(b): return mulT((a, init(b), Z), count(eta))
    cb = cof(b)
    if cb[0] == 'big':
        mu = cb[1]
        if lt(mu, a): return (a, fs(b, eta), Z)
        g = Z
        for _ in range(count(eta)): g = (mu, fs(b, g), Z)
        return (a, fs(b, g), Z)
    return (a, fs(b, eta), Z)
def fsD(t, eta):
    if not t: return Z
    a, b, c = t
    if c: return (a, b, fsD(c, eta))
    if not b:
        if not a: return Z
        if isSucc(a): return eta
        return (fsD(a, eta), Z, Z)
    if isSucc(b): return mulT((a, init(b), Z), count(eta))
    cb = cof(b)
    if cb[0] == 'big': return (a, fs(b, eta), Z)
    return (a, fsD(b, eta), Z)
def ohole(t):
    if not t: return False
    a, b, c = t
    if c: return ohole(c)
    if not b: return bool(a) and (isSucc(a) or ohole(a))
    if isSucc(b): return False
    if cof(b)[0] == 'big': return True
    return ohole(b)
def holelev(t):
    if not t: return Z
    a, b, c = t
    if c: return holelev(c)
    if not b: return init(a) if isSucc(a) else holelev(a)
    cb = cof(b)
    if cb[0] == 'big': return cb[1]
    return holelev(b)
def etaOm(mu): return (mu, (succ(mu), Z, Z), Z)
def notNode(t): return not (t and not t[2] and t[1] and cof(t[1])[0] == 'big')
def comps(u, t):
    if not t: return []
    v, x, c = t
    r = [] if lt(v, u) else [x] + comps(u, x) + comps(u, v)
    return r + comps(u, c)
def isOT(t):
    if not t: return True
    a, b, c = t
    if not (isOT(a) and isOT(b) and isOT(c)): return False
    if c and not le((c[0], c[1], Z), (a, b, Z)): return False
    return all(lt(g, b) for g in comps(a, b))
def single(t): return bool(t) and not t[2] and isOT(t)
def sumN(l):
    s = Z
    for t in l: s = Y.sf(Y.add(s, t))
    return s
def spa(a, S): return Y.sp(a, Z, S)[1] if S else Z
def split(t, th):
    if not t: return (Z, Z)
    a, b, c = t
    if lt((a, b, Z), th): return (Z, t)
    r = split(c, th); return ((a, b, r[0]), r[1])
def step(a, b, s, y):
    if lt(b, y) and lt((a, Z, Z), (s, y, Z)):
        t = Y.cut(Y.add(s, ONE), y); return Y.add(t, Y.sub((s, y, Z), (s, t, Z)))
    return Y.add(b, (s, y, Z))
def dec(l): return all(le(l[k + 1], l[k]) for k in range(len(l) - 1))
def closedZ(t): return all(le(g, t) for g in comps(Z, t))          # Closed a t（u = 0 が一番強い）
def vsmallV(t): return all(le(g, (t, Z, Z)) for g in comps(Z, t))
def levels(t, acc):
    if not t: return
    acc.add(t[0]); levels(t[0], acc); levels(t[1], acc); levels(t[2], acc)
def lhd(b, a):
    """Lhd z b a（標本近似）。"""
    if not lt(b, a): return False
    cs = [a]; t = a
    for _ in range(4):
        cf = cof(t)
        if cf[0] == 'zero': break
        if cf[0] == 'succ': t = fs(t, Z)
        elif cf[0] == 'omega': t = fs(t, mulT(ONE, 2))
        else: t = fs(t, (cf[1], ONE, Z))
        if lt(b, t): cs.append(t)
        else: break
    lv = set([Z]); levels(b, lv); levels(a, lv)
    for c in cs:
        for u in lv:
            ys = comps(u, c) + [Z]
            for g in comps(u, b):
                if not any(le(g, y) for y in ys): return False
    return True

def std(M):
    s = ''.join('(%d,%d,%d)' % c for c in M)
    r = subprocess.run([BMS, '-s', s], capture_output=True, text=True)
    return r.stdout.strip() == '1'

# ---- matrix-side helpers ----
class Ctx:
    def __init__(s, M):
        s.M = M; s.e = Y2.Ev2(M); s.ok = s.e.value() is not None
    def o(s, i): return s.e.o(i)
    def v(s, i): return s.e.v(i)
    def ch(s, i): return s.e.children[i]
    def counted(s, i, d): return s.M[d] != s.e.bump(i) and not (d in s.e.upgs and s.e.topped(d))
    def CL(s, i): return [d for d in s.ch(i) if s.counted(i, d)]
    def cnt(s, i, d): return s.o(d) if s.counted(i, d) else Z
    def vOpt1(s, i):
        p = s.e.par(1, i); return s.v(p) if p is not None else Z
    def e12(s, i): return s.M[i][1] != 0 and s.M[i][2] != 0
    def bumpTerm(s, i, j):
        return Y.omega(sumN([s.o(k) for k in s.ch(j)])) if s.M[j] == s.e.bump(i) else Z
    def bumpW(s, i): return Y.omega(sumN([ONE] + [s.bumpTerm(i, j) for j in s.ch(i)]))
    def pre(s, i, L): return spa(s.v(i), sumN([t for t in (s.cnt(i, d) for d in L) if t != Z]))
    def upg(s, i): return s.e._upg[i]

FIELDS = ['Good3', 'VSmallF', 'FrameClosed', 'FrameOT', 'BumpKidsDec', 'BumpTermDec', 'AbsD', 'AbsU',
          'TP1', 'TPLo', 'TP1W', 'TPLoW', 'AbsUW', 'AbsDW', 'TrigOm', 'TPLoN', 'AbsDN', 'rootS', 'rootP']
DFIELDS = ['argT', 'VSmallNew', 'BumpWeakSrc', 'UpgAbsX', 'BumpAbsC']

def inv_fields(C, note):
    """note(field, ok, info): ok=None は前件が立たなかった（数えない）。"""
    M = C.M; n = len(M)
    for i in range(n):
        note('Good3', isOT(C.o(i)) and isOT(C.v(i)), ('ot', i))
        note('Good3', dec([t for t in (C.cnt(i, d) for d in C.ch(i)) if t != Z]), ('dec', i))
        vi = C.v(i)
        # 数える子の枠
        cl = C.CL(i)
        for idx, c in enumerate(cl):
            B = spa(vi, sumN([C.o(d) for d in cl[:idx]]))
            s, y, _ = C.o(c)
            trig = lt(B, y) and lt((vi, Z, Z), (s, y, Z))
            vc = C.v(c)
            note('VSmallF', all(le(g, (vc, Z, Z)) for g in comps(vi, vc)) and (not trig or vsmallV(vc)), (i, c))
            note('FrameOT', isOT((vi, B, Z)), (i, c))
            if trig: note('FrameClosed', closedZ(B), (i, c))
        # すべての子の枠（preState）
        chs = C.ch(i)
        for idx, c in enumerate(chs):
            P = C.pre(i, chs[:idx])
            s, y, _ = C.o(c)
            if not (lt(P, y) and lt((vi, Z, Z), (s, y, Z))): continue
            if ohole(y):
                note('TP1', lt(P, fsD(y, (holelev(y), ONE, Z))), (i, c))
                if cof(y)[0] == 'omega': note('TP1W', lt(P, fsD(y, ONE)), (i, c))
            if y and not y[2] and not y[1] and isSucc(y[0]):
                note('TrigOm', P == Z, (i, c))
        # 段の項
        if C.e12(i):
            for j in chs:
                if M[j] == C.e.bump(i): note('BumpKidsDec', dec([C.o(k) for k in C.ch(j)]), (i, j))
            note('BumpTermDec', dec([t for t in (C.bumpTerm(i, j) for j in chs) if t != Z]), (i,))
            W = C.bumpW(i)
            if ohole(W):
                qs = [q for q in summ(C.vOpt1(i)) if lt(q, W)]
                note('AbsD', all(lt(q, fsD(W, etaOm(holelev(W)))) for q in qs), (i,))
                if cof(W)[0] == 'omega':
                    note('AbsDW', all(lt(q, fsD(W, (holelev(W), ONE, Z))) for q in qs), (i,))
                    if notNode(W): note('AbsDN', all(lt(q, fsD(W, ONE)) for q in qs), (i,))
        k = C.upg(i)
        if k is not None:
            lv = last(C.v(k))
            if ohole(lv):
                qs = [q for q in summ(C.vOpt1(i)) if lt(q, lv)]
                note('AbsU', all(lt(q, fsD(lv, etaOm(holelev(lv)))) for q in qs), (i, k))
                if cof(lv)[0] == 'omega': note('AbsUW', all(lt(q, fsD(lv, ONE)) for q in qs), (i, k))
        # TPLo 系（列ごと）
        s, y, _ = C.o(i)
        if y and split(y, (succ(s), Z, Z))[1] == Z:
            l = last(y)
            if not l[1]:
                a = l[0]
                if not isSucc(a) and ohole(a):
                    th = (succ(s), Z, Z)
                    note('TPLo', not lt((fsD(a, etaOm(holelev(y))), Z, Z), th), (i,))
                    if cof(a)[0] == 'omega':
                        note('TPLoW', not lt((fsD(a, (holelev(y), ONE, Z)), Z, Z), th), (i,))
                        if notNode(a): note('TPLoN', not lt((fsD(a, ONE), Z, Z), th), (i,))
    roots = [i for i in range(n) if M[i] == (0, 0, 0)]
    for r in roots: note('rootS', single(C.o(r)), (r,))
    note('rootP', dec([C.o(r) for r in roots]), ())

def drop_fields(C, T, note):
    """N = C.M、x = len − 1、σ = C、σ' = T（N.take x の評価）。"""
    M = C.M; x = len(M) - 1
    for i in range(x):
        cl = [d for d in T.ch(i) if T.counted(i, d)]
        vi = C.v(i)
        if cl:
            cs = cl[-1]; Lc = cl[:-1]
            B = spa(vi, sumN([C.o(d) for d in Lc]))
            s2, y2, _ = T.o(cs)
            if not lt(s2, vi):
                st = step(vi, B, s2, y2)
                note('argT', all(le(g, st) for g in comps(vi, y2)), (i, cs))
            if T.v(cs) != C.v(cs):
                vn = T.v(cs)
                s, y, _ = C.o(cs)
                trig = lt(B, y) and lt((vi, Z, Z), (s, y, Z))
                note('VSmallNew', all(le(g, (vn, Z, Z)) for g in comps(vi, vn)) and (not trig or vsmallV(vn)),
                     (i, cs))
    for i in range(len(M)):
        if not C.e12(i): continue
        V = C.vOpt1(i)
        for j in C.ch(i):
            if M[j] != C.e.bump(i): continue
            kids = C.ch(j)
            for idx, k in enumerate(kids):
                ok_ = C.o(k)
                if ok_[1] == Z and ok_[2] == Z and ok_[0] != Z and \
                        ((k == x and kids == [x]) or (k < x and T.o(k) != ok_)):
                    note('BumpWeakSrc', C.ch(i) == [j] and idx == 0 and all(lt(g, OM1) for g in comps(Z, V)),
                         (i, j, k))
        cond = all(not (M[j] == C.e.bump(i) and C.ch(j) == [x]) or C.v(x) == Z for j in C.ch(i))
        if cond:
            W = C.bumpW(i)
            for r in summ(V):
                if not lt(r, W2) and lt(r, W): note('BumpAbsC', lhd(r, W), (i, r))
    i = x - 1
    k = C.upg(i) if i >= 0 else None
    if k is not None:
        vk = C.v(k); V = C.vOpt1(i); sl = summ(vk)
        for st in range(len(sl)):
            Wt = Z
            for q in reversed(sl[st:]): Wt = (q[0], q[1], Wt)
            if Wt == Z or Y.add(V, Wt) != vk: continue
            for r in summ(V):
                if lt(r, Wt): note('UpgAbsX', lhd(r, Wt), (i, k, r))

def anc(par, a, b):
    """a は b の祖先（b 自身を含む）か（par で辿る）。"""
    while b is not None:
        if b == a: return True
        b = par(b)
    return False

EDGE = {'o<-o(child)': 1, 'o<-v(self)': 2, 'v<-v(par1)': 4, 'v<-v(upg)': 8, 'v<-o(bumpkid)': 16,
        'v<-bumpchild(shape)': 32}

def rhs_deps(C, i):
    """評価器の式の右辺が使う節点（Lean の oRhs / vRhs）と辺の種類。
    ('s', j) は段の子 j の形（j があること、その子の並び）。"""
    o = [(('v', i), 'o<-v(self)')] + [(('o', c), 'o<-o(child)') for c in C.CL(i)]
    v = []
    if C.M[i][1] != 0:
        p = C.e.par(1, i)
        if p is not None: v.append((('v', p), 'v<-v(par1)'))
        if C.M[i][2] == 0:
            k = C.upg(i)
            if k is not None: v.append((('v', k), 'v<-v(upg)'))
        else:
            for j in C.ch(i):
                if C.M[j] == C.e.bump(i):
                    v.append((('s', j), 'v<-bumpchild(shape)'))
                    v += [(('o', k), 'v<-o(bumpkid)') for k in C.ch(j)]
    return {('o', i): o, ('v', i): v, ('s', i): []}

def mech(CA, CN, b0):
    """N で値が変わりうる節点 -> (必要な辺の種類の最小集合（ビット）, 源の種類) の一覧。
    源 = ブロックの節点と、右辺が使う古い節点の組が A と N で違う古い節点。"""
    dA = {}; dN = {}
    for i in range(len(CA.M)): dA.update(rhs_deps(CA, i))
    for i in range(len(CN.M)): dN.update(rhs_deps(CN, i))
    rev = {}
    for nd, ds in dN.items():
        for d, k in ds: rev.setdefault(d, []).append((nd, EDGE[k]))
    best = {}; todo = []
    def push(nd, m, tag):
        cur = best.setdefault(nd, [])
        if any((x & m) == x for x, _ in cur): return
        cur[:] = [(x, t) for x, t in cur if (m & x) != m] + [(m, tag)]
        todo.append((nd, m, tag))
    for nd in dN:
        if nd[1] >= b0: push(nd, 0, 'block'); continue
        oldA = sorted(d for d, _ in dA[nd]); oldN = sorted(d for d, _ in dN[nd] if d[1] < b0)
        if oldA != oldN:
            if nd[0] == 'o': tag = 'src:counted-children-changed'
            elif nd[0] == 'v' and CA.upg(nd[1]) != CN.upg(nd[1]): tag = 'src:upg-changed'
            else: tag = 'src:other-rhs'
            push(nd, 0, tag)
        elif nd[0] == 's' and CA.ch(nd[1]) != CN.ch(nd[1]):
            push(nd, 0, 'src:bumpchild-children-changed')
    while todo:
        nd, m, tag = todo.pop()
        for nx, b in rev.get(nd, []): push(nx, m | b, tag)
    return best

def mstr(m): return '+'.join(k for k, b in EDGE.items() if m & b) or 'source'

def block_changes(M, cnt, note_ex):
    """M[n-1] -> M[n]（n = 1..3）で変わる列の分類。"""
    if len(M) < 2 or M[-1] == (0, 0, 0): return
    for n in (1, 2, 3):
        A = trio.expand(M, n - 1); N = trio.expand(M, n)
        if not A or not N: continue
        if N[:len(A)] != A:
            cnt[('blk', 'not prefix')] += 1; continue
        if len(N) == len(A): continue
        CA = Ctx(A); CN = Ctx(N)
        if not (CA.ok and CN.ok): cnt[('blk', 'noval')] += 1; continue
        b0 = len(A); blk = range(b0, len(N))
        cnt[('blk', 'blocks')] += 1
        best = mech(CA, CN, b0)
        for c in range(len(A)):
            for kind, va, vn in (('o', CA.o(c), CN.o(c)), ('v', CA.v(c), CN.v(c))):
                if va == vn: continue
                ms = best.get((kind, c))
                key = ('mech', kind, 'UNEXPLAINED') if not ms else \
                    ('mech', kind, ' | '.join(sorted('%s[%s]' % (mstr(m), t) for m, t in ms)))
                cnt[key] += 1
                note_ex(key, (M, n, c, Y.tstr(va), Y.tstr(vn)))
                if ms:
                    TREE = EDGE['o<-o(child)'] | EDGE['o<-v(self)'] | EDGE['v<-v(par1)']
                    UPG = EDGE['v<-v(upg)']; BMP = EDGE['v<-o(bumpkid)'] | EDGE['v<-bumpchild(shape)']
                    def pick(ok):
                        for m, t in ms:
                            if ok(m): return t
                    for name, ok in (('tree edges only', lambda m: m & ~TREE == 0),
                                     ('needs bump edge', lambda m: m & UPG == 0),
                                     ('needs upg edge', lambda m: m & BMP == 0),
                                     ('needs upg+bump', lambda m: True)):
                        t = pick(ok)
                        if t is not None:
                            cnt[('sum', kind, name, t)] += 1; break
        for c in range(len(A)):
            for kind, va, vn in (('o', CA.o(c), CN.o(c)), ('v', CA.v(c), CN.v(c))):
                if va == vn: continue
                a0 = anc(lambda t: CN.e.par(0, t), c, b0)
                a1 = anc(lambda t: CN.e.par(1, t), c, b0)
                if c == b0 - 1:   # 最後の列には upg がない（Lean の upg）。最後でなくなると upg がつきうる
                    cl = 'old last col' + \
                        (' upg none->some' if CA.upg(c) is None and CN.upg(c) is not None else '') + \
                        (' anc0(root)' if a0 else '')
                elif a0 and a1: cl = 'anc0&anc1(root)'
                elif a0: cl = 'anc0(root) only'
                elif a1: cl = 'anc1(root) only'
                elif anc(lambda t: CN.e.par(0, t), c, b0 - 1): cl = 'anc0(old last col)'
                elif any(anc(lambda t: CN.e.par(0, t), c, d) for d in blk): cl = 'anc0(other block col)'
                elif any(anc(lambda t: CN.e.par(1, t), c, d) for d in blk): cl = 'anc1(other block col)'
                else: cl = 'OTHER'
                cnt[('blk', kind, cl)] += 1
                if not cl.startswith('anc0&') and not cl.endswith('only'):
                    note_ex(('blk', kind, cl), (M, n, c, Y.tstr(va), Y.tstr(vn)))

def check(M):
    M = list(M)
    cnt = Counter(); ex = {}
    def note_ex(k, info):
        if len(ex.setdefault(k, [])) < 2: ex[k].append(info)
    C = Ctx(M)
    if not C.ok:
        cnt['noval'] += 1; return cnt, ex
    cnt['mats'] += 1
    def note(f, ok, info):
        cnt[(f, 'cases')] += 1
        if not ok:
            cnt[(f, 'FAIL')] += 1; note_ex((f, 'FAIL'), (M, info))
    inv_fields(C, note)
    if len(M) >= 2:
        T = Ctx(M[:-1])
        if T.ok:
            cnt['drops'] += 1
            drop_fields(C, T, note)
    block_changes(M, cnt, note_ex)
    return cnt, ex

if __name__ == '__main__':
    mats = pickle.load(open(sys.argv[1], 'rb'))
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    tot = Counter(); exs = {}
    with Pool(nproc) as p:
        for c, ex in p.imap_unordered(check, mats, chunksize=50):
            tot.update(c)
            for k, v in ex.items():
                if len(exs.setdefault(k, [])) < 2: exs[k].extend(v[:2 - len(exs[k])])
    print('mats', tot['mats'], 'noval', tot['noval'], 'drops', tot['drops'])
    for f in FIELDS + DFIELDS:
        print('%-12s cases %7d  FAIL %d' % (f, tot[(f, 'cases')], tot[(f, 'FAIL')]))
    for k in sorted([k for k in tot if isinstance(k, tuple) and k[0] in ('blk', 'sum')], key=str):
        print(k, tot[k])
    for k, v in exs.items():
        if k[0] == 'mech': continue
        for M, *info in v:
            print('EX', k, 'std' if std(M) else 'nonstd', ''.join('(%d,%d,%d)' % c for c in M), info)
