"""Measure seven value invariants of Ytosk on BMS matrices, exactly as the Lean definitions say.

Run with ``nice -n 15`` (the script also lowers its own priority to 15). Only matrices
strictly below SRO (Python list comparison ``M < SRO``) are measured.

Usage:
    nice -n 15 python3 probe_frame7.py [SET ...] [--data DIR] [--output DIR]
        [--workers N<=4] [--sample N --seed S]

Notation: x = M.length - 1 (the last column), rho = the evaluation of M (Ctx(M)),
rho' = the evaluation of M.take x (Ctx(M[:x])), D = DepX M x (probe_inv2.dependencies),
d_i = dOf M x (loQ M rho mu b) (lbQ M rho mu b) i (probe_trigs0.lift_counts),
Y = app b (psi (succ mu) z z) = b_r, A = psi mu Y z = rho.o r.

Frames (the leading antecedents):
  F_ne (AbsDS):  par M 1 x = some r, par M 0 x != some r, entry M 2 x = 0, rho.o r = psi mu b z.
  F_qr (AbsUWL, AbsDW, AbsUW0, TPLoN, TPLoW):
                 par M 1 x = some r, par M 0 x = some r, entry M 2 x = 0,
                 rho.o r = psi mu (app b (psi (succ mu) z z)) z.
  AbsDN has no frame (all columns i < M.length).

Correspondence table (Python check -> Lean definition, line by line)
=====================================================================
| check   | Lean (file, name)                    | correspondence                                    |
|---------|--------------------------------------|---------------------------------------------------|
| AbsDS   | V3SeedFields.lean, AbsDS             | forall r mu b + 4 frame hyps -> F_ne; r = par1 x, |
|         |                                      | (mu, b) = C.o(r) when its tail is Z.              |
|         |                                      | forall i, i < x -> loop i in range(x).            |
|         |                                      | DepX M x false i -> (False, i) in D.              |
|         |                                      | entry 1 i != 0, entry 2 i != 0 -> C.e12(i).       |
|         |                                      | OHole (bumpW M rho i) -> ohole(C.bumpW(i)).       |
|         |                                      | holeLev W = mu -> holelev(W) == mu.               |
|         |                                      | forall q in summands (vOpt rho (par M 1 i)),      |
|         |                                      |   q < W -> q in summ(C.vOpt1(i)), lt(q, W).       |
|         |                                      | conclusion q < fsD W ((drop1 M x rk).o r) ->      |
|         |                                      |   lt(q, fsD(W, Ctx(M[:x]).o(r))).                 |
| AbsUWL  | V3QRLocV.lean, AbsUWL                | F_qr; i < x; (False, i) in D; upg M i = some k -> |
|         |                                      | k = C.upg(i) is not None; L = last(C.v(k));       |
|         |                                      | OHole L; cof L = .omega -> cof(L) == ('omega',);  |
|         |                                      | q in summ(vOpt1 i), lt(q, L) ->                   |
|         |                                      | lt(q, fsD(L, gamS mu Y one (max 1 d_i))).         |
| AbsDW   | V3QRLocV.lean, AbsDW                 | F_qr; i < x; (False, i) in D; e12(i);             |
|         |                                      | W = bumpW i; OHole W; cof W = .omega;             |
|         |                                      | q in summ(vOpt1 i), lt(q, W) ->                   |
|         |                                      | lt(q, fsD(W, gamS mu Y one (max 1 d_i))).         |
| AbsUW0  | V3QRFinal4.lean, AbsUW0 (l. 289)     | as AbsUWL plus d_i == 0, with the index           |
|         |                                      | (drop1 M x rk).o r = Ctx(M[:x]).o(r).             |
| TPLoN   | V3QRFinal4.lean, TPLoN (l. 50)       | forall rho' rk', Cons (M.take x) rho' ->          |
|         | (the frame form; NOT TPLoNAll,       |   Rk (M.take x) rk' -> ... : only rho'.o r is     |
|         | which is only a sufficient           |   used, and it is unique, = Ctx(M[:x]).o(r)       |
|         | condition via tplon_of_all)          |   (see "exactness" below).                        |
|         |                                      | F_qr; c < x; (True, c) in D; d_c == 0;            |
|         |                                      | (s, y) = C.o(c) when its tail is Z;               |
|         |                                      | y != Y; split(y, (succ s, Z, Z))[1] == Z;         |
|         |                                      | last y = psi a z z -> l = last(y), l != Z,        |
|         |                                      |   l[1] == Z, a = l[0];                            |
|         |                                      | isSucc a = false; OHole a; cof a = .omega;        |
|         |                                      | NotNode a -> notNode(a);                          |
|         |                                      | not (psi (fsD a (rho'.o r)) z z < psi (succ s) z z)|
| AbsDN   | V3QRFinal4.lean, AbsDN (l. 70)       | forall i < M.length; e12(i); W = bumpW i;         |
|         |                                      | OHole W; cof W = .omega; NotNode W;               |
|         |                                      | q in summ(vOpt1 i), lt(q, W) -> lt(q, fsD(W, one))|
| TPLoW   | V3QRKeep.lean, TPLoW (l. 32)         | as TPLoN but without d_c == 0 and NotNode a,      |
|         |                                      | with index gamS mu Y one (max 1 d_c).             |

Auxiliary definitions and their Python mirrors:
  gamS (FSS.lean)          -> gamS() below: gamS 0 = seed, gamS (k+1) = psi mu (fs b (gamS k)) z,
                              with probe_inv3_prefix.fs (same clauses as FS.lean fs).
  DepX (V3Dep.lean)        -> probe_inv2.dependencies (least fixed point of the six constructors).
  DepL / dOf (V3QRIdx.lean), loQ / lbQ (V3QRDiag.lean)
                           -> probe_trigs0.lift_counts(C, x, A): least-weight paths from (true, x).
  bumpW (V3BumpDrop.lean)  -> Ctx.bumpW = omega (sumN (one :: map bumpTerm (children i))).
  OHole (V3Mono.lean), holeLev (V3FrameT1.lean), fsD (FSD.lean), cof (FS.lean), split / last
  (Term.lean), summands (SF.lean), init / isSucc / count (FS.lean), app / succ (Basic.lean)
                           -> probe_inv3_prefix.ohole / holelev / fsD / cof / split / last / summ /
                              init / isSucc / app / succ.
  NotNode (V3QRFinal4.lean) -> probe_inv3_prefix.notNode: not (t = psi a b z with cof b = big _).
  drop1 (V3MainT1D.lean)   -> Ctx(M[:x]).o(r) (see exactness).
  T's < (Order.lean)       -> lt(x, y) (the instance is lt x y = true).

Exactness (how the infinite quantifiers become finite checks)
-------------------------------------------------------------
* forall r mu b / s y / a / k: each is fixed by an equation with a function value
  (par, rho.o r = psi mu Y z, rho.o c = psi s y z, last y = psi a z z, upg i = some k).
  T is a free algebra, so psi mu Y z = C.o(r) fixes mu, Y; and Y = app b X with
  X = psi (succ mu) z z a single summand holds iff last(Y) == X, and then b = init(Y) is the
  only solution (app is concatenation of summand lists). So one value per binder: exact.
* forall i < x, forall c < x, forall i < M.length, forall q in summands: finite.
* dOf = Nat.find of {d | DepL false i d}, else of {d | DepL true i d}, else 0. Every DepL
  derivation is a chain (each constructor has one DepL premise) from leaf (true, x) with
  added weights lo i c in {0,1} and lb i j k in {0,1,2}. So the least d is the least path
  weight in a finite graph with nonnegative weights, which lift_counts computes by
  relaxation to a fixed point. Exact. (lift_counts sums the earlier bump terms without nzs;
  sumN l = z iff sumN (nzs l) = z, since every term is z or nonzero, so the test is the same.)
  An internal check compares the vertices reached by lift_counts with D; a mismatch is
  counted as 'internal.depx_mismatch'.
* rho: the fields are statements about a given valuation rho; the probe takes rho = the
  evaluator value Ctx(M) (in the Lean uses rho is Cons M rho with Rk M rk, which makes rho
  unique on columns < M.length by cons_unique). If Ctx(M) has a cycle, 'eval_failed'.
* drop1 M x rk (AbsDS, AbsUW0): rk is a free parameter of the field. In every use rk is a
  ranking of M (Rk M rk), and then Cons (M.take x) (drop1 M x rk) (t2_drop_ctx / cons_of_rk),
  so by cons_unique (drop1 M x rk).o r = Ctx(M[:x]).o(r) for r < x. For an rk that is not a
  ranking, drop1 is an unrelated valuation; the probe does NOT cover that case (it is not a
  case the proofs use). This is the one place where the probe measures the field only at the
  intended rk.
* forall rho' rk' with Cons (M.take x) rho' and Rk (M.take x) rk' (TPLoN): the Python
  evaluator raises Cycle exactly when the dependency graph used by Rk has a cycle, so
  Ctx(M[:x]).ok iff some Rk (M.take x) rk' exists. If none exists, TPLoN is vacuous at that
  frame (counted as 'TPLoN.vacuous_no_rank'). If one exists, Ctx(M[:x]) is a Cons solution
  and every Cons rho' agrees with it at r < x (cons_unique). So one value of rho'.o r: exact.
  (This relies on ytosk_eval2.Ev2 mirroring oRhs/vRhs/par/children/upg/bump/topped of Lean,
  which the earlier probes established; it is not re-proved here.)
* For AbsDS / AbsUW0, if Ctx(M[:x]) fails in a frame, the probe counts 'seed_eval_failed'
  and skips the frame (under Rk M rk it cannot fail, by t2_drop_ctx).

Counters: '<Field>.cases' / '<Field>.failures' count the innermost instance (each summand q
with q < W for the Abs* fields; each column c for TPLo*). '<Field>.frames' counts the columns
i / c where all antecedents before the summand quantifier hold.
"""
import argparse
from collections import Counter
import json
from multiprocessing import Pool
import os
from pathlib import Path
import pickle
import random
import sys
import time

TOOLS = '/home/koteitan/proofs/trio/tools'
if TOOLS not in sys.path:
    sys.path.insert(0, TOOLS)

from probe_inv3_prefix import (  # noqa: E402
    Ctx, Z, ONE, cof, fs, fsD, holelev, isSucc, last, lt, notNode, ohole, split,
    succ, summ, sumN, Y as YE,
)
from probe_inv2 import SRO, dependencies  # noqa: E402
from probe_trigs0 import lift_counts  # noqa: E402

FIELDS = ('AbsDS', 'AbsUWL', 'AbsDW', 'AbsUW0', 'TPLoN', 'AbsDN', 'TPLoW')
SETS = ('Cprime', 't0ext', 'd3s', 'deep2', 'deep3', 'ext1', 'ext1x',
        't2ext', 'ext2', 'expP')
DEFINITIONS = ('V3SeedFields.lean:AbsDS', 'V3QRLocV.lean:AbsUWL', 'V3QRLocV.lean:AbsDW',
               'V3QRFinal4.lean:AbsUW0', 'V3QRFinal4.lean:TPLoN', 'V3QRFinal4.lean:AbsDN',
               'V3QRKeep.lean:TPLoW')
OMEGA = ('omega',)


def gamS(mu, b, seed, k):
    """FSS.lean gamS: gamS 0 = seed, gamS (k+1) = psi mu (fs b (gamS k)) z."""
    g = seed
    for _ in range(k):
        g = (mu, fs(b, g), Z)
    return g


def ts(t):
    return YE.tstr(t)


def measure(matrix):
    """Count cases and failures of the seven fields at one matrix."""
    M = [tuple(c) for c in matrix]
    counts = Counter(input=1)
    examples = {}
    if not M < SRO:
        counts['outside_SRO'] += 1
        return counts, examples
    C = Ctx(M)
    if not C.ok:
        counts['eval_failed'] += 1
        examples['eval_failed'] = {'matrix': M}
        return counts, examples
    counts['measured'] += 1

    def note(field, ok, **info):
        counts[field + '.cases'] += 1
        if not ok:
            counts[field + '.failures'] += 1
            examples.setdefault(field, {'matrix': M, **info})

    # ---- AbsDN (V3QRFinal4.lean l. 70): every column, eta = one ----
    for i in range(len(M)):
        if not C.e12(i):                       # entry 1 i != 0, entry 2 i != 0
            continue
        W = C.bumpW(i)
        if not (ohole(W) and cof(W) == OMEGA and notNode(W)):
            continue
        counts['AbsDN.frames'] += 1
        F = fsD(W, ONE)
        for q in summ(C.vOpt1(i)):
            if lt(q, W):
                note('AbsDN', lt(q, F), i=i, W=ts(W), q=ts(q), fsD=ts(F))

    # ---- the last-column frames ----
    x = len(M) - 1
    if x < 1:
        return counts, examples
    r = C.e.par(1, x)
    if r is None or M[x][2] != 0:           # par M 1 x = some r, entry M 2 x = 0
        return counts, examples
    o_r = C.o(r)
    if o_r == Z or o_r[2] != Z:             # rho.o r = psi mu _ z
        return counts, examples
    mu, br = o_r[0], o_r[1]
    q0 = C.e.par(0, x)
    D = dependencies(C, x)
    T = None

    def seed_of():
        nonlocal T
        if T is None:
            T = Ctx(M[:x])
        return T.o(r) if T.ok else None

    if q0 != r:
        # ---- AbsDS (V3SeedFields.lean): frame F_ne, b = br (any) ----
        counts['frame.ne'] += 1
        seed = None
        for i in range(x):
            if (False, i) not in D or not C.e12(i):
                continue
            W = C.bumpW(i)
            if not (ohole(W) and holelev(W) == mu):
                continue
            if seed is None:
                seed = seed_of()
                if seed is None:
                    counts['seed_eval_failed'] += 1
                    examples.setdefault('seed_eval_failed', {'matrix': M})
                    break
            counts['AbsDS.frames'] += 1
            F = fsD(W, seed)
            for q in summ(C.vOpt1(i)):
                if lt(q, W):
                    note('AbsDS', lt(q, F), i=i, r=r, W=ts(W), q=ts(q), seed=ts(seed), fsD=ts(F))
        return counts, examples

    # ---- frame F_qr: Y = app b (psi (succ mu) z z) ----
    if br == Z or last(br) != (succ(mu), Z, Z):
        return counts, examples
    Yb = br  # Y; the unique b with app b Omega_{mu+1} = Y is init(Y) (loQ/lbQ only use Y)
    counts['frame.qr'] += 1
    d = lift_counts(C, x, o_r)
    _check_lifts(C, x, o_r, D, d, counts)

    seed = None
    seed_tried = False

    def seed_once():
        nonlocal seed, seed_tried
        if not seed_tried:
            seed_tried = True
            seed = seed_of()
        return seed

    for i in range(x):
        di = d[i]
        eta_L = None
        if (False, i) in D:
            # AbsUWL / AbsUW0: upgrades
            k = C.upg(i)
            if k is not None:
                L = last(C.v(k))
                if ohole(L) and cof(L) == OMEGA:
                    qs = [q for q in summ(C.vOpt1(i)) if lt(q, L)]
                    eta_L = gamS(mu, Yb, ONE, max(1, di))
                    counts['AbsUWL.frames'] += 1
                    F = fsD(L, eta_L)
                    for q in qs:
                        note('AbsUWL', lt(q, F), i=i, k=k, r=r, d_i=di, L=ts(L), q=ts(q),
                             eta=ts(eta_L), fsD=ts(F))
                    if di == 0:
                        s0 = seed_once()
                        if s0 is None:
                            counts['seed_eval_failed'] += 1
                            examples.setdefault('seed_eval_failed', {'matrix': M})
                        else:
                            counts['AbsUW0.frames'] += 1
                            F0 = fsD(L, s0)
                            for q in qs:
                                note('AbsUW0', lt(q, F0), i=i, k=k, r=r, L=ts(L), q=ts(q),
                                     seed=ts(s0), fsD=ts(F0))
            # AbsDW: bump terms
            if C.e12(i):
                W = C.bumpW(i)
                if ohole(W) and cof(W) == OMEGA:
                    if eta_L is None:
                        eta_L = gamS(mu, Yb, ONE, max(1, di))
                    counts['AbsDW.frames'] += 1
                    F = fsD(W, eta_L)
                    for q in summ(C.vOpt1(i)):
                        if lt(q, W):
                            note('AbsDW', lt(q, F), i=i, r=r, d_i=di, W=ts(W), q=ts(q),
                                 eta=ts(eta_L), fsD=ts(F))
        if (True, i) in D:
            # TPLoW / TPLoN at the o call c = i
            c = i
            oc = C.o(c)
            if oc == Z or oc[2] != Z:
                continue
            s, y = oc[0], oc[1]
            if y == Yb:
                continue
            if split(y, (succ(s), Z, Z))[1] != Z:
                continue
            l = last(y)
            if l == Z or l[1] != Z:
                continue
            a = l[0]
            if isSucc(a) or not ohole(a) or cof(a) != OMEGA:
                continue
            th = (succ(s), Z, Z)
            eta = gamS(mu, Yb, ONE, max(1, d[c]))
            Fa = fsD(a, eta)
            note('TPLoW', not lt((Fa, Z, Z), th), c=c, r=r, d_c=d[c], s=ts(s), y=ts(y),
                 a=ts(a), eta=ts(eta), fsD=ts(Fa))
            if d[c] == 0 and notNode(a):
                s0 = seed_once()
                if s0 is None:
                    counts['TPLoN.vacuous_no_rank'] += 1
                else:
                    F0 = fsD(a, s0)
                    note('TPLoN', not lt((F0, Z, Z), th), c=c, r=r, s=ts(s), y=ts(y),
                         a=ts(a), seed=ts(s0), fsD=ts(F0))
    return counts, examples


def _check_lifts(C, x, A, D, d, counts):
    """Independent re-derivation of DepL (V3QRIdx.lean) as a dict of least weights.

    Checks (1) the vertices with a DepL derivation are exactly DepX (depX_of_depL / depL_of_depX)
    and (2) dOf from this dict equals lift_counts. Mismatches are 'internal.*' counters."""
    from math import inf
    br = A[1]
    best = {(True, x): 0}
    while True:
        changed = False

        def relax(key, val):
            nonlocal changed
            if val < best.get(key, inf):
                best[key] = val
                changed = True
        for i, col in enumerate(C.M):
            ch = C.ch(i)
            # ov
            if (False, i) in best:
                relax((True, i), best[(False, i)])
            # ochild with lo = loQ i c
            for c in ch:
                if (True, c) in best and C.counted(i, c):
                    L = [e for e in ch if e < c]
                    lo = 1 if (C.o(c) == A and lt(C.pre(i, L), br)
                               and lt((C.v(i), Z, Z), A)) else 0
                    relax((True, i), best[(True, c)] + lo)
            if col[1] == 0:
                continue
            p = C.e.par(1, i)
            if p is not None and (False, p) in best:          # vpar
                relax((False, i), best[(False, p)])
            if col[2] == 0:
                k = C.upg(i)
                if k is not None and (False, k) in best:      # vupg
                    relax((False, i), best[(False, k)])
            else:
                for j in ch:                                   # vbump with lb = lbQ i j k
                    if C.M[j] != C.e.bump(i):
                        continue
                    for k in C.ch(j):
                        if (True, k) not in best:
                            continue
                        lb = 0
                        if C.ch(j) == [k] and C.o(k) == A:
                            prior = [t for t in (C.bumpTerm(i, e) for e in ch if e < j) if t != Z]
                            lb = 2 if sumN(prior) == Z else 1
                        relax((False, i), best[(True, k)] + lb)
        if not changed:
            break
    if set(best) != D:
        counts['internal.depx_mismatch'] += 1
    for i in range(len(C.M)):
        dv = best.get((False, i), best.get((True, i), 0))
        if dv != d[i]:
            counts['internal.dOf_mismatch'] += 1
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])

    def set_name(value):
        if value not in SETS:
            raise argparse.ArgumentTypeError('unknown set: ' + value)
        return value

    parser.add_argument('sets', nargs='*', type=set_name, default=list(SETS), metavar='SET')
    parser.add_argument('--data', type=Path,
                        default=Path('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent / 'out_frame7')
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    parser.add_argument('--sample', type=int, default=0,
                        help='measure only N matrices drawn at random (testing)')
    parser.add_argument('--seed', type=int, default=0)
    args = parser.parse_args()
    cur = os.nice(0)
    if cur < 15:
        os.nice(15 - cur)
    args.output.mkdir(parents=True, exist_ok=True)
    with Pool(args.workers) as pool:
        for name in args.sets:
            started = time.monotonic()
            with (args.data / (name + '.pkl')).open('rb') as f:
                matrices = pickle.load(f)
            if args.sample:
                rnd = random.Random(args.seed)
                matrices = rnd.sample(matrices, min(args.sample, len(matrices)))
            total, examples = Counter(), {}
            print(f'{name}: start {len(matrices)} matrices', flush=True)
            for index, (counts, ex) in enumerate(pool.imap(measure, matrices, chunksize=100), 1):
                total.update(counts)
                for field, example in ex.items():
                    examples.setdefault(field, example)
                if index % 100000 == 0:
                    print(f'{name}: {index}/{len(matrices)}', flush=True)
            report = {'set': name, 'sample': args.sample, 'counts': dict(sorted(total.items())),
                      'examples': examples, 'seconds': round(time.monotonic() - started, 2),
                      'definitions': DEFINITIONS, 'fields': FIELDS,
                      'case_unit': 'summand q < W (Abs*), column c (TPLo*)'}
            (args.output / (name + '.json')).write_text(
                json.dumps(report, ensure_ascii=False, indent=2) + '\n')
            print(json.dumps({'set': name, 'counts': report['counts'],
                              'failures': {k: v for k, v in examples.items()}},
                             ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
