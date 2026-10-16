"""Measure the four pending Inv3V2 fields, without sampling or old /tmp imports.

Definitions: V3SeedFields.lean, V3Inv2.lean, V3VSRAll.lean. Run with nice -n 15.
Only matrices strictly below SRO are measured. JSON includes skipped matrices,
case counts, failures, and complete counterexamples. No Lhd approximation is used.
"""
import argparse
from collections import Counter
import json
from multiprocessing import Pool
from pathlib import Path
import pickle
import time

from probe_inv3_prefix import (
    Ctx, Z, ONE, app, comps, fsD, holelev, init, isSucc, last, le,
    lt, ohole, split, succ, summ,
)

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
SETS = ('Cprime', 't0ext', 'd3s', 'deep2', 'deep3', 'ext1', 'ext1x',
        't2ext', 'ext2', 'expP')
FIELDS = ('AbsUS', 'TPLoS', 'TrigS', 'VSmallRAll')


def dependencies(C, x):
    """Least closure of the six constructors of DepX (V3Dep.lean)."""
    D = {(True, x)}
    while True:
        before = len(D)
        for i, col in enumerate(C.M):
            if (False, i) in D or any((True, c) in D for c in C.CL(i)):
                D.add((True, i))
            if col[1] == 0:
                continue
            p = C.e.par(1, i)
            hit = p is not None and (False, p) in D
            if col[2] == 0:
                k = C.upg(i)
                hit |= k is not None and (False, k) in D
            else:
                hit |= any(C.M[j] == C.e.bump(i) and
                           any((True, k) in D for k in C.ch(j)) for j in C.ch(i))
            if hit:
                D.add((False, i))
        if len(D) == before:
            return D


def measure(matrix):
    M = list(matrix)
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

    # PathLvAll.top/step: children have larger indices, so one forward pass
    # computes the complete set of reachable levels, including every child.
    paths = [set() for _ in M]
    for k in range(len(M)):
        cl = C.CL(k)
        a = C.v(k)
        for idx, c in enumerate(cl):
            s, y, _ = C.o(c)
            B = C.pre(k, cl[:idx])
            if not (lt(B, y) and lt((a, Z, Z), (s, y, Z))):
                continue
            levels = paths[k] | {a}
            paths[c].update(levels)
            if split(y, (succ(s), Z, Z))[0] == Z:
                continue
            for u in levels:
                if lt(a, u):
                    continue
                ds = comps(u, a)
                for g in comps(u, s):
                    note('VSmallRAll', le(g, (s, Z, Z)) or le(g, B) or
                         any(le(g, d) for d in ds), k=k, c=c, u=u, g=g)

    x = len(M) - 1
    if x < 1 or M[x][1] == 0 or M[x][2] != 0:
        return counts, examples
    r, q = C.e.par(1, x), C.e.par(0, x)
    if r is None:
        return counts, examples
    T = Ctx(M[:x])
    if not T.ok:
        counts['seed_eval_failed'] += 1
        examples['seed_eval_failed'] = {'matrix': M}
        return counts, examples
    mu, br, _ = C.o(r)
    seed = T.o(r)
    D = dependencies(C, x)
    if q != r:
        for i in range(x):
            if (False, i) in D:
                k = C.upg(i)
                if k is not None:
                    W = last(C.v(k))
                    if ohole(W) and holelev(W) == mu:
                        F = fsD(W, seed)
                        for t in summ(C.vOpt1(i)):
                            if lt(t, W):
                                note('AbsUS', lt(t, F), i=i, k=k, summand=t)
            if (True, i) in D:
                s, y, _ = C.o(i)
                l = last(y)
                if (l and l[1] == Z and not isSucc(l[0]) and ohole(l[0])
                        and holelev(y) == mu and split(y, (succ(s), Z, Z))[1] == Z):
                    note('TPLoS', not lt((fsD(l[0], seed), Z, Z),
                                        (succ(s), Z, Z)), c=i)
    elif br and last(br) == (succ(mu), Z, Z) and lt(seed, (mu, ONE, Z)):
        b = init(br)
        for i in range(x):
            if (True, i) not in D:
                continue
            ch = C.ch(i)
            for idx, c in enumerate(ch):
                if (True, c) not in D or not C.counted(i, c):
                    continue
                s, y, _ = C.o(c)
                B = C.pre(i, ch[:idx])
                if y == br and lt(B, y) and lt((C.v(i), Z, Z), (s, y, Z)):
                    note('TrigS', lt(B, app(b, seed)), i=i, c=c, state=B, seed=seed)
    return counts, examples


def main(measure_fn=measure, fields=FIELDS, case_unit=
         'quantified summand/component, or TPLoS/TrigS frame',
         definitions=('V3SeedFields.lean', 'V3Inv2.lean', 'V3VSRAll.lean')):
    parser = argparse.ArgumentParser(description=measure_fn.__doc__ or __doc__)
    def set_name(value):
        if value not in SETS:
            raise argparse.ArgumentTypeError('unknown set: ' + value)
        return value

    parser.add_argument('sets', nargs='*', type=set_name, default=list(SETS),
                        metavar='SET', help='sets to scan; default: all ten sets')
    parser.add_argument('--data', type=Path, default=Path(__file__).resolve().parents[1] /
                        'tmp/ytosk-handoff/sets')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    with Pool(args.workers) as pool:
        for name in args.sets:
            started = time.monotonic()
            with (args.data / (name + '.pkl')).open('rb') as f:
                matrices = pickle.load(f)
            total, examples = Counter(), {}
            print(f'{name}: start {len(matrices)} matrices', flush=True)
            for index, (counts, ex) in enumerate(pool.imap(measure_fn, matrices, chunksize=100), 1):
                total.update(counts)
                for field, example in ex.items():
                    examples.setdefault(field, example)
                if index % 100000 == 0:
                    print(f'{name}: {index}/{len(matrices)}', flush=True)
            report = {'set': name, 'counts': dict(total), 'examples': examples,
                      'seconds': round(time.monotonic() - started, 2),
                      'definitions': definitions,
                      'fields': fields, 'case_unit': case_unit}
            (args.output / (name + '.json')).write_text(
                json.dumps(report, ensure_ascii=False, indent=2) + '\n')
            print(json.dumps(report, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
