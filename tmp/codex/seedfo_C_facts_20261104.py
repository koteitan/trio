"""G5: exact finite C-frame facts used by V3Main.SeedFO.seedFO_C/data_C.

Selection matches tmp/claude/measure_un.py, without a below-SRO filter.
n is explicitly sampled at 2,3; this is not proof of the infinite quantifier.
All valuations are canonical. Cons equations and existence of Rk are checked;
uniqueness of Cons under Rk justifies testing the prefix valuation once.
Std/SInv/Inv3V3 are dataset assumptions, NOT re-certified here.
False facts and evaluation errors have separate records, with full source M.
Checkpoints are atomic per (manifest index, shard), including empty datasets.
"""
from pathlib import Path
import argparse, collections, json, multiprocessing, os, sys, time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tmp/codex'))
import inv3v3_inputs_audit_20261101 as B
A = B.A
Z, ONE = B.Z, B.ONE
OUT = ROOT / 'tmp/codex/seedfo_C_facts_20261104'
MANIFEST = ROOT / 'tmp/codex/inv3v3_inputs_sets_20261101.json'
NS = (2, 3)


def context_facts(C):
    """Literal Val.Cons / V3Good.Good3; Rk by exact acyclicity."""
    cons, ot_o, ot_v, dec = True, True, True, True
    for i, col in enumerate(C.M):
        rhs_o = A.Y.sf((C.v(i), B.sumN([C.cnt(i, d) for d in C.ch(i)]), Z))
        if col[1] == 0:
            rhs_v = Z
        else:
            k = C.upg(i)
            w = C.bumpW(i) if col[2] != 0 else (ONE if k is None else B.last(C.v(k)))
            rhs_v = A.Y.sf(A.Y.add(C.vOpt1(i), w))
        cons = cons and C.o(i) == rhs_o and C.v(i) == rhs_v
        ot_o = ot_o and B.isOT(C.o(i))
        ot_v = ot_v and B.isOT(C.v(i))
        vals = [C.cnt(i, d) for d in C.ch(i) if C.cnt(i, d) != Z]
        dec = dec and all(B.le(b, a) for j, a in enumerate(vals) for b in vals[j+1:])
    return dict(Cons=bool(cons), Rk=bool(A.rank_ok(A.S(C.M))),
                Good3_ot_o=bool(ot_o), Good3_ot_v=bool(ot_v), Good3_dec=bool(dec))


def inspect(index, raw):
    M = list(map(tuple, raw)); x = len(M)-1
    cnt = collections.Counter(matrices=1); failures = []
    if x < 1 or M[x][1] == 0 or M[x][2] == 0:
        return cnt, failures
    base = dict(index=index, matrix=M, x=x)
    try:
        # Structural selection does not depend on successful value evaluation.
        S = A.S(M); r = S.par(2, x); q = S.par(0, x)
        if r is None or q is None or q == r:
            return cnt, failures
        cl = [d for d in S.children[r] if S.col(d) != S.bump(r)
              and not (d in S.upgs and S.topped(d))]
        if cl and cl[-1] == q:
            return cnt, failures
        un = S.up[x-1] is None
        partition = 'un_true' if un else 'un_false'
        cnt['C.sources'] += 1; cnt['C.'+partition] += 1
        base.update(r=r, L=x-r, q=q, upg_xminus1=S.up[x-1], CL_M_r=cl, partition=partition)
        C = A.ctx(M); T = A.ctx(M[:x])
        if not C.ok or not T.ok:
            raise ValueError('source/prefix canonical evaluation failed')
        source = context_facts(C); prefix = context_facts(T)
        qns = A.Y.add(C.v(r), A.Y.omega(B.sumN([ONE] +
                      [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
        common = {'hun': un, 'hqP': not T.counted(r, q), 'hv0': T.v(r) == C.v(r),
                  'vqP': T.v(q) == qns, 'hnu_not_upg_to_x': S.up[x-1] != x}
        common.update({'source.'+k: v for k,v in source.items()})
        common.update({'prefix.'+k: v for k,v in prefix.items()})
        lc0 = T.CL(r); a0 = T.v(r)
        common['prefix.FrameOT_r'] = all(B.isOT((a0, B.spa(a0, B.sumN([T.o(d) for d in lc0[:j]])), Z))
                                           for j in range(len(lc0)))
        common['prefix.full_state_OT_r'] = B.isOT((a0, B.spa(a0, B.sumN([T.o(d) for d in lc0])), Z))
        for n in NS:
            try:
                N = list(map(tuple, B.trio.expand([list(c) for c in M], n)))
                CN = A.ctx(N)
                if not CN.ok:
                    raise ValueError('target canonical evaluation failed')
                facts = dict(common)
                facts.update({'target.'+k:v for k,v in context_facts(CN).items()})
                facts.update(hvq0=T.v(q) == CN.v(q), vq_eq_gexp=CN.v(q) == qns,
                             CL_N_r=CN.CL(r) == T.CL(r)+[q],
                             prefix_o_agree=all(CN.o(d) == T.o(d) for d in T.CL(r)),
                             v_N_r=CN.v(r) == C.v(r), CL_N_q=CN.CL(q) == [x])
                # These are conclusions/diagnostics, NOT additional premises.
                for i, label in [(r, 'r'), (q, 'q')]:
                    lc = CN.CL(i); a = CN.v(i)
                    facts['QFO_'+label] = all(B.isOT((a, B.spa(a, B.sumN([CN.o(d) for d in lc[:j]])), Z))
                                                 for j in range(len(lc)))
                cnt['C.n'+str(n)+'.frames'] += 1
                for name, value in facts.items():
                    state = 'true' if value else 'false'
                    cnt[f'all.n{n}.{name}.{state}'] += 1
                    cnt[f'{partition}.n{n}.{name}.{state}'] += 1
                if not all(facts.values()):
                    failures.append(dict(base, n=n, status='FALSE_FACT', facts=facts,
                        false=[k for k,v in facts.items() if not v],
                        CL_T_r=T.CL(r), CL_N_r=CN.CL(r), CL_N_q=CN.CL(q),
                        values=dict(v_M_r=C.v(r), v_T_r=T.v(r), v_N_r=CN.v(r),
                                    v_T_q=T.v(q), v_N_q=CN.v(q), qnS=qns)))
            except Exception as e:
                cnt[f'{partition}.n{n}.UNRESOLVED'] += 1
                failures.append(dict(base, n=n, status='UNRESOLVED', error=repr(e)))
    except Exception as e:
        cnt['selection_or_source.UNRESOLVED'] += 1
        failures.append(dict(base, status='UNRESOLVED', error=repr(e)))
    return cnt, failures


def batch(task):
    start, mats = task
    counts = collections.Counter(); failures = []
    for offset, raw in enumerate(mats):
        c, f = inspect(start+offset, raw); counts.update(c); failures.extend(f)
    return counts, failures


def atomic(path, data):
    temp = path.with_suffix(path.suffix+'.tmp')
    temp.write_text(json.dumps(data, ensure_ascii=False)+'\n')
    os.replace(temp, path)


def main():
    p = argparse.ArgumentParser(); p.add_argument('--workers', type=int, default=3)
    p.add_argument('--shard-size', type=int, default=10000)
    p.add_argument('--self-test', action='store_true'); args = p.parse_args()
    if args.self_test:
        # Exercises actual C path and atom-free fixtures without loading datasets.
        M = [(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),
             (3,1,0),(1,1,1),(2,1,0),(3,2,1),(4,2,1),(5,2,0),
             (3,2,1),(4,2,1),(5,1,0),(4,2,1)]
        c, f = inspect(0, M)
        assert c['C.sources'] == 1, (c,f)
        assert not any(k.endswith('UNRESOLVED') for k in c), (c,f)
        assert c['C.n2.frames'] == c['C.n3.frames'] == 1, (c,f)
        assert all(rec['facts']['hqP'] and not rec['facts']['hvq0']
                   and rec['facts']['QFO_r'] and rec['facts']['QFO_q'] for rec in f)
        print(json.dumps(dict(C_sources=c['C.sources'], records=len(f),
              false_by_n={str(rec['n']):rec['false'] for rec in f}))); return
    if not 1 <= args.workers <= 3:
        p.error('use 1..3 workers: driver + workers <= 4 processes')
    OUT.mkdir(parents=True, exist_ok=True)
    sets = json.loads(MANIFEST.read_text()); totals = collections.Counter(); files=[]
    with multiprocessing.Pool(args.workers) as pool:
        for si, filename in enumerate(sets):
            mats = A.load(filename)
            for start in range(0, max(1,len(mats)), args.shard_size):
                path = OUT / f'set{si:03d}-shard{start:09d}.json'
                if path.exists():
                    rec = json.loads(path.read_text())
                    assert rec['set'] == filename and rec['total'] == len(mats)
                    assert rec['shard_size'] == args.shard_size
                else:
                    tic = time.monotonic(); counts=collections.Counter(); failures=[]
                    stop = min(start+args.shard_size,len(mats))
                    tasks=((j,mats[j:min(j+100,stop)]) for j in range(start,stop,100))
                    for c,f in pool.imap_unordered(batch,tasks,chunksize=1):
                        counts.update(c); failures.extend(f)
                    rec=dict(set=filename, set_index=si, shard=start, shard_size=args.shard_size,
                             total=len(mats), n_samples=list(NS), counts=counts,
                             failures=failures, seconds=round(time.monotonic()-tic,2))
                    atomic(path,rec)
                    print(json.dumps({k:rec[k] for k in ['set','shard','counts','seconds']}),flush=True)
                totals.update(rec['counts']); files.append(str(path.relative_to(ROOT)))
    atomic(OUT/'summary.json',dict(complete=True, manifest=str(MANIFEST), datasets=len(sets),
           n_samples=list(NS), counts=totals, checkpoints=files,
           assumptions='Std/SInv/source Inv3V3 are inherited dataset assumptions; no SRO filter'))
    print('COMPLETE '+json.dumps(dict(totals)),flush=True)


if __name__ == '__main__':
    main()
