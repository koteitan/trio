"""Exact-shape audit of the repaired t=0 and t=2 absorption inputs.

Checks the finite n=2,3 instances of Lean's AbsWNxU, UpgAbsShape, BdXU,
NotBumpKidXU, T0AbsWU and T2BelowAtV3U clauses.  Each failed frame includes
the full source matrix.  Results are append-only JSONL, deduplicated by
(set, shard), so interrupted runs can resume safely.
"""
from pathlib import Path
import sys, json, collections, time
from multiprocessing import Pool

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tmp/codex"))
import inv3v3_inputs_audit_20261101 as B
A = B.A
from probe_inv3_prefix import Z, W2, lt, summ
from lhd_exact import comps, indices, lhd

def bad_abs_shape(C, CN, i):
    m = C.e.par(0, i)
    if m is None or C.e.par(1, i) != m:
        return False
    if C.CL(i) or CN.CL(i):
        return False
    clm, cln = C.CL(m), CN.CL(m)
    if not clm or clm[-1] != i or cln != clm:
        return False
    if any(CN.o(d) != C.o(d) for d in clm[:-1]):
        return False
    if CN.v(m) != C.v(m):
        return False
    return all(C.upg(j) != i for j in range(len(C.M)))

def upg_abs_shape(C, CN, i):
    m = C.e.par(0, i)
    if m is None or C.e.par(1, i) != m or C.CL(i) or CN.CL(i):
        return False, None
    if i in C.CL(m):
        return False, None
    ups = [j for j in range(len(C.M)) if C.upg(j) == i]
    if len(ups) != 1:
        return False, {"upgrade_sources": ups}
    c = ups[0]
    if any(C.upg(j) == c for j in range(len(C.M))):
        return False, {"upgrade_sources": ups, "someone_upgrades_to_source": True}
    p = C.e.par(0, c)
    if p is None or C.CL(c) or CN.CL(c):
        return False, {"upgrade_sources": ups, "p": p}
    for a in (m, p):
        q = C.e.par(0, a)
        if q is not None and tuple(C.M[a]) == tuple(C.e.bump(q)):
            return False, {"upgrade_sources": ups, "bump_parent": a, "parent": q}
    # comps(u, v(m)) changes only at levels appearing in either finite term.
    us = {Z}
    indices(C.v(m), us)
    indices(CN.o(c), us)
    for u in us:
        for g in comps(u, C.v(m)):
            if not lt(g, CN.o(c)):
                return False, {"upgrade_sources": ups, "m": m, "c": c,
                               "failed_component": (u, g, CN.o(c))}
    return True, {"m": m, "c": c, "p": p}

def abs_at(C, CN, i):
    Wm, Wn = C.bumpW(i), CN.bumpW(i)
    for q in summ(C.vOpt1(i)):
        if not lt(q, W2) and not lt(q, Wn) and lt(q, Wm) and not lhd(q, Wm):
            return False, (q, Wm, Wn)
    return True, None

def check_inputs(M, C, CN, bnd, label):
    cnt = collections.Counter()
    examples = {}
    states = {}
    def record_failure(key, info):
        cnt[key + ".fail"] += 1
        examples.setdefault(key, {"matrix": [list(c) for c in M], "info": repr(info)[:2000]})
    for i in range(bnd):
        if M[i][1] == 0 or M[i][2] == 0:
            continue
        cnt[label + ".AbsWNxU.column_cases"] += 1
        okA, infoA = abs_at(C, CN, i)
        if okA:
            cnt[label + ".AbsWNxU.AbsAt"] += 1
            states[i] = (False, False, False)
            continue
        cnt[label + ".AbsWNxU.absorption_fail"] += 1
        okB = bad_abs_shape(C, CN, i)
        okU, infoU = upg_abs_shape(C, CN, i)
        if okB:
            cnt[label + ".AbsWNxU.BadAbsShape"] += 1
        elif okU:
            cnt[label + ".AbsWNxU.UpgAbsShape"] += 1
        else:
            record_failure(label + ".AbsWNxU", {"i": i, "AbsAt_failure": infoA,
                           "BadAbsShape": okB, "UpgAbsShape": infoU})
        states[i] = (not okA, okB, okU)

    # Literal BdXU = BdX or BdU or an upgrader of a BdU column.
    bdu = {}
    bdx = {}
    for i in range(len(M)):
        in_range = i < bnd and M[i][1] != 0 and M[i][2] != 0
        if not in_range:
            bdu[i] = bdx[i] = False
            continue
        noabs, bshape, ushape = states.get(i, (False, False, False))
        bdx[i] = noabs and bshape
        bdu[i] = noabs and ushape
    for i in range(len(M)):
        is_bdxu = bdx[i] or bdu[i] or any(C.upg(i) == k and bdu.get(k, False) for k in range(len(M)))
        if not is_bdxu:
            continue
        cnt[label + ".BdXU.columns"] += 1
        m = C.e.par(0, i)
        if m is None:
            continue
        p = C.e.par(0, m)
        if p is None:
            continue
        cnt[label + ".NotBumpKidXU.cases"] += 1
        if tuple(M[m]) == tuple(C.e.bump(p)):
            record_failure(label + ".NotBumpKidXU", {"i": i, "m": m, "p": p,
                           "BdX": bdx[i], "BdU": bdu[i],
                           "upgrades_to_BdU": [k for k in range(len(M)) if C.upg(i) == k and bdu.get(k, False)]})
    if not any(k.startswith(label + ".AbsWNxU") and k.endswith(".fail") for k in cnt):
        cnt[label + ".AbsWNxU.pass"] += 1
    if not any(k.startswith(label + ".NotBumpKidXU") and k.endswith(".fail") for k in cnt):
        cnt[label + ".NotBumpKidXU.pass"] += 1
    return cnt, examples

def one(raw):
    M = [tuple(c) for c in raw]
    cnt = collections.Counter(input=1)
    ex = {}
    if len(M) < 2 or not M < B.SRO:
        return cnt, ex
    x = len(M) - 1
    if M[x][1] == 0:
        row, label = 0, "hAbsU"
    elif M[x][2] == 0:
        row, label = 1, "skip"
    else:
        row, label = 2, "hBXU"
    if label == "skip":
        return cnt, ex
    C = A.ctx(M)
    if not C.ok:
        cnt["evaluation.fail"] += 1
        ex["evaluation"] = {"matrix": [list(c) for c in M], "info": "source evaluator failed"}
        return cnt, ex
    parent = C.e.par(row, x)
    if parent is None:
        cnt[label + ".no_frame"] += 1
        return cnt, ex
    if label == "hBXU":
        r, bnd = parent, x
        # T2BelowAtV3U only ranges over an actual terminal row-2 frame.
        if C.e.par(2, x) != r or r >= x:
            return cnt, ex
    else:
        r, bnd = parent, parent
    cnt[label + ".source_frames"] += 1
    for n in (2, 3):
        N = [tuple(c) for c in B.trio.expand([list(c) for c in M], n)]
        CN = A.ctx(N)
        cnt[label + ".n" + str(n) + ".expansions"] += 1
        if not CN.ok:
            cnt[label + ".target_eval.fail"] += 1
            ex.setdefault(label + ".target_eval", {"matrix": [list(c) for c in M], "info": n})
            continue
        c, e = check_inputs(M, C, CN, bnd, label)
        cnt.update(c)
        ex.update({k: v for k, v in e.items() if k not in ex})
    return cnt, ex

def work(batch):
    cnt = collections.Counter()
    ex = {}
    for M in batch:
        try:
            c, e = one(M)
        except Exception as err:
            c = collections.Counter({"exception.fail": 1})
            e = {"exception": {"matrix": M, "info": repr(err)}}
        cnt.update(c)
        for k, v in e.items():
            if k not in ex or (len(v["matrix"]), v["matrix"]) < (len(ex[k]["matrix"]), ex[k]["matrix"]):
                ex[k] = v
    return cnt, ex

if __name__ == "__main__":
    out = Path(sys.argv[1]); nproc = int(sys.argv[2]); assert 1 <= nproc <= 5
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            if line.strip():
                rec = json.loads(line); done.add((rec["set"], rec["shard"]))
    for f in sys.argv[3:]:
        mats = A.load(f)
        for sh in range(0, len(mats), 10000):
            if (f, sh) in done:
                continue
            started = time.time(); total = collections.Counter(); examples = {}
            part = mats[sh:sh + 10000]
            with Pool(nproc, maxtasksperchild=100) as pool:
                jobs = [part[j:j + 20] for j in range(0, len(part), 20)]
                for c, e in pool.imap_unordered(work, jobs):
                    total.update(c)
                    for k, v in e.items():
                        if k not in examples or (len(v["matrix"]), v["matrix"]) < (len(examples[k]["matrix"]), examples[k]["matrix"]):
                            examples[k] = v
            rec = {"set": f, "shard": sh, "total": len(mats), "n": len(part),
                   "seconds": round(time.time() - started, 2), "counts": dict(total), "examples": examples,
                   "expansion_values": [2, 3], "lean_forms": ["T0AbsWU", "T2BelowAtV3U.AbsWNxU", "T2BelowAtV3U.NotBumpKidXU"]}
            with out.open("a") as fp:
                fp.write(json.dumps(rec) + "\n")
            print(json.dumps({k: v for k, v in rec.items() if k != "examples"}), flush=True)
            if total.get("exception.fail") or total.get("evaluation.fail"):
                print("EVALUATION FAILURE", json.dumps(examples), flush=True)
