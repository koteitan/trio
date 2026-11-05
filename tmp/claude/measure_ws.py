"""BumpWeakSrcB2 = BumpWeakShapeSrcB ∧ WeakCS2 (WfSdP2.lean) on all 86 input sets below SRO, x = |M| − 1,
ρ = values of M, ρ' = values of M.take x.  wsB from tmp/wf/WfReM/hdropB.py; WeakCS2 i < x:
¬ LhdE (ρ'.v i) (ρ.v i) → CS (ρ'.v i) ∨ WCS2 (vOpt ρ (par M 0 i)) (ρ'.v i)."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tools', '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD',
          '/home/koteitan/proofs/trio/tmp/wf/WfReM']:
    sys.path.insert(0, p)
import probe_dropres as D, invd
from probe_inv3_prefix import Ctx, Z
from lhd_exact import lhdE
from pv2 import WCS2, load
import hdropB as HB


def probe(M):
    M = [tuple(c) for c in M]; cnt = collections.Counter(); ex = {}
    if not M < invd.SRO or len(M) < 3: return cnt, ex
    x = len(M) - 1; C = Ctx(M); T = Ctx(M[:x])
    if not (C.ok and T.ok): cnt['unresolved'] += 1; return cnt, ex
    for _, ok in HB.wsB(C, T):
        cnt['shape.cases'] += 1
        if not ok: cnt['shape.FAIL'] += 1; ex.setdefault('shape', (len(M), invd.ms(M)))
    for i in range(x):
        if lhdE(T.v(i), C.v(i)): continue
        cnt['wcs.cases'] += 1
        p0 = C.e.par(0, i); a = C.v(p0) if p0 is not None else Z
        if not (D.CS(T.v(i)) or WCS2(a, T.v(i))):
            cnt['wcs.FAIL'] += 1; ex.setdefault('wcs', (len(M), invd.ms(M), i))
    return cnt, ex


def work(b):
    cnt = collections.Counter(); ex = {}
    for M in b:
        try: c, e = probe(M)
        except Exception as er: c = collections.Counter({'exc': 1}); e = {'exc': repr(er)[:200]}
        cnt.update(c)
        for k, v in e.items(): ex.setdefault(k, v)
    return cnt, ex


if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            ms = load(f)
            for c, e in pool.imap_unordered(work, [ms[i:i + 500] for i in range(0, len(ms), 500)]):
                tot.update(c)
                for k, v in e.items(): exs.setdefault(k, v)
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str)[:3000])
