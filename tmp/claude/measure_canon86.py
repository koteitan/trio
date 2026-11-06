"""HCanon (V3SeedCanon.lean: CanonicalNeed of every standard matrix) on the 86 sets below SRO, at every matrix M and its
prefix M.take (len - 1): at a parent p, adjacent children a < b with e1 = e1 p + 1, e2 = 1, P1 = p, upg(a-1) = a,
a topped, upg(b-1) != b, b counted at p  ==>  v(b) <= v(a)."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, lt
import ytosk_eval as Y
from pv2 import load


def le(x, y): return x == y or lt(x, y)


def check(M, cnt, ex, tag):
    C = Ctx(M)
    if not C.ok: cnt[tag + '.eval_failed'] += 1; return
    for p in range(len(M)):
        ch = C.ch(p)
        for ia in range(len(ch) - 1):
            a, b = ch[ia], ch[ia + 1]
            if not all(M[d][1] == M[p][1] + 1 and M[d][2] == 1 and C.e.par(1, d) == p for d in (a, b)): continue
            if not (a >= 1 and C.upg(a - 1) == a and C.e.topped(a)): continue
            if C.upg(b - 1) == b or not C.counted(p, b): continue
            cnt[tag + '.cases'] += 1
            if not le(C.v(b), C.v(a)):
                cnt[tag + '.failures'] += 1
                if tag not in ex or len(M) < len(ex[tag]['matrix']):
                    ex[tag] = dict(matrix=M, p=p, a=a, b=b, va=Y.tstr(C.v(a)), vb=Y.tstr(C.v(b)))


def measure(matrix):
    M = list(map(tuple, matrix)); cnt = collections.Counter(); ex = {}
    if not M < SRO or len(M) < 3: return cnt, ex
    check(M, cnt, ex, 'M')
    if len(M) >= 4: check(M[:-1], cnt, ex, 'T')
    return cnt, ex


if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=200):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
