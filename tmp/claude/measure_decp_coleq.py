import sys, json, collections
exec(open('/tmp/claude-1000/-home-koteitan-proofs-trio/8c329c0c-7a78-462d-b46d-3d8c95984fd0/scratchpad/decp_split2_86.py').read().split("def measure")[0])
def m2(m):
    M = list(map(tuple, m)); cnt = collections.Counter()
    if not M < SRO: return cnt
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt
    C = Ctx(M)
    if not C.ok: return cnt
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None or q == r: return cnt
    clM = C.CL(r)
    if (clM and clM[-1] == q) or C.upg(x - 1) is not None: return cnt
    T = Ctx(M[:-1])
    if not T.ok: return cnt
    cl = T.CL(r)
    if not cl: return cnt
    c0 = cl[-1]
    if not T.e.topped(c0): return cnt
    chs = [w for w in T.ch(r) if c0 <= w <= q]
    for w, w2 in zip(chs, chs[1:]):
        cnt['pair'] += 1
        cnt['e1eq.%d' % (M[w][1] == M[w2][1])] += 1
        cnt['coleq.%d' % (M[w] == M[w2])] += 1
    return cnt
sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
tot = collections.Counter()
for f in sets[int(sys.argv[1]):int(sys.argv[2])]:
    for c in map(m2, load(f)): tot.update(c)
print(dict(tot))
