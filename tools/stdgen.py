# SRO から展開と接頭辞でたどり着く標準形のうち、FLOOR より大きく長さ LMAX 以下のものを全部作り、候補を測る
import os, sys, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trio
FLOOR = tuple(eval(sys.argv[1].replace(')(', '),(')))
LMAX = int(sys.argv[2]); NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3
SRO = ((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
seen = {SRO}
frontier = [SRO]
while frontier:
    nxt = []
    for M in frontier:
        for n in range(1, NMAX + 1):
            N = tuple(map(tuple, trio.expand([list(c) for c in M], n)))
            for k in range(1, min(len(N), LMAX) + 1):
                P = N[:k]
                if P <= FLOOR or P in seen:
                    continue
                seen.add(P); nxt.append(P)
    frontier = nxt
    print('frontier', len(frontier), 'seen', len(seen), file=sys.stderr, flush=True)
out = sys.argv[4]
pickle.dump(sorted(seen - {SRO}), open(out, 'wb'))
print(len(seen) - 1)
