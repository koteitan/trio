"""T が SRO から展開（n = 1..4）と接頭辞でたどり着けるか（標準形か）を幅優先で探し、道を表示する。
T より大きい行列だけを持つ（展開は値を下げるので、T に届く行列は T より大きい）。
usage: python3 std_reach.py "(0,0,0)(1,1,1)..." [LMAX]"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trio
T = tuple(eval(sys.argv[1].replace(')(', '),(')))
LMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 12
SRO = ((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
seen = {SRO: None}
frontier = [SRO]
found = False
while frontier and not found:
    nxt = []
    for M in frontier:
        for n in range(1, 5):
            N = tuple(map(tuple, trio.expand([list(c) for c in M], n)))
            for k in range(1, len(N) + 1):
                P = N[:k]
                if P == T:
                    seen[P] = (M, n); found = True; break
                if len(P) > LMAX or P <= T or P in seen:
                    continue
                seen[P] = (M, n); nxt.append(P)
            if found: break
        if found: break
    frontier = nxt
    print('frontier', len(frontier), 'seen', len(seen), flush=True)
if found:
    P = T
    while P is not None and seen[P] is not None:
        M, n = seen[P]; print(''.join(str(c).replace(' ', '') for c in M), '[%d] ->' % n, ''.join(str(c).replace(' ', '') for c in P)); P = M
else:
    print('not found')
