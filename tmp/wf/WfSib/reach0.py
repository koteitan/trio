import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
def parse(s): return [tuple(map(int, c.split(','))) for c in s.strip('()').split(')(')]
def reach(X, lim=100000):
    Y = SRO; path = []
    for _ in range(lim):
        if Y == X: return path
        if Y < X: return None
        n = 0
        while True:
            Z = [tuple(c) for c in trio.expand([list(c) for c in Y], n)]
            if X <= Z or n > 60: break
            n += 1
        if n > 60: return None
        path.append(n); Y = Z
    return None
if __name__=="__main__":
 for s in sys.argv[1:]:
    p=reach(parse(s)); print(len(p) if p is not None else None, p)
