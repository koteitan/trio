"""3 行の変換の失敗を (1) 最小の型に絞り (2) 正しい像を総当たりで探す。

    python3 probe3.py min  [列数上限]      … R が壊れる最小の行列を並べる
    python3 probe3.py want "<BMS 行列>"    … R を満たす DBMS 標準形を探す
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, expand, isstd, cmpmat
from rows3 import gen3, b2d3, key


def cols_upto(amax):
    for a in range(amax + 1):
        for b in range(max(a - 1, 0) + 1):
            for c in range(max(b - 1, 0) + 1):
                yield (a, b, c)


def cands(Sk, extra):
    """`Sk` より真に大きい DBMS 標準形を、分岐してから `extra` 列まで集める。"""
    out = []

    def rec(N, i, over, used):
        if over:
            out.append(N)
            if used >= extra:
                return
        amax = (N[-1][0] + 1) if N else 0
        for c in cols_upto(amax):
            if not over:
                if i < len(Sk):
                    if c < Sk[i]:
                        continue
                    nover = c > Sk[i]
                else:
                    nover = True
            else:
                nover = True
            T = N + (c,)
            if not isstd(T, 'DBMS'):
                continue
            rec(T, i + 1, nover, used + 1 if nover else 0)

    rec((), 0, False, 0)
    return out


def want(M, K=10, extra=6, mm=3, show_n=4):
    """R（像<m> が f(M<n>) に一致）を満たす DBMS 標準形を小さい順に。"""
    S = {tuple(b2d3(expand(M, n))): n for n in range(1, K + 1)}
    Sk = max(S, key=lambda m: key(m))
    res = []
    for N in cands(Sk, extra):
        E = [tuple(expand(N, m)) for m in range(1, mm + 1)]
        if len(set(E)) == mm and all(e in S for e in E):
            res.append(N)
    res.sort(key=key)
    return res[:show_n]


def Rfail(M, nr=6, mm=12, nn=24):
    N = b2d3(M)
    img = {tuple(expand(N, m)) for m in range(1, mm + 1)}
    for n in range(1, nr + 1):
        if not any(tuple(b2d3(expand(M, np))) in img for np in range(n, n + nn + 1)):
            return n
    return 0


def minimal(lim):
    t0 = time.time()
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    bad = set()
    for M in A:
        if len(M) > 1 and Rfail(M):
            bad.add(M)
    ns = {M for M in A if not isstd(b2d3(M), 'DBMS')}
    root = [M for M in sorted(bad, key=key)
            if not any(M[:i] in bad for i in range(1, len(M)))]
    print('BMS 3 行 z<2 <=%d 列: %d 個  R 違反 %d  像が非標準 %d  (%.1fs)'
          % (lim, len(A), len(bad), len(ns), time.time() - t0))
    print('R が壊れる最小の行列（接頭辞に壊れたものが無いもの）: %d 個' % len(root))
    for M in root:
        print('   %-40s -> %s' % (show(M), show(b2d3(M))))
    nsroot = [M for M in sorted(ns, key=key)
              if not any(M[:i] in ns for i in range(1, len(M)))]
    print('像が非標準になる最小の行列: %d 個' % len(nsroot))
    for M in nsroot:
        print('   %-40s -> %s' % (show(M), show(b2d3(M))))


if __name__ == '__main__':
    if sys.argv[1] == 'min':
        minimal(int(sys.argv[2]) if len(sys.argv) > 2 else 6)
    else:
        for t in sys.argv[2:]:
            M = parse(t, 3)
            t0 = time.time()
            r = want(M)
            print('%s\n  いま     %s\n  R を満たす %s  (%.1fs)'
                  % (t, show(b2d3(M)),
                     ' | '.join(show(x) for x in r) or '（なし）', time.time() - t0),
                  flush=True)
