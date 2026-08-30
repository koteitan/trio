"""変換の正しさを、順序数の定義から直接確かめる。

ord は系に依らず内在的に決まる:
    ord(空) = 0
    ord(M) = ord(M - 末尾列) + 1      （末尾列が全 0 のとき）
    ord(M) = sup_n ord(M[n])          （それ以外）

f(M) = N が正しいなら ord(M) = ord(N)。M も N も極限なら、
両者の基本列は**互いに共終**でなければならない:

    ∀n ∃m: ord(M[n]) <= ord(N[m])        （N は上界）
    ∀m ∃n: ord(N[m]) <= ord(M[n])        （N は大きすぎない）

ord(M[n]) は f(M[n]) の順序数に等しく、比較はすべて DBMS 側で閉じるので、
    ∀n ∃m: f(M[n]) <= N[m]
    ∀m ∃n: N[m] <= f(M[n])
を有限の n, m で確かめればよい。これは標準形・単調性より遥かに強い検査で、
シートを一切使わない。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import expand, cmpmat, isstd, show
import rule as R


def is_succ(m):
    return bool(m) and all(v == 0 for v in m[-1])


def cofinal(M, N, K=4, conv=None):
    """M（BMS）の像が N（DBMS）でよいかを、ord の定義から来る 2 つの必要条件で見る。

      (A) 上界:  f(M[n]) < N        （n = 1..K）
      (B) 大きすぎない: N[1] <= f(M[K])

    N[1] は「N から末尾列を取ったもの」に等しい（BMS 系の展開の性質）ので、
    (B) は展開なしで確かめられる。K を大きくしないので計算量も抑えられる。
    """
    conv = conv or (lambda z: R.convert(z, 3))
    if not M:
        return (not N, '空')
    if is_succ(M):
        return ((is_succ(N)), '後続' if is_succ(N) else 'M は後続だが N は極限')
    if is_succ(N):
        return (False, 'M は極限だが N は後続')
    fm = []
    for n in range(1, K + 1):
        try:
            fm.append(conv(expand(M, n)))
        except Exception as e:
            return (None, '展開できず %r' % (e,))
    for n, a in enumerate(fm, 1):
        if cmpmat(a, N) >= 0:
            return (False, '(A) f(M[%d]) が N 以上（N が小さすぎ）' % n)
    if cmpmat(N[:-1], fm[-1]) > 0:
        return (False, '(B) N[1] が f(M[%d]) を超える（N が大きすぎ）' % K)
    return (True, '共終の必要条件を満たす')


def check_one(M, N=None, K=4):
    if N is None:
        N = R.convert(M, 3)
    if not isstd(N, 'DBMS'):
        return (False, '非標準形')
    return cofinal(M, N, K)


if __name__ == '__main__':
    from check_sheet import load
    import collections
    d = [x for x in load() if x[3] == 3]
    c = collections.Counter()
    bad = []
    for r, mb, md, _ in d[:400]:
        v, why = check_one(mb, md, K=3)
        c[v] += 1
        if v is False:
            bad.append((r['row'], why))
    print('シートの真値に対する共終検査（先頭 400 行）:', dict(c))
    for rw, why in bad[:10]:
        print('  row %-5s %s' % (rw, why))
