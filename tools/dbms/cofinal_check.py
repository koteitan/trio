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


def cofinal(M, N, K=4, KM=8, conv=None):
    """M（BMS）と N（DBMS）の基本列が互いに共終かを有限近似で確かめる。

    戻り値 (判定, 理由)。判定は True/False/None（判断できず）。
    """
    conv = conv or (lambda z: R.convert(z, 3))
    if not M:
        return (not N, '空')
    if is_succ(M):
        if not is_succ(N):
            return (False, 'M は後続だが N は極限')
        return (None, '後続なので前段に帰着')
    if is_succ(N):
        return (False, 'M は極限だが N は後続')

    fm = []
    for n in range(1, K + 1):
        try:
            fm.append(conv(expand(M, n)))
        except Exception as e:
            return (None, '展開できず %r' % (e,))
    nm = []
    for m in range(1, KM + 1):
        try:
            nm.append(expand(N, m))
        except Exception as e:
            return (None, 'N の展開できず %r' % (e,))

    for n, a in enumerate(fm, 1):
        if not any(cmpmat(a, b) <= 0 for b in nm):
            return (False, 'f(M[%d]) を超える N[m] が無い（N が小さすぎ）' % n)
    for m, b in enumerate(nm[:K], 1):
        if not any(cmpmat(b, a) <= 0 for a in fm):
            return (False, 'N[%d] を超える f(M[n]) が無い（N が大きすぎ）' % m)
    return (True, '共終')


def check_one(M, N=None, K=4, KM=8):
    if N is None:
        N = R.convert(M, 3)
    if not isstd(N, 'DBMS'):
        return (False, '非標準形')
    return cofinal(M, N, K, KM)


if __name__ == '__main__':
    from check_sheet import load
    import collections
    d = [x for x in load() if x[3] == 3]
    c = collections.Counter()
    bad = []
    for r, mb, md, _ in d[:400]:
        v, why = check_one(mb, md)
        c[v] += 1
        if v is False:
            bad.append((r['row'], why))
    print('シートの真値に対する共終検査（先頭 400 行）:', dict(c))
    for rw, why in bad[:10]:
        print('  row %-5s %s' % (rw, why))
