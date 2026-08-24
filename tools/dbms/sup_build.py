"""極限行列の像を、基本列から**構成する**。

BMS 系の展開には次の性質がある（`crosscheck.py` で C 実装と一致を確認済み）:

    N が極限なら  N[1] = N から末尾列を落としたもの

したがって像 N は「ある行列 P に列 c を 1 本足したもの」であり、P は基本列の
どれかに一致するはずである。基本列の添字は系によってずれる（BMS の M[n] と
DBMS の N[m] は 1 対 1 ではない）ので、ずれ s を 0,1,2 と振って

    N = f(M[1+s]) ++ [c]     かつ   N[2] = f(M[2+s])

を満たす c を探す。c の候補は P の値から上に 1 以内に限られるので有限。

これは規則ではなく ord の定義からの構成なので、規則の答え合わせに使える。
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import expand, isstd, cmpmat, show, rows
import rule as R


def is_succ(m):
    return bool(m) and all(v == 0 for v in m[-1])


def cand_cols(P, Y):
    """P の末尾に足せる列の候補。各行は P に出た値 +1 まで。"""
    hi = [max((c[y] for c in P), default=0) + 1 for y in range(Y)]
    for a in range(hi[0] + 1):
        for b in range(min(a, hi[1]) + 1):
            if Y < 3:
                yield (a, b)
                continue
            for c in range(min(b, hi[2]) + 1):
                yield (a, b, c)


TRACE = bool(os.environ.get('SUPTRACE'))


def _t(msg):
    if TRACE:
        print(msg, flush=True)


def build(M, Y=3, K=5, conv=None):
    """M（極限）の像を基本列から構成する。見つからなければ None。"""
    conv = conv or (lambda z: R.convert(z, Y))
    if not M:
        return ()
    if is_succ(M):
        _t('      後続なので f(M-末尾) に全 0 列を足す')
        return conv(M[:-1]) + (tuple([0] * Y),)
    L = []
    for n in range(1, K + 1):
        try:
            e = expand(M, n)
            v = conv(e)
            L.append(v)
            _t('      M[%d] %2d 列 -> f= %s' % (n, len(e), show(v, 1)[:76]))
        except Exception as ex:
            _t('      M[%d] 展開できず %r' % (n, ex))
            break
    if len(L) < 2:
        return None
    # 受理条件は等号ではなく共終条件:
    #   N はすべての f(M[n]) の上界であり、N[m] は f(M[n]) のどれかに収まる。
    # 条件を満たすうち**最小**が sup。
    top = L[-1]
    best = None
    # P は「基本列のどれかの接頭辞」でよい（接頭辞は元より小さいので上界を壊さない）
    seen = set()
    Ps = []
    for s in range(min(3, len(L))):
        for k in range(1, len(L[s]) + 1):
            q = L[s][:k]
            if q not in seen:
                seen.add(q); Ps.append(q)
    _t('      土台 P の候補 %d 個（基本列の接頭辞）' % len(Ps))
    ntry = nstd = 0
    for P in Ps:
        for c in cand_cols(P, Y):
            ntry += 1
            N = P + (c,)
            if best is not None and cmpmat(N, best) >= 0:
                continue
            if not isstd(N, 'DBMS'):
                continue
            nstd += 1
            if any(cmpmat(a, N) >= 0 for a in L):      # 上界か
                continue
            try:
                ok = all(cmpmat(expand(N, m), top) <= 0 for m in (2, 3))
            except Exception:
                continue
            if not ok:                                  # 大きすぎないか
                continue
            _t('      候補 %s' % show(N, 1)[:76])
            best = N
    _t('      試した %d 通り（標準形 %d）  結果 %s'
       % (ntry, nstd, show(best, 1)[:70] if best else 'なし'))
    return best


if __name__ == '__main__':
    from check_sheet import load
    import collections
    d = [x for x in load() if x[3] == 3]
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    cap = int(os.environ.get('SUPCAP', '40'))   # 列数がこれを超える行は飛ばす
    c = collections.Counter(); bad = []
    for i, (r, mb, md, _) in enumerate(d[:n]):
        print('  [%4d/%d] row %-5s %d 列 %s' % (i + 1, min(n, len(d)), r['row'],
                                                len(mb), show(mb, 1)[:60]),
              flush=True)
        if TRACE:
            print('      真値 %s' % show(md, 1)[:76], flush=True)
        if len(mb) > cap:
            c['大きすぎて飛ばした'] += 1
            continue
        b = build(mb)
        if b is None:
            c['構成できず'] += 1
        elif b == md:
            c['真値と一致'] += 1
            _t('      => 真値と一致')
        else:
            c['真値と不一致'] += 1
            if len(bad) < 5:
                bad.append((r['row'], show(mb, 1), show(md, 1), show(b, 1)))
    print('シート先頭 %d 行での構成結果: %s' % (n, dict(c)))
    for rw, a, t, g in bad:
        print('  row %-5s %s' % (rw, a))
        print('     真値 %s' % t); print('     構成 %s' % g)
