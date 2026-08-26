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
from core import expand, isstd, cmpmat, show, rows, diagcol
import rule as R


def is_succ(m):
    return bool(m) and all(v == 0 for v in m[-1])


def common_prefix(Ls):
    """行列たちの最長共通接頭辞。基本列の像は G ++ 悪い部分の複製 という形なので、
    n を増やしても この接頭辞は変わらない（有限の観測からの外挿）。"""
    if not Ls:
        return ()
    q = Ls[0]
    for L in Ls[1:]:
        k = 0
        while k < len(q) and k < len(L) and q[k] == L[k]:
            k += 1
        q = q[:k]
    return q


def surely_exceeds(A, Q):
    """A が「Q を接頭辞に持つどんな行列」も超えるか。

    A と Q を平らにして比べ、Q の長さの内側で A が上回っていれば、
    その先に何を足しても A のほうが大きい。n をいくら増やしても追いつけない、
    という決定的な判定になる（打ち切りではない）。
    """
    fa = [v for c in A for v in c]
    fq = [v for c in Q for v in c]
    for i in range(min(len(fa), len(fq))):
        if fa[i] != fq[i]:
            return fa[i] > fq[i]
    return False


def cand_cols(P, Y):
    """P の末尾に足せる列の候補。

    上限は 2 つある。
      ・DBMS の対角: 位置 x では行 y は max(x-y, 0) まで（行 y は位置 y からしか立てない）
      ・P に出た値 +1: 値は 1 つずつしか伸びない
    厳しいほうを採る。
    """
    x = len(P)
    dc = diagcol('DBMS', x, Y)
    hi = [min(max((c[y] for c in P), default=0) + 1, dc[y]) for y in range(Y)]
    # DBMS の列は「0 でない成分は厳密に減る」。
    # c[y] > 0 なら c[y-1] > c[y]（対角 max(x-y,0) の帰結。シート全行で確認済み）。
    for a in range(hi[0] + 1):
        for b in range(min(a - 1, hi[1]) + 1) if a > 0 else (0,):
            if Y < 3:
                yield (a, b)
                continue
            for c in range(min(b - 1, hi[2]) + 1) if b > 0 else (0,):
                yield (a, b, c)


TRACE = bool(os.environ.get('SUPTRACE'))
MMAX = int(os.environ.get('SUPMMAX', '6'))   # N[m] をどこまで伸ばして見るか


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
    Q = common_prefix(L)
    _t('      基本列の共通接頭辞 Q = %s' % show(Q, 1)[:76])
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
            # 「大きすぎないか」を m を伸ばしながら決定的に見る。
            #   N[m] <= f(M[K])                     -> この m は問題なし
            #   N[m] が Q の内側で Q を超える        -> どんな n でも追いつけない。棄却
            #   どちらでもない                        -> 判断保留。m を伸ばす
            ok = True
            try:
                for m in range(2, MMAX + 1):
                    A = expand(N, m)
                    if cmpmat(A, top) <= 0:
                        continue          # この m は f(M[K]) に収まる
                    # 収まらない。追いつけないと決まるか、判断保留か
                    ok = False            # 保留はどちらも棄却に倒す（安全側）
                    if surely_exceeds(A, Q):
                        _t('        棄却（決定的）: N[%d] が Q を内側で超える' % m)
                    break
            except Exception:
                continue
            if not ok:
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
