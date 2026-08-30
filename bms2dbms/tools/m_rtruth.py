"""性質 R を、シートの正解表だけで（変換器を使わずに）判定する。

性質 R:  M が標準形で |M|>1 のとき、任意の n>=1 に対し
         ある m>=1 と n'>=n があって  f(M)<m> = f(M<n'>)   （行列として完全一致）

正解表 T は BM4-Analysis シートの (BMS 列, DBMS 列) の対（sheet3.load）。
f は順序を保つので、基本列 <k> は k について狭義単調増加である（core.fsindex
がそれを使っている）。したがって次の 2 方向の照合は**窓に依らず確定的**である。

  n' 方向: M<n'> がシートに載っていれば E = f(M<n'>) が分かる。
           k = fsindex(D, E) は D<k> >= E となる最小の k なので、
           D<k> == E なら当たり、そうでなければ**どんな m でも当たらない**。
  m  方向: D<m> がシートの DBMS 列に載っていれば B = f^{-1}(D<m>) が分かる。
           k = fsindex(M, B) を同じように使えば、B が M の基本列の項かどうかが
           確定する。項でなければ**その m はどんな n' でも当たらない**。

どちらの表にも載っていないところだけが「判定不能」である。

  python3 m_rtruth.py [NP] [MM] [pad] [出す例の数]
"""
import sys, os, json, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, rows, isstd, expand, cmpmat, fsindex
import core
import sheet3

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'psiI.json')

YES, NO, UNK = 1, -1, 0


def table(pad=False):
    """BMS -> (DBMS, シート行番号)。pad なら 2 行・1 行のシート行も 0 詰めで足す。"""
    T = {}
    for row, b, d in sheet3.load(1):
        T[b] = (d, row)
    if pad:
        for r in json.load(open(DATA)):
            if not (r.get('bms') and r.get('dbms')):
                continue
            r = sheet3.fix(r)
            try:
                b0 = parse(r['bms'])
            except Exception:
                continue
            if not b0 or rows(b0) >= 3:
                continue
            try:
                b, d = parse(r['bms'], 3), parse(r['dbms'], 3)
            except Exception:
                continue
            if not isstd(b, 'BMS') or b in T:
                continue
            T[b] = (d, r['row'])
    return T


def isterm(A, B):
    """B が A の基本列の項 A<k> (k>=1) なら k、そうでなければ None（確定判定）。"""
    if cmpmat(B, A) >= 0:
        return None
    k = fsindex(A, B)
    if k is None:
        return None
    # 後続の行列では expand(A,n) が n に依らないので fsindex が 0 を返す。
    # R は m>=1 を要求するので 1 に持ち上げて確かめる。
    k = max(k, 1)
    return k if expand(A, k) == B else None


def scan(T, NP, MM):
    Tinv = {}
    for b, (d, row) in T.items():
        Tinv.setdefault(d, b)
    res = []
    items = [(row, b, d) for b, (d, row) in T.items() if len(b) > 1]
    items.sort(key=lambda t: (len(t[1]), t[0]))
    t0 = time.time()
    for i, (row, M, D) in enumerate(items):
        nside = {}   # n' -> (状態, m)
        mside = {}   # m  -> (状態, n')
        for np_ in range(1, NP + 1):
            Mn = expand(M, np_)
            if Mn not in T:
                nside[np_] = (UNK, None)
                continue
            E = T[Mn][0]
            k = isterm(D, E)
            nside[np_] = ((YES, k) if k is not None else (NO, None))
        for m in range(1, MM + 1):
            Dm = expand(D, m)
            B = Tinv.get(Dm)
            if B is None:
                mside[m] = (UNK, None)
                continue
            k = isterm(M, B)
            mside[m] = ((YES, k) if k is not None else (NO, None))
        res.append((row, M, D, nside, mside))
        if len(core._exp_memo) > 300000:
            core._exp_memo.clear(); core._flat_memo.clear()
    return res, time.time() - t0


def summarize(rec, NP, MM):
    """行ごとの当たり (n',m) の集合と、確定的な外れの集合。"""
    row, M, D, nside, mside = rec
    hits = set()
    for np_, (st, m) in nside.items():
        if st == YES:
            hits.add((np_, m))
    for m, (st, np_) in mside.items():
        if st == YES:
            hits.add((np_, m))
    non = sorted(n for n, (st, _) in nside.items() if st == NO)   # 確定外れの n'
    nom = sorted(m for m, (st, _) in mside.items() if st == NO)   # 確定外れの m
    unkn = sorted(n for n, (st, _) in nside.items() if st == UNK)
    unkm = sorted(m for m, (st, _) in mside.items() if st == UNK)
    return hits, non, nom, unkn, unkm


def prefix(nside, NP):
    """n'=1,2,... のうちシートに載っている連続の頭の長さ K。"""
    K = 0
    for n in range(1, NP + 1):
        if nside[n][0] == UNK:
            break
        K = n
    return K


def diffcols(D, E):
    """E に一番近い D<k> (k>=1) を取り、E との違いを返す。
       (k, 一致する列数, D<k> の列数, E の列数, 末尾 1 列だけの差なら差分ベクトル)"""
    k = fsindex(D, E)
    if k is None:
        return None
    k = max(k, 1)
    F = expand(D, k)
    same = 0
    for a, b in zip(F, E):
        if a != b:
            break
        same += 1
    d = None
    if len(F) == len(E) and same == len(E) - 1:
        d = tuple(E[-1][y] - F[-1][y] for y in range(3))
    return (k, same, len(F), len(E), d)


def main():
    NP = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    MM = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    pad = len(sys.argv) > 3 and sys.argv[3] == '1'
    nex = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    T = table(pad)
    res, dt = scan(T, NP, MM)
    print('正解表 T: %d 対 (pad=%d)   走査 %d 行 %.1f 秒 (NP=%d, MM=%d)'
          % (len(T), pad, len(res), dt, NP, MM))

    A, B, C = [], [], []
    cn = collections.Counter()
    kdist = collections.Counter()
    for rec in res:
        row, M, D, nside, mside = rec
        hits, non, nom, unkn, unkm = summarize(rec, NP, MM)
        K = prefix(nside, NP)
        kdist[K] += 1
        hK = [h for h in hits if h[0] is not None and h[0] <= K]
        item = (rec, hits, non, nom, K)
        if K >= 3 and not hK:
            B.append(item)                 # n'=1..K が全部「どんな m でも当たらない」
        elif hits and (K >= 3 or max(n for n, _ in hits if n) >= NP):
            A.append(item)
        else:
            C.append(item)
        cn['hit'] += len(hits); cn['non'] += len(non); cn['nom'] += len(nom)
        cn['unkn'] += len(unkn); cn['unkm'] += len(unkm)

    print('(a) R 成立確認 %d   (b) R 破れ確認 %d   (c) 判定不能 %d'
          % (len(A), len(B), len(C)))
    print("n' 側 %d 個: 確定当たり %d / 確定外れ %d / 判定不能 %d"
          % (len(res) * NP, cn['hit'], cn['non'], cn['unkn']))
    print('m  側 %d 個: 確定外れ %d / 判定不能 %d'
          % (len(res) * MM, cn['nom'], cn['unkm']))
    print("シートに載っている n' の連続の頭 K の分布: %s"
          % sorted(kdist.items()))

    # (b) の外れの形: 末尾 1 列だけの差か
    st = collections.Counter()
    dv = collections.Counter()
    for rec, hits, non, nom, K in B:
        row, M, D, nside, mside = rec
        for n in range(1, K + 1):
            E = T[expand(M, n)][0]
            r = diffcols(D, E)
            if r is None:
                st['近い D<k> 無し'] += 1
                continue
            k, same, lf, le, d = r
            if d is not None:
                st['末尾 1 列だけ違う'] += 1
                dv[d] += 1
            elif lf != le:
                st['列数が違う (%+d)' % (le - lf)] += 1
            else:
                st['末尾 %d 列が違う' % (le - same)] += 1
    print()
    print('(b) の外れ %d 件の形: %s' % (sum(st.values()), dict(st)))
    print('末尾 1 列の差 (行0,行1,行2) の内訳: %s'
          % sorted(dv.items(), key=lambda t: -t[1]))

    B.sort(key=lambda t: (len(t[0][1]), t[0][0]))
    for rec, hits, non, nom, K in B[:nex]:
        row, M, D, nside, mside = rec
        print()
        print('=== シート行 %d  (K=%d) ===' % (row, K))
        print('M        = %s' % show(M))
        print('f(M)     = %s' % show(D))
        for m in (1, 2, 3):
            print('f(M)<%d>  = %s' % (m, show(expand(D, m))))
        for n in (1, 2, 3):
            print('M<%d>     = %s' % (n, show(expand(M, n))))
        for n in (1, 2, 3):
            Mn = expand(M, n)
            print('f(M<%d>)  = %s' % (n, show(T[Mn][0]) if Mn in T else '（シートに無い）'))
        print("確定外れ n' = %s   確定外れ m = %s   当たり = %s"
              % (non, nom, sorted(hits)))
        # f(M)<m> の逆像（シートに載っていれば）。M の基本列の項ではないことを見る。
        Tinv = {}
        for b, (d, r2) in T.items():
            Tinv.setdefault(d, (b, r2))
        for m in nom:
            Dm = expand(D, m)
            b, r2 = Tinv[Dm]
            print('   f^-1(f(M)<%d>) = 行%-5d %s' % (m, r2, show(b)))


if __name__ == '__main__':
    main()
