"""シート外で標準形にならない行列を集め、どの列の深さを変えれば直るかを調べる。

シートを使わない判定（DBMS 標準形か／1 列短い行列の像より大きいか）を神託にして、
「本当はこうあるべき深さ」を総当たりで求め、いまの規則との差を特徴で見る。
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import isstd, show, cmpmat
import rule as R
import verify_gen as VG


def wrong_sites(m, Y=3, maxflip=3):
    """m の出力が標準形でないとき、直すのに要る深さの反転を返す。"""
    ds = R.depths(m)
    Z = R.dedup(R._stair(m, Y, lambda x, c: ds[x]))
    if isstd(Z, 'DBMS'):
        return 'ok'  
    lo = None
    if len(m) > 1 and isstd(m[:-1], 'BMS'):
        try:
            lo = R.convert(m[:-1], Y)
        except Exception:
            lo = None
    br = [x for x, c in enumerate(m) if R.is_branching(c)]
    import itertools
    for relay in (True, False):
        for k in range(0, maxflip + 1):
            for f in itertools.combinations(br, k):
                e = list(ds)
                for i in f:
                    e[i] ^= 1
                try:
                    W = R.dedup(R._stair(m, Y, lambda x, c, e=e: e[x], relay=relay))
                except Exception:
                    continue
                if isstd(W, 'DBMS') and (lo is None or cmpmat(lo, W) < 0):
                    return (f, e, W, relay)
    return None


if __name__ == '__main__':
    ms = VG.gen(VG.seeds())
    bad = [m for m in ms if not isstd(R.convert(m, 3), 'DBMS')]
    print('標準形にならない行列 %d 個' % len(bad))
    cnt = collections.Counter()
    ex = []
    for m in bad:
        w = wrong_sites(m)
        if w is None:
            cnt['深さの反転では直らない'] += 1
            continue
        if w == 'ok':
            cnt['もともと標準形'] += 1
            continue
        f, e, W, relay = w
        cnt['反転 %d 箇所 relay=%s' % (len(f), relay)] += 1
        for i in f:
            c = m[i]
            nxt = m[i + 1] if i + 1 < len(m) else None
            pv = m[i - 1] if i > 0 else None
            key = ('c=%s' % (c,), 'nxt=%s' % (nxt,), 'pv=%s' % (pv,),
                   'hi=%s' % R.hi_block(m, i), '正=%d' % e[i])
            ex.append((len(m), i, key))
    print(dict(cnt))
    g = collections.Counter(k for _, _, k in ex)
    print('要る反転の文脈（多い順）:')
    for k, v in g.most_common(12):
        print('  %-70s %d' % (' '.join(k), v))
