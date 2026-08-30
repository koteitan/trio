"""接頭辞を固定した全数展開で `ResidBlkT` / `DmapInT` の反例を狩る。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r1, rows3
from core import isstd


def gen_ext(pref, lim, zcap=1):
    """`pref`（標準形）から始まる長さ <= lim の標準形を全部。"""
    assert isstd(pref, 'BMS')
    cur, out = [pref], []
    while cur:
        nxt = []
        for S in cur:
            if len(S) >= lim:
                continue
            amax = S[-1][0] + 1
            for a in range(amax + 1):
                for b in range(a + 1):
                    for c in range(min(b, zcap) + 1):
                        T = S + ((a, b, c),)
                        if isstd(T, 'BMS'):
                            nxt.append(T)
        out.extend(nxt)
        cur = nxt
    return out


if __name__ == '__main__':
    pref = tuple(eval(sys.argv[1]))
    lim = int(sys.argv[2])
    t = time.time()
    P = gen_ext(pref, lim)
    print('prefix', pref, '-> lim', lim, ':', len(P), '%.1fs' % (time.time() - t))
    c, e = r1.run(P, 'ext %s lim %d' % (str(pref), lim))
    for k in ('KMID', 'FOREST', 'RDMIN', 'CRD'):
        if e.get(k):
            print('### %s (%d 例まで)' % (k, len(e[k])))
            for x in e[k][:5]:
                print('   ', x)
