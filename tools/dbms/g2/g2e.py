"""G2 段 5: 逆写像 d2b3 が出す候補 B と目標 T の**最初の食い違い**を指紋にする。

`maxpre`（段 2）は「T のどこから先が像で有り得ないか」を言うが、直す側から見て
効くのは「素直な候補 B に conv3 をかけたとき、どの柱が、どちらの向きに、
どの条項でずれるか」である。ここはぜんぶ安い（DFS を使わない）。
"""
import sys, collections, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, inv3
from core import show, isstd, parse
from rows3 import key
from g2a import ctype, tail2

SC = '/home/koteitan/proofs/dbms/tools/dbms/g2/'


def pstr(p):
    return (p[0] + ('' if p[2] is None else ':' + p[2])
            + ('' if not p[3] else '@' + '/'.join(p[3])))


def diag(A, m, T):
    """候補 B = d2b3(T) を作って conv3 B と T をくらべる。"""
    o = dict(A=A, m=m, T=T)
    try:
        B = tuple(map(tuple, inv3.d2b3(list(T))))
    except Exception:
        B = None
    if not B:
        o['cls'] = 'd2b3 が返さない'
        return o
    o['B'] = B
    if not (isstd(B, 'BMS') and all(c[2] <= 1 for c in B)):
        o['cls'] = 'B が BMS 標準形でない'
        return o
    Q, PR = provc.b2d3p(list(B))
    o['Q'] = Q
    i = 0
    while i < min(len(Q), len(T)) and Q[i] == T[i]:
        i += 1
    o['i'] = i
    if i == len(Q) == len(T):
        o['cls'] = '一致（破れでない）'
        return o
    if i >= len(Q) or i >= len(T):
        o['cls'] = '長さだけ違う %+d' % (len(Q) - len(T))
        return o
    q, t = Q[i], T[i]
    o['qc'], o['tc'] = q, t
    o['prov'] = PR[i]
    o['bcol'] = B[PR[i][1]]
    d = tuple(x - y for x, y in zip(q, t))
    o['delta'] = d
    o['cls'] = ('conv3 が深い' if d[1] > 0 else
                ('conv3 が浅い' if d[1] < 0 else
                 ('行 0 が違う' if d[0] != 0 else '行 2 が違う')))
    return o


def run(pkl=SC + 'bad6.pkl'):
    bad = pickle.load(open(pkl, 'rb'))
    byA = collections.defaultdict(list)
    for A, m, T in bad:
        byA[tuple(A)].append((m, tuple(map(tuple, T))))
    out = {}
    for A in sorted(byA, key=key):
        m, T = sorted(byA[A])[0]
        out[A] = diag(A, m, T)
    C = collections.Counter(o['cls'] for o in out.values())
    print('=== 候補 B = d2b3(T) に conv3 をかけたときの最初の食い違い ===')
    for k, v in C.most_common():
        print('  %-24s %3d' % (k, v))
    print('\n-- ずれの中身（型 / ずれ / それを出した分岐 / もとの BMS 柱） --')
    D = collections.Counter()
    for A, o in out.items():
        if 'delta' not in o:
            D[(o['cls'], '-', '-', '-')] += 1
        else:
            D[(o['cls'], str(o['delta']), pstr(o['prov']),
               ctype(o['bcol']))] += 1
    for k, v in D.most_common():
        print('%3d  %-14s ずれ %-11s %-20s もとの柱 %s'
              % (v, k[0], k[1], k[2], k[3]))
    print('\n-- 族（末尾 2 柱 x 食い違いの型） --')
    E = collections.Counter((tail2(A), out[A]['cls'],
                             pstr(out[A]['prov']) if 'prov' in out[A] else '-')
                            for A in out)
    for k, v in E.most_common():
        print('%3d  %-12s %-16s %s' % (v, k[0], k[1], k[2]))
    pickle.dump(out, open(SC + 'diag6.pkl', 'wb'))
    return out


if __name__ == '__main__':
    run()
