"""課題 R2: 森の枝の中身を木ごとに測る。`rows3.py` は触らない（monkeypatch）。

`conv_resid` の while ループが 1 本の木ごとに呼ぶ `conv3(head, rd, ...)` を、
**呼び出し元のフレームが `conv_resid` かどうか**で見分けて記録する。
ループの再実装はしない（＝像は 1 ビットも変わらない）。
"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from rows3 import gen3, key
from core import expand, isstd

_conv3 = rows3.conv3
_conv_resid = rows3.conv_resid

C = {}
FOREST = []          # 森になった発火の記録
CUR = [None]
TREES = [None]       # いま記録中の木のリスト


def bump(k, n=1):
    C[k] = C.get(k, 0) + n


def conv3_probe(*a, **kw):
    fr = sys._getframe(1)
    from_resid = (fr.f_code.co_name == 'conv_resid')
    M = a[0] if a else kw.get('M')
    d = a[1] if len(a) > 1 else kw.get('d', 0)
    out = _conv3(*a, **kw)
    if from_resid and TREES[0] is not None:
        TREES[0].append({
            'm0': (M[0][0] if M else None),      # この木の**もとの**開始深さ
            'rd': d,                             # この木の**像の**開始深さ
            'n': len(M),
            'omin': (min(c[0] for c in out) if out else None),
            'omax': (max(c[0] for c in out) if out else None),
            'out': tuple(tuple(c) for c in out),
        })
    return out


def conv_resid_probe(rest, rd, Lr, ps, pw, st, nx, off):
    prev = TREES[0]
    TREES[0] = []
    outer_d = sys._getframe(1).f_locals.get('d')
    p = sys._getframe(1).f_locals.get('p')
    out = _conv_resid(rest, rd, Lr, ps, pw, st, nx, off)
    trees = TREES[0]
    TREES[0] = prev
    bump('fires')
    bump('trees', len(trees))
    if len(trees) >= 2:
        bump('forest')
        bump('forest_%d_trees' % len(trees))
        if len(FOREST) < 500:
                FOREST.append({'M': CUR[0], 'rest': tuple(tuple(c) for c in rest),
                           'rd0': rd, 'd': outer_d,
                           'p': (tuple(p) if p else None),
                           'off': off, 'trees': trees,
                           'out': tuple(tuple(c) for c in out)})
    # 主張の検定
    for t in trees:
        if t['omin'] is not None and t['omin'] < t['rd']:
            bump('T1_viol')          # (T1) 木ごとに rd 以上
        if t['omin'] is not None and t['omin'] < t['rd'] + 1:
            bump('T1_pc_viol')       # 陽性対照（わざと 1 きつく）
    for i in range(len(trees) - 1):
        if not (trees[i + 1]['rd'] < trees[i]['rd']):
            bump('T2_viol')          # (T2) rd は真に下がる
        if not (trees[i + 1]['rd'] <= trees[i]['rd']):
            bump('T2w_viol')         # (T2 弱) 下がるか同じ
        if not (trees[i + 1]['m0'] < trees[i]['m0']):
            bump('T2m_viol')         # もとの深さも真に下がる
        # 切り詰め: rd_{k+1} == rd_k - (m0_k - m0_{k+1}) がそのまま成り立つか
        if trees[i + 1]['rd'] != trees[i]['rd'] - (trees[i]['m0'] - trees[i + 1]['m0']):
            bump('CLAMP')
    if trees:
        if trees[-1]['rd'] < 0:
            bump('rd_neg')
        if outer_d is not None:
            if min(t['rd'] for t in trees) < outer_d:
                bump('T3_viol')      # (T3) どの木の rd も外側の d 以上
            if min(t['rd'] for t in trees) < outer_d + 1:
                bump('T3_pc_viol')
        if trees[-1]['rd'] == 0:
            bump('rd_zero')
        # 側条件 H: ∀ c ∈ rest, d + rest[0].1 <= rd0 + c.1
        if outer_d is not None and rest:
            if any(outer_d + rest[0][0] > rd + c[0] for c in rest):
                bump('H_viol')
            if any(outer_d + 1 + rest[0][0] > rd + c[0] for c in rest):
                bump('H_pc_viol')
    return out


rows3.conv3 = conv3_probe
rows3.conv_resid = conv_resid_probe


def run1(M):
    CUR[0] = tuple(M)
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    return rows3.conv3(list(M), st=st)


def run(pop, name, show=0):
    t0 = time.time()
    for M in pop:
        run1(M)
    print('== %s  母数 %d  %.1fs' % (name, len(pop), time.time() - t0))
    for k in sorted(C):
        print('   %-20s %d' % (k, C[k]))
    return dict(C)


def table():
    """森になった発火を表にする。"""
    print()
    print('| # | 行列 | d | rest | 木ごとの (m0, rd, 出した柱の最小深さ) |')
    print('|--:|---|--:|---|---|')
    for i, f in enumerate(FOREST):
        ms = ''.join(str(c).replace(' ', '') for c in f['M'])
        rs = ''.join(str(c).replace(' ', '') for c in f['rest'])
        ts = ' '.join('(%d,%d,%s)' % (t['m0'], t['rd'], t['omin'])
                      for t in f['trees'])
        print('| %d | `%s` | %d | `%s` | %s |' % (i + 1, ms, f['d'], rs, ts))


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else '8'
    P = [tuple(M) for M in sorted(gen3('BMS', int(what), zcap=1), key=key)]
    run(P, 'gen3 <=%s' % what)
    table()
    with open('/home/koteitan/proofs/dbms/tools/dbms/r2_%s.pkl' % what,
              'wb') as f:
        pickle.dump({'c': dict(C), 'forest': FOREST, 'n': len(P)}, f)
