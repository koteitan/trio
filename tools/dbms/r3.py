"""課題 R3 の前段: L16 が待っている 3 件を `<=8` 列 ＋ 展開閉包で測り直す。

  (i)   節 12'（チームリード版）  ∀ k < p.1, st.dmap[k] <= d
  (ii)  Dm12（L2 版, 保存）       ∀ k < M.head.1, dmap の項が変わらない
  (iii) BlkOK_app の側条件 6 本   a1 a3 a4 a5 b1 b2

`rows3.py` は触らない。呼び出し点は**呼び出し元フレームの行番号**で見分ける
（`sys._getframe(1).f_lineno`）ので、`conv3` の中を書き換えずに済む。
"""
import sys, os, time, pickle, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from rows3 import gen3, key
from core import expand, isstd

_conv3 = rows3.conv3

# ---- 呼び出し点の行番号 -> 名前（rows3.py の本文から拾う。行がずれても追随する）
SRC = open(rows3.__file__).read().split('\n')
SITE = {}
for _i, _l in enumerate(SRC, 1):
    t = _l.strip()
    if t.startswith('cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False'):
        SITE[_i] = 'cA_contr'
    elif t.startswith('cU = conv3(U, d + 1'):
        SITE[_i] = 'cU_contr'
    elif t.startswith('cB = conv3(Bq, d,'):
        SITE[_i] = 'cB_contr'
    elif t.startswith('cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0'):
        SITE[_i] = 'cA_plain'
    elif t.startswith('cB = conv3(B, d, LS'):
        SITE[_i] = 'cB_plain'
    elif t.startswith('out += conv3(head, rd'):
        SITE[_i] = 'cR_tree'
    elif t.startswith('cR = conv_resid('):
        SITE[_i] = 'cR_call'
assert len(set(SITE.values())) == 7, SITE

C = {}
EX = {}
CUR = [None]


def bump(k, n=1):
    C[k] = C.get(k, 0) + n


def ex(k, item, lim=5):
    L = EX.setdefault(k, [])
    if len(L) < lim:
        L.append(item)


def conv3_probe(*a, **kw):
    fr = sys._getframe(1)
    site = SITE.get(fr.f_lineno) if fr.f_code.co_name in ('conv3', 'conv_resid') else None
    M = a[0] if a else kw.get('M')
    d = a[1] if len(a) > 1 else kw.get('d', 0)
    st = a[8] if len(a) > 8 else kw.get('st')
    dm0 = list(st['dmap']) if st is not None else None

    # ---- (i) 節 12': ∀ k < p.1, st.dmap[k] <= d  （入口、p = M[0]）
    if M and st is not None:
        m = M[0][0]
        bump('n12p_calls')
        for k in range(min(m, len(dm0))):
            if not (dm0[k] <= d):
                bump('n12p_viol_d')
                ex('N12P', (CUR[0], tuple(M[0]), k, dm0, d), lim=40)
            if not (dm0[k] <= d - 1):
                bump('n12p_viol_dm1')       # 陽性対照（1 きつく）
            if not (dm0[k] <= d + 1):
                bump('n12p_viol_dp1')       # **これが 0 なら 修正版が真**
                ex('N12P1', (CUR[0], tuple(M[0]), k, dm0, d), lim=20)
            if not (dm0[k] <= d + 2):
                bump('n12p_viol_dp2')
            if dm0[k] == d + 1:
                bump('n12p_eq_dp1')         # タイトさ

    # ---- (iii) 側条件（呼び出し点ごと）
    if site and fr.f_code.co_name == 'conv3':
        L = fr.f_locals
        p = L.get('p'); pd = L.get('d')
        hd_ = (M[0][0] if M else None)
        if p is not None and hd_ is not None:
            if site in ('cA_contr', 'cA_plain'):
                if not (hd_ <= p[0] + 1):
                    bump('sc_%s_viol' % site)
                if not (hd_ <= p[0]):
                    bump('sc_%s_pc' % site)
            elif site == 'cU_contr':
                if not (hd_ <= p[0] + 1):
                    bump('sc_cU_viol')
                if not (hd_ <= p[0] - 1):
                    bump('sc_cU_pc')
            elif site in ('cB_contr', 'cB_plain'):
                if not (hd_ <= p[0]):
                    bump('sc_%s_viol' % site)
                if not (hd_ <= p[0] - 1):
                    bump('sc_%s_pc' % site)
    r = _conv3(*a, **kw)

    # ---- (ii) Dm12（保存）: ∀ k < M.head.1 で dmap の項が変わらない
    if M and st is not None:
        m = M[0][0]
        dm1 = st['dmap']
        for k in range(min(m, len(dm1))):
            if k < len(dm0) and dm1[k] != dm0[k]:
                bump('dm12w_viol')       # 弱い版（古い項があるときだけ等号）
                ex('DM12W', (CUR[0], tuple(M[0]), k, dm0, list(dm1), site))
            if not (k < len(dm0) and dm1[k] == dm0[k]):
                bump('dm12_viol')
                bump('dm12_viol_at_%s' % (site or 'top'))
                ex('DM12', (CUR[0], tuple(M[0]), k, dm0, list(dm1), site),
                   lim=20)
        for k in range(min(m + 1, len(dm1))):      # 陽性対照: 添字を 1 つ広げる
            if not (k < len(dm0) and dm1[k] == dm0[k]):
                bump('dm12_pc')
        if site in ('cB_contr', 'cB_plain'):       # L2 の rB 版（m = B.head.1）
            for k in range(min(m, len(dm1))):
                if not (k < len(dm0) and dm1[k] == dm0[k]):
                    bump('dm12_rB_viol')
            for k in range(min(m + 1, len(dm1))):
                if not (k < len(dm0) and dm1[k] == dm0[k]):
                    bump('dm12_rB_pc')
        if site in ('cA_contr', 'cA_plain'):       # L2 の rA 版（m = p.1+1）
            p = fr.f_locals.get('p')
            if p is not None:
                for k in range(min(p[0] + 1, len(dm1))):
                    if not (k < len(dm0) and dm1[k] == dm0[k]):
                        bump('dm12_rA_viol')
                for k in range(min(p[0] + 2, len(dm1))):
                    if not (k < len(dm0) and dm1[k] == dm0[k]):
                        bump('dm12_rA_pc')
    return r


_conv_resid = rows3.conv_resid


def conv_resid_probe(rest, rd, Lr, ps, pw, st, nx, off):
    # ---- (iii) a4: d + rest2.head.1 <= rd + p.1
    L = sys._getframe(1).f_locals
    p = L.get('p'); d = L.get('d')
    if rest and p is not None and d is not None:
        bump('sc_a4_calls')
        if not (d + rest[0][0] <= rd + p[0]):
            bump('sc_a4_viol'); ex('A4', (CUR[0], tuple(p), tuple(rest[0]), rd, d))
        if not (d + rest[0][0] <= rd + p[0] - 1):
            bump('sc_a4_pc')            # 1 段きつく
        if d + rest[0][0] == rd + p[0]:
            bump('sc_a4_eq')            # 等号（タイトさの目安）
    return _conv_resid(rest, rd, Lr, ps, pw, st, nx, off)


rows3.conv3 = conv3_probe
rows3.conv_resid = conv_resid_probe


def run1(M):
    CUR[0] = tuple(M)
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    return rows3.conv3(list(M), st=st)


def run(pop, name):
    t0 = time.time()
    for M in pop:
        run1(M)
    print('== %s  母数 %d  %.1fs' % (name, len(pop), time.time() - t0))
    for k in sorted(C):
        print('   %-20s %d' % (k, C[k]))
    for k in sorted(EX):
        print('   ### %s:' % k)
        for x in EX[k][:3]:
            print('      ', x)
    return dict(C)


def pop_exp(lim=6, ns=(1, 2, 3), rounds=2, maxlen=24):
    base = set(tuple(M) for M in gen3('BMS', lim, zcap=1))
    seen = set(base); cur = set(base)
    for _ in range(rounds):
        nxt = set()
        for M in cur:
            for n in ns:
                E = expand(M, n)
                if E and len(E) <= maxlen and E not in seen and isstd(E, 'BMS'):
                    seen.add(E); nxt.add(E)
        cur = nxt
    return sorted(seen - base, key=key)


if __name__ == '__main__':
    w = sys.argv[1] if len(sys.argv) > 1 else '7'
    if w == 'exp':
        P = pop_exp(6); nm = '<=6 の展開閉包'
    else:
        P = [tuple(M) for M in sorted(gen3('BMS', int(w), zcap=1), key=key)]
        nm = 'gen3 <=%s' % w
    run(P, nm)
    pickle.dump({'c': dict(C), 'e': EX, 'n': len(P)},
                open('/home/koteitan/proofs/dbms/tools/dbms/r3_%s.pkl' % w, 'wb'))
