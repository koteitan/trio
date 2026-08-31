"""課題 R1: `ResidBlkT`（残余は単一の木）と `DmapInT`（dmapAt の範囲内の枝）の全数測定。

`rows3.py` は**触らない**。`rows3.conv3` / `rows3.conv_resid` / `rows3.dmap_at` を
モジュール属性の差し替え（monkeypatch）で包むだけ。conv3 の再帰も、縮約の枝の
`conv_resid(...)` / `dmap_at(...)` も**全部モジュール大域の引き当て**なので、
差し替えれば漏れなく捕まる。像は 1 ビットも変えない（包むだけ）。
"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from rows3 import gen3, key
from core import expand, isstd

_conv3 = rows3.conv3
_conv_resid = rows3.conv_resid
_dmap_at = rows3.dmap_at

C = {}          # カウンタ
EX = {}         # 例（種類ごとに先頭 5 個）
CUR = [None]    # いま走らせている行列


def bump(k, n=1):
    C[k] = C.get(k, 0) + n


def ex(k, item, lim=5):
    L = EX.setdefault(k, [])
    if len(L) < lim:
        L.append(item)


# ---------------------------------------------------------------- (1) 残余
def conv_resid_probe(rest, rd, Lr, ps, pw, st, nx, off):
    bump('resid_calls')
    fr = sys._getframe(1).f_locals
    pp = fr.get('p')
    blk = fr.get('blk'); pre = fr.get('pre')
    if blk and pre:
        dmn = len(st['dmap'])
        if dmn == blk[-1][0] + 1:
            bump('dm_eq_blklast')
        else:
            bump('dm_ne_blklast')
            ex('DMNE', (CUR[0], dmn, tuple(blk), tuple(pre),
                        list(st['dmap'])), lim=20)
        if rest and not (rest[0][0] <= pre[-1][0] + 1):
            bump('head_gt_prelast1')
    if rest and pp is not None:
        if rest[0][0] == pp[0] + 1:
            bump('resid_head_p1')
        else:
            bump('resid_head_deep')
            ex('DEEPHEAD', (CUR[0], tuple(rest), pp, fr.get('off')), lim=20)
    if not rest:
        bump('resid_empty')
    else:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        if i < len(rest):
            bump('resid_FOREST')
            ex('FOREST', (CUR[0], tuple(rest), rd, off), lim=60)
        else:
            bump('resid_tree')
        # 森の枝の rd の推移を追う（clamp するか / d を下回るか）
        rr, mm, rest_, ntree, clamp = rd, m0, list(rest), 0, False
        rmin = rd
        while rest_:
            m1 = rest_[0][0]
            j = 1
            while j < len(rest_) and rest_[j][0] >= m1:
                j += 1
            ntree += 1
            rmin = min(rmin, rr)
            if j >= len(rest_):
                break
            nr = rr - (m1 - rest_[j][0])
            if nr < 0:
                clamp = True
            rr = max(0, nr)
            rest_ = rest_[j:]
        bump('resid_trees', ntree)
        if clamp:
            bump('resid_rd_clamped')
        dd_ = sys._getframe(1).f_locals.get('d')
        if dd_ is not None and rmin < dd_:
            bump('resid_rdmin_lt_d')
            ex('RDMIN', (CUR[0], tuple(rest), rd, rmin, dd_), lim=20)
        # 陽性対照: わざと外した主張「先頭より真に深い柱しかない」
        if any(c[0] <= m0 for c in rest[1:]):
            bump('pc_strict_viol')
    ST0 = len(st['ST']); dm0 = list(st['dmap'])
    out = _conv_resid(rest, rd, Lr, ps, pw, st, nx, off)
    ST1 = len(st['ST']); dm1 = list(st['dmap'])
    # BlkOK の 8 節を、開始深さ `dd_`（外側の conv3 の d）と `rd` の両方で判定
    dO = sys._getframe(1).f_locals.get('d')
    for tag, dv in (('D', dO), ('RD', rd)):
        if dv is None:
            continue
        v = []
        if any(out[i + 1][0] > out[i][0] + 1 for i in range(len(out) - 1)):
            v.append(1)
        if not (dv <= ST1):
            v.append(2)
        if not out and ST1 != ST0:
            v.append(3)
        if out and not (out[0][0] <= ST0):
            v.append(4)
        if out and not (out[-1][0] + 1 == ST1):
            v.append(5)
        if any(c[0] < dv for c in out):
            v.append(6)
        if dm0 and not dm1:
            v.append(7)
        if dm1 and not (dm1[-1] + 1 == ST1):
            v.append(8)
        for j in v:
            bump('blkok_%s_c%d' % (tag, j))
        if v:
            bump('blkok_%s_ANY' % tag)
            ex('BLK' + tag, (CUR[0], tuple(rest), rd, dv, tuple(out), v), lim=20)
    dd_ = sys._getframe(1).f_locals.get('d')
    if dd_ is not None and any(c[0] < dd_ for c in out):
        bump('cR_depth_lt_d')
        ex('CRD', (CUR[0], tuple(rest), rd, dd_, tuple(out)), lim=20)
    if out and any(c[0] < out[0][0] for c in out):
        bump('cR_not_block')
    return out


# ---------------------------------------------------------------- (2) dmap
def dmap_at_probe(st, k):
    f = sys._getframe(1).f_locals
    d = f.get('d')
    p = f.get('p')
    rest2 = f.get('rest2')
    dm = st['dmap']
    ST = st['ST']
    bump('dmapat_calls')
    r = _dmap_at(st, k)
    if any(x > len(ST) for x in dm):
        bump('AT_inv_le_viol')
    if k < len(dm):
        bump('dmapat_IN')
        if k == len(dm) - 1:
            bump('dmapat_IN_klast')
        else:
            bump('dmapat_IN_kmid')
            ex('KMID', dict(M=CUR[0], d=d, k=k, dmap=list(dm),
                            ST=list(ST), val=r), lim=20)
        if not (d + 2 <= len(ST)):
            bump('dmapat_IN_d2_viol')
        pd = f.get('p')
        if pd is not None:
            for j in range(pd[0] + 1, len(dm)):
                if not (d <= dm[j]):
                    bump('dmapat_pdeep_viol')
            if not (d <= dm[k]):
                bump('dmapat_IN_dlow_viol')
        okd = (d is not None and d <= r)
        oks = (r <= len(ST))
        if not okd:
            bump('dmapat_IN_d_viol')
        if not oks:
            bump('dmapat_IN_ST_viol')
        ex('DMAPIN', dict(M=CUR[0], d=d, k=k, dmap=list(dm), ST=list(ST),
                          val=r, p=p, rest2=(tuple(rest2) if rest2 else ()),
                          off=f.get('off'), e=f.get('e')), lim=40)
    else:
        bump('dmapat_OUT')
        if k == len(dm):
            bump('dmapat_OUT_exact')
        if not (d is not None and d <= r):
            bump('dmapat_OUT_d_viol')
        if not (r <= len(ST)):
            bump('dmapat_OUT_ST_viol')
    return r


# ---------------------------------------------------------------- (3) 不変量
def _chk(st, d, tag):
    dm, ST = st['dmap'], st['ST']
    bump('conv3_' + tag)
    if dm:
        if not (dm[-1] + 1 == len(ST)):
            bump('inv_last_viol_' + tag)
        if any(x > len(ST) for x in dm):
            bump('inv_le_viol_' + tag)
            ex('INVLE_' + tag, (CUR[0], list(dm), len(ST)))
        if any(x >= len(ST) for x in dm):       # 陽性対照（わざと 1 きつく）
            bump('pc_lt_viol_' + tag)
        if any(x > len(ST) - 1 for x in dm[:-1]):
            bump('inv_le_m1_viol_' + tag)       # dmap[:-1] <= |ST|-1 か
    if d is not None and not (d <= len(ST)):
        bump('inv_d_le_ST_viol_' + tag)


def conv3_probe(*a, **kw):
    st = a[8] if len(a) > 8 else kw.get('st')
    d = a[1] if len(a) > 1 else kw.get('d', 0)
    M0 = a[0] if a else kw.get('M')
    if st is not None:
        _chk(st, d, 'in')
        pre_dm = list(st['dmap'])
    r = _conv3(*a, **kw)
    if st is not None:
        _chk(st, d, 'out')
        # 節 9 の候補: この呼び出しが**書いた** dmap の項は全部 d 以上
        dm = st['dmap']
        for kk in range(len(dm)):
            keep = kk < len(pre_dm) and dm[kk] == pre_dm[kk]
            if not (d <= dm[kk] or keep):
                bump('c9_viol')
                ex('C9', (CUR[0], d, kk, pre_dm, list(dm)))
            # 陽性対照: わざと 1 きつくした版（d+1 <= dmap[kk]）
            if not (d + 1 <= dm[kk] or keep):
                bump('c9_pc_viol')
        # 節 10 の候補: `m = M[0][0]` として `d + (j - m) <= dmap[j]` (j >= m)
        if M0:
            m = M0[0][0]
            for j in range(m, len(dm)):
                if not (d + (j - m) <= dm[j]):
                    bump('c10_viol')
                    ex('C10', (CUR[0], d, m, j, list(dm)))
                if not (d + 1 + (j - m) <= dm[j]):
                    bump('c10_pc_viol')
    return r


rows3.conv3 = conv3_probe
rows3.conv_resid = conv_resid_probe
rows3.dmap_at = dmap_at_probe


def run(pop, name):
    C.clear(); EX.clear()
    t0 = time.time()
    for M in pop:
        CUR[0] = tuple(M)
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
              'rec': {}}
        rows3.conv3(list(M), st=st)
    print('== %s  母数 %d  %.1fs' % (name, len(pop), time.time() - t0))
    for k in sorted(C):
        print('   %-28s %d' % (k, C[k]))
    return dict(C), {k: list(v) for k, v in EX.items()}


# ---------------------------------------------------------------- 母集団
def pop_gen(lim):
    return [tuple(M) for M in sorted(gen3('BMS', lim, zcap=1), key=key)]


def pop_exp(lim=6, ns=(1, 2, 3), rounds=2, maxlen=24):
    """<=lim 列の標準形を n∈ns で `rounds` 回展開した閉包（標準形のみ）。"""
    base = set(pop_gen(lim))
    seen = set(base)
    cur = set(base)
    for _ in range(rounds):
        nxt = set()
        for M in cur:
            for n in ns:
                E = expand(M, n)
                if E and len(E) <= maxlen and E not in seen and isstd(E, 'BMS'):
                    seen.add(E); nxt.add(E)
        cur = nxt
    out = [M for M in seen if M not in base]
    return sorted(out, key=key)


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else '6'
    if what == 'exp':
        P = pop_exp(int(sys.argv[2]) if len(sys.argv) > 2 else 6)
        nm = 'expansion closure of <=%s' % (sys.argv[2] if len(sys.argv) > 2 else 6)
    else:
        P = pop_gen(int(what))
        nm = 'gen3 <=%s' % what
    c, e = run(P, nm)
    with open('/home/koteitan/proofs/dbms/bms2dbms/tools/r1_%s.pkl' % what, 'wb') as f:
        pickle.dump({'c': c, 'e': e, 'n': len(P)}, f)
