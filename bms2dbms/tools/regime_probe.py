"""「(a,1,1) で段の regime が開き直る」形の分離条件を探す。

結論（2026-08-23）: 分離条件は**見つからなかった**。
シートだけを負例にすると `regime_reopened`（直前のアンカー以降に (a,1,1) がある）が
54/54 を覆い負例 296 を 1 つも巻き込まないが、シート外の負例 1876 個まで広げると
覆える条件が消える。実際この規則を入れるとシートは 1621/1621 のままだが、
生成 40033 個で非標準形が 79 -> 1045、衝突が 0 -> 360 に増える。

あわせて fix_search.py の結果: 標準形にならない 79 個のうち 61 個は
**深さをどう振っても（3 箇所まで反転・敷き直し on/off）直らない**。
つまり残りの穴は深さ規則ではなく、階段か敷き直しの側にある。

シート外で標準形にならない行列のうち、深さの反転で直るものの地点（＝深くすべき）と、
シートで prev==0 により浅いと決めている地点（＝浅くて正しい）を並べ、
両者を分ける条件を総当たりで探す。
"""
import sys, os, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import isstd, show, cmpmat, pim
import rule as R
import verify_gen as VG
from check_sheet import load
from fix_search import wrong_sites


def feats(m, x):
    c = m[x]
    nxt = m[x + 1] if x + 1 < len(m) else None
    pv = m[x - 1] if x > 0 else None
    P = pim(m)
    # 直前のアンカー (1,1,0) 以降に regime を開く列 (a,1,1) があるか
    b = max([q for q in range(x) if R.is_anchor1(m[q])], default=0)
    opener = [q for q in range(b, x)
              if len(m[q]) > 2 and m[q][2] >= 1 and m[q][1] <= m[q][2]]
    op = opener[-1] if opener else None
    return {
        'regime_open': op is not None,
        'op_gap': (x - op) if op is not None else -1,
        'op_row0': m[op][0] if op is not None else -1,
        'nxt_rel': ('なし' if nxt is None else
                    '+1' if nxt[0] == c[0] + 1 else
                    '同' if nxt[0] == c[0] else
                    '戻り' if nxt[0] < c[0] else '飛び'),
        'nxt_lv': -1 if nxt is None else nxt[1] + (10 if len(nxt) > 2 and nxt[2] else 0),
        'pv_is_opener': pv is not None and len(pv) > 2 and pv[2] >= 1 and pv[1] <= pv[2],
        'hi': R.hi_block(m, x),
        'p1_root': P[x][1] == 0,
        'p1_is_op': op is not None and P[x][1] == op,
        'c0_gt_op': op is not None and c[0] > m[op][0],
    }


def collect_deep():
    """深くすべき地点（シート外・標準形にならない行列から）"""
    ms = VG.gen(VG.seeds())
    bad = [m for m in ms if not isstd(R.convert(m, 3), 'DBMS')]
    out = []
    for m in bad:
        w = wrong_sites(m)
        if w in (None, 'ok'):
            continue
        f, e, W, relay = w
        for i in f:
            if e[i] == 1:
                out.append((m, i, feats(m, i)))
    return out


def collect_shallow(gen=True, limit=4000):
    """浅くて正しい地点。

    シートは真値と一致する行から、シート外は出力が DBMS 標準形になる行列から、
    prev==0 で浅いと決めている地点を集める。
    """
    out = []
    src = []
    for r, mb, md, Y in load():
        if mb:
            src.append((mb, Y, md))
    if gen:
        for m in VG.gen(VG.seeds())[:limit]:
            if m:
                src.append((m, 3, None))
    for mb, Y, md in src:
        ds = R.depths(mb)
        Z = R.dedup(R._stair(mb, Y, lambda x, c: ds[x]))
        if md is not None:
            if Z != md:
                continue
        elif not isstd(Z, 'DBMS'):
            continue
        prev = [None]
        for x, c in enumerate(mb):
            if R.is_anchor1(c):
                prev[0] = 0
            if not R.is_branching(c):
                continue
            if prev[0] == 0 and ds[x] == 0:
                out.append((mb, x, feats(mb, x)))
            prev[0] = ds[x]
    return out


if __name__ == '__main__':
    D = collect_deep()
    S = collect_shallow()
    print('深くすべき地点 %d、浅くて正しい地点 %d' % (len(D), len(S)))
    keys = list(D[0][2]) if D else []
    atoms = []
    for k in keys:
        for v in sorted({d[2][k] for d in D} | {s[2][k] for s in S}, key=str):
            atoms.append((k, v))
    best = []
    for L in (1, 2, 3):
        for cond in itertools.combinations(atoms, L):
            if len({k for k, v in cond}) != L:
                continue
            nd = sum(1 for _, _, f in D if all(f[k] == v for k, v in cond))
            ns = sum(1 for _, _, f in S if all(f[k] == v for k, v in cond))
            if ns == 0 and nd > 0:
                best.append((nd, cond))
        if best:
            break
    best.sort(reverse=True)
    print('浅い側を 1 つも巻き込まずに深い側を覆う条件（上位）:')
    for n, cond in best[:10]:
        print('  %-58s %d/%d' % (' かつ '.join('%s=%s' % kv for kv in cond), n, len(D)))
    if not best:
        print('  （見つからず）')
