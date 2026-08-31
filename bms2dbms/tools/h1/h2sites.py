# -*- coding: utf-8 -*-
"""兄弟の付け場所（影の横 d か、本体の横 dd か）の教師つきデータ。

正例（dd = mode 2 が要る）: ImgClosedT の破れた (A,m) の証人 B = d2b3(T)
負例（d のまま）          : シート 1354 行（強制すると壊れるもの）
"""
import sys, pickle, itertools, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3sib, inv3, sheet3
from core import expand, isstd, show

rows3sib.SIBMODE[0] = 2


def sites_of(B):
    rows3sib.SIBREC[0] = True; del rows3sib.SIBSITES[:]
    rows3sib.SIBFORCE.clear()
    rows3sib.b2d3(list(B))
    rows3sib.SIBREC[0] = False
    out, seen = [], set()
    for s in rows3sib.SIBSITES:
        if s['off'] in seen: continue
        seen.add(s['off']); out.append(s)
    return out


def run(B, force):
    rows3sib.SIBFORCE.clear(); rows3sib.SIBFORCE.update(force)
    try:
        q = tuple(rows3sib.b2d3(list(B)))
    except Exception:
        q = None
    rows3sib.SIBFORCE.clear()
    return q


def label_one(B, T, maxsub=3):
    """B の兄弟 site のうち、どれを dd にすると T に一致するか。
    返り値 (一致した force の集合 or None, site の一覧)"""
    S = [s['off'] for s in sites_of(B)]
    if run(B, ()) == T:
        return frozenset(), S          # そのままで一致（全 site が負例）
    for r in range(1, min(len(S), maxsub) + 1):
        for c in itertools.combinations(S, r):
            if run(B, c) == T:
                return frozenset(c), S
    return None, S


def collect_pos(lim=6, mmax=3, verbose=1):
    F = pickle.load(open('/tmp/h1work/fail%d_%d.pkl' % (lim, mmax), 'rb'))
    rows, c = [], Counter()
    for M in F:
        fM = tuple(map(tuple, rows3.b2d3(list(M))))
        for m in range(1, mmax + 1):
            T = tuple(expand(fM, m))
            try:
                B = inv3.d2b3(T)
            except Exception:
                B = None
            if not B or not isstd(B, 'BMS') or any(c2[2] > 1 for c2 in B):
                c['B なし/非標準'] += 1; continue
            Bt = tuple(map(tuple, B))
            if tuple(rows3.b2d3(list(B))) == T:
                c['もともと一致'] += 1; continue
            f, S = label_one(list(B), T)
            if f is None:
                c['直せない'] += 1
                rows.append(dict(kind='unsolved', A=tuple(map(tuple,M)), m=m, B=Bt, T=T, sites=S))
            else:
                c['直った（force %d 本）' % len(f)] += 1
                rows.append(dict(kind='solved', A=tuple(map(tuple,M)), m=m, B=Bt, T=T,
                                 sites=S, force=sorted(f)))
    if verbose:
        for k in sorted(c): print('   %-24s %d' % (k, c[k]))
    return rows


def collect_neg(zcap=1, verbose=1):
    """シート 1354 行: 各 site を 1 つずつ dd にして、像が壊れるか。"""
    T = sheet3.load(zcap)
    rows, c = [], Counter()
    for row, b, d in T:
        d = tuple(map(tuple, d))
        if tuple(rows3.b2d3(list(b))) != d:
            continue
        Bt = tuple(map(tuple, b))
        for s in sites_of(list(b)):
            q = run(list(b), (s['off'],))
            broke = (q != d)
            c['壊れる' if broke else '変わらない'] += 1
            rows.append(dict(kind='sheet', row=row, B=Bt, off=s['off'],
                             site=s, broke=broke))
    if verbose:
        for k in sorted(c): print('   %-24s %d' % (k, c[k]))
    return rows


if __name__ == '__main__':
    t0=time.time()
    print('=== 正例（破れた対の証人）')
    P = collect_pos()
    print('=== 負例（シート）')
    N = collect_neg()
    pickle.dump((P, N), open('/tmp/h1work/sib_data.pkl','wb'))
    print('%.0fs  正例 %d 行 / 負例 %d 行' % (time.time()-t0, len(P), len(N)))
