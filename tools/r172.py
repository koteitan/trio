# -*- coding: utf-8 -*-
"""(w1) の**対照**。r171 の 0% が本物か、コードのバグかを分ける。

- **陰性対照 A**: 同じコードで `(d,e)` を**毎段自由**に選ぶ ⟹ §R167 の「30 段続く」を
  再現するはず。**再現しなければ r171 のコードがバグ。**
- **診断**: `oper` が出す `(d', e')` の値の分布。0 に潰れていないか。
- **診断**: 1 段目で止まる 69% は何が起きているか。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det


def step_free(Q, d, e, n, j):
    """§R167 と同じ: `(d,e)` は呼び出し側が自由に決める。"""
    r = step_det(Q, d, e, n, j)
    return None if r is None else r[0]


def chain(Q0, d0, e0, cap, NS, free):
    cur, d, e = list(Q0), d0, e0
    seq = [len(cur)]; des = []
    for s in range(cap):
        nxt = None
        cands = [(dd, ee) for dd in range(4) for ee in range(4)] if free else [(d, e)]
        for (dd, ee) in cands:
            for n in NS:
                for j in range(len(cur)):
                    r = step_det(cur, dd, ee, n, j)
                    if r and len(r[0]) >= len(cur):
                        nxt = r; break
                if nxt: break
            if nxt: break
        if nxt is None:
            return s, seq, des
        cur, d, e = list(nxt[0]), nxt[1], nxt[2]
        des.append((nxt[1], nxt[2])); seq.append(len(cur))
    return cap, seq, des


def run(L, cap, nmax, free, tag):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in (0, 1)]
    c = Counter(); de = Counter(); t0 = time.time(); done = 0
    import random; random.seed(7)
    pool = []
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            pool.append([root] + list(t))
    random.shuffle(pool)
    for Q0 in pool:
        for d0 in range(4):
            for e0 in range(4):
                s, seq, des = chain(Q0, d0, e0, cap, (2, 3), free)
                c['本数'] += 1
                c[('止', min(s, 6))] += 1
                if s >= cap: c['★続いた'] += 1
                for x in des: de[x] += 1
                done += 1
                if done >= nmax: break
            if done >= nmax: break
        if done >= nmax: break
    tot = c['本数']
    print(f'### {tag} |Q0|={L} 鎖 {tot} 本 {cap} 段  [{time.time()-t0:.1f}s]')
    print(f'  **★ {cap} 段続いた … {c["★続いた"]} / {tot} ({100*c["★続いた"]/max(tot,1):6.2f}%)**')
    print('  止まった段: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print('  出てきた `(d\',e\')` 上位: ', de.most_common(8))
    print()


if __name__ == '__main__':
    for L in (3, 4, 5):
        run(L, 30, 600, True,  '陰性対照A `(d,e)` 毎段自由')
        run(L, 30, 600, False, '本命 `(d,e)` は `oper` 決め打ち')
