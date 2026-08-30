# -*- coding: utf-8 -*-
"""**(C4-W-b) / (C4-W) / (C4-RED)。**

## ⚠ 論理の向き（大事）

`Reach ⊆ W`（健全な下からの近似）なので:

    ★★★ **`Reach` の中に C4 を破る元が出れば ⟹ (C4-W) は偽と「確定」します**
    ⛔ 逆に `Reach` 全部が C4 を満たしても ⟹ **(C4-W) の証明にはなりません**（肯定的証拠のみ）
    ⚠ そして「反例が `Reach` に入らない」も ⟹ **`∉ W` の証明にはなりません**（未確定）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import expand, diag
from collections import Counter
from r126 import srow
from r257 import C4
from r248 import hlocQ
from r259 import shift0

CE = {
    'L3 §250 Bce': ((0,0,0), (1,5,0), (2,1,0), (2,9,0)),
    'L3 §248 B':   ((0,0,0), (1,2,0), (2,1,0), (3,9,0)),
    'H12 (NZ2) Q': ((0,1,0), (1,5,0), (2,3,0)),
}


def reach(vs, ns, depth):
    seen = set(); frontier = [tuple(map(tuple, diag(3, v, 1))) for v in vs]
    for _ in range(depth):
        nxt = []
        for S in frontier:
            if S in seen: continue
            seen.add(S)
            for n in ns:
                T = tuple(map(tuple, expand([list(x) for x in S], n)))
                if T not in seen: nxt.append(T)
        frontier = nxt
    seen.update(frontier)
    out = set()
    for S in seen:
        for k in range(1, len(S) + 1): out.add(S[:k])
    return out


def lev(S, j): return 2 * S[j][1] + S[j][2]


def main():
    t0 = time.time()
    for vs, ns, depth in (((1,2,3,4), (1,2,3), 6),
                          ((1,2,3,4), (1,2,3,4), 5),
                          ((1,2,3,4,5,6), (1,2,3), 5),
                          ((1,2,3,4), (1,2,3,4,5), 4)):
        R = reach(vs, ns, depth)
        c = Counter(); bad = []
        for S in R:
            X = [tuple(x) for x in S]
            c['分母（Reach の元）'] += 1
            c[f'   水準 lev(根)={lev(X,0)}'] += 1
            if C4(X): c['★ C4 を満たす'] += 1
            else:
                c['⛔ **C4 を破る**'] += 1
                if len(bad) < 6: bad.append(X)
            # ★ 窓（H12 の window_mem_W: (M.drop p).take k ∈ W (lev M p)）
            for p in range(len(X) - 1):
                for k in range(2, len(X) - p + 1):
                    Wd = X[p:p + k]
                    c['窓（drop p / take k）'] += 1
                    if C4(Wd): c['★ 窓も C4'] += 1
                    else:
                        c['⛔ **窓が C4 を破る**'] += 1
                        if len(bad) < 12: bad.append(('窓', X, p, k, Wd))
        dn = c['分母（Reach の元）']
        dw = c['窓（drop p / take k）']
        print(f'### Reach(D_{vs}, n∈{ns}, depth={depth})  [{time.time()-t0:.1f}s]')
        print(f'  ★★ (C4-W) 分母 {dn}  ★ **C4 を満たす** {c["★ C4 を満たす"]} '
              f'({100*c["★ C4 を満たす"]/max(dn,1):8.4f}%)  '
              f'⛔ **破る** {c["⛔ **C4 を破る**"]}')
        print(f'      窓 {dw}  ★ **窓も C4** {c["★ 窓も C4"]} '
              f'({100*c["★ 窓も C4"]/max(dw,1):8.4f}%)  '
              f'⛔ **破る** {c["⛔ **窓が C4 を破る**"]}')
        print('      水準の分布: ' + str({int(k.split('=')[1]): v for k, v in c.items()
                                          if k.startswith('   水準')}))
        for b in bad[:4]: print(f'      ⛔ {b}')
        # ---------- (C4-W-b) ----------
        for nm, B in CE.items():
            hit = B in R or any(shift0(B, k) in R for k in range(4))
            print(f'      (C4-W-b) **{nm}** = {list(B)}: C4={"★真" if C4([tuple(x) for x in B]) else "⛔偽"}'
                  f'  Reach に入る? **{hit}**')
        print()


if __name__ == '__main__':
    main()
