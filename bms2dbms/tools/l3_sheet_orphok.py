# -*- coding: utf-8 -*-
"""L3 §255-256: BM4-Analysis シートで `OrphOK` の破れを測る。

  python3 bms2dbms/tools/l3_sheet_orphok.py

シートの DBMS 列を M とし、1 <= L < |M| で A = M[:L], T = M[L:] に切る。
`hr0(T)` と `hz0(T)` が成り立つ切り方だけを分母に取る（組み立てで成り立つ条件）。
分子 = 「T の中で孤児」かつ「M では親を持つ」列 = OrphOK の破れ。

あわせて L3 の 2 つの十分条件を検算する:
  (S1) §255 orphOK_of_cone        : 的が T の錐の中なら破れないはず
  (S2) §256 orphOK_of_no_le0_cross: 接頭辞が行 0 で越境しなければ破れないはず
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse
from l3_sheet_hlocq import e, le0, le1, srow, parents


def load():
    data = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'psiI.json')
    seen, mats = set(), []
    for r in json.load(open(data)):
        s = r.get('dbms')
        if not s or 'Empty' in s:
            continue
        try:
            M = parse(s)
        except Exception:
            continue
        if not M:
            continue
        c = tuple(tuple(list(x) + [0, 0, 0])[:3] for x in M)
        if c not in seen:
            seen.add(c)
            mats.append(list(c))
    return [M for M in mats if 2 <= len(M) <= 14 and all(x[2] <= 1 for x in M)]


def main():
    mats = load()
    den = viol = conein = blk = blkcross = 0
    ex = []
    for M in mats:
        n = len(M)
        for Lp in range(1, n):
            T = M[Lp:]
            if not all(e(T, 0, 0) < e(T, 0, x) for x in range(1, len(T))):
                continue
            if e(T, 2, 0) != 0:
                continue
            for j1 in range(1, len(T)):
                den += 1
                if parents(T, srow(T, j1), j1):
                    continue
                pM = parents(M, srow(M, Lp + j1), Lp + j1)
                if pM:
                    viol += 1
                    if len(ex) < 5:
                        ex.append((M, Lp, j1, pM))
                    if le1(T, 0, j1):
                        conein += 1
                    if e(T, 1, j1) <= e(T, 1, 0):
                        blk += 1
                        if any(le0(M, c, Lp + j1) for c in range(Lp)):
                            blkcross += 1
    print(f'(A,T,j1) with hr0(T) & hz0(T) : {den}')
    print(f'OrphOK violations             : {viol}')
    print(f'  (S1) target in T cone       : {conein}   <- 0 なら §255 と整合')
    print(f'  blocker                     : {blk}')
    print(f'  (S2) prefix le0-cross       : {blkcross} <- viol と等しければ §256 と整合')
    for x in ex:
        print(f'  ex {x}')


if __name__ == '__main__':
    main()
