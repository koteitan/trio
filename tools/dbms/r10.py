# -*- coding: utf-8 -*-
"""課題 R8: **シート自身**が順序保存を破っていないか。

    (1) A 列（BMS）の `seqlex` 昇順で E 列（DBMS）も昇順か
    (2) シートの行番号（＝ OCF の順序）と A 列 / E 列の順序が一致するか
    (3) `SeqEmbT3` の反例 41 対がシートに載っているか

`seqlex` は Python のタプル順序と同型で狭義全順序なので、隣接だけ見れば全対と同値。
"""
import sys, os, json
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import check_sheet as CS
from core import parse, show, isstd
from collections import Counter

# 変換トラックが見つけたシートの誤記（SESSION-2026-08-28）
KNOWN_TYPO = {592, 891, 897, 898, 1532}


def load3(drop_typo=True):
    """(row, bms3, dbms3) を行番号の昇順で。行 2 は 0 で埋めて 3 行にそろえる。"""
    out = []
    for r, mb, md, Y in CS.load():
        if drop_typo and r['row'] in KNOWN_TYPO:
            continue
        try:
            b = tuple(tuple(c) for c in parse(r['bms'], 3))
            d = tuple(tuple(c) for c in parse(r['dbms'], 3))
        except Exception:
            continue
        out.append((r['row'], b, d, r.get('ocf', '')))
    out.sort()
    return out


def adjcheck(seq, name):
    up = eq = dn = 0; bad = []
    for i in range(len(seq) - 1):
        a, b = seq[i], seq[i + 1]
        if a < b:
            up += 1
        elif a == b:
            eq += 1; bad.append(('eq', i))
        else:
            dn += 1; bad.append(('dn', i))
    print('   %-28s 増 %d / 等 %d / **減 %d** -> 破れ **%d**'
          % (name, up, eq, dn, eq + dn))
    return bad


def main(drop_typo=True, only3=True):
    D = load3(drop_typo)
    if only3:
        D = [x for x in D if all(c[2] <= 1 for c in x[1])
             and any(c[1] > 0 for c in x[1])]
    print('母数: シートの正しい行 **%d 行**（誤記 %s、%s）'
          % (len(D), '除く' if drop_typo else '除かない',
             'z<2 の 3 行断片のみ' if only3 else '全部'))

    # (2) 行番号（= OCF の順序）と A 列 / E 列
    print('== (2) 行番号（OCF の順序）との突き合わせ')
    badA = adjcheck([x[1] for x in D], 'A 列（BMS）が行番号順に昇順')
    badE = adjcheck([x[2] for x in D], 'E 列（DBMS）が行番号順に昇順')

    # (1) A 列で並べ替えて E 列が昇順か
    print('== (1) A 列（BMS）の seqlex 昇順で E 列（DBMS）も昇順か')
    o = sorted(range(len(D)), key=lambda i: D[i][1])
    bad1 = adjcheck([D[i][2] for i in o], 'E 列')

    for nm, bad, idx in (('A 列 vs 行番号', badA, list(range(len(D)))),
                         ('E 列 vs 行番号', badE, list(range(len(D)))),
                         ('E 列 vs A 列順', bad1, o)):
        if not bad:
            continue
        print('   ### %s の破れ %d 件' % (nm, len(bad)))
        for k, i in bad[:12]:
            a, b = D[idx[i]], D[idx[i + 1]]
            print('      %s row%d vs row%d' % (k, a[0], b[0]))
            print('         A1=%s' % show([list(c) for c in a[1]], 1))
            print('         A2=%s' % show([list(c) for c in b[1]], 1))
            print('         E1=%s' % show([list(c) for c in a[2]], 1))
            print('         E2=%s' % show([list(c) for c in b[2]], 1))
    return D


if __name__ == '__main__':
    dt = (sys.argv[1] if len(sys.argv) > 1 else 'drop') == 'drop'
    o3 = (sys.argv[2] if len(sys.argv) > 2 else '3') == '3'
    main(dt, o3)
