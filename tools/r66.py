# -*- coding: utf-8 -*-
"""課題 R66-2: **`wcert2` をシートの順序数ラダーで測る。**

母集団は乱択ではなく **`psiI.json` の 3 行 z<2 行を「シートの行番号順」＝順序数順**。
乱択の 71% はシートに当てると 0.0% になった（教訓 11 の再発）ので、
**進捗指標は「先頭から連続で覆えている行数」**（ラダーのどこまで届いたか）にする。
"""
import sys, os, json, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import sheet3
from core import parse, rows, isstd
from wcert import wcert
from wcert2 import wself2, why2_detail, lev0


def load_ladder(zcap=1, std_only=False):
    """(シート行番号, 行列, OCF ラベル) を**シートの行番号順**に。"""
    out = []
    for r in json.load(open(sheet3.DATA)):
        if not r.get('bms'):
            continue
        r = sheet3.fix(r)
        try:
            b = parse(r['bms'])
            if rows(b) != 3:
                continue
            b = tuple(tuple(c) for c in parse(r['bms'], 3))
        except Exception:
            continue
        if any(c[2] > zcap for c in b):
            continue
        if std_only and not isstd(b, 'BMS'):
            continue
        out.append((r['row'], b, r.get('ocf', '')))
    out.sort(key=lambda t: t[0])
    return out


if __name__ == '__main__':
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 9
    T = load_ladder()[:LIM]
    print('母集団: psiI.json の 3 行 z<2 **%d 行**（シートの行番号順 ＝ 順序数順）'
          % len(T), flush=True)
    print('   列数 %d..%d' % (min(len(b) for _, b, _ in T),
                              max(len(b) for _, b, _ in T)), flush=True)
    t0 = time.time(); ok = []; res = []
    for i, (row, b, ocf) in enumerate(T):
        if time.time() - t0 > 1800:
            print('   **時間切れ（%d / %d 行）**' % (i, len(T)), flush=True)
            T = T[:i]; break
        res.append((row, b, ocf, wself2(b), wcert(b)))
    n2 = sum(1 for r in res if r[3])
    n1 = sum(1 for r in res if r[4])
    print('== (a) 覆い率 (%.0fs)' % (time.time() - t0))
    print('   `wcert`（R45、分割なし）  %d / %d (%.2f%%)'
          % (n1, len(res), 100.0 * n1 / len(res)))
    print('   **`wcert2`（分割つき）     %d / %d (%.2f%%)**'
          % (n2, len(res), 100.0 * n2 / len(res)))
    # (b) 先頭から連続で覆えている行数
    run = 0
    for row, b, ocf, c2, c1 in res:
        if not c2:
            break
        run += 1
    print('== (b) **ラダーの到達点: 先頭から連続 %d 行**' % run)
    if run:
        row, b, ocf, c2, _ = res[run - 1]
        print('   最後に届いた行: %d  %s' % (row, ocf))
        print('      %s   [%s]' % (''.join(map(str, b)), c2))
    if run < len(res):
        row, b, ocf, _, _ = res[run]
        print('== (c) **最初に落ちた行: %d  %s**' % (row, ocf))
        print('      %s' % ''.join(map(str, b)))
        print('      内訳 %s' % why2_detail(b))
    # (d) 落ちた行の内訳
    d = Counter()
    for row, b, ocf, c2, c1 in res:
        if c2:
            d['**覆えた（%s）**' % c2.split('(')[0].split('+')[0]] += 1
            continue
        w = why2_detail(b)
        if sum(w.values()) == 0:
            d['落ちた: 分割点が 1 つも無い'] += 1
        elif w['左片が覆えない'] + w['右片が覆えない'] > 0 and \
                w['lev0(B)>u'] + w['rsum が破れる'] == 0:
            d['**落ちた: 側条件は通るが断片が覆えない**'] += 1
        elif w['左片が覆えない'] + w['右片が覆えない'] == 0:
            d['**落ちた: 断片以前に側条件で全部落ちる**'] += 1
        else:
            d['落ちた: 両方混在'] += 1
    print('== (d) 内訳')
    for k in sorted(d, key=str):
        print('   %-46s %d' % (k, d[k]))
