# -*- coding: utf-8 -*-
"""課題 R72: ラダーを **BM4-Analysis ブック全 7 シート**（天井 `psi(K*w)`）と
**`D_v = (0,0,0)(1,1,1)(2,2,1)...`** まで伸ばす。"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import wcert2
from wcert2 import wself2
from book import load_book

T = load_book()
print('母集団: ブック全 7 シートの 3 行 z<2 **%d 行**（シート順・行番号順）、列数 %d..%d'
      % (len(T), min(len(b) for *_, b, _ in T), max(len(b) for *_, b, _ in T)),
      flush=True)


def ladder(asm, label, bud=900):
    wcert2.ASSUME = set(asm); wcert2._MEMO.clear()
    t0 = time.time(); n = 0; last = None; to = False; c = Counter()
    for sh, nm, rn, b, lab in T:
        if time.time() - t0 > bud:
            to = True; break
        wcert2._BUDGET[0] = 20000
        cc = wself2(b)
        if not cc:
            break
        n += 1; last = (sh, rn, lab, cc); c[cc.split('(')[0].split('+')[0]] += 1
    nxt = T[n] if n < len(T) and not to else None
    print('%-40s **ラダー %s%d / %d 行**  (%.0fs)'
          % (label, '>=' if to else '', n, len(T), time.time() - t0), flush=True)
    if last:
        print('     最後 sheet%d 行%d  %-34s [%s]' % last, flush=True)
    if nxt:
        print('     **次   sheet%d 行%d  %-34s %s**'
              % (nxt[0], nxt[2], nxt[4], ''.join(map(str, nxt[3]))), flush=True)
    if c:
        print('     内訳', dict(c), flush=True)
    return n


ladder(['LASTMIN'], '対照: strict（連結は split_lastMin のみ）')
ladder(['WSTAR', 'LASTMIN'], '**Wstar3 のみ（連結は split_lastMin のみ）**')

# --- R72-b: D_v そのもの
print('== R72-b: `D_v = (0,0,0)(1,1,1)(2,2,1)(3,3,1)...`（ブックのどの行列より大きい）')
for asm, lab in [(['LASTMIN'], 'strict'), (['WSTAR', 'LASTMIN'], 'Wstar3')]:
    wcert2.ASSUME = set(asm); wcert2._MEMO.clear()
    out = []
    for v in range(1, 13):
        D = tuple([(0, 0, 0), (1, 1, 1)] + [(j, j, 1) for j in range(2, v + 1)])
        wcert2._BUDGET[0] = 200000
        out.append('D_%d:%s' % (v, wself2(D) or '**×**'))
    print('   %-8s %s' % (lab, '  '.join(out)), flush=True)
