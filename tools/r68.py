# -*- coding: utf-8 -*-
"""課題 R68: **仮定つきラダー**を厳密な族認識で測る。

`expfam`（`wcert2.py`）は `oper_unfold` の形から **`M⟦1⟧` と `M⟦2⟧` だけで**
`A0 / Q0 / D` を確定する（k について 1 次なので推定が要らない）。検算 50304/50304。

族: (F2) D≡0 複製【証明ずみ `W_flatMap_copies`】/ (F3) 一様シフト【(TOW)】
    (F4) 一様持ち上げ【(LTOW)】/ (F5e) 行 0 が列ごと【(MTOW)】/ (F5) 行 1 も列ごと【(MLIFT)】
"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import wcert2
from wcert2 import wself2, expfam, famname
from wcert import wcert
from r66 import load_ladder

T = load_ladder()
COVN = 800     # 覆いは先頭 800 行で測る（C13 が全行だと重すぎる）
print('母集団: psiI.json 3 行 z<2 **%d 行**（行番号順）' % len(T), flush=True)

# --- 族の分布（母数を先に出す）
c = Counter()
for row, b, ocf in T:
    r = expfam(b)
    c[famname(r[2]) if r else '族なし（Pred 型）'] += 1
print('== 展開の族の分布')
for k in sorted(c, key=str):
    print('   %-22s %d (%.1f%%)' % (k, c[k], 100.0 * c[k] / len(T)))


def ladder(assume, no_c13=False):
    wcert2.ASSUME = set(assume)
    wcert2._MEMO.clear()
    if no_c13:
        bak = wcert2._clause2_induction
        wcert2._clause2_induction = lambda M, N=6: None
    run = 0; last = None
    for row, b, ocf in T:
        cc = wself2(b)
        if not cc:
            break
        run += 1; last = (row, ocf, cc)
    nxt = T[run] if run < len(T) else None
    cov = sum(1 for _, b, _ in T[:COVN] if wself2(b))
    if no_c13:
        wcert2._clause2_induction = bak
    return run, last, nxt, cov


print('== R68-a 仮定つきラダー（**連続到達行数** ＝ 公式指標）', flush=True)
rows = []
for nm, asm, nc in [('strict（Lean 換算。C13 も外す）', [], True),
                    ('strict + C13（C13 は未 Lean 化）', [], False),
                    ('+ (TOW)', ['TOW'], False),
                    ('+ (TOW),(LTOW)', ['TOW', 'LTOW'], False),
                    ('+ (MTOW)', ['TOW', 'LTOW', 'MTOW'], False),
                    ('+ (MLIFT)', ['TOW', 'LTOW', 'MTOW', 'MLIFT'], False)]:
    t0 = time.time()
    run, last, nxt, cov = ladder(asm, nc)
    rows.append((nm, run, last, nxt, cov))
    print('   %-34s **ラダー %4d 行**  先頭 %d 行の覆い %4d (%.1f%%)  (%.0fs)'
          % (nm, run, COVN, cov, 100.0 * cov / COVN, time.time() - t0), flush=True)
print('== R68-b 各段で最後に届いた行 / 次に落ちる行')
for nm, run, last, nxt, cov in rows:
    print('   %s' % nm)
    if last:
        print('      最後 %4d  %-42s [%s]' % (last[0], last[1], last[2]))
    if nxt:
        print('      **次  %4d  %-42s %s**' % (nxt[0], nxt[2], ''.join(map(str, nxt[1]))))
wcert2.ASSUME = set(); wcert2._MEMO.clear()
