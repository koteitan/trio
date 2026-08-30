# -*- coding: utf-8 -*-
"""**課題 H45 —— 判別子の正体は `srow` か。**

リードの説（L2 の L57）:
    `srow = 1` … 写しの行 1 は段ごとに `d1` 増える ⟹ 親は必ず段の中
    `srow = 2` … **行 2 は写しで不変**（上昇行列 `A_xy` は行 2 に乗らない）
                 ⟹ 親は段の外にありうる

`srow` は 2 通り測れる（持ち上げで行 1 が増えると `srow` が変わりうるので**両方**）:
    `sr_blk` = 生の段 `blk` の最後の列の `srow`
    `sr_exp` = `M⟦2⟧` の**最後の列**の `srow`（実際に親を探す列）
"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import r66, h41, h42, h43b
import trio
import wcert as wc
from collections import Counter

T = r66.load_ladder()
rows = []
for row, M, ocf in T:
    M = [tuple(c) for c in M]
    n = len(M) - 1
    t = h42.srow(M, n)
    r0 = trio.parent(M, t, n)
    if r0 is None:
        continue
    blk = M[r0:n]
    b = len(blk)
    E2 = [tuple(c) for c in trio.expand(list(M), 2)]
    m2 = len(E2) - 1
    sr_exp = h42.srow(E2, m2)
    r1 = trio.parent(E2, sr_exp, m2)
    esc = not (r1 is not None and r1 >= r0 + b)
    inblk = (b >= 2 and trio.parent(list(blk), h42.srow(blk, b - 1), b - 1)
             is not None)
    rows.append(dict(row=row, M=M, ocf=ocf, t=t, a=r0, b=b, blk=blk,
                     sr_blk=h42.srow(blk, b - 1) if b else None,
                     sr_exp=sr_exp, esc=esc, inblk=inblk))

R = [r for r in rows if r['b'] >= 2]
print('母集団: `b >= 2` の **%d 行**（`b = 1` は自明なので除く）' % len(R))
print()

# ---- H45-a --------------------------------------------------------
print('**H45-a `srow` で測り直す**')
for key, nm in (('sr_blk', '生の段の最後の列の `srow`'),
                ('sr_exp', '`M⟦2⟧` の最後の列の `srow`（実際に親を探す列）')):
    print('   %s' % nm)
    c = Counter((r[key], r['esc']) for r in R)
    for s in sorted({k for k, _ in c}):
        a, b = c[(s, True)], c[(s, False)]
        mark = ''
        if a == 0:
            mark = '  ⟸ **復活しない、例外ゼロ**'
        elif b == 0:
            mark = '  ⟸ **必ず復活、例外ゼロ**'
        print('      `srow`=%d  復活 **%4d / %4d (%.1f%%)**%s'
              % (s, a, a + b, 100.0 * a / max(1, a + b), mark))
    bad = sum(1 for r in R if (r[key] == 2) != r['esc'])
    print('      ⟹ 「`srow` = 2 ⟺ 復活」の食い違い **%d / %d (%.2f%%)**'
          % (bad, len(R), 100.0 * bad / len(R)))
print()
print('   **判別子どうしの比較（`b>=2` の %d 行）**' % len(R))
for nm, g in (('段の最後の列の印 = 0（H43）', None),
              ('`sr_blk` = 2', lambda r: r['sr_blk'] == 2),
              ('**`sr_exp` = 2**', lambda r: r['sr_exp'] == 2),
              ('**段内で孤児（H44）**', lambda r: not r['inblk'])):
    if g is None:
        continue
    bad = [r for r in R if g(r) != r['esc']]
    print('      %-30s 食い違い **%d**' % (nm, len(bad)))
    for r in sorted(bad, key=lambda r: r['row'])[:3]:
        print('         行 %-5d %-24s t=%d b=%d sr_blk=%d sr_exp=%d 復活=%s'
              % (r['row'], r['ocf'][:24], r['t'], r['b'], r['sr_blk'],
                 r['sr_exp'], r['esc']))
print()
print('   **H44-a の例外 13 件は `srow` で消えるか**')
ex = [r for r in R if r['t'] == 2 and r['b'] >= 2]
# H43 の印を再現
h13 = []
for r in ex:
    mk = [1 if trio.is_ancestor(r['M'], 1, r['a'], r['a'] + i) else 0
          for i in range(r['b'])]
    if mk[-1] == 0 and not r['esc']:
        h13.append(r)
print('      例外 13 件の `sr_blk` の分布: %s'
      % dict(Counter(r['sr_blk'] for r in h13)))
print('      例外 13 件の `sr_exp` の分布: %s'
      % dict(Counter(r['sr_exp'] for r in h13)))
print('      例外 13 件の「段内に親」の分布: %s'
      % dict(Counter(r['inblk'] for r in h13)))
print()

# ---- H45-c --------------------------------------------------------
print('**H45-c `srow = 2` の段が最初に現れる行**')
for key in ('sr_blk', 'sr_exp'):
    s2 = [r for r in R if r[key] == 2]
    print('   `%s` = 2 の行は %d 件。最小:' % (key, len(s2)))
    for r in sorted(s2, key=lambda r: r['row'])[:3]:
        print('      行 %-5d %-34s 復活=%s' % (r['row'], r['ocf'][:34], r['esc']))
        print('         M = %s' % ''.join('(%d,%d,%d)' % q for q in r['M']))
print()

# ---- H45-d --------------------------------------------------------
print('**H45-d 復活の回数を `srow` で分ける**')
cnt = Counter()
for r in rows:
    X = [tuple(c) for c in r['M']]
    k = 0
    while k < 12:
        f = h43b.feats(X)
        if f is None or f['loc'] == '段 1（新しい段）':
            break
        k += 1
        X = [tuple(c) for c in trio.expand(list(X), 2)]
        if len(X) > 3000:
            k = -1
            break
    cnt[(r['sr_exp'], k)] += 1
for s in sorted({k[0] for k in cnt}):
    tot = sum(v for k, v in cnt.items() if k[0] == s)
    line = '   `sr_exp`=%d（%4d 行）: ' % (s, tot)
    for k in sorted({k[1] for k in cnt if k[0] == s}):
        line += '%d 回:%d  ' % (k, cnt[(s, k)])
    print(line)
print()
print('**退化検査**')
wc.audit(R, lambda r: r['esc'], lambda r: r['sr_exp'] == 2, '復活 vs `sr_exp` = 2')
wc.audit(R, lambda r: r['esc'], lambda r: r['sr_blk'] == 2, '復活 vs `sr_blk` = 2')
wc.audit(R, lambda r: r['esc'], lambda r: not r['inblk'], '復活 vs 段内で孤児')
