# -*- coding: utf-8 -*-
"""**H44-d —— 「(TOWER-易) = 復活しない塔」を神託に足してラダーがどこまで伸びるか。**

H44 の法則: **復活する ⟺ 段の最後の列が段の中では孤児**（例外 0 / 3743）。
⟹ (TOWER-易) が使えるのは「段の最後の列が段の中で親を持つ」ときちょうど。
"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import r66
import ladder, trio, h42
from collections import Counter


def blk_parented(Q):
    """段 `Q` の最後の列が `Q` の中で親を持つか（＝復活しない）。"""
    Q = [tuple(c) for c in Q]
    if len(Q) < 2:
        return False
    return trio.parent(Q, h42.srow(Q, len(Q) - 1), len(Q) - 1) is not None


class Cert2(ladder.Cert):
    """`ladder.Cert` に神託 `TOWEASY`（復活しない塔）を足したもの。"""

    def _go(self, M, depth):
        r = ladder.Cert._go(self, M, depth)
        if r or 'TOWEASY' not in self.assume:
            return r
        f = ladder.family(M)
        if f is None:
            return None
        A, Q, D = f
        if not blk_parented(Q):
            return None                       # 復活する ⟹ (TOWER-易) は使えない
        if not self(A, depth - 1):
            return None
        if not (self(Q, depth - 1) or ladder.seg_cert(A, Q)):
            return None
        if not ladder.rootmin(Q):
            return None
        return 'C12+TOWEASY'


def run(name, cls, asm, ml=False):
    ladder.MLIFT = ml
    C = cls(asm)
    ok = [bool(C(M, 80)) for _, M, _ in T]
    lead = 0
    for x in ok:
        if x:
            lead += 1
        else:
            break
    ladder.MLIFT = False
    return name, sum(ok), lead


T = r66.load_ladder()
print('母集団: `psiI.json` の 3 行 z<2 **%d 行**（シート行番号順 ＝ 順序数順）' % len(T))
print()
print('| 神託 | 覆い | **連続到達行数** |')
print('|---|--:|--:|')
for args in ((('なし（Lean 証明ずみのみ）'), ladder.Cert, ()),
             ('(TOW)', ladder.Cert, ('TOW',)),
             ('**(TOWER-易)**', Cert2, ('TOWEASY',)),
             ('(TOW) + **(TOWER-易)**', Cert2, ('TOW', 'TOWEASY')),
             ('(TOW)+(LTOW)', ladder.Cert, ('TOW', 'LTOW')),
             ('(TOW)+(LTOW)+**(TOWER-易)**', Cert2, ('TOW', 'LTOW', 'TOWEASY')),
             ('(TOW)+(LTOW)+(MTOW)', ladder.Cert, ('TOW', 'LTOW', 'MTOW'))):
    nm, n, lead = run(args[0], args[1], args[2])
    print('| %s | %d (%.1f%%) | **%d** |' % (nm, n, 100.0 * n / len(T), lead))
nm, n, lead = run('+MLIFT（全部）', ladder.Cert, ('TOW', 'LTOW', 'MTOW'), True)
print('| %s | %d (%.1f%%) | **%d** |' % (nm, n, 100.0 * n / len(T), lead))
print()
# 連続到達が止まる行
ladder.MLIFT = False
C = Cert2(('TOW', 'TOWEASY'))
for i, (row, M, ocf) in enumerate(T):
    if not C(M, 80):
        print('**(TOW)+(TOWER-易) が最初に止まる行: %d  %s**' % (row, ocf))
        print('   M = %s' % ''.join('(%d,%d,%d)' % q for q in M))
        break
