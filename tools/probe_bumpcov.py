# -*- coding: utf-8 -*-
"""bump 規則を足すと、緑の補題の閉包はどこまで伸びるか。

規則はすべて **健全**（Lean で緑の補題に 1 対 1 で対応）。`prove_w.py` の R7
（`mem_of_oper_mem` を n<=K で打ち切る）は健全でないので外してある。

  R0 zeroRow2_mem_Wself   行 2 ≡ 0
  R1 snoc_zeroRow2        行 2 ≡ 0 のブロック ++ 任意の 1 列
  R2 two_col_mem_W        2 列で根が深さ 0
  R3 snoc_orphan_W        dropLast が済み ＋ 末尾が孤児（または全零）
  R4 mem_W_of_flat_root   dropLast が済み ＋ srow(末尾)=0 ＋ parent=0
  R5 prefixCopies_of_rsum srow(末尾)=0 ＋ バッドルートが深さ 0
  R6 W_add                A ++ B に切れて B の根が深さ 0
  R8 bump_z2 ★新          M = A ++ C, A が Deep で済み, C = bump B
                          （C の全列が深さ>=1・行2=0、深さ 1 の列は (1,0,0)）
"""
import os, subprocess, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import parent, expand

BMS = os.path.expanduser('~/code/yaBMS/c/bms')
CAP = 40


def s(m): return ''.join('(%d,%d,%d)' % c for c in m)
def lev(c): return 2 * c[1] + c[2]
def srow(c): return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


_std = {}
def standard(m):
    k = tuple(m)
    if k not in _std:
        _std[k] = subprocess.run([BMS, '-s', s(m)], capture_output=True,
                                 text=True).stdout.strip() == '1'
    return _std[k]


def forms(maxlen, maxval):
    out = []
    def rec(m):
        if m: out.append(tuple(m))
        if len(m) >= maxlen: return
        for x in range(maxval + 1):
            for y in range(maxval + 1):
                for z in (0, 1):
                    c = (x, y, z)
                    if not m and c != (0, 0, 0): continue
                    if m and not standard(list(m) + [c]): continue
                    rec(m + [c])
    rec([])
    return out


def deep(A):
    return len(A) > 0 and A[0][0] == 0 and all(c[0] >= 1 for c in A[1:])


def bumpshape(C, d):
    """C = shiftr01 d 0 B で B が 行2≡0 ∧ Zroot ∧ 根が深さ 0 か。"""
    if not C or d < 1 or C[0] != (d, 0, 0):
        return False
    for c in C:
        if c[0] < d or c[2] != 0:
            return False
        if c[0] == d and (c[1] != 0 or c[2] != 0):
            return False
    return True


def deep_d(A, d):
    return len(A) > 0 and A[0][0] == 0 and all(c[0] >= d for c in A[1:])


def gen_ok(B):
    """B が Zroot ∧ Mono(行2<=行1) ∧ 根が深さ 0 か。"""
    if not B or B[0][0] != 0:
        return False
    for c in B:
        if c[2] > c[1]:
            return False
        if c[0] == 0 and (c[1] != 0 or c[2] != 0):
            return False
    return True


def unbump(C):
    """C = bump B の B（C の全列が深さ>=1 のときだけ）。"""
    if not C or any(c[0] < 1 for c in C):
        return None
    return tuple((c[0] - 1, c[1], c[2]) for c in C)


def deps(M):
    out = []
    if len(M) >= 2:
        out.append(M[:-1])
        for i in range(1, len(M)):
            b = unbump(M[i:])
            if b is not None: out.append(b)
        x = len(M) - 1
        L = list(M)
        if srow(M[x]) == 0:
            j0 = parent(L, 0, x)
            if j0 is not None: out += [M[:j0], M[j0:x]]
        for i in range(1, len(M)): out += [M[:i], M[i:]]
    return [d for d in out if 0 < len(d) <= CAP]


def rule(M, known, use_bump):
    if len(M) <= 1: return 'R2'
    if all(c[2] == 0 for c in M): return 'R0'
    if all(c[2] == 0 for c in M[:-1]): return 'R1'
    if len(M) == 2 and M[0][0] == 0: return 'R2'
    x = len(M) - 1
    L = list(M)
    t = srow(M[x])
    if M[:-1] in known:
        if parent(L, t, x) is None: return 'R3'
        if t == 0 and parent(L, 0, x) == 0 and M[0][0] == 0: return 'R4'
    if t == 0:
        j0 = parent(L, 0, x)
        if (j0 is not None and M[j0][0] == 0 and lev(M[j0]) <= lev(M[0])
                and (j0 == 0 or M[:j0] in known) and M[j0:x] in known): return 'R5'
    for i in range(1, len(M)):
        if M[i][0] == 0 and lev(M[i]) <= lev(M[0]) and M[:i] in known and M[i:] in known:
            return 'R6'
    if use_bump:
        for i in range(1, len(M)):
            A, C = M[:i], M[i:]
            d = C[0][0]
            if deep_d(A, d) and bumpshape(C, d) and A in known:
                return 'R8' if d == 1 else 'R8d'
        if ORACLE_TOW1 and len(M) >= 2:
            A, c = M[:-1], M[-1]
            if (c[0] == 1 and c[2] == 0 and deep_d(A, 1) and gen_ok(A)
                    and A in known):
                return 'R9'
        if ORACLE_TOW1 and len(M) >= 3:
            A, c1, c2 = M[:-2], M[-2], M[-1]
            if (c1[0] == 1 and c1[2] == 0 and c2 == (2, 0, 0)
                    and deep_d(A, 1) and gen_ok(A) and A in known):
                return 'R10'
        if ORACLE_GEN:
            for i in range(1, len(M)):
                A, C = M[:i], M[i:]
                if not deep_d(A, 1) or A not in known: continue
                B = unbump(C)
                if B is not None and gen_ok(B) and B in known:
                    return 'R8g'
    if ORACLE_PC and t == 0:
        j0 = parent(L, 0, x)
        if (j0 is not None and (j0 == 0 or M[:j0] in known)
                and M[j0:x] in known): return 'PC'
    return None


ORACLE_PC = False
ORACLE_GEN = False
ORACLE_TOW1 = False


def closure(D, use_bump):
    known, tag = set(), {}
    for _ in range(60):
        added = 0
        for M in sorted(D, key=len):
            if M in known: continue
            r = rule(M, known, use_bump)
            if r: known.add(M); tag[M] = r; added += 1
        if not added: break
    return tag


if __name__ == '__main__':
    LEN = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    VAL = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    F = forms(LEN, VAL)
    print('z<2 標準形（<=%d 列・値<=%d）: %d 個' % (LEN, VAL, len(F)))
    D = set(F)
    front = list(F)
    for _ in range(8):
        nxt = []
        for M in front:
            for d in deps(M):
                if d not in D:
                    D.add(d); nxt.append(d)
        front = nxt
        if not front: break
    print('母集団（依存を閉じたもの）: %d 個' % len(D))
    import builtins
    for use, oracle, gen, label in (
            (False, False, False, 'bump なし'),
            (True, False, False, 'bump（行2≡0 の B）'),
            (True, False, True, 'bump 一般版（B は Zroot+Mono で W 0 の元）'),
            (True, False, 'tow1', '上 ＋ TOW1（A ++ [(1,e,0)]）'),
            (True, True, 'tow1', '上 ＋ PrefixCopies 神託')):
        globals()['ORACLE_PC'] = oracle
        globals()['ORACLE_GEN'] = bool(gen)
        globals()['ORACLE_TOW1'] = (gen == 'tow1')
        tag = closure(D, use)
        hit = [M for M in F if M in tag]
        by = Counter(len(M) for M in hit)
        tot = Counter(len(M) for M in F)
        print('--- %s : 標準形 %d / %d' % (label, len(hit), len(F)))
        for l in sorted(tot):
            print('    %d 列  %4d / %4d' % (l, by.get(l, 0), tot[l]))
        if use:
            print('    規則の内訳: %s'
                  % dict(sorted(Counter(tag[M] for M in hit).items())))
            miss = [M for M in F if M not in tag]
            print('    届かない最小の 10 個:')
            for M in sorted(miss, key=lambda m: (len(m), m))[:10]:
                print('      %s' % s(M))
