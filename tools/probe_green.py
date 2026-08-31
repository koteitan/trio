# -*- coding: utf-8 -*-
"""How far do the *green* W-membership lemmas reach on their own?

Four lemmas put a matrix in `Wself` without touching the residue:

  R0 zeroRow2_mem_Wself   行 2 が全部 0
  R1 snoc_zeroRow2        行 2 ≡ 0 のブロック ++ 任意の 1 列
  R2 two_col_mem_W        [(0,v,z), t]（2 列、根が深さ 0）
  R3 snoc_orphan_W        dropLast が済み ＋ 末尾列が孤児
  R4 mem_W_of_flat_root   dropLast が済み ＋ srow(末尾)=0 ＋ parent(末尾)=0
  R5 prefixCopies_of_rsum srow(末尾)=0 ＋ バッドルートが深さ 0（rsum が自明）
  R6 W_add                A ++ B に切れて B の根が深さ 0（rsum が自明）

R3-R6 recurse on shorter matrices, so this is a closure. Prints the coverage by
length and the smallest matrices the closure does not reach.
"""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import parent

BMS = os.path.expanduser('~/code/yaBMS/c/bms')

def s(m): return ''.join('(%d,%d,%d)' % c for c in m)

def standard(m):
    return subprocess.run([BMS, '-s', s(m)], capture_output=True,
                          text=True).stdout.strip() == '1'

def srow(c): return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)

def forms(maxlen, maxval):
    """Every z<2 standard form up to maxlen columns with entries <= maxval."""
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

def lev(c): return 2 * c[1] + c[2]

_memo = {}

def why(M):
    """Which green lemma puts M in `W (lev M 0)`, or None.  Memoised."""
    if M in _memo: return _memo[M]
    _memo[M] = None                              # guard against re-entry
    r = _why(M)
    _memo[M] = r
    return r

def prov(M): return M == () or why(M) is not None

def _why(M):
    if len(M) <= 1: return 'R2'
    if all(c[2] == 0 for c in M): return 'R0'
    if all(c[2] == 0 for c in M[:-1]): return 'R1'
    if len(M) == 2 and M[0][0] == 0: return 'R2'
    x = len(M) - 1
    L = list(M)
    t = srow(M[x])
    if prov(M[:-1]):
        if parent(L, t, x) is None: return 'R3'
        if t == 0 and parent(L, 0, x) == 0 and M[0][0] == 0: return 'R4'
    if t == 0:                                   # copies are verbatim
        j0 = parent(L, 0, x)
        if (j0 is not None and M[j0][0] == 0 and lev(M[j0]) <= lev(M[0])
                and prov(M[:j0]) and prov(M[j0:x])): return 'R5'
    for i in range(1, len(M)):                   # A ++ B at depth 0
        if M[i][0] == 0 and lev(M[i]) <= lev(M[0]) and prov(M[:i]) and prov(M[i:]):
            return 'R6'
    return None

def main(maxlen=6, maxval=4):
    fs = forms(maxlen, maxval)
    print('z<2 標準形 (<=%d 列, 値<=%d): %d' % (maxlen, maxval, len(fs)))
    tag = {}
    for M in sorted(fs, key=len):
        r = why(M)
        if r: tag[M] = r
    prov = set(tag)
    from collections import Counter
    print('\n長さ別の到達率:')
    for n in range(1, maxlen + 1):
        tot = [M for M in fs if len(M) == n]
        got = [M for M in tot if M in prov]
        print('  %d 列: %4d / %4d' % (n, len(got), len(tot)))
    print('\n使われた補題:', dict(Counter(tag.values())))
    rest = sorted((M for M in fs if M not in prov), key=lambda M: (len(M), M))
    print('\n届かない最小のもの (%d 個中):' % len(rest))
    for M in rest[:12]: print('   ', s(M))

if __name__ == '__main__':
    main(*(int(a) for a in sys.argv[1:]))
