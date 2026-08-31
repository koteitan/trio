# -*- coding: utf-8 -*-
"""緑の補題だけで `M in W (lev M 0)` を導けるかを、需要駆動の不動点で判定する。

`probe_green.py` の `why` は再帰＋再入ガードなので、深い依存で自分自身を None と
みなして止まってしまう。ここでは

  1. 目標から依存（dropLast / 分割 / 展開）を BFS で集めて母集団 D を作り
  2. 「既に済んだもの `known` だけを使って規則が当たるか」を D 全体に繰り返し当て
  3. 増えなくなるまで回す

という形にする。導出は最小不動点なので、この向きなら循環に落ちない。

規則（すべて Lean で緑）:
  R0 zeroRow2_mem_Wself   R1 snoc_zeroRow2        R2 two_col_mem_W
  R3 snoc_orphan_W        R4 mem_W_of_flat_root   R5 prefixCopies_of_rsum
  R6 W_add                R7 mem_of_oper_mem（n<=K で打ち切り。n の帰納法が別途要る）
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import parent, expand

K = 6          # R7 で見る n の個数
CAP = 40       # 依存に入れる行列の長さ上限
ROUNDS = 40    # 不動点の反復上限

def lev(c): return 2 * c[1] + c[2]
def srow(c): return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)
def s(m): return ''.join('(%d,%d,%d)' % c for c in m)

def deps(M):
    """M の導出に要りうる行列を列挙する。"""
    out = []
    if len(M) >= 2:
        out.append(M[:-1])
        x = len(M) - 1
        L = list(M)
        if srow(M[x]) == 0:
            j0 = parent(L, 0, x)
            if j0 is not None: out += [M[:j0], M[j0:x]]
        for i in range(1, len(M)): out += [M[:i], M[i:]]
        for n in range(1, K + 1):
            E = tuple(expand(L, n))
            if len(E) <= CAP: out.append(E)
    return [d for d in out if 0 < len(d) <= CAP]

def rule(M, known):
    """known だけを使って M に当たる規則（当たらなければ None）。"""
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
    ok = True
    for n in range(1, K + 1):
        E = tuple(expand(L, n))
        if len(E) > CAP or E not in known: ok = False; break
    if ok: return 'R7'
    return None

DEPTH = 6      # 依存を辿る段数（母集団が爆発するので切る）
SIZE = 40000   # 母集団の上限

def universe(target):
    """target から依存を DEPTH 段だけ辿って母集団を作る。"""
    seen, front = {target}, [target]
    for _ in range(DEPTH):
        nxt = []
        for M in front:
            for d in deps(M):
                if d not in seen:
                    seen.add(d); nxt.append(d)
                    if len(seen) >= SIZE: return seen
        front = nxt
        if not front: break
    return seen

def prove(target, verbose=False):
    D = universe(target)
    known, tag = set(), {}
    for _ in range(ROUNDS):
        added = 0
        for M in sorted(D, key=len):
            if M in known: continue
            r = rule(M, known)
            if r: known.add(M); tag[M] = r; added += 1
        if not added: break
    if verbose:
        print('  母集団 %d, 導出できた %d' % (len(D), len(known)))
    return tag.get(target)

if __name__ == '__main__':
    X = [(0, 0, 0), (1, 1, 1)]
    print('鎖 C(k,1) = X ++ (1,0,0)(2,0,0)...(k,0,0)')
    for k in range(1, 7):
        M = tuple(X + [(j, 0, 0) for j in range(1, k + 1)])
        print('  k=%d  %-4s %s' % (k, prove(M) or '—', s(M)))
    print()
    print('7 個')
    for c in ['1,1,0', '1,1,1', '2,0,0', '2,1,0', '2,1,1', '2,2,0', '2,2,1']:
        col = tuple(int(v) for v in c.split(','))
        print('  X(%s)  %s' % (c, prove(tuple(X + [col])) or '—'))
