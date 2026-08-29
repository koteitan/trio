# -*- coding: utf-8 -*-
"""ラダー到達行数 —— 節 2（展開の族認識）を入れた覆い。

健全性の向き:
  * 深さ切れ・長さ切れは **覆えない側**に倒す（False が安全）。
  * 族の認識は有限個の n で「形」を推定し、**残りの n で検算**する。
    検算に落ちたら覆わない。
  * `assume` で (TOW)/(LTOW) を仮定に足せる。`strict` は Lean 証明ずみのみ。
"""
import sys, re
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from wcert import wcert, rsum, lev0

MAXLEN = 400
MLIFT = False        # (MLIFT)「行 1 が列ごとに 0 か d だけ上がる持ち上げ」を仮定するか
NPROBE = 4          # 族の形を推定する n の個数
NCHECK = 3          # 検算に使う追加の n


def exp(M, n):
    return tuple(tuple(c) for c in trio.expand([list(c) for c in M], n))


def bump(Q, D, k):
    """列ごとの増分 `D`（各列に (dx,dy,dz)）を k 倍して足す。"""
    return tuple((c[0] + k * D[i][0], c[1] + k * D[i][1], c[2] + k * D[i][2])
                 for i, c in enumerate(Q))


def family(M):
    """`M⟦n⟧ = A ++ gTower(Q,e,d,n-1)` を推定して (A,Q,e,d) を返す。無ければ None。

    A = M⟦1⟧、S_k = M⟦k+1⟧ から M⟦k⟧ を引いた差分、S_{k+1} = shift(S_k,e,d)。"""
    E = []
    for n in range(1, NPROBE + NCHECK + 1):
        e_ = exp(M, n)
        if len(e_) > MAXLEN:
            return None
        E.append(e_)
    A = E[0]
    S = []
    for k in range(len(E) - 1):
        if E[k + 1][:len(E[k])] != E[k]:
            return None                     # 伸び方が接頭辞的でない
        S.append(E[k + 1][len(E[k]):])
    if not S or not S[0]:
        return None
    Q = S[0]
    if any(len(s) != len(Q) for s in S):
        return None
    if len(S) > 1:
        D = tuple((S[1][i][0] - Q[i][0], S[1][i][1] - Q[i][1],
                   S[1][i][2] - Q[i][2]) for i in range(len(Q)))
    else:
        D = tuple((0, 0, 0) for _ in Q)
    if any(x < 0 or y < 0 or z != 0 for x, y, z in D):
        return None                         # 行 2 は展開で上がらないはず
    for k, s in enumerate(S):               # 検算（NCHECK 個ぶんを含む）
        if s != bump(Q, D, k):
            return None
    return A, Q, D


def seg_cert(A, Q):
    """(C13) `Q` が `A` の連続断片を一様にずらしたものか。

    健全性: `W_segment`（`Wtower2.lean:2981`）で `A[j:j+k] ∈ W (lev A j)`、
    `W_shift`（`Wset.lean:1320`）で行 0 のずらしは段を上げず、
    `ulift_mem_W`（`Wslift.lean:461`）で `shiftr01 0 d X ∈ W (m + 2d)`。
    `lev Q 0 = lev A j + 2d` なので `Q ∈ Wself` がちょうど出る。**すべて証明ずみ。**"""
    n = len(Q)
    if n == 0 or n > len(A):
        return None
    for j in range(len(A) - n + 1):
        seg = A[j:j + n]
        if any(Q[i][2] != seg[i][2] for i in range(n)):
            continue
        dxs = [Q[i][0] - seg[i][0] for i in range(n)]
        dys = [Q[i][1] - seg[i][1] for i in range(n)]
        if any(v < 0 for v in dxs + dys):
            continue
        if len(set(dxs)) == 1 and len(set(dys)) == 1:
            return 'C13'                     # 一様（証明ずみ: W_shift + ulift_mem_W）
        if MLIFT and len(set(dxs)) == 1 and set(dys) <= {0, max(dys)}:
            return 'C13m'                    # **(MLIFT) 仮定**: 行 1 が列ごとに 0 か d
    return None


def rootmin(Q):
    return all(Q[0][0] <= p[0] for p in Q)


class Cert(object):
    def __init__(self, assume=()):
        self.assume = set(assume)           # 'TOW' / 'LTOW'
        self.memo = {}
        self.why = {}

    def __call__(self, M, depth=6):
        M = tuple(tuple(p) for p in M)
        key = (M, depth)
        if key in self.memo:
            return self.memo[key]
        if depth <= 0 or len(M) > MAXLEN:
            self.memo[key] = None
            return None
        self.memo[key] = None               # 循環は覆えない側に倒す
        r = self._go(M, depth)
        self.memo[key] = r
        return r

    def _go(self, M, depth):
        c = wcert(list(M))
        if c:
            return c
        for k in range(1, len(M)):          # (C11) W_add / (C10) 連結分割
            A, B = M[:k], M[k:]
            if lev0(B) <= lev0(A) and rsum(A, B) and self(A, depth) and self(B, depth):
                return 'C11'
        f = family(M)                       # (C12) 節 2
        if f is None:
            return None
        A, Q, D = f
        e = max(x for x, y, z in D) if D else 0
        d = max(y for x, y, z in D) if D else 0
        uni = len(set(D)) <= 1              # 全列おなじ増分か（＝ shiftr01 型）
        if not self(A, depth - 1):
            return None
        if not (self(Q, depth - 1) or seg_cert(A, Q)):
            return None
        if not rootmin(Q):
            return None
        if e == 0 and d == 0 and A == Q:
            return 'C12+C10'                # W_flatMap_copies（証明ずみ）
        if uni and d == 0:
            return 'C12+TOW' if 'TOW' in self.assume else None
        if uni:
            return 'C12+LTOW' if 'LTOW' in self.assume else None
        return 'C12+MTOW' if 'MTOW' in self.assume else None
