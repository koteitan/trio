"""行列が表す順序数どうしの比較（システム非依存）。

ord は展開規則だけで決まる:
    ord(空) = 0,  ord(A) = ord(A-末尾列)+1 (末尾列が全零),  ord(A) = sup_n ord(A[n])
なので BMS 標準形と DBMS 標準形を直接比べられる。

実装は後続/極限の場合分けによる相互再帰:
  A == B（行列として同一）        -> 0
  同じシステムの標準形どうし      -> cmpmat（そのシステムの順序と一致）
  succ vs succ                    -> 前者どうし
  succ vs lim                     -> ord(A-1) < ord(B) なら -1 さもなくば +1
  lim  vs lim                     -> ∃m A <= B[m] なら -1 / ∃n A[n] >= B なら +1
                                     どちらも無ければ等しい（LIM 回まで）

どちらの system に属するかは呼び出し側がタグで渡す。展開・末尾切りは標準形を
保つので、タグは再帰でそのまま引き継げる（isstd を呼ばずに済み、かなり速い）。
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import Mat, expand, cmpmat, isstd

LIM = 3
_memo: dict = {}
stats = {'ocmp': 0}


def blocks(A: Mat):
    """行 0 が 0 の列で切る（＝順序数の和の項。標準形では非増加列）。"""
    out, cur = [], []
    for c in A:
        if c[0] == 0 and cur:
            out.append(tuple(cur)); cur = []
        cur.append(c)
    if cur:
        out.append(tuple(cur))
    return out


def kind(A: Mat) -> str:
    if not A:
        return 'zero'
    return 'succ' if all(v == 0 for v in A[-1]) else 'lim'


def ocmp(A: Mat, ta: str, B: Mat, tb: str) -> int:
    if A == B:
        return 0
    if ta == tb:
        return cmpmat(A, B)
    # 片方がもう一方のシステムでも標準形なら、共通のシステムで cmpmat が使える。
    # 対角違反なら isstd は即 False を返すので、この判定は安い方向だけ試す。
    if isstd(A, tb) or isstd(B, ta):
        return cmpmat(A, B)
    key = (A, ta, B, tb)
    r = _memo.get(key)
    if r is not None:
        return r
    r = _ocmp(A, ta, B, tb)
    _memo[key] = r
    return r


def _ocmp(A, ta, B, tb) -> int:
    stats['ocmp'] += 1
    # 加法分解: 和どうしは項別に比較できる（項は非増加なので辞書式）
    ba, bb = blocks(A), blocks(B)
    if len(ba) > 1 or len(bb) > 1:
        for i in range(min(len(ba), len(bb))):
            c = ocmp(ba[i], ta, bb[i], tb)
            if c:
                return c
        return (len(ba) > len(bb)) - (len(ba) < len(bb))
    ka, kb = kind(A), kind(B)
    if ka == 'zero':
        return 0 if kb == 'zero' else -1
    if kb == 'zero':
        return 1
    if ka == 'succ' and kb == 'succ':
        return ocmp(A[:-1], ta, B[:-1], tb)
    if ka == 'succ':
        return -1 if ocmp(A[:-1], ta, B, tb) < 0 else 1
    if kb == 'succ':
        return 1 if ocmp(A, ta, B[:-1], tb) > 0 else -1
    for i in range(1, LIM + 1):
        if ocmp(A, ta, expand(B, i), tb) <= 0:
            return -1
        if ocmp(expand(A, i), ta, B, tb) >= 0:
            return 1
    return 0
