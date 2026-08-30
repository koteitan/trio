# -*- coding: utf-8 -*-
"""**健全な `W` 所属判定器 v2 —— メモの毒を除いたもの。**

⚠ **既存の `inW`（`probe_cap2.py` / `h1/h57.py` / `r89.py` が共有）にはバグがある。**

    memo[key] = None            # 循環ガード。**深さを鍵に含めていない**
    ...
    memo[key] = out             # out が None でも**恒久的に**保存される

このため:
  (1) **深さ切れの None が恒久化する。** 残り深さ 0 で評価されたノードが None で
      メモされ、あとから深さがたっぷりある経路で参照されても None のまま
  (2) **循環ガードの None が伝播して毒になる。** 進行中の祖先を見た子は None を返し、
      その子自身が None として恒久メモされる（本当は True かもしれない）

実際に R92b で **深さ 9 → 11 に上げても `unknown` が 702 のまま動かなかった**。
予算の限界ではなく計器の限界だった。

修正:
  * `True` / `False` は恒久メモ（正しい。深さに依らない）
  * `None` は「その深さまでで未定」として深さつきで記録し、**深い予算では再計算する**
  * 循環は進行中集合 `stack` で検出し、**メモせずに** None を返す
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio


def lev(c):
    return 2 * c[1] + c[2]


def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


def inW2(S, a, depth, memo, maxlen, NS=(1, 2, 3), stack=None):
    """True = 閉じた / **False = 確定した非所属**（健全） / None = 未定。

    `memo[(S,a)]` は `True` / `False` / `('unk', d)`（深さ `d` までで未定）。
    """
    if stack is None:
        stack = set()
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    v = memo.get(key)
    if v is True or v is False:
        return v
    if isinstance(v, tuple) and v[1] >= depth:
        return None                       # この深さでは既に未定と分かっている
    if len(S) == 0:
        memo[key] = True
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if depth <= 0 or len(S) > maxlen:
        return None                       # ⚠ メモしない（呼び出し側の予算の問題）
    if key in stack:
        return None                       # 循環。**メモしない**
    stack.add(key)
    out = True
    for n in NS:
        r = inW2(trio.expand(list(S), n), a, depth - 1, memo, maxlen, NS, stack)
        if r is False:
            stack.discard(key)
            memo[key] = False
            return False
        if r is None:
            out = None
    stack.discard(key)
    if out is True:
        memo[key] = True
    else:
        prev = memo.get(key)
        d = depth if not isinstance(prev, tuple) else max(prev[1], depth)
        memo[key] = ('unk', d)
    return out


def selftest():
    memo = {}
    print('### winw.inW2 陽性対照')
    for S, a, want in ((([(0, 1, 0)]), 0, False), (([(0, 0, 1)]), 0, False),
                       (([(0, 0, 0)]), 0, True), (([(0, 0, 0), (1, 0, 0)]), 0, True)):
        got = inW2(S, a, 12, memo, 30)
        print(f'  inW2({S}, a={a}) = {got}   (期待 {want})  '
              f'{"OK" if got == want else "**NG**"}')


if __name__ == '__main__':
    selftest()
