# -*- coding: utf-8 -*-
"""平行移動での再現（BM2 の非停止反例と同じ形）を探す。

反例の形（Bubby3, 2018）:
  M の展開 M[n] の**初期区間** P をとると、P の末尾 k 列が M の末尾 k 列の
  平行移動（各行に定数を足したもの）になる。これが自分自身に適用できるので
  無限降下列が作れる。

ここでは bms を呼んで版（-v2 / BM4）を切り替えられるようにしてある。
"""
import os, subprocess, sys

BMS = os.path.expanduser('~/code/yaBMS/c/bms')

def s(m): return ''.join('(%s)' % ','.join(map(str, c)) for c in m)

def parse(t):
    t = t.strip()
    if not t: return []
    return [tuple(int(x) for x in c.split(',')) for c in t.strip('()').split(')(')]

def run(args):
    return subprocess.run([BMS] + args, capture_output=True, text=True).stdout.strip()

_std = {}
def standard(m, ver):
    k = (s(m), ver)
    if k not in _std:
        a = (['-v2'] if ver == 2 else []) + ['-s', s(m)]
        _std[k] = run(a) == '1'
    return _std[k]

_exp = {}
def expand(m, n, ver):
    k = (s(m), n, ver)
    if k not in _exp:
        a = (['-v2'] if ver == 2 else []) + ['%s[%d]' % (s(m), n)]
        _exp[k] = parse(run(a))
    return _exp[k]

def trans(a, b):
    """b = a + 定数ベクトル なら その差、違えば None。"""
    if len(a) != len(b) or not a: return None
    d = tuple(b[0][r] - a[0][r] for r in range(len(a[0])))
    for x, y in zip(a, b):
        if any(y[r] - x[r] != d[r] for r in range(len(x))): return None
    return d

def find(M, ver, nmax=3, kmin=2, kmax=8, cap=400):
    """M の展開の初期区間で、末尾が M の末尾の平行移動になるものを探す。"""
    out = []
    for n in range(1, nmax + 1):
        E = expand(M, n, ver)
        if not E or len(E) > cap: continue
        for L in range(len(M) + 1, len(E) + 1):
            P = E[:L]
            if not standard(P, ver): continue
            for k in range(kmin, min(kmax, len(M), L) + 1):
                d = trans(M[-k:], P[-k:])
                if d and d[0] > 0:
                    out.append((n, L, k, d, P))
    return out

if __name__ == '__main__':
    print('=== 検証: BM2 の既知反例（Bubby3 2018）===')
    M1 = parse('(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)'
               '(7,3,1,0)(8,4,2,1)(9,5,2,1)(10,6,2,1)(11,5,0,0)(12,4,1,1)(13,5,1,1)')
    for ver in (2, 4):
        r = find(M1, ver)
        print('  BM%d : %d 件' % (ver, len(r)))
        for n, L, k, d, P in r[:3]:
            print('     n=%d 長さ%d 末尾%d列 差=%s' % (n, L, k, d))
            print('       %s' % s(P))


def norm(t):
    """末尾ブロックを 1 列目の各行が 0 になるように正規化。"""
    b = t[0]
    return tuple(tuple(c[r] - b[r] for r in range(len(c))) for c in t)


def iterate(M, ver, steps=12, nmax=2, cap=400):
    """平行移動の再現を反復して、同じ形が続くかを見る。

    続いた段数を返す。BM2 の反例なら steps まで続く。"""
    cur, shape, k0 = M, None, None
    for i in range(steps):
        hits = find(cur, ver, nmax=nmax, cap=cap)
        if not hits: return i
        # 形が保たれる遷移を選ぶ（初回は最大の k）
        cand = None
        for n, L, k, d, P in sorted(hits, key=lambda h: -h[2]):
            if shape is None or (k == k0 and norm(P[-k:]) == shape):
                cand = (n, L, k, d, P); break
        if cand is None: return i
        n, L, k, d, P = cand
        if shape is None: shape, k0 = norm(P[-k:]), k
        cur = P
        if len(cur) > cap: return i + 1
    return steps
