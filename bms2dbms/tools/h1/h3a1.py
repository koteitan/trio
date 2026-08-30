# -*- coding: utf-8 -*-
"""A1 の像を動かして ImgClosedT が立つかを調べる。"""
import sys, time, itertools
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, inv3, imgfast
from core import expand, parse, show, isstd
from rows3 import cmpmat

PRE = tuple(map(tuple, parse('(0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,0,0)(5,1,0)(6,2,1)', 3)))
LO  = PRE + ((2,1,0),(3,2,1))          # 直前の行列の像（これより大きくないといけない）

def tails(maxlen=4, maxa=9):
    """PRE の後ろに付ける列の並び（DBMS 標準形になるものだけ）。"""
    out = []
    def rec(t):
        if t:
            N = PRE + tuple(t)
            if isstd(N, 'DBMS'):
                out.append(tuple(t))
        if len(t) >= maxlen:
            return
        last = t[-1][0] if t else PRE[-1][0]
        for a in range(0, min(last + 2, maxa) + 1):
            for b in range(0, a + 1):
                for c in range(0, min(b, 1) + 1):
                    N = PRE + tuple(t) + ((a,b,c),)
                    if isstd(N, 'DBMS'):
                        rec(t + [(a,b,c)])
    rec([])
    return out

def preimage(T, mmax=3):
    """T が conv3 の像か（d2b3 -> 探索）。"""
    try:
        B = inv3.d2b3(T)
    except Exception:
        B = None
    if B and isstd(B,'BMS') and all(c[2] <= 1 for c in B) and tuple(rows3.b2d3(list(B))) == T:
        return tuple(B)
    for SL, cap, uselo, extra in imgfast.LADDER_FAST:
        Lmax = (len(T) + extra) if extra is not None else None
        _, Bs, st = imgfast.search2((), 1, f=rows3.b2d3, SL=SL, Lmax=Lmax,
                                    lo=False, hi=None,
                                    nodecap=imgfast.capfor(cap, T), T=T)
        if Bs:
            return Bs[0]
    return None

if __name__ == '__main__':
    ML = int(sys.argv[1]) if len(sys.argv)>1 else 3
    MM = int(sys.argv[2]) if len(sys.argv)>2 else 3
    T0 = tails(ML)
    C = [PRE + t for t in T0 if cmpmat(LO, PRE + t) < 0 and t[-1][2] == 1]
    # すでに他の行列の像になっているものは除く（衝突）
    IM = set(tuple(rows3.b2d3(list(M))) for M in rows3.gen3('BMS', 7, zcap=1))
    C = [N for N in C if N not in IM]
    print('候補 %d 個（tail<=%d 列, LO より大きい）' % (len(C), ML), flush=True)
    t0=time.time(); good=[]
    for N in C:
        ok = True; Bs = []
        for m in range(1, MM+1):
            T = tuple(expand(N, m))
            B = preimage(T)
            if B is None: ok=False; break
            Bs.append(B)
        if ok:
            good.append((N, Bs))
            print('  **成立** %s' % show([list(c) for c in N]), flush=True)
            for m,B in enumerate(Bs,1):
                print('      m=%d の逆像 %s' % (m, show([list(c) for c in B])), flush=True)
    print('%d/%d が m<=%d で逆像を持つ  %.0fs' % (len(good), len(C), MM, time.time()-t0))
