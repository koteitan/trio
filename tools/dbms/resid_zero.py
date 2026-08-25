"""RDzeroRes2（コミット済みの段 0 の残余）を、その仮定そのままで全数検査する。"""
import sys, collections
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show
from rows2 import convC, split, colOK, descOK
from resid_check import blockok, argPatOK, hpOK, fOK, ladOf, check, gen_blocks

def main(maxlen=5, bdmax=2, plevmax=3):
    blocks = gen_blocks(maxlen, bdmax)
    acc = collections.Counter(); bad = []; cnt = 0
    for B in blocks:
        cnt += 1
        if cnt % 2000 == 0: core._exp_memo.clear(); core._flat_memo.clear()
        bd = B[0][0]
        if not (blockok(bd, B) and colOK(B) and descOK(B) and argPatOK(B)): continue
        if B[-1][1] != 0: continue
        p, r = B[0], B[1:]
        for d in range(bd, bd + 3):
            for plev in range(0, plevmax + 1):
                for first in (False, True):
                    for force in (False, True):
                        if not hpOK(B, d, plev, first, force): continue
                        if not fOK(B, d, plev, force): continue
                        if not ladOf(p[1], d, plev, first, force): continue
                        if p[1] < 1: continue
                        acc['zero2'] += 1
                        res = check(B, d, plev, first, force)
                        if res is not None:
                            acc['BAD'] += 1; bad.append((B, d, plev, first, force, res))
    print('maxlen=%d bdmax=%d counts: %s' % (maxlen, bdmax, dict(acc)))
    seen=set()
    for B,d,plev,first,force,n in bad:
        if B in seen: continue
        seen.add(B)
        print('   BAD B=%-30s d=%d plev=%d first=%s force=%s n=%d' % (show(B),d,plev,first,force,n))

if __name__ == '__main__':
    a=[int(x) for x in sys.argv[1:]]
    main(*a) if a else main()
