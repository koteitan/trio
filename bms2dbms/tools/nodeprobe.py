import sys, collections
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show, pim
from rows2 import convC, split, colOK, descOK
from resid_check import (blockok, argPatOK, argCtrOK, adjLev, hpOK, fOK,
                         headCtrOK, ladOf, par1, gen_blocks)

def main(maxlen=5, bdmax=3, plevmax=4):
    blocks = gen_blocks(maxlen, bdmax)
    ladcases = collections.Counter()
    nodes = []
    cnt=0
    for B in blocks:
        cnt+=1
        if cnt % 2000 == 0: core._exp_memo.clear(); core._flat_memo.clear()
        bd = B[0][0]
        if not (blockok(bd, B) and colOK(B) and descOK(B)): continue
        if not argPatOK(B): continue
        if not adjLev(B): continue
        if not argCtrOK(B): continue
        p, r = B[0], B[1:]
        A, T = split(p, list(r))
        L = len(B); lev1 = B[-1][1]
        j1 = par1(B) if lev1 > 0 else None
        for d in (bd, bd+1):
            for plev in range(0, plevmax+1):
                if plev > d: continue
                for first in (False, True):
                    if first and d == bd and not (plev == 0 or plev + 1 < bd): continue
                    for force in (False, True):
                        if not hpOK(B, d, plev, first, force): continue
                        if not fOK(B, d, plev, force): continue
                        if first and not headCtrOK(B, plev): continue
                        lad = ladOf(p[1], d, plev, first, force)
                        if lad:
                            ladcases[(p, bd, d, plev, first, force)] += 1
                        if L >= 2 and lev1 > 0 and not lad and j1 == 0 and not T:
                            nodes.append((B, d, plev, first, force))
    print('ladder param combos (p,bd,d,plev,first,force):')
    for k,v in sorted(ladcases.items()):
        print('   ', k, v)
    print('node instances:', len(nodes))
    # for each node instance, find the (n -> m) relation
    rel = collections.Counter()
    for (B,d,plev,first,force) in nodes[:400]:
        out = tuple(convC(list(B), d, plev, first, force))
        row=[]
        for n in range(1,4):
            tgt = tuple(convC(list(expand(tuple(B), n)), d, plev, first, force))
            found=None
            for m in range(1,20):
                if tuple(expand(out,m)) == tgt: found=m; break
            row.append(found)
        rel[tuple(row)] += 1
    print('n=1,2,3 -> m pattern counts:', dict(rel))
    # print a few examples
    seen=set()
    for (B,d,plev,first,force) in nodes:
        if B in seen: continue
        seen.add(B)
        if len(seen)>8: break
        out = tuple(convC(list(B), d, plev, first, force))
        print('B=%-28s d=%d plev=%d first=%s force=%s' % (show(B),d,plev,first,force))
        print('   convC B      =', show(out))
        for n in (1,2,3):
            e = expand(tuple(B), n)
            print('   B[%d]         = %-30s convC = %s' % (n, show(e), show(convC(list(e),d,plev,first,force))))
        for m in (1,2,3):
            print('   (convC B)[%d] = %s' % (m, show(expand(out,m))))

main(*[int(x) for x in sys.argv[1:]])
