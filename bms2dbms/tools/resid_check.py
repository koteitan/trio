"""残余 RDlad / RDnopar / RDnode を不変量つきで全数検査（不変量の抜き差しつき）。"""
import sys, collections
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show, pim
from rows2 import convC, split, colOK, descOK, units_split, contrPre


def blockok(bd, B):
    if not B: return True
    if B[0][0] != bd: return False
    if any(c[0] < bd for c in B): return False
    return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))

def headPatOK(B, plev):
    if not B: return True
    p, r = B[0], B[1:]
    if p[1] != plev: return True
    A, _ = split(p, list(r))
    if not A: return True
    return A[0][1] != p[1] + 1

def argPatOK(M):
    if not M: return True
    p, r = M[0], M[1:]
    A, T = split(p, list(r))
    return headPatOK(list(A), p[1]) and argPatOK(list(A)) and argPatOK(list(T))

def ctrHead(p, A, T):
    U, B2 = units_split(p, list(T))
    if not B2: return True
    q, r2 = B2[0], B2[1:]
    Aq, Bq = split(q, list(r2))
    if q[1]+1 != p[1] or q[0] != p[0]: return True
    pre = contrPre(p, U, list(A))
    if list(Aq[:len(pre)]) != pre: return True
    rest2 = list(Aq[len(pre):])
    if not rest2: return True
    if rest2[0][0] != p[0]+1: return True
    return rest2[0][1] < p[1]

def headCtrOK(B, plev):
    if not B: return True
    p, r = B[0], B[1:]
    if p[1] != plev + 1: return True
    A, T = split(p, list(r))
    return ctrHead(p, A, T)

def argCtrOK(M):
    if not M: return True
    p, r = M[0], M[1:]
    A, T = split(p, list(r))
    return headCtrOK(list(A), p[1]) and argCtrOK(list(A)) and argCtrOK(list(T))

def adjLev(M):
    return all(not (M[i+1][0] == M[i][0]+1 and M[i+1][1] > M[i][1]+1) for i in range(len(M)-1))

def hpOK(B, d, plev, first, force):
    if not first: return True
    return headPatOK(B, plev) or (d == 0 and plev == 0 and not force)

def fOK(B, d, plev, force):
    if not force: return True
    return (not B or B[0][1] != plev + 1) or (d <= plev + 1)

def hlOK(B, plev):
    return (not B) or B[0][1] <= plev + 1

def ladOf(s, d, plev, first, force):
    return first and s == plev + 1 and (d <= s or force)

def par1(B):
    S = tuple(B); x = len(S) - 1
    if S[x][1] == 0: return None
    P = pim(S); r = P[x][1]
    return None if r == -1 else r

def check(B, d, plev, first, force, nmax=3, mmax=14, dn=5):
    out = tuple(convC(list(B), d, plev, first, force))
    for n in range(1, nmax + 1):
        ok = False
        for np_ in range(n, n + dn + 1):
            tgt = tuple(convC(list(expand(tuple(B), np_)), d, plev, first, force))
            for m in range(1, mmax + 1):
                if tuple(expand(out, m)) == tgt: ok = True; break
            if ok: break
        if not ok: return n
    return None

def gen_blocks(maxlen, bdmax):
    out = []
    for bd in range(bdmax + 1):
        for y in range(bd + 1):
            stack = [[(bd, y)]]
            while stack:
                cur = stack.pop()
                out.append(tuple(cur))
                if len(cur) < maxlen:
                    for a in range(bd, cur[-1][0] + 2):
                        for b in range(a + 1):
                            stack.append(cur + [(a, b)])
    return out

ALL = ['adjLev', 'argPat', 'hlOK', 'hpOK', 'fOK', 'plev<=d', 'd<=bd+1', 'c2', 'hcOK', 'nolad']

def main(maxlen=4, bdmax=2, plevmax=4, drop=''):
    off = set(drop.split(',')) if drop else set()
    blocks = gen_blocks(maxlen, bdmax)
    acc = collections.Counter(); bad = collections.defaultdict(list); cnt = 0
    for B in blocks:
        cnt += 1
        if cnt % 2000 == 0: core._exp_memo.clear(); core._flat_memo.clear()
        bd = B[0][0]
        if not (blockok(bd, B) and colOK(B) and descOK(B)): continue
        if 'argPat' not in off and not argPatOK(B): continue
        if 'adjLev' not in off and not adjLev(B): continue
        if 'hcOK' not in off and not argCtrOK(B): continue
        p, r = B[0], B[1:]
        A, T = split(p, list(r))
        L = len(B); lev1 = B[-1][1]
        j1 = par1(B) if lev1 > 0 else None
        drange = range(bd, bd + 3) if 'd<=bd+1' in off else (bd, bd + 1)
        for d in drange:
            for plev in range(0, plevmax + 1):
                if 'plev<=d' not in off and plev > d: continue
                for first in (False, True):
                    if 'c2' not in off and first and d == bd and not (plev == 0 or plev + 1 < bd):
                        continue
                    for force in (False, True):
                        if 'hpOK' not in off and not hpOK(B, d, plev, first, force): continue
                        if 'fOK' not in off and not fOK(B, d, plev, force): continue
                        if 'hlOK' not in off and not hlOK(B, plev): continue
                        if 'hcOK' not in off and first and not headCtrOK(B, plev): continue
                        lad = ladOf(p[1], d, plev, first, force)
                        cases = []
                        if lad and lev1 == 0: cases.append('zero2')
                        if lad and T and L >= 2 and lev1 > 0: cases.append('poslad')
                        if L >= 2 and lev1 > 0 and ('nolad' in off or not lad):
                            if j1 is None: cases.append('nopar')
                            elif j1 == 0 and not T: cases.append('node')
                        for c in cases:
                            acc[c] += 1
                            res = check(B, d, plev, first, force)
                            if res is not None:
                                acc[c + '_BAD'] += 1
                                bad[c].append((B, d, plev, first, force, res))
    print('drop=%-20s counts: %s' % (drop or '(なし)', dict(sorted(acc.items()))))
    for c, xs in bad.items():
        seen = set()
        for B, d, plev, first, force, n in xs:
            if B in seen: continue
            seen.add(B)
            if len(seen) > 4: break
            print('   BAD %s B=%-30s d=%d plev=%d first=%s force=%s n=%d'
                  % (c, show(B), d, plev, first, force, n))

if __name__ == '__main__':
    import sys
    a = sys.argv[1:]
    main(int(a[0]) if len(a)>0 else 4, int(a[1]) if len(a)>1 else 2,
         int(a[2]) if len(a)>2 else 4, a[3] if len(a)>3 else '')
