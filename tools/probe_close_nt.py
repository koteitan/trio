# -*- coding: utf-8 -*-
"""P = S1 ∧ S3 ∧ S4 ∧ PH3c ∧ FC3 の実測（probe_close_ph3 の P を FC=1・SKIP=S2 で、プロセスは 6 個まで）。
NARROW=T: PH3c の cut の位置を cutsNT（最上位の項そのものを除く、Lean V3PDef と同じ）に狭める。
  python3 probe_close_nt.py std <mats.pkl> | perturb <mats.pkl> <seed0> <seed1>（MID=1 で途中の列を崩す）"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('FC', '1'); os.environ.setdefault('SKIP', 'S2')
import multiprocessing
import probe_close_ph3 as PC
from probe_inv3_prefix import le, split, succ, Z
_Pool = multiprocessing.Pool
PC.Pool = lambda n, **kw: _Pool(6, **kw)
def scut(s, h):
    if not h: return []
    a = h[0]
    return ([(s, Z, Z)] if le(s, a) else []) + [(t, Z, Z) for t in scut(s, a)]
def cutsNT(s, h):
    if not h: return []
    a, x, c = h
    return [(t, Z, Z) for t in PC.cuts(a, s)] + [(a, t, Z) for t in PC.cuts(x, s)] + [(a, x, t) for t in cutsNT(s, c)]
def kindN(B, hi, lo, s):
    k = PC.ph3c_kind(B, hi, lo, s)
    if k in ('eq', 'pre'): return k
    if s == Z or not hi: return None
    if os.environ.get('NARROW') == '1':
        return 'cutS' if B in [(t, Z, Z) for t in scut(s, hi[0])] else None
    if os.environ.get('NARROW') == 'T':
        return 'cutNT' if B in cutsNT(s, hi) else None
    a, x, c = hi
    return 'cutH' if B in [(t, Z, Z) for t in PC.cuts(a, s)] + [(a, t, Z) for t in PC.cuts(x, s)] else None
def PH3n(M):
    f = PC.frames(list(M))
    if f is None: return False
    return all(kindN(B, hi, lo, s) for i, c, B, hi, lo, s in f)
if os.environ.get('NARROW') in ('1', 'H', 'T'): PC.PH3c = PH3n
if __name__ == '__main__':
  t = time.time()
  mode = sys.argv[1]
  if mode == 'perturb': PC.main_perturb(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
  elif mode == 'std': PC.main_std(sys.argv[2])
  print('time', time.time() - t)
