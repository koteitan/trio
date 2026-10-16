"""Exact decision of Lean's FrameDom (V3NodeLhd.lean):
  FrameDom a B s X := ∀ u, ¬ a < u → ∀ C, B < C → ψ_s(0) < C → C ≤ X →
    ∀ g, (g ∈ comps u B ∨ g ∈ comps u s) → ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d.
C ranges over all trees.  Failure at (u, g) with max(comps u a) < g:
  ∃ C ∈ (max(B, ψ_s 0), X] with C < g and K_u(C) < g   (K_u(C) = max(z :: comps u C)).
For fixed (B, s, a) the obligations and comps u a are constant between consecutive indices of B, s, a;
comps u C shrinks as u grows, so the largest u of each interval is the worst: u ∈ {indices ≤ a} ∪ {a}.
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lhd_exact import lt, le, comps, succ, tmax, ex_K, indices, meet, Z

def frame_dom(a, B, s, X, why=False):
    m = B if lt((s, Z, Z), B) else (s, Z, Z)
    if not lt(m, X): return True
    us = set([Z]); indices(B, us); indices(s, us); indices(a, us)
    us = [u for u in us if le(u, a)] + [a]
    for u in set(us):
        ga = tmax(comps(u, a))
        for g in set(comps(u, B) + comps(u, s)):
            if le(g, ga): continue
            if le(g, m): continue
            I = (succ(m), (X, True))
            I = meet(I, (None, (g, False)))
            if ex_K(u, g)(I):
                return (False, u, g) if why else False
    return (True,) if why else True
