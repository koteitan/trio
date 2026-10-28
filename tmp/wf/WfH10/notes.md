# WfH10 notes (H10Big = T0H10Core.T0BadSeedsH10Big)

## 1. Structure forced by Bad2 in the H10 frame
x = r+L (last), P0 x = r, e1 x = 0.  Bad2 gives p = P0(x-1), b = P0 p, col p = bump b,
and (Anc0 b x or e2 x != 0).  e1 x = 0 gives e2 x = 0 (R12), so Anc0 b x.
p != r (Counted g r), so p is a strict descendant of r, b >= r, and b ancestor of x => b = r.
So: p = bump child of r (last child of r before x), x-1 = child of p, x = child of r.

The 68 codex U3 failures all have b != r (Bad2_ancestor = False): they are NOT antecedents
of H10Big.  Of the 2373 graft antecedent rows of codex's json, only 2 have the b = r shape,
both e1 g = 1.

## 2. Shape graft generator (gen_shape.py)
For M in a set, every r with e2 r = 1, upg(r-1) = r, every prefix end j in r's subtree,
every a in 1..e1 r: N = M[:j] + [bump(r), (e0r+2,a,0), (e0r+1,0,0)]  (+ variant with an
extra child (e0r+2,a2,0) of p).  Keep structural antecedents, then bms -s = 1 and < SRO.

d3s: 130,844 structural candidates, 1,609 standard (e1g: 1:802, 2:786, 3:21).

## 3. U3' (v(P1(x-1)) finite) is FALSE
151 + 6 + 2 standard antecedents with V = omega (p(1)) or omega+omega.  Smallest (24 cols):
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,0)(5,3,1)(6,3,1)(7,3,0)(5,3,1)(6,3,1)(7,2,0)(6,0,0)
r=20, g=16 (e1 g = 2), x=23, k=upg(22)=15, P1(22)=8, V = v(8) = omega, W = bumpW(15) = omega.
Strong absorption holds (V = W: nothing absorbed).  bms -s = 1, below SRO.

## 4. What the consumer needs, and what the data shows
UpgAbsX at x for every Cons sigma (sigma = rho by cons_unique with Inv3V2's Rk).
By upg_target_val + add_right_injective, W = bumpW k.  If W < E0, lhd_lt_small closes it.
On all 1609 d3s antecedents: k = upg(x-1) has exactly ONE child (never a bump child),
so W = omega.  Danger(V, W) false everywhere.

## 5. Lean (green)
Ytosk/lean/Ytosk/WfH10Bridge.lean:
- KNoBump (residual candidate): H10Big frame + e1 g >= 2 + upg(r-1)=r + upg(x-1)=k + Bad2 shape
  (P0(x-1)=p, P0 p=b, col p = bump b, Anc0 b x)  ->  no child of k is a bump child of k.
- h10Big_of_kNoBump : KNoBump -> T0H10Core.T0BadSeedsH10Big.  axioms [propext, Classical.choice, Quot.sound].
