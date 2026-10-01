/-
**3 行・t = 1・q = r: 組み立て（枠の局所条件を仮定に置いた形）。**

列 i の添字を Zf_m(i) = gamS μ b_r seed (m + d_i)（d_i = `dOf`、葉 x からの引き上げの数）とおく。
各 m で D の呼び出しに局所条件 `OLocZ`・`VLocZ` が成り立てば、`qr_path` で局所の等式が出て、
`qr_chain` で n ≥ 2 のすべてに評価がつく（`qr_main`）。残る仮定は局所条件・根・r の引き上げ 0・M[1]。
-/
import Ytosk.V3QRIdx

namespace Ytosk

open T

/-- The per-column index at level `m`. -/
noncomputable def zfQ (M : Mat) (x : Nat) (lo : Nat → Nat → Nat) (lb : Nat → Nat → Nat → Nat)
    (μ br seed : T) (m : Nat) (i : Nat) : T :=
  gamS μ br seed (m + dOf M x lo lb i)

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2`** (`t = 1`, `q = r`), given the local conditions with the per-column indices. -/
theorem qr_main (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    {μ br seed : T} (hbr : br ≠ z) (hcb : cof br = .big μ)
    (hro : ρ.o r = psi μ br z) (hrD : DepX M (r + L) true r)
    (hox : ∀ ζ, fsD (ρ.o (r + L)) ζ = ζ)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the lifts
    {lo : Nat → Nat → Nat} {lb : Nat → Nat → Nat → Nat}
    (hxv : ¬ DepX M (r + L) false (r + L))
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hdr : dOf M (r + L) lo lb r = 0)
    -- the local conditions and the root at every level
    (hO : ∀ m i, i < r + L → DepX M (r + L) true i →
      OLocZ M (r + L) ρ (zfQ M (r + L) lo lb μ br seed m) i)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocZ M (r + L) ρ (zfQ M (r + L) lo lb μ br seed m) i)
    (hRt : ∀ m, Single (fsD (ρ.o Rt) (zfQ M (r + L) lo lb μ br seed m Rt)) ∧
      fsD (ρ.o Rt) (zfQ M (r + L) lo lb μ br seed m Rt) < ρ.o Rt)
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hdx : dOf M (r + L) lo lb (r + L) = 0 := dOf_x hx hxv hOS hVS
  refine qr_chain hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hRM hbr hcb hro hrD hRA hR0 hRlast
    hRd hsM hpM ?_ hC1 hR1 hr1 hPv1
  intro n _ ρP _ hPr
  refine ⟨zfQ M (r + L) lo lb μ br seed (n - 2), ?_, ?_, hRt (n - 2)⟩
  · unfold zfQ; rw [hdr, Nat.add_zero]
  · apply qr_path hC hG hx ?_ (hO (n - 2)) (hV (n - 2))
    show ρP.o (r + L - L) = _
    rw [show r + L - L = r by omega, hox, hPr]
    unfold zfQ; rw [hdx, Nat.add_zero]

end

end Ytosk
