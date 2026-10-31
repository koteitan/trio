/-
**WfQrL5 (2026-11-01): the equations of `M[n]` for the glue with given `D` values** (`cons_N_t1Q`).

`glueQ` is a `glueZ` of a modified valuation: put `ρ̃ = oq i + 1` / `vq i + 1` on `D` (and `ρ` off `D`); then
`fsD(X + 1, η) = X` (`fsD_succ_one`) for every index, so `glueQ M x ρ ρN oq vq = glueZ M x ρ̃ ρN Z` for any `Z`
(`glueQ_eq_glueZ`).  The copy lemmas (`cons_copy`) take any `ρ`, so they apply to `ρ̃`; the part below `x` is
`cons_glueQ_lt` (WfQrL1).  Result: `cons_N_t1Q`, the analog of `cons_N_t1` with the local equations
`oRhs (glueQ) i = oq i`, `vRhs (glueQ) i = vq i` (from `qr_pathQ`).
-/
import Ytosk.WfQrL4
import Ytosk.V3T1

namespace Ytosk.WfQrL5
open T Ytosk Ytosk.WfQrL1

/-- `fsD(X + 1, η) = X`. -/
theorem fsD_succ_one (X η : T) : fsD (app X one) η = X := by
  rw [fsD_app X (by simp [one]) η]
  show app X (fsD (psi z z z) η) = X
  simp [fsD]

open Classical in
/-- The modified valuation: `oq i + 1` / `vq i + 1` on `D`, `ρ` off `D`. -/
noncomputable def tildeV (M : Mat) (x : Nat) (ρ : Valn) (oq vq : Nat → T) : Valn :=
  ⟨fun i => if DepX M x true i then app (oq i) one else ρ.o i,
   fun i => if DepX M x false i then app (vq i) one else ρ.v i⟩

/-- **`glueQ` is a `glueZ`.** -/
theorem glueQ_eq_glueZ (M : Mat) (x : Nat) (ρ ρN : Valn) (oq vq : Nat → T) (Z : Nat → T) :
    glueQ M x ρ ρN oq vq = glueZ M x (tildeV M x ρ oq vq) ρN Z := by
  unfold glueQ glueZ tildeV
  congr 1
  · funext i
    by_cases hi : i < x
    · by_cases hd : DepX M x true i
      · simp only [if_pos hi, if_pos hd, fsD_succ_one]
      · simp only [if_pos hi, if_neg hd]
    · simp only [if_neg hi]
  · funext i
    by_cases hi : i < x
    · by_cases hd : DepX M x false i
      · simp only [if_pos hi, if_pos hd, fsD_succ_one]
      · simp only [if_pos hi, if_neg hd]
    · simp only [if_neg hi]

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The equations of `M[n]` for the glue with given `D` values** (`t = 1`; analog of `cons_N_t1`). -/
theorem cons_N_t1Q (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {oq vq : Nat → T} (hC : Cons M ρ) (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueQ M (r + L) ρ (shiftV ρP L) oq vq).v g = ρP.v g)
    (hF : ∀ i, i < r + L →
      (DepX M (r + L) true i → oRhs M (glueQ M (r + L) ρ (shiftV ρP L) oq vq) i = oq i) ∧
      (DepX M (r + L) false i → vRhs M (glueQ M (r + L) ρ (shiftV ρP L) oq vq) i = vq i)) :
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) := by
  have hlN := len_N (d0 := d0) hlen hn
  intro i hi
  rcases Nat.lt_or_ge i (r + L) with h | h
  · exact cons_glueQ_lt (by omega) hC (sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux)
      (fun i hi _ m _ hm => reads_lt_x hlen hx2 hi hm) hF i h
  · rw [glueQ_eq_glueZ M (r + L) ρ (shiftV ρP L) oq vq (fun _ => z)] at hagree ⊢
    have := cons_copy hlen hL hA hd0e hn hpath hz2 hCP hagree (i - (r + L)) (by omega)
    rw [show r + L + (i - (r + L)) = i by omega] at this
    exact this

end

end Ytosk.WfQrL5
