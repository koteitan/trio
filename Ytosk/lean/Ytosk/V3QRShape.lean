/-
**3 行・t = 1・q = r: 形。**

x は r の最後の子（q = r）で数える子、o(x) = Ω_{μ+1}（μ = v(r)）。r の前の子はどれも行 1 が r より大きく
（`e1_child_r`）、P_1 = r なので v > μ、o ≥ Ω_{μ+1}。よって
o(r) = ψ_μ(b + Ω_{μ+1})、b（前の子の状態）の加数はどれも Ω_{μ+1} 以上（`qr_o_r`）。
D について: o(r) は D、v(r) は D でない、r と x の間の列は D でない（`qr_dep`）。
-/
import Ytosk.V3VLocT1

namespace Ytosk

open T

/-- `x` (row 2 zero) is never upgraded to. -/
theorem not_isUpg_e2z {M : Mat} {x : Nat} (hx2 : entry M 2 x = 0) : isUpg M x = false := by
  unfold isUpg
  rw [Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨k, _, hk⟩ := h
  exact upg_ne_e2z (of_decide_eq_true hk) hx2

section
variable {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hq : par M 0 x = some r)
include hx h1 hx2 hq

omit hR0 hZ2 hSD hZ1 hUAT hUAB in
/-- The children of `r`: the earlier ones, then `x`. -/
theorem qr_children : children M r = (children M r).filter (fun d => decide (d < x)) ++ [x] :=
  children_split_x hx (mem_children_iff.mpr ⟨by omega, hq⟩)

omit hR0 hZ2 hSD hZ1 hUAT hUAB in
/-- `x` is a counted child of `r`. -/
theorem qr_x_counted : Counted M r x := by
  refine ⟨?_, ?_⟩
  · intro h
    have := e2_of_col (show col M x = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  · rintro ⟨h, _⟩; rw [not_isUpg_e2z hx2] at h; cases h

include hR0 hSD in
/-- **`o(r) = ψ_μ(b + Ω_{μ+1})`** with every summand of `b` at least `Ω_{μ+1}`. -/
theorem qr_o_r {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) :
    ∃ b, ρ.o r = psi (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) z ∧
      b = preState M ρ r ((children M r).filter (fun d => decide (d < x))) ∧
      AllGeT (psi (succ (ρ.v r)) z z) b := by
  have hrx : r < x := par_lt M 1 x r h1
  have hrM : r < M.length := by omega
  have hxM : x < M.length := by omega
  have hch := qr_children hx h1 hx2 hq
  obtain ⟨hcb, hcu⟩ := qr_x_counted hx h1 hx2 hq
  have hframe := o_frame hC hG hrM (L := (children M r).filter (fun d => decide (d < x))) (R := [])
    hch hcb hcu (by simp) hxM
  have hox := o_last_t1 hx hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  set μ := ρ.v r with hμ
  set b := preState M ρ r ((children M r).filter (fun d => decide (d < x))) with hb
  -- the summands of the state are at least `Ω_{μ+1}`
  have hμot : isOT μ = true := hG.ot_v r hrM
  have hel : ∀ t ∈ nzs (((children M r).filter (fun d => decide (d < x))).map (cnt M ρ r)),
      isOT t = true ∧ AllGeT (psi (succ μ) z z) t := by
    intro t ht
    simp only [nzs, List.mem_filter, List.mem_map] at ht
    obtain ⟨⟨c, hc, rfl⟩, hnz⟩ := ht
    have hcM : c ∈ children M r := hc.1
    have hcl := (mem_children hcM).2
    by_cases hcnt : Counted M r c
    · rw [cnt_eq_ite, if_pos hcnt]
      refine ⟨hG.ot_o c hcl, ?_⟩
      have he := e1_child_r hx hR0 hSD h1 hcM
      have hp1 := par1_of_child (mem_children_iff.mp hcM).2 he
      have hgt := v_par1_lt hC hG hR _ c r (Nat.le_refl _) hcl (by omega) hp1
      obtain ⟨σc, hσc⟩ := o_psi_sub hC hcl
      rw [hσc, sf_ot (hG.ot_v c hcl)]
      intro q hq
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rw [hq, psi_lt_psi_z_iff]
      rintro (h | ⟨_, h⟩)
      · exact lt_irrefl' _ (lt_of_lt_of_le hgt (lt_succ_iff.mp h))
      · exact T.not_lt_z _ h
    · rw [cnt_eq_ite, if_neg hcnt] at hnz; simp at hnz
  have hS := allGeT_foldl _ z rfl (allGeT_z _) hel
  have hSot : isOT (sumN (nzs (((children M r).filter (fun d => decide (d < x))).map (cnt M ρ r))))
      = true := isOT_sumN _ (fun t ht => (hel t ht).1)
  have hbge : AllGeT (psi (succ μ) z z) b :=
    allGeT_spArg ⟨_, rfl⟩ _ z hSot hS (allGeT_z _)
  refine ⟨b, ?_, rfl, hbge⟩
  rw [hframe, hox, spArg_single]
  unfold step
  rw [if_neg (by intro h; exact T.not_lt_z _ h.1)]
  rw [add_eq_app_of_ge ⟨_, _, rfl⟩ b (fun q hq => le_of_not_gt (hbge q hq))]


include hR0 hZ2 hSD hZ1 hUAT hUAB in
/-- **`D` for `q = r`**: `o(r)` is in `D`, `v(r)` is not, and no call strictly between `r` and `x` is. -/
theorem qr_dep :
    DepX M x true r ∧ ¬ DepX M x false r ∧ ∀ b i, r < i → i < x → ¬ DepX M x b i := by
  have hrx : r < x := par_lt M 1 x r h1
  obtain ⟨hcb, hcu⟩ := qr_x_counted hx h1 hx2 hq
  have hxr : x ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  refine ⟨DepX.ochild hxr hcb hcu DepX.leaf, nodep_v_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq, ?_⟩
  intro b i hri hix hD
  have hAr : Anc0 M r x := Anc0.step hq (Anc0.refl r)
  have hAi : Anc0 M r i := anc_between hAr i (by omega) (by omega)
  obtain ⟨c, hcr, hci⟩ := anc0_child hAi (by omega)
  have hcl : c < M.length := by have := hci.le; omega
  have hcM : c ∈ children M r := mem_children_iff.mpr ⟨hcl, hcr⟩
  have hcx : c < x := by have := hci.le; omega
  exact nodep_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq (Anc0.refl x) (fun h => absurd h (lt_irrefl _))
    _ c (Nat.le_refl _) hcM hcx b i hD hci

end

end Ytosk
