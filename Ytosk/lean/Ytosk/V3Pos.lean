/-
**3 行・t = 1・q ≠ r: 穴の位置。**

r 以下の列の値では穴は対角化の点 ψ_{a'}(b_r)（a' ≤ v(r)）の下にあり、共終数は Ω_{μ+1} ではない
（`DiagAt.cof_ne`）。r より後ろの列の親は r 以後（r は x の祖先なので r と x の間は r の子孫）。
これで o の枠の通過条件は、x より前の r より後ろの列で μ < v(i) が成り立つこと（F1）だけから出る（`t1_hole`）。
-/
import Ytosk.V3PathT

namespace Ytosk

open T

/-- Below a diagonal point the cofinality is not `Ω_{μ+1}`. -/
theorem DiagAt.cof_ne {a b μ : T} {t : T} (h : DiagAt a b μ t) : cof t ≠ .big μ := by
  induction h with
  | here hb hc hμ =>
    have hs := not_succ_of_cof_big hc
    unfold cof
    rw [if_neg hb, if_neg (by rw [hs]; simp), hc]
    simp only
    rw [if_neg hμ]; simp
  | rest _ ih => simpa [cof] using ih
  | @arg a' b' hb hs _ ih =>
    unfold cof
    rw [if_neg hb, if_neg (by rw [hs]; simp)]
    cases hcb : cof b' with
    | big μ' =>
      simp only
      split
      · intro he; cases he; exact ih hcb
      · simp
    | zero => simp
    | succ => simp
    | omega => simp
  | @sub a' ha hs _ ih =>
    unfold cof
    rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp)]
    exact ih

/-- The diagonal point through an `o` frame (the right branch of `holeT_oframe`). -/
theorem diag_oframe {μ br vr a b s y : T} (hc : isOT (psi s y z) = true)
    (hD : ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (psi s y z)) (hμ : μ = vr) (hbr : br ≠ z)
    (hcbr : cof br = .big μ) :
    ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (psi a (step a b s y z) z) := by
  obtain ⟨a', ha', hD⟩ := hD
  rcases step_cases (a := a) (b := b) hc with ⟨B, hB⟩ | ⟨hy, _, hyz, _, htr2⟩
  · rw [hB]
    have hD' := DiagAt.append B (by simp) hD
    exact ⟨a', ha', DiagAt.arg (DiagAt.ne_z hD') (DiagAt.not_succ hD') hD'⟩
  · rw [hy]
    by_cases hne : s = a' ∧ y = br
    · obtain ⟨rfl, rfl⟩ := hne
      have has : ¬ lt s a = true := by
        intro h
        have : psi a z z < psi s y z := htr2
        rw [psi_lt_psi_z_iff] at this
        rcases this with h' | ⟨h', _⟩
        · exact lt_irrefl' _ (lt_trans h h')
        · rw [h'] at h; exact lt_irrefl' _ h
      refine ⟨a, ?_, DiagAt.here hbr hcbr ?_⟩
      · intro h
        exact has (lt_of_le_of_lt (le_of_not_gt ha') (show vr < a from h))
      · rw [hμ]; intro h
        exact has (lt_of_le_of_lt (le_of_not_gt ha') (show vr < a from h))
    · have hDy := DiagAt.arg_inv hD hyz hne
      exact ⟨a', ha', DiagAt.arg hyz (DiagAt.not_succ hDy) hDy⟩

/-- The diagonal point through `ω^G`. -/
theorem diag_omega {a' br μ G : T} (hot : isOT G = true) (hD : DiagAt a' br μ G) :
    DiagAt a' br μ (omega G) := by
  by_cases hE : G < E0
  · rw [omega_small hE]
    exact DiagAt.arg (DiagAt.ne_z hD) (DiagAt.not_succ hD) hD
  · cases G with
    | z => exact absurd rfl (DiagAt.ne_z hD)
    | psi s b c =>
      rw [omega_big' hot hE]
      by_cases hlo : loOf s b = z
      · rw [if_pos hlo]
        by_cases hcz : c = z
        · subst hcz
          have hb : hiOf s b = b := by
            have := split_app (psi (succ s) z z) b
            unfold hiOf; unfold loOf at hlo; rw [hlo, app_z_right] at this; exact this
          rw [app_z_right, hb]; exact hD
        · have hDc : DiagAt a' br μ c := by
            cases c with
            | z => exact absurd rfl hcz
            | psi c1 c2 c3 =>
              cases hD with
              | rest h' => exact h'
          have hD' := DiagAt.append (hiOf s b) hcz hDc
          exact DiagAt.arg (DiagAt.ne_z hD') (DiagAt.not_succ hD') hD'
      · rw [if_neg hlo]
        have hD' := DiagAt.append (hiOf s b) (by simp) hD
        exact DiagAt.arg (DiagAt.ne_z hD') (DiagAt.not_succ hD') hD'

/-- The value of an upgrade-type subscript: `v(i) = B ++ v(U i)`. -/
theorem upg_val {M : Mat} {ρ : Valn} {i k : Nat} (hC : Cons M ρ) (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k) (hV : Single (ρ.v k))
    (hAot : isOT (vOpt ρ (par M 1 i)) = true) : ∃ B, ρ.v i = app B (ρ.v k) := by
  obtain ⟨hVot, s, y, hsy⟩ := hV
  obtain ⟨B, X, _, _, hadd⟩ := add_prefix s y (vOpt ρ (par M 1 i))
  refine ⟨B, ?_⟩
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_pos h2, hu]
  simp only
  rw [hsy]; simp only [last]
  rw [sf_ot (isOT_add hAot (by rw [← hsy]; exact hVot)), hadd]

/-- The value of an `o` call with no counted children: `Ω_{v(i)}`. -/
theorem o_nocnt {M : Mat} {ρ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hiM : i < M.length)
    (hnc : ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) :
    ρ.o i = psi (ρ.v i) z z := by
  have hcv : cvals M ρ i = [] := by
    unfold cvals
    exact nzs_zeros _ (fun t ht => by obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact cnt_unc ρ (hnc d hd))
  rw [o_spArg hC hG hiM, hcv]; rfl

end Ytosk
