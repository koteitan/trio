/-
**落とす補題の組み立て (1)**: 数える子の列。

列 i の数える子の列 `CL M i`。M.take x の数える子の列は M の数える子の列の先頭部分（`cl_prefix`）。
数える子でなくなりうるのは M.take x での最後の子だけで、x はもとから最後なので、余分な子は末尾に付く。
-/
import Ytosk.V3ChgS

namespace Ytosk

open T

instance (M : Mat) (i : Nat) : DecidablePred (Counted M i) := fun c => by
  unfold Counted; infer_instance

/-- The counted children of `i`, left to right. -/
def CL (M : Mat) (i : Nat) : List Nat := (children M i).filter (fun c => decide (Counted M i c))

/-- **The counted values are the values of the counted children.** -/
theorem cvals_eq_map {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (i : Nat) :
    cvals M ρ i = (CL M i).map ρ.o := by
  unfold cvals CL
  have : (children M i).map (cnt M ρ i) = (children M i).map (fun c => if Counted M i c then ρ.o c else z) := by
    apply List.map_congr_left; intro c _; exact cnt_eq_ite M ρ i c
  rw [this]
  apply nzs_map_ite
  intro c hc _
  exact single_ne_z (single_o hC hG (mem_children hc).2)

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
include hx hR0 hZ2 hSD hZ1 hUAT

omit hR0 hZ2 hSD hZ1 hUAT in
/-- A child whose counting changes is the last child in `M.take x`. -/
theorem cnt_change_last {i c : Nat} (hi : i < x) (hc : c ∈ children M i) (hcx : c < x)
    (h : ¬ (Counted (M.take x) i c ↔ Counted M i c)) : ∀ d ∈ children M i, d < x → d ≤ c := by
  intro d hd hdx
  have hAc : Anc0 M c (x - 1) := by
    rcases cnt_change hx hi hcx h with hxc | hu
    · exact anc_xm1 hx (Anc0.step (mem_children_iff.mp hxc).2 (Anc0.refl c)) hcx
    · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
      rcases hcase with h' | ⟨hA, _⟩
      · omega
      · exact hA
  by_contra hlt
  have hcd : Anc0 M c d := anc_between hAc d (by omega) (by omega)
  have hpd : par M 0 d = some i := (mem_children_iff.mp hd).2
  have := (anc0_par hcd (by omega) hpd).le
  have := (mem_children hc).1
  omega

/-- **The counted children of `M.take x` are a prefix of those of `M`.** -/
theorem cl_prefix {i : Nat} (hi : i < x) : ∃ Tl, CL M i = CL (M.take x) i ++ Tl := by
  have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = x by omega] at hcnt
  -- the children of `i` in `M`: those below `x`, then possibly `x`
  set A := (children M i).filter (fun d => decide (d < x)) with hA
  have hchM : ∃ X, children M i = A ++ X ∧ ∀ d ∈ X, d = x := by
    by_cases hxi : x ∈ children M i
    · exact ⟨[x], children_split_x hx hxi, by simp⟩
    · exact ⟨[], by rw [hA, children_filter_x hx hxi]; simp, by simp⟩
  obtain ⟨X, hchM, hX⟩ := hchM
  have hchT : children (M.take x) i = A := children_take M x i
  -- agreement of the two countings except at the last element of `A`
  have hagree : ∀ d ∈ A, (∃ e ∈ A, d < e) →
      (decide (Counted (M.take x) i d) = decide (Counted M i d)) := by
    intro d hd ⟨e, he, hde⟩
    rw [hA, List.mem_filter] at hd he
    have hdx : d < x := by simpa using hd.2
    have hex : e < x := by simpa using he.2
    apply decide_eq_decide.mpr
    by_contra hne
    have := cnt_change_last hx hi hd.1 hdx hne e he.1 hex
    omega
  unfold CL
  rw [hchT, hchM, List.filter_append]
  -- split `A` at its last element
  rcases List.eq_nil_or_concat A with hnil | ⟨A', ℓ, hAl⟩
  · rw [hnil]; simp
  · rw [List.concat_eq_append] at hAl
    have hsorted : A.Pairwise (· < ·) := (children_sorted M i).filter _
    rw [hAl] at hsorted ⊢
    have hA'ℓ : ∀ d ∈ A', d < ℓ := by
      intro d hd
      exact (List.pairwise_append.mp hsorted).2.2 d hd ℓ (by simp)
    have hfilt : A'.filter (fun d => decide (Counted M i d)) =
        A'.filter (fun d => decide (Counted (M.take x) i d)) := by
      apply List.filter_congr
      intro d hd
      exact (hagree d (by rw [hAl]; simp [hd]) ⟨ℓ, by rw [hAl]; simp, hA'ℓ d hd⟩).symm
    have hℓx : ℓ < x := by
      have : ℓ ∈ A := by rw [hAl]; simp
      rw [hA, List.mem_filter] at this; simpa using this.2
    have hℓM : ℓ ∈ children M i := by
      have : ℓ ∈ A := by rw [hAl]; simp
      rw [hA, List.mem_filter] at this; exact this.1
    simp only [List.filter_append, hfilt, List.filter_cons, List.filter_nil, List.append_assoc]
    by_cases hT : Counted (M.take x) i ℓ
    · have hM : Counted M i ℓ :=
        hcnt i ℓ hi (by rw [children_take, List.mem_filter]; exact ⟨hℓM, by simpa using hℓx⟩) hT
      simp only [decide_eq_true hT, decide_eq_true hM, if_true]
      exact ⟨X.filter (fun d => decide (Counted M i d)), by simp⟩
    · simp only [decide_eq_false hT]
      exact ⟨(if Counted M i ℓ then [ℓ] else []) ++ X.filter (fun d => decide (Counted M i d)), by
        by_cases hM : Counted M i ℓ <;> simp [hM]⟩

end

/-! ## t = 1・q ≠ r の基底: r とその下の v は変わらない -/

/-- The row-1 parent of a child with a larger row 1 is its parent. -/
theorem par1_of_child {M : Mat} {p r : Nat} (hp : par M 0 p = some r) (h1 : entry M 1 r < entry M 1 p) :
    par M 1 p = some r := by
  show climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 p)) (p + 1) (par M 0 p) = some r
  rw [hp]
  simp [climb, h1]

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **`v(r)` does not change** (`t = 1`, `q ≠ r`). -/
theorem v_r_not_chg {r : Nat} (hA : Anc0 M r x) (hrx : r ≠ x) (hqr : par M 0 x ≠ some r)
    (hpath : ∀ s, Anc0 M r s → Anc0 M s x → s ≠ r → s ≠ x → entry M 1 r < entry M 1 s) :
    ¬ ChgX M x false r := by
  intro hC
  have hr : r < x := lt_of_le_of_ne hA.le hrx
  obtain ⟨p, hpr, hpx⟩ := anc0_child hA hrx
  have hpne : p ≠ x := fun e => hqr (e ▸ hpr)
  have hpx' : p < x := lt_of_le_of_ne hpx.le hpne
  have h1 := hpath p (Anc0.step hpr (Anc0.refl r)) hpx (by have := par_lt M 0 p r hpr; omega) hpne
  exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).1 rfl hr |>.2.2 p hpx' (par1_of_child hpr h1)

/-- **A `v` read through `P_1` or an ancestor-type upgrade from a column before `x` does not change.** -/
theorem v_read_not_chg {g d : Nat} (hd : d < x)
    (h : par M 1 d = some g ∨ (upg M d = some g ∧ g < d)) : ¬ ChgX M x false g := by
  intro hC
  have hgd : g < d := by
    rcases h with h | h
    · exact par_lt M 1 d g h
    · exact h.2
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).1 rfl (by omega)
  rcases h with h | ⟨hu, _⟩
  · exact hT.2.2 d hd h
  · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with h' | ⟨hAg, _⟩
    · omega
    · exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT (by omega) hu hAg hgd

end

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **Below a column with row 2 nonzero, changes are only under its last child** (in `M.take x`). -/
theorem chg_only_last {i j j' d : Nat} {b : Bool} (h2 : entry M 2 i ≠ 0) (hj : j ∈ children M i)
    (hj' : j' ∈ children (M.take x) i) (hjj : j < j') (hC : ChgX M x b d) (hjd : Anc0 M j d) : False := by
  have hij := (mem_children hj).1
  have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
  rw [children_take, List.mem_filter] at hj'
  have hj'x : j' < x := by simpa using hj'.2
  have hpj' : par M 0 j' = some i := (mem_children_iff.mp hj'.1).2
  have hjx : j < x := by omega
  have hnj : ¬ Anc0 M j (x - 1) := by
    intro hA
    have h1 := anc_between hA j' (by omega) (by omega)
    have := (anc0_par h1 (by omega) hpj').le; omega
  obtain ⟨c', ⟨hjc', hall', hnot'⟩, hc'x, hup', _⟩ :=
    (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).2 j hjx hjd hnj
  have hA1 : Anc0 M j (c' - 1) := hall' (c' - 1) (by omega) (by omega)
  obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hup'
  have he0 : entry M 0 c' = entry M 0 m + 1 := by
    have : entry M 0 c' = (col M c').1 := rfl
    rw [this, hcol]
  have he2c : entry M 2 c' = entry M 2 m + 1 := by
    have : entry M 2 c' = (col M c').2.2 := rfl
    rw [this, hcol]
  have hmc := par_lt M 1 _ _ hm2
  obtain ⟨hh, hph⟩ := par0_some_of (M := M) hmc (by omega)
  have hR := hR0 c' hh hph
  have hhc := par_lt M 0 c' hh hph
  have hAh : Anc0 M hh (c' - 1) :=
    anc_between (Anc0.step hph (Anc0.refl hh)) (c' - 1) (by omega) (by omega)
  have hAm : Anc0 M m (c' - 1) := anc0_of_par M 1 m (c' - 1) hm1
  have hhm : hh = m := anc0_eq_of_e0 hAh hAm (by omega)
  have hz := hZ2 c'
  have hh0 : entry M 2 hh = 0 := by rw [hhm]; omega
  have hAi : Anc0 M i (c' - 1) := Anc0.trans (Anc0.step hpj (Anc0.refl i)) hA1
  rcases anc0_total hAh hAi with hhi | hih
  · by_cases hhi' : hh = i
    · rw [hhi'] at hh0; omega
    · have hc'j' : c' ≤ j' := by
        by_contra hlt
        have := (anc0_par (hall' j' (by omega) (by omega)) (by omega) hpj').le; omega
      have hAic : Anc0 M i c' := anc_between (Anc0.step hpj' (Anc0.refl i)) c' (by omega) hc'j'
      have hih := anc0_par hAic (by omega) hph
      exact hhi' (Nat.le_antisymm hhi.le hih.le)
  · rcases anc0_total hAh hA1 with hhj | hjh
    · by_cases hhj' : hh = j
      · exact hnot' (Anc0.step hph (hhj' ▸ Anc0.refl hh))
      · have hhi := anc0_par hhj hhj' hpj
        have : hh = i := Nat.le_antisymm hhi.le hih.le
        rw [this] at hh0; omega
    · exact hnot' (Anc0.step hph hjh)

end

/-! ## 弱い子での回復 -/

/-- **Recovery at a parent of a weak child**: if dropping the child gives `ψ_a(B) ◁ ψ_a(X)` and the new
child `c′` dominates its own components, then `ψ_a(B + c′) ◁ ψ_a(X)`. -/
theorem lhd_weak_child {a B c' X : T} (hdrop : Lhd z (psi a B z) (psi a X z)) (hc : c' ≠ z)
    (hsmall : ∀ u, ∀ g ∈ comps u c', g ≤ app B c') (hlt : app B c' < X) :
    Lhd z (psi a (app B c') z) (psi a X z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩, fun u c h1 h2 => ?_⟩
  obtain ⟨C, R, rfl, hC1, hC2⟩ := between_psi h1 h2
  have hBc : psi a B z < psi a C R := by
    apply lt_of_lt_of_le _ (le_of_lt h1)
    rw [psi_lt_psi_z_iff]; right; refine ⟨rfl, ?_⟩
    have := app_lt_app_left B (show z < c' by cases c' with | z => exact absurd rfl hc | psi _ _ _ => exact T.z_lt_psi _ _ _)
    rwa [app_z_right] at this
  intro g hg
  simp only [comps, List.mem_append] at hg
  rcases hg with hg | hg
  · split at hg
    · simp at hg
    · rename_i hau
      simp only [List.mem_cons, List.mem_append] at hg
      have hCmem : C ∈ comps u (psi a C R) := by
        simp only [comps, List.mem_append]; left; rw [if_neg hau]; simp
      rcases hg with rfl | (hg | hg)
      · exact ⟨C, List.mem_append_left _ hCmem, hC1⟩
      · rw [comps_app] at hg
        rcases List.mem_append.mp hg with hg | hg
        · -- a component of `B`: from the drop
          have hgB : g ∈ comps u (psi a B z) := by
            simp only [comps, List.mem_append]; left; rw [if_neg hau]; simp [hg]
          exact hdrop.2 u (psi a C R) hBc h2 g hgB
        · exact ⟨C, List.mem_append_left _ hCmem, le_trans (hsmall u g hg) hC1⟩
      · have hgB : g ∈ comps u (psi a B z) := by
          simp only [comps, List.mem_append]; left; rw [if_neg hau]; simp [hg]
        exact hdrop.2 u (psi a C R) hBc h2 g hgB
  · simp at hg

/-- `ψ_w(0)` above `ψ_0(Ω_1)` is a fixed point of `ω^`. -/
theorem omega_psi_fix {w : T} (hw : isOT w = true) (hE : ¬ psi w z z < E0) : omega (psi w z z) = psi w z z := by
  have hot : isOT (psi w z z) = true := by
    rw [isOT_psi_iff]; exact ⟨hw, rfl, rfl, z_le _, fun g hg => by simp [comps] at hg⟩
  rw [omega_big hot hE]
  simp [split]

/-! ## ε_0 より下 -/

/-- All summands of a standard term with leading subscript `0` have subscript `0`, and its components
at level `0` are at most its leading argument. -/
theorem comps_le_head_arg : ∀ {b c : T}, isOT (psi z b c) = true → ∀ g ∈ comps z (psi z b c), g ≤ b
  | b, c, h, g, hg => by
    obtain ⟨_, _, hc, hhc, hcb⟩ := isOT_psi_iff.mp h
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · rw [if_neg (by simp [lt])] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact le_refl _
      · exact le_of_lt (hcb g hg)
      · simp at hg
    · cases c with
      | z => simp [comps] at hg
      | psi a' b' c' =>
        simp only [head] at hhc
        have ha' : a' = z := by
          rcases (le_iff _ _).mp hhc with h1 | h1
          · rw [T.psi_lt_psi] at h1
            rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
            · exact absurd h1 (T.not_lt_z _)
            · rfl
            · rfl
          · simp only [psi.injEq] at h1; exact h1.1
        subst ha'
        have hb' : b' ≤ b := by
          rcases (le_iff _ _).mp hhc with h1 | h1
          · rw [T.psi_lt_psi] at h1
            rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, h1, _⟩
            · exact absurd h1 (T.not_lt_z _)
            · exact le_of_lt h1
            · rw [h1]
          · simp only [psi.injEq] at h1; rw [h1.2.1]
        exact le_trans (comps_le_head_arg hc g hg) hb'

/-- **Below `ψ_0(Ω_1)`, every smaller standard term is `◁`.** -/
theorem lhd_lt_small {r w : T} (hr : isOT r = true) (hw : w < E0) (h : r < w) : Lhd z r w := by
  refine ⟨h, fun u c h1 h2 => ?_⟩
  intro g hg
  cases r with
  | z => simp [comps] at hg
  | psi a b d =>
    have hrE : psi a b d < E0 := lt_trans h hw
    have ha : a = z := by
      unfold E0 at hrE; rw [T.psi_lt_psi] at hrE
      rcases hrE with h' | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
      · exact absurd h' (T.not_lt_z _)
      · rfl
      · rfl
    subst ha
    have hcE : c < E0 := lt_of_le_of_lt h2 hw
    cases c with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a2 f c2 =>
      have ha2 : a2 = z := by
        unfold E0 at hcE; rw [T.psi_lt_psi] at hcE
        rcases hcE with h' | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
        · exact absurd h' (T.not_lt_z _)
        · rfl
        · rfl
      subst ha2
      have hbf : b ≤ f := by
        rw [T.psi_lt_psi] at h1
        rcases h1 with h' | ⟨_, h'⟩ | ⟨_, h', _⟩
        · exact absurd h' (lt_irrefl' _)
        · exact le_of_lt h'
        · rw [h']
      by_cases hu : u = z
      · subst hu
        refine ⟨f, List.mem_append_left _ ?_, le_trans (comps_le_head_arg hr g hg) hbf⟩
        simp only [comps, List.mem_append]; left; rw [if_neg (by simp [lt])]; simp
      · -- above level `0` there are no components
        exfalso
        have hall : ∀ {b d : T}, isOT (psi z b d) = true → comps u (psi z b d) = [] := by
          intro b d hot
          induction d generalizing b with
          | z =>
            simp only [comps]
            rw [if_pos (by cases u with | z => exact absurd rfl hu | psi _ _ _ => rfl)]; rfl
          | psi a' b' c' _ _ ih2 =>
            obtain ⟨_, _, hc, hhc, _⟩ := isOT_psi_iff.mp hot
            have ha' : a' = z := by
              simp only [head] at hhc
              rcases (le_iff _ _).mp hhc with h1 | h1
              · rw [T.psi_lt_psi] at h1
                rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
                · exact absurd h1 (T.not_lt_z _)
                · rfl
                · rfl
              · simp only [psi.injEq] at h1; exact h1.1
            subst ha'
            have := ih2 hc
            simp only [comps] at this ⊢
            rw [if_pos (by cases u with | z => exact absurd rfl hu | psi _ _ _ => rfl)] at this ⊢
            have hzu : lt z u = true := by cases u with | z => exact absurd rfl hu | psi _ _ _ => rfl
            simpa [hzu] using this
        rw [hall hr] at hg; simp at hg

end Ytosk
