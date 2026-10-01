/-
**3 行・t = 1・q = r: 始点が小さい場合（r = x − 1）だけが残ることと、その場合の値の不変条件。**

- r + 1 < x なら、r の最初の子 r + 1 は M.take x でも数えられ（`first_child_counted_take_r`）、
  v(r) は M.take x で変わらない（r + 1 の行 1 の親が r）。よって始点 ≥ ψ_μ(1)（`qr_seed_big`）。
  始点が ψ_μ(1) より小さいのは r + 1 = x（b = 0）のときだけ。
-/
import Ytosk.V3QRN

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 x = some r)
include hx hR0 hZ2 hSD hZ1 hUAB h1

/-- **In `M.take x`, the first child `r + 1` of `r` is counted** (when `r + 1 < x`). -/
theorem first_child_counted_take_r (hr1x : r + 1 < x) :
    r + 1 ∈ children (M.take x) r ∧ Counted (M.take x) r (r + 1) := by
  have hA := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  have hpar : par M 0 (r + 1) = some r := child_succ hA (by omega)
  have hmemM : r + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hpar⟩
  have hmemT : r + 1 ∈ children (M.take x) r := by
    rw [children_take, List.mem_filter]; exact ⟨hmemM, by simpa using hr1x⟩
  refine ⟨hmemT, ?_, ?_⟩
  · rw [col_take M hr1x, bump_take M hrx]
    exact no_bump_child_r hx hR0 hSD h1 (r + 1) hmemM
  · rintro ⟨hiu, htop⟩
    obtain ⟨k, hk, hu⟩ := (isUpg_take M (by omega) (r + 1)).mp hiu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with h | ⟨hAk, hlt⟩
    · have hkr : k = r := by omega
      rw [hkr] at hu
      have := leaf_of_upg_next hR0 hu x hA
      omega
    · have he2 : entry M 2 (r + 1) = 1 := by have := upg_target_e2 hu; have := hZ2 (r + 1); omega
      obtain ⟨p', hp', hp'k⟩ := anc0_child hAk (by omega)
      have hp'k' := hp'k.le
      have hp'x : p' < x := by omega
      have hp'M : p' ∈ children M (r + 1) := mem_children_iff.mpr ⟨by omega, hp'⟩
      have hp'T : p' ∈ children (M.take x) (r + 1) := by
        rw [children_take, List.mem_filter]; exact ⟨hp'M, by simpa using hp'x⟩
      unfold topped at htop
      cases hl : (children (M.take x) (r + 1)).getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hp'T; simp at hp'T
      | some ℓ =>
        rw [hl] at htop
        simp only [decide_eq_true_eq] at htop
        have hlast : children (M.take x) (r + 1) = (children (M.take x) (r + 1)).dropLast ++ [ℓ] := by
          rw [List.dropLast_append_getLast? _ hl]
        have hall := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x)
          (Z1C_take hZ1 x) (by rw [entry_take M 2 hr1x]; exact he2) hlast htop p' hp'T
        rw [col_take M hp'x, bump_take M hr1x] at hall
        exact hUAB k (r + 1) hu (by omega) p' hp'M hall hp'k

include hUAT in
/-- **If `r + 1 < x`, the seed is at least `ψ_{v(r)}(1)`** (`q = r` or not). -/
theorem qr_seed_big {ρ ρ1 : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC1 : Cons (M.take x) ρ1) (hRk1 : Rk (M.take x) rk) (hr1x : r + 1 < x) :
    psi (ρ.v r) one z ≤ ρ1.o r := by
  have hA := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  obtain ⟨hmem, hcnt⟩ := first_child_counted_take_r hx hR0 hZ2 hSD hZ1 hUAB h1 hr1x
  have hpar : par M 0 (r + 1) = some r := child_succ hA (by omega)
  have hmemM : r + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hpar⟩
  have hp1 : par M 1 (r + 1) = some r := par1_of_child hpar (e1_child_r hx hR0 hSD h1 hmemM)
  have hv1 : ρ1.v r = ρ.v r :=
    (chg_off hx hC hG hC1 hRk1 r hrx).2 (v_read_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hr1x (Or.inl hp1))
  obtain ⟨σ, hσ, hσz⟩ := o_arg_ne_z hC1 (by rw [List.length_take]; omega) hmem hcnt
  rw [hσ, hv1, sf_ot (hG.ot_v r (by omega))]
  exact le_psi_arg (one_le_of_ne_z hσz)

end

/-! ## 引き上げのない列で、穴の最後の Ω_a の a は A でない -/

theorem last_last : ∀ t : T, last (last t) = last t
  | z => rfl
  | psi _ _ z => rfl
  | psi _ _ (psi c d e) => by
    show last (last (psi c d e)) = last (psi c d e)
    exact last_last (psi c d e)

theorem succ_ne_A {μ μ' br : T} (hbr : br ≠ z) : succ μ' ≠ psi μ br z := by
  intro h
  have h1 := isSucc_succ μ'
  rw [h, isSucc_psi_z (Or.inr hbr)] at h1
  cases h1

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b : T} (hx : x + 1 = M.length)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hq : par M 0 x = some r) (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hb : AllGeT (psi (succ μ) z z) b)
include hx hC hG hKD hTD hq hro hOS hVS hBk hb

/-- **Without a lift, `A` is never the subscript of a last `Ω_a`, nor the last summand of a `v`.** -/
theorem qr_lastNA {bb : Bool} {i d : Nat} (hD : DepL M x (loQ M ρ μ b) (lbQ M ρ μ b) bb i d) :
    i < x → d = 0 →
    (bb = true → (∀ s y, ρ.o i = psi s y z → ∀ a, last y = psi a z z →
        a ≠ psi μ (app b (psi (succ μ) z z)) z) ∧
      (∀ a, ρ.o i = psi a z z → a ≠ psi μ (app b (psi (succ μ) z z)) z)) ∧
    (bb = false → last (ρ.v i) ≠ psi μ (app b (psi (succ μ) z z)) z) := by
  have hbr : app b (psi (succ μ) z z) ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  have hall : ∀ q ∈ summands (app b (psi (succ μ) z z)), ¬ q < psi (succ μ) z z := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hb q hq
    · simp [summands] at hq; rw [hq]; exact lt_irrefl' _
  have hlo : (split (app b (psi (succ μ) z z)) (psi (succ (μ)) z z)).2 = z := split_snd_z_of_ge hall
  induction hD with
  | leaf => intro h; omega
  | @ochild i c d hc hcb hcu hdc ih =>
    intro hi hd0
    have hd : d = 0 := by omega
    have hlo0 : loQ M ρ μ b i c = 0 := by omega
    have hcm := mem_children hc
    have hcM := hcm.2
    have hiM : i < M.length := by omega
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    rcases Nat.lt_or_ge c x with hcx | hcx
    · obtain ⟨ihc1, ihc2⟩ := (ih hcx hd).1 rfl
      have hDi : DepX M x true i := DepX.ochild hc hcb hcu (depX_of_depL hdc)
      rcases hOS i hi hDi with ⟨_, hnc⟩ | ⟨_, L, c', R, hch, _, _, hR, hLnd⟩
      · exact absurd (hnc c hc) (by rintro (h | h); exact hcb h; exact hcu h)
      have hcc : c = c' := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd (depX_of_depL hdc) (hLnd c h ⟨hcb, hcu⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c h with h' | h'
            · exact absurd h' hcb
            · exact absurd h' hcu
      subst hcc
      have hfl := filter_lt_split (children_sorted M i) hch
      obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
      have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
      have hframe := o_frame hC hG hiM hch hcb hcu hR hcM
      rw [hcv, spArg_single] at hframe
      refine ⟨?_, ?_⟩
      · intro s' y' ho a hla
        rw [hframe] at ho
        have hy' := (T.psi.inj ho).2.1
        rcases step_cases (a := ρ.v i) (b := preState M ρ i L) hcot with ⟨B, hB⟩ | ⟨hy, _, hyz, htr1, htr2⟩
        · rw [hB] at hy'
          rw [← hy', last_app B (by simp)] at hla
          obtain ⟨rfl, rfl, _⟩ := T.psi.inj hla
          exact ihc2 s hcv
        · rw [hy] at hy'
          rw [← hy'] at hla
          exact ihc1 s y hcv a hla
      · intro a ho
        rw [hframe] at ho
        exact absurd (T.psi.inj ho).2.1 (step_ne_z hcot)
    · have hcx' : c = x := by omega
      subst hcx'
      have hir : i = r := by
        have := (mem_children_iff.mp hc).2; rw [hq] at this; exact (Option.some.inj this).symm
      subst hir
      refine ⟨?_, ?_⟩
      · intro s y ho a hla
        rw [hro] at ho
        have hy := (T.psi.inj ho).2.1
        rw [← hy, last_app b (by simp)] at hla
        have ha : a = succ μ := by simp [last] at hla; exact hla.symm
        rw [ha]; exact succ_ne_A hbr
      · intro a ho
        rw [hro] at ho
        exact absurd (T.psi.inj ho).2.1 hbr
  | @ov i d hv ih =>
    intro hi hd0
    have ihv := (ih hi hd0).2 rfl
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    rcases hOS i hi (DepX.ov (depX_of_depL hv)) with ⟨_, hnc⟩ | ⟨hnv, _⟩
    · have hoi := o_nocnt hC hG (by omega) hnc
      refine ⟨?_, ?_⟩
      · intro s y ho a hla
        rw [hoi] at ho
        have := (T.psi.inj ho).2.1
        rw [← this] at hla
        simp [last] at hla
      · intro a ho heq
        rw [hoi] at ho
        have hva := (T.psi.inj ho).1
        apply ihv
        rw [hva, heq]; rfl
    · exact absurd (depX_of_depL hv) hnv
  | @vpar i m d h1 hp hdm _ =>
    intro hi _
    exact absurd (depX_of_depL hdm) ((hVS i hi (DepX.vpar h1 hp (depX_of_depL hdm))).2.1 m hp)
  | @vupg i k d h1 h2 hu hdk ih =>
    intro hi hd0
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    have hDi : DepX M x false i := DepX.vupg h1 h2 hu (depX_of_depL hdk)
    obtain ⟨_, _, hcase⟩ := hVS i hi hDi
    have hkx : k < x := by
      rcases hcase with ⟨_, hu', hlt, _⟩ | ⟨h2', _⟩
      · rw [hu] at hu'; cases hu'; exact hlt
      · exact absurd h2 h2'
    have ihk := (ih hkx hd0).2 rfl
    have hDk := qr_diag0 hx hC hG hKD hTD hq hro hOS hVS hBk hdk hkx hd0
    simp only [valB, cond_false] at hDk
    have hkM : k < M.length := by omega
    have hvkz : ρ.v k ≠ z := DiagAt.ne_z hDk
    have hVs : Single (last (ρ.v k)) := ⟨isOT_last (hG.ot_v k hkM), last_psi_form hvkz⟩
    obtain ⟨B, hvi⟩ := upg_valL hC (by omega) h1 h2 hu hVs (vOpt_ot hG (by omega))
    rw [hvi, last_app B (single_ne_z hVs), last_last]
    exact ihk
  | @vbump i j k d h1 h2 hj hjb hk hdk ih =>
    intro hi hd0
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    have hd : d = 0 := by omega
    have hlb : lbQ M ρ μ b i j k = 0 := by omega
    have hDi : DepX M x false i := DepX.vbump h1 h2 hj hjb hk (depX_of_depL hdk)
    have hiM : i < M.length := by omega
    obtain ⟨_, _, hcase⟩ := hVS i hi hDi
    rcases hcase with ⟨h2', _⟩ | ⟨_, L, K, j', k', hch, hjb', hchj, _, hKnd, hLnd⟩
    · exact absurd h2' h2
    have hjj : j = j' := by
      rw [hch] at hj
      rcases List.mem_append.mp hj with h | h
      · exact absurd (depX_of_depL hdk) (hLnd j h k hk).2
      · exact List.mem_singleton.mp h
    subst hjj
    have hkk : k = k' := by
      rw [hchj] at hk
      rcases List.mem_append.mp hk with h | h
      · exact absurd (depX_of_depL hdk) (hKnd k h)
      · exact List.mem_singleton.mp h
    subst hkk
    have hBD : BumpData M ρ μ i L K j k := bump_data hC hG hKD hTD h1 h2 hch hjb hchj
    have hvi := v_bump_valueG hC hiM h1 h2 hch hjb hchj hBD.sK hBD.pK hBD.sL hBD.pp hBD.gt
      (vOpt_ot hG (by omega))
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hGz : G ≠ z := by rw [hGe]; intro he; exact single_ne_z hkS (app_eq_z he).2
    have hsW := single_omega hBD.potW
    have hWz : omega (app (sumN P) (omega G)) ≠ z := single_ne_z hsW
    obtain ⟨B, hvi2⟩ : ∃ B, ρ.v i = app B (omega (app (sumN P) (omega G))) := by
      obtain ⟨_, s0, y0, hW0⟩ := hsW
      obtain ⟨B, X, _, _, hadd⟩ := add_prefix s0 y0 (vOpt ρ (par M 1 i))
      exact ⟨B, by rw [hvi, hW0, hadd]⟩
    rw [hvi2, last_app B hWz]
    obtain ⟨_, s0, y0, hW0⟩ := hsW
    rw [hW0]
    show psi s0 y0 z ≠ _
    rw [← hW0]
    intro hWA
    -- `W = A` forces the lift `2`
    have hfix := omega_single_nolo hBD.potW
      (fun h => single_ne_z (single_omega hGot) (app_eq_z h).2) hWA hlo
    rw [hfix] at hWA
    have hP0 : sumN P = z := by
      by_contra hP
      exact app_single_ne hP (single_ne_z (single_omega hGot)) hWA
    rw [hP0] at hWA
    have hωG : omega G = psi μ (app b (psi (succ μ) z z)) z := hWA
    have hfixG := omega_single_nolo hGot hGz hωG hlo
    rw [hfixG] at hωG
    have hK0 : sumN (K.map ρ.o) = z := by
      by_contra hK
      exact app_single_ne hK (single_ne_z hkS) (by rw [← hGe]; exact hωG)
    have hok : ρ.o k = psi μ (app b (psi (succ μ) z z)) z := by rw [← hωG, hGe, hK0]; rfl
    have hKn : K = [] := by
      by_contra hKne
      exact sumN_ne_z_of_single (fun t ht => hBD.sK t (List.mem_append_left _ ht))
        (List.pairwise_append.mp hBD.pK).1 (by simpa using hKne) hK0
    have hfl : (children M i).filter (fun d => decide (d < j)) = L :=
      filter_lt_split (children_sorted M i) (show children M i = L ++ j :: [] from hch)
    have : lbQ M ρ μ b i j k = 2 := by
      unfold lbQ
      rw [if_pos ⟨by rw [hchj, hKn]; rfl, hok⟩, hfl, if_pos hP0]
    omega

end

end Ytosk
