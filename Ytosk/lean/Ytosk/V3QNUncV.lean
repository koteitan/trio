/-
**t2 の残り QNUncRes を値の残り UpgSibV から（2026-10-17、top）。**

QNUncRes（V3T2QNSig）: t = 2・q ≠ r で q が r の最後の数える子のとき、r の q より前の数えない子 d は
s′ < v(d)。T2SeedCBig（C の場合、V3CBigV）と同じ右からの帰納法で示す。
- r の子はどれも q 以下で、列は (e0 r + 1, e1 r + 1, 1)、P_1 = r（`t_child_col`・`t_col_x`）。
- 数える子 c は CL の o の減少で o(c) ≥ o(q)、よって v(c) ≥ v(q) > s′（`qn_vqlt`）。
- 数えない子 d は上げの的で topped（UAT）。次の兄弟 dn が dn − 1 から上げられるなら v(dn) < v(d)
  （`upg_next_lt`）、上げられないなら UpgSibV で v(dn) ≤ v(d)。どちらも dn の主張から。
-/
import Ytosk.V3CBigV
import Ytosk.V3T2QNSig

namespace Ytosk

open T

set_option linter.unusedSectionVars false

open Classical in
/-- **`QNUncRes` from `UpgSibV`** of `M`. -/
theorem qnUncRes_of_sibV {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (hSib : UpgSibV M ρ) : QNUncRes M ρ r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hC := I.cons
  have hG := I.good
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := hX.loc.2.2.1 q (r + L) hxq Txb
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have he1x : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  -- the children of `r`
  have hle_q : ∀ c ∈ children M r, c ≤ q := by
    intro c hc
    have hpc : par M 0 c = some r := (mem_children_iff.mp hc).2
    have hcL := (mem_children hc).2
    by_contra hlt
    have hcx : c ≠ r + L := by intro h; rw [h] at hpc; rw [hq] at hpc; cases hpc; exact hqr rfl
    have hA : Anc0 M q c := anc_between (anc0_of_par M 0 q (r + L) hq) c (by omega) (by omega)
    have := (anc0_par hA (by omega) hpc).le; omega
  have hcolr : ∀ c ∈ children M r, entry M 1 c = entry M 1 r + 1 ∧ entry M 2 c = 1 ∧ par M 1 c = some r := by
    intro c hc
    have hpc : par M 0 c = some r := (mem_children_iff.mp hc).2
    have hcol := t_child_col hX hpq (by omega) he2q (by omega) hc (hle_q c hc)
    have hcqx := t_col_x hX hpq (by omega) he2q (by omega)
    have h1 : entry M 1 c = entry M 1 r + 1 := by
      have : entry M 1 c = (col M c).2.1 := rfl; rw [this, hcol, hcqx]
    have h2 : entry M 2 c = 1 := by
      have : entry M 2 c = (col M c).2.2 := rfl; rw [this, hcol, hcqx]
    exact ⟨h1, h2, par1_of_child hpc (by omega)⟩
  have hqC : q ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hrL : r < M.length := by omega
  -- an uncounted child is topped and upgraded from the previous column
  have huncnt : ∀ c ∈ children M r, ¬ Counted M r c → topped M c = true ∧ upg M (c - 1) = some c := by
    intro c hc hnc
    have hb : col M c ≠ bump M r := by
      intro h
      have : entry M 1 c = (col M c).2.1 := rfl
      rw [h] at this; simp [bump] at this; have := (hcolr c hc).1; omega
    have hut : isUpg M c = true ∧ topped M c = true := by
      by_contra hn; exact hnc ⟨hb, hn⟩
    refine ⟨hut.2, ?_⟩
    unfold isUpg at hut
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hut.1
    have hu : upg M i = some c := of_decide_eq_true hi
    by_cases hci : c = i + 1
    · rw [hci, Nat.add_sub_cancel]; rw [hci] at hu; exact hu
    · have := hX.toSInv.uat i c hu hci; rw [this] at hut; simp at hut
  -- counted children are above `s′`
  have hvq := qn_vqlt hM hS I hlen hr hq hqr
  have hcntd : ∀ d ∈ children M r, Counted M r d → qnS M ρ r L q < ρ.v d := by
    intro d hd hcnt
    have hdCL : d ∈ CL M r := List.mem_filter.mpr ⟨hd, decide_eq_true hcnt⟩
    obtain ⟨_, hdec⟩ := cl_vals hC hG hrL
    have hle : ρ.o q ≤ ρ.o d := by
      rw [hCL] at hdCL hdec
      rcases List.mem_append.mp hdCL with h | h
      · exact (List.pairwise_append.mp (List.pairwise_map.mp hdec)).2.2 d h q (by simp)
      · simp at h; rw [h]
    have hl := lev_le_of_le hle
    rw [o_cl_eq hC hG (by omega), o_cl_eq hC hG (mem_children hd).2] at hl
    simp only [lev_psi] at hl
    exact lt_of_lt_of_le hvq hl
  have hqcnt : Counted M r q := by
    have : q ∈ CL M r := by rw [hCL]; simp
    exact of_decide_eq_true (List.mem_filter.mp this).2
  -- induction from the right
  have key : ∀ n d, q - d ≤ n → d ∈ children M r → d ≤ q → qnS M ρ r L q < ρ.v d := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro d hn hd hdq
    by_cases hcnt : Counted M r d
    · exact hcntd d hd hcnt
    have hdq' : d < q := by
      rcases Nat.eq_or_lt_of_le hdq with h | h
      · exact absurd (h ▸ hqcnt) hcnt
      · exact h
    have hex : ∃ e, e ∈ children M r ∧ d < e := ⟨q, hqC, hdq'⟩
    let dn := Nat.find hex
    obtain ⟨hdn, hddn⟩ := Nat.find_spec hex
    have hcons : ∀ e ∈ children M r, d < e → dn ≤ e :=
      fun e he hde => Nat.find_min' hex ⟨he, hde⟩
    have hdnq : dn ≤ q := hcons q hqC hdq'
    have hIH := ih (q - dn) (by omega) dn le_rfl hdn hdnq
    by_cases hu : upg M (dn - 1) = some dn
    · have hlt := upg_next_lt hX hC hG hd hdn hddn hcons (hcolr d hd).1 (hcolr d hd).2.1 (hcolr d hd).2.2
        (hcolr dn hdn).2.1 (hcolr dn hdn).2.2 (huncnt d hd hcnt).1 hu
      exact lt_trans hIH hlt
    · have hle := hSib r d dn hd hdn hddn hcons (huncnt d hd hcnt).2 (huncnt d hd hcnt).1 hu
      exact lt_of_lt_of_le hIH hle
  intro d hd hdq hnc
  exact key (q - d) d le_rfl hd hdq.le

end Ytosk
