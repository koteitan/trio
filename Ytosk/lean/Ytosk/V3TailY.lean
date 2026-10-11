/-
**TailY の証明（2026-10-12、drop-fix）。**

尾の子 t（M で数えられ、M.take x で数えられない、t ≠ x）について:
- x が t の子でなければ、t の topped も isUpg も M.take x と M で同じなので数え方は変わらない。よって t = P_0(x)。
- M.take x で t は「上げの先で topped」。上げの先の行 2 は 1（Z2）。M.take x での t の子は最後が bump(t) なので、
  SibDec・Z1C からすべて bump(t)（`all_bump_of_last`）。したがって M で t の数える子は x だけ（か、なし）で、
  o(t) = ψ_{v(t)}(Ω_{v(x)})（か ψ_{v(t)}(0)）。
- v(x) ≤ v(t): x の行 1 は t の行 1 以下（Z1C）なので v(P_1 x) ≤ v(P_1 t)（`vOpt_par1_le_child`）。
  v(x) = v(P_1 x) + 1 か v(P_1 x) + ω、v(t) = v(P_1 t) + W_t（W_t ≥ ω）。
- よって y = Ω_{v(x)} ≤ Ω_{v(t)} ≤ ψ_{v(t)}(y)。
-/
import Ytosk.V3TailNR
import Ytosk.V3ExpT1A
import Ytosk.V3ExpT1L
import Ytosk.V3ChgS
import Ytosk.V3Pos

namespace Ytosk

open T

/-- **`v(P_1 c) ≤ v(P_1 t)`** for a child `c` of `t` whose row 1 is at most that of `t`. -/
theorem vOpt_par1_le_child {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) {c t : Nat} (h0 : par M 0 c = some t) (h1 : entry M 1 c ≤ entry M 1 t) :
    vOpt ρ (par M 1 c) ≤ vOpt ρ (par M 1 t) := by
  have hfind : par M 1 c = (ancL M t).find? (fun q => decide (entry M 1 q < entry M 1 c)) := by
    rw [par1_find, ancL_eq h0, List.find?_cons]
    simp only [show ¬ entry M 1 t < entry M 1 c by omega, decide_false]
  cases hpt : par M 1 t with
  | none =>
    have hn : par M 1 c = none := by
      rw [hfind, List.find?_eq_none]
      intro q hq
      rw [par1_find, List.find?_eq_none] at hpt
      have := hpt q hq
      simp only [decide_eq_true_eq] at this ⊢
      omega
    rw [hn]
  | some m =>
    have hm := hpt
    rw [par1_find] at hm
    have hmem := List.mem_of_find?_eq_some hm
    have hmt : m < t := par_lt M 1 t m hpt
    have htM : t < M.length := by
      have := par_lt M 0 c t h0
      by_contra hh
      rw [par0_out' (by omega)] at h0
      cases h0
    obtain ⟨S, hS, hSp⟩ := ancL_through (anc0_of_mem_ancL hmem) (by omega)
    have hSn : ∀ s ∈ S, ¬ entry M 1 s < entry M 1 t := by
      intro s hs hlt
      rw [hS, List.find?_append] at hm
      cases hf : S.find? (fun q => decide (entry M 1 q < entry M 1 t)) with
      | none =>
        rw [List.find?_eq_none] at hf
        exact absurd (by simpa using hlt) (hf s hs)
      | some s' =>
        rw [hf] at hm
        simp only [Option.some_or, Option.some.injEq] at hm
        subst hm
        have := (hSp _ (List.mem_of_find?_eq_some hf)).1
        omega
    have hSc : S.find? (fun q => decide (entry M 1 q < entry M 1 c)) = none := by
      rw [List.find?_eq_none]
      intro s hs; have := hSn s hs; simp; omega
    rw [hfind, hS, List.find?_append, hSc, Option.none_or, List.find?_cons]
    by_cases hmc : entry M 1 m < entry M 1 c
    · simp only [decide_eq_true hmc]
      exact le_refl _
    · simp only [decide_eq_false hmc]
      cases hp : (ancL M m).find? (fun q => decide (entry M 1 q < entry M 1 c)) with
      | none => exact z_le _
      | some p =>
        exact le_of_lt (v_find_lt hC hG hR m (by omega) (entry M 1 c) p (by omega) hp)

/-- **A leaf child below a column with rows 1, 2 nonzero** (row 1 at most the parent's, no upgrade) has
`v` at most the parent's. -/
theorem v_le_of_leaf_child {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) {c t : Nat} (hc : c < M.length) (h0 : par M 0 c = some t) (he1t : entry M 1 t ≠ 0)
    (he2t : entry M 2 t ≠ 0) (h1 : entry M 1 c ≤ entry M 1 t) (hch : children M c = [])
    (hu : upg M c = none) : ρ.v c ≤ ρ.v t := by
  have htM : t < M.length := by have := par_lt M 0 c t h0; omega
  have hVot : ∀ q : Nat, q < M.length → isOT (vOpt ρ (par M 1 q)) = true := by
    intro q _
    cases hp : par M 1 q with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 q m hp; omega)
  -- `v(t) = v(P_1 t) + W_t`
  have hY : isOT (sumN (one :: (children M t).map (bumpTerm M ρ t))) = true := by
    apply isOT_sumN
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu
      exact isOT_bumpTerm_of (fun k hk => hG.ot_o k hk) t j
  have hvt := (hC t htM).2
  unfold vRhs at hvt
  rw [if_neg he1t, if_neg he2t, sf_ot (isOT_add (hVot t htM) (isOT_omega hY))] at hvt
  by_cases he1c : entry M 1 c = 0
  · rw [v_z_of_e1L hC hc he1c]; exact z_le _
  have hle := vOpt_par1_le_child hC hG hR h0 h1
  have hvc := (hC c hc).2
  unfold vRhs at hvc
  rw [if_neg he1c] at hvc
  rw [hvt]
  have hW1 : one ≤ omega (sumN (one :: (children M t).map (bumpTerm M ρ t))) := one_le_omega hY
  by_cases he2c : entry M 2 c = 0
  · rw [if_pos he2c, hu] at hvc
    simp only at hvc
    rw [sf_ot (isOT_add (hVot c hc) rfl)] at hvc
    rw [hvc]
    exact le_trans (add_le_add_right one (hVot t htM) rfl hle) (add_le_add_left _ hW1)
  · rw [if_neg he2c, hch] at hvc
    simp only [List.map_nil] at hvc
    have h1ot : isOT (sumN [one]) = true := isOT_sumN _ (by simp; rfl)
    rw [sf_ot (isOT_add (hVot c hc) (isOT_omega h1ot))] at hvc
    rw [hvc]
    refine le_trans (add_le_add_right _ (hVot t htM) (isOT_omega h1ot) hle) (add_le_add_left _ ?_)
    apply omega_le_omega h1ot hY
    have := le_sumN_append [one] ((children M t).map (bumpTerm M ρ t)) (by simp; rfl)
      (fun u hu => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu
        exact isOT_bumpTerm_of (fun k hk => hG.ot_o k hk) t j)
    simpa using this

/-- **`TailY` holds** (the core of `TailNR`): a child `t` counted in `M` after the counted children of
`M.take x` is `P_0(x)`, its only possible counted child is `x`, and `v(x) ≤ v(t)`. -/
theorem tailY_holds {M : Mat} {x : Nat} {ρ : Valn} {rk : Bool → Nat → Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) : TailY M x ρ := by
  intro i hi Lc cs Tl R hcl hclM hxT t ht s y hot
  have hsort : (CL M i).Pairwise (· < ·) := by unfold CL; exact (children_sorted M i).filter _
  have htM : t ∈ CL M i := by rw [hclM]; simp [ht]
  have htc : t ∈ children M i := cl_mem_children htM
  have htlen : t < M.length := (mem_children htc).2
  have htx : t ≠ x := fun h => hxT (h ▸ ht)
  have htx' : t < x := by omega
  have hnT : t ∉ CL (M.take x) i := by
    rw [hcl]; intro h
    rw [hclM, List.append_assoc] at hsort
    have hs2 := (List.pairwise_append.mp hsort).2.2 t (by simpa using h) t (by simp [ht])
    exact lt_irrefl _ hs2
  have hcM : Counted M i t := by
    unfold CL at htM; simpa using (List.mem_filter.mp htM).2
  have hcT : ¬ Counted (M.take x) i t := by
    intro h; apply hnT; unfold CL; rw [List.mem_filter]
    exact ⟨mem_take_children htc htx', by simpa using h⟩
  unfold Counted at hcM hcT
  rw [col_take M htx', bump_take M (by omega : i < x)] at hcT
  have hUT : isUpg (M.take x) t = true ∧ topped (M.take x) t = true := by
    by_contra h; exact hcT ⟨hcM.1, h⟩
  obtain ⟨j, hj, hjt⟩ := (isUpg_take M (by omega) t).mp hUT.1
  have hIU : isUpg M t = true := by
    unfold isUpg; rw [List.any_eq_true]
    exact ⟨j, List.mem_range.mpr (by omega), by simp [hjt]⟩
  have hxt : x ∈ children M t := by
    by_contra hn
    have htop := hUT.2
    rw [topped_take_eq hx htx' hn] at htop
    exact hcM.2 ⟨hIU, htop⟩
  have he2t : entry M 2 t = 1 := by have := upg_target_e2 hjt; have := hZ2 t; omega
  have he1t : entry M 1 t ≠ 0 := (upg_target_val hC hG (by omega) hjt).2.1
  -- the children of `t` other than `x` are bump columns
  have hbump : ∀ c ∈ children M t, c ≠ x → col M c = bump M t := by
    intro c hc hcx
    have hcxl : c < x := by have := (mem_children hc).2; omega
    have hcT' : c ∈ children (M.take x) t := mem_take_children hc hcxl
    have htop := hUT.2
    unfold topped at htop
    cases hl : (children (M.take x) t).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hcT'; simp at hcT'
    | some jj =>
      rw [hl] at htop
      have htop' : col (M.take x) jj = bump (M.take x) t := by simpa using htop
      obtain ⟨L', hL'⟩ := List.getLast?_eq_some_iff.mp hl
      have he2T : entry (M.take x) 2 t = 1 := by rw [entry_take M _ htx']; exact he2t
      have := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x) (Z1C_take hZ1 x)
        he2T hL' htop' c hcT'
      rwa [col_take M hcxl, bump_take M htx'] at this
  have hCLx : ∀ c ∈ CL M t, c = x := by
    intro c hc
    by_contra hcx
    have hcc := cl_mem_children hc
    have hcnt : Counted M t c := by unfold CL at hc; simpa using (List.mem_filter.mp hc).2
    exact hcnt.1 (hbump c hcc hcx)
  have hCL : CL M t = [] ∨ CL M t = [x] := by
    have hs : (CL M t).Pairwise (· < ·) := by unfold CL; exact (children_sorted M t).filter _
    cases hL : CL M t with
    | nil => exact Or.inl rfl
    | cons a l =>
      right
      have ha : a = x := hCLx a (by rw [hL]; simp)
      cases l with
      | nil => rw [ha]
      | cons b l' =>
        exfalso
        have hb : b = x := hCLx b (by rw [hL]; simp)
        rw [hL] at hs
        have := List.rel_of_pairwise_cons hs (List.mem_cons_self)
        omega
  have hot' := o_cl_eq hC hG htlen
  rw [hot] at hot'
  simp only [psi.injEq] at hot'
  obtain ⟨hs, hy, -⟩ := hot'
  rcases hCL with h | h
  · rw [hy, h]; exact z_le _
  · have hox : ρ.o x = psi (ρ.v x) z z :=
      o_nocnt hC hG (by omega) (fun d hd => by have := mem_children hd; omega)
    have hy' : y = psi (ρ.v x) z z := by
      rw [hy, h, List.map_singleton, sumN_singleton (single_o hC hG (by omega)), hox,
        spArg_leaf (A := z) (by simp [summands])]
      rfl
    rw [hy', hs]
    apply psi_le_psi_z
    have hxch : children M x = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro d hd; have := mem_children hd; omega
    exact v_le_of_leaf_child hC hG hR (by omega) (mem_children_iff.mp hxt).2 he1t (by omega)
      (hZ1 t x he2t hxt) hxch (upg_last_none hx)

/-- **`TailNR` holds**: the tail condition of `DropResR` needs no hypothesis. -/
theorem tailNR_holds {M : Mat} {x : Nat} {ρ : Valn} {rk : Bool → Nat → Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) : TailNR M x ρ :=
  tailNR_of hx hC hG (tailNRL_of hx hC hG (tailY_holds hx hR0 hZ2 hSD hZ1 hC hG hR))

end Ytosk
