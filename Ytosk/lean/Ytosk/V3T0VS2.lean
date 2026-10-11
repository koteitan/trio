/-
**3 行・t = 0: VSmallF の残り（D）を v_N(c) の最後の加数の形に（t1-exp の VSFRes2 と同じ形）。**

N の枠 i（数える子を持つので v(i) は変わらない）で、`comps_init_v_nil`（t1-exp の V3ExpT1A、任意の行列で成り立つ。ここに t0c_ の名前で写した）から
v_N(c) の最後の加数より前の部分は段 v(i) で成分を持たない。
-/
import Ytosk.V3T0NoVB

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `t0c_upg_target_val`（groupA の V3GroupA）の写し。 -/
theorem t0c_upg_target_val {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i k : Nat} (hiM : i < M.length)
    (hu : upg M i = some k) :
    k < M.length ∧ entry M 1 k ≠ 0 ∧ entry M 2 k ≠ 0 ∧ par M 1 k = par M 1 i ∧
      ρ.v k = add (vOpt ρ (par M 1 i)) (bumpW M ρ k) ∧ Single (bumpW M ρ k) := by
  obtain ⟨m, hm, hmk, hcol, _⟩ := upg_spec hu
  have hkM := upg_lt hiM hu
  have h1k : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact (upg_e12 hu).1
  have h2k : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
  have hpar : par M 1 k = par M 1 i := by rw [hmk, hm]
  have hmM : m < M.length := by have := par_lt M 1 i m hm; omega
  have hVot : isOT (vOpt ρ (par M 1 k)) = true := by rw [hmk]; exact hG.ot_v m hmM
  have hoot : ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  obtain ⟨sW, yW, hv, hWot, _⟩ := v_bump_form hC hkM h1k h2k hVot hoot
  have hW : bumpW M ρ k = psi sW yW z := by
    have hY : isOT (sumN (one :: (children M k).map (bumpTerm M ρ k))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
        unfold bumpTerm
        split
        · rename_i hjb
          apply isOT_omega; apply isOT_sumN
          intro t' ht'
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ht'
          exact hoot j hj hjb k' hk'
        · rfl
    have hv' := (hC k hkM).2
    unfold vRhs at hv'
    rw [if_neg h1k, if_neg h2k, sf_ot (isOT_add hVot (isOT_omega hY))] at hv'
    rw [hv] at hv'
    -- both sides are `add V (single)`; compare the last summands
    have := congrArg last hv'
    rw [last_add_single] at this
    obtain ⟨s', y', hs'⟩ := (single_omega hY).2
    unfold bumpW; rw [hs']; rw [hs', last_add_single] at this; exact this.symm
  refine ⟨hkM, h1k, h2k, hpar, ?_, ?_⟩
  · rw [hv, hW, hpar]
  · rw [hW]; exact ⟨hWot, _, _, rfl⟩

theorem t0c_upg_target_last {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i k : Nat} (hiM : i < M.length)
    (hu : upg M i = some k) : last (ρ.v k) = bumpW M ρ k := by
  obtain ⟨_, _, _, _, hv, _, s, y, hW⟩ := t0c_upg_target_val hC hG hiM hu
  rw [hv, hW, last_add_single]

/-! ## v の前の部分の成分（V3ExpT1A の comps_init_v_nil の写し、import の名前の衝突を避けるため） -/

theorem t0c_init_app_psi : ∀ (B : T) (a b : T), init (app B (psi a b z)) = B
  | z, _, _ => rfl
  | psi a1 b1 c1, a, b => by
    show init (psi a1 b1 (app c1 (psi a b z))) = psi a1 b1 c1
    have hne : app c1 (psi a b z) ≠ z := by cases c1 <;> simp [app]
    cases hc : app c1 (psi a b z) with
    | z => exact absurd hc hne
    | psi a2 b2 c2 => simp only [init]; rw [← hc, t0c_init_app_psi c1 a b]

/-- `v` grows along the row-1 parent chain: the first row-0 ancestor of `i` below a threshold `t ≤ e1 i`
has a smaller `v`. -/
theorem t0c_v_find_lt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) :
    ∀ i, i < M.length → ∀ t p, t ≤ entry M 1 i →
      (ancL M i).find? (fun q => decide (entry M 1 q < t)) = some p → ρ.v p < ρ.v i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi t p ht hp
  have hpmem := List.mem_of_find?_eq_some hp
  have hpt : entry M 1 p < t := by simpa using List.find?_some hp
  have he1 : entry M 1 i ≠ 0 := by omega
  have hsome : ((ancL M i).find? (fun q => decide (entry M 1 q < entry M 1 i))).isSome := by
    rw [List.find?_isSome]; exact ⟨p, hpmem, by simp; omega⟩
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  have hpar : par M 1 i = some m := by rw [par1_find]; exact hm
  have hmi : m < i := par_lt M 1 i m hpar
  have hvm : ρ.v m < ρ.v i :=
    v_par1_lt_ot hC (fun j hj => hG.ot_v j hj) (fun j hj => hG.ot_o j hj) hR (rk false i) i m (le_refl _) hi he1 hpar
  have hmem := List.mem_of_find?_eq_some hm
  obtain ⟨S, hS, hSp⟩ := ancL_through (anc0_of_mem_ancL hmem) (by omega)
  -- the elements before `m` are at or above row 1 of `i`
  have hSn : ∀ s ∈ S, ¬ entry M 1 s < entry M 1 i := by
    intro s hs hlt
    rw [hS, List.find?_append] at hm
    cases hf : S.find? (fun q => decide (entry M 1 q < entry M 1 i)) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simpa using hlt) (hf s hs)
    | some s' =>
      rw [hf] at hm
      simp only [Option.some_or, Option.some.injEq] at hm
      subst hm
      have := (hSp _ (List.mem_of_find?_eq_some hf)).1
      omega
  rw [hS, List.find?_append] at hp
  have hSt : S.find? (fun q => decide (entry M 1 q < t)) = none := by
    rw [List.find?_eq_none]
    intro s hs; have := hSn s hs; simp; omega
  rw [hSt, Option.none_or, List.find?_cons] at hp
  by_cases hmt : entry M 1 m < t
  · simp only [decide_eq_true hmt] at hp
    cases hp; exact hvm
  · simp only [decide_eq_false hmt] at hp
    exact lt_trans' (ih m hmi (by omega) t p (by omega) hp) hvm

/-- **`v(P_1 c) ≤ v(P_0 c)`.** -/
theorem t0c_v_par1_le_par0 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) {c i p : Nat} (hc : c < M.length) (h0 : par M 0 c = some i) (h1 : par M 1 c = some p) :
    ρ.v p ≤ ρ.v i := by
  have hic : i < c := par_lt M 0 c i h0
  rw [par1_find, ancL_eq h0, List.find?_cons] at h1
  by_cases hit : entry M 1 i < entry M 1 c
  · simp only [decide_eq_true hit] at h1
    cases h1; exact (le_iff _ _).mpr (Or.inr rfl)
  · simp only [decide_eq_false hit] at h1
    exact (le_iff _ _).mpr (Or.inl (t0c_v_find_lt hC hG hR i (by omega) _ p (by omega) h1))

/-- The prefix of `add V (single)` has no components at a level at or above `V`. -/
theorem t0c_comps_init_add_nil {u V a b : T} (hVot : isOT V = true) (hVu : V ≤ u) :
    comps u (init (add V (psi a b z))) = [] := by
  obtain ⟨B, X, hV, _, hadd⟩ := add_prefix a b V
  rw [hadd, t0c_init_app_psi]
  apply comps_eq_nil_of_lev
  intro q hq
  have hqV : q ∈ summands V := by rw [hV, summands_app]; exact List.mem_append_left _ hq
  obtain ⟨s, y, rfl⟩ := mem_summands hq
  show s < u
  have h1 : psi s y z ≤ head V := summands_le_head hVot _ hqV
  exact lt_of_lt_of_le (sub_lt_psi s y z) (le_trans h1 (le_trans (head_le_self V) hVu))

/-- **The prefix of `v(c)` has no components at the level `v(P_0 c)`.** -/
theorem t0c_comps_init_v_nil {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) {c i : Nat} (hc : c < M.length) (h0 : par M 0 c = some i) :
    comps (ρ.v i) (init (ρ.v c)) = [] := by
  have hic : i < c := par_lt M 0 c i h0
  have hVot : isOT (vOpt ρ (par M 1 c)) = true := vOpt_ot hG hc
  have hVu : vOpt ρ (par M 1 c) ≤ ρ.v i := by
    cases hp : par M 1 c with
    | none => exact z_le _
    | some p => exact t0c_v_par1_le_par0 hC hG hR hc h0 hp
  have hv := (hC c hc).2
  unfold vRhs at hv
  by_cases he1 : entry M 1 c = 0
  · rw [if_pos he1] at hv; rw [hv]; rfl
  rw [if_neg he1] at hv
  by_cases he2 : entry M 2 c = 0
  · rw [if_pos he2] at hv
    cases hu : upg M c with
    | none =>
      rw [hu] at hv; simp only at hv
      rw [sf_ot (isOT_add hVot rfl)] at hv
      rw [hv, show one = psi z z z from rfl]
      exact t0c_comps_init_add_nil hVot hVu
    | some k =>
      rw [hu] at hv; simp only at hv
      obtain ⟨_, _, _, _, _, hWs⟩ := t0c_upg_target_val hC hG hc hu
      obtain ⟨hWot, sW, yW, hW⟩ := hWs
      rw [t0c_upg_target_last hC hG hc hu, hW] at hv
      rw [sf_ot (isOT_add hVot (by rw [← hW]; exact hWot))] at hv
      rw [hv]; exact t0c_comps_init_add_nil hVot hVu
  · rw [if_neg he2] at hv
    have hY : isOT (sumN (one :: (children M c).map (bumpTerm M ρ c))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
        exact isOT_bumpTerm_of (fun k hk => hG.ot_o k hk) c j
    obtain ⟨_, sW, yW, hW⟩ := single_omega hY
    rw [hW, sf_ot (isOT_add hVot (by rw [← hW]; exact isOT_omega hY))] at hv
    rw [hv]; exact t0c_comps_init_add_nil hVot hVu

/-- **Residual (D) in the last-summand form**: only the components of the last summand of the new `v(c)` matter
(the earlier part has no components at the level `v(i)`, `comps_init_v_nil` in `N`). -/
def T0VSResD2 : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (last (σ.v c)), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))

theorem t0VSResD_of (h : T0VSResD2) : T0VSResD := by
  intro M ρ rk r L n σ rkN hctx i Lc c R hi hc hCL hv g hg
  obtain ⟨_, _, I, _, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcM : c ∈ children M i := cl_mem_children hcCL
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  -- the frame of `i` in `N`: `c` is still a child of `i`, and `v(i)` does not change
  have hig : par M 0 r ≠ some i ∨ par M 0 r = some i := by tauto
  have hcN0 : par (TRIO.gexp M r L 0 0 n) 0 c = some i := by
    have hcN : c ∈ children (TRIO.gexp M r L 0 0 n) i := by
      rcases hig with hig | hig
      · rw [children_pre0 hlen hL hp hn hi hig]; exact hcM
      · rw [children_g0 hlen hL hp hn hig]; exact List.mem_append_left _ hcM
    exact (mem_children_iff.mp hcN).2
  have hcNl : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hinit := t0c_comps_init_v_nil hCN hGN hRN hcNl hcN0
  have hvi : σ.v i = ρ.v i := by
    have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
      (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good
      (cons_of_rk (rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)))
      (fun j hj hd => (chg_off (show r + L + 1 = M.length from hlen) I.cons I.good
        (cons_of_rk (rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)))
        (rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)) j hj).2 hd) hCN hRN
    rw [(hvC i (by rw [hlN]; omega)).2 (fun h => ?_), tau_v_lt hi]
    have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
    exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
      (by omega) h.2 hcM hccnt
  rw [hvi] at hinit
  rw [← init_app_last (σ.v c), comps_app, hinit, List.nil_append] at hg
  exact h M ρ rk r L n σ rkN hctx i Lc c R hi hc hCL hv g hg

/-- **`hExp` for `t = 0`** with the `VSmallF` residual in the last-summand form. -/
theorem hExp_t0_mainN2
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hIV : T0IVRes) (hII : T0IIRes) (hG : T0VSResG) (hS : T0ShapeR3) (hVS : T0VSResD2)
    (hRest : T0VSResD → T0RestH2) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W) (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN :=
  hExp_t0_mainN hLast hIV hII hG hS (hRest (t0VSResD_of hVS)) hC1 hC1W hCT

end Ytosk
