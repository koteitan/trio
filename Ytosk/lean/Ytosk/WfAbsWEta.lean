/-
**Bad2・t = 2 の吸収を ◁ の許容つき版で置き換える道具（2026-10-31, WfAbsW）。**

AbsWN M M[n] は 36 列の標準形の Bad2 で偽（WfSrcC3Cex）。その行列で M[2] の i = 32 の v と o は `◁`（Lhd z）で
下がらないが、許容 η = V = v(P₁ i) をつけた `Lhd V` では下がり、親 m = P₀ i = P₁ i（v(m) = V は変わらない、
i は m の最後の数える子、i は数える子を持たない）の o(m) で `Lhd z` に戻る（tmp/wf/WfAbsW/notes.md）。

- `lhd_mono_eta`: `Lhd z b a → Lhd η b a`。`lhd_of_compsSub`: 成分が η の成分なら `Lhd η`。
- `lhd_sub_eta`: `Lhd η a' a → Lhd η ψ_{a'}(0) ψ_a(0)`。`lhd_psi_dis`: `Lhd V b' b → Lhd z ψ_V(b') ψ_V(b)`（許容の解消）。
- `lhd_add_eta`: 吸収つきの和 `V + w′ ◁_V V + w`（吸収の仮定なし）。
- `v_bump_lhdV`: bump 型の v の枠で、AbsWN なしに `Lhd (v(P₁ i)) (σ.v i) (ρ.v i)`。
- `o_frame_lhdV`: 親の o の枠: 最後の数える子 c が `Lhd (v(i))` で下がり、c の o の引数が 0 なら、`Lhd z (σ.o i) (ρ.o i)`。
-/
import Ytosk.V3DepLhd
import Ytosk.V3DropMain
import Ytosk.V3DropAsm
import Ytosk.TwoRowF

namespace Ytosk.WfAbsW

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `Lhd z` is the strongest allowance. -/
theorem lhd_mono_eta {η b a : T} (h : Lhd z b a) : Lhd η b a := by
  refine ⟨h.1, fun u c h1 h2 g hg => ?_⟩
  obtain ⟨y, hy, hgy⟩ := h.2 u c h1 h2 g hg
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ hy, hgy⟩
  · have : y = z := by simpa [Gc, comps] using hy
    subst this
    exact ⟨z, List.mem_append_right _ (by simp [Gc]), hgy⟩

/-- Below, with all components among those of the allowance. -/
theorem lhd_of_compsSub {η b a : T} (hlt : b < a) (h : ∀ u, ∀ g ∈ comps u b, g ∈ comps u η) :
    Lhd η b a :=
  ⟨hlt, fun u c _ _ g hg => ⟨g, List.mem_append_right _ (List.mem_cons_of_mem _ (h u g hg)), le_refl _⟩⟩

theorem comps_head_sub {u a b c g : T} (hg : g ∈ comps u (psi a b z)) : g ∈ comps u (psi a b c) := by
  simp only [comps, List.mem_append] at hg ⊢
  rcases hg with h | h
  · exact Or.inl h
  · simp at h

theorem comps_rest_sub {u a b c g : T} (hg : g ∈ comps u c) : g ∈ comps u (psi a b c) := by
  simp only [comps, List.mem_append]; exact Or.inr hg

theorem comps_of_summand {u g : T} : ∀ (X t : T), t ∈ summands X → g ∈ comps u t → g ∈ comps u X
  | z, t, ht, _ => by simp [summands] at ht
  | psi a b c, t, ht, hg => by
    simp only [summands, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact comps_head_sub hg
    · exact comps_rest_sub (comps_of_summand c t ht hg)

/-- **Collapse with the allowance discharged**: the allowance `V` is the collapsing level. -/
theorem lhd_psi_dis {V b0 b : T} (h : Lhd V b0 b) : Lhd z (psi V b0 z) (psi V b z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h.1⟩, fun u c h1 h2 => ?_⟩
  obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
  intro x hx
  have hsub : ∀ w ∈ comps u (psi V c0 z), w ∈ comps u (psi V c0 c1) := by
    intro w hw; simp only [comps, List.mem_append] at hw ⊢; left; simpa using hw
  rcases (le_iff _ _).mp hc1 with hc1 | rfl
  · simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · rename_i hvu
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨c0, List.mem_append_left _ (by simp [comps, hvu]), le_of_lt hc1⟩
        · obtain ⟨y, hy, hxy⟩ := h.2 u c0 hc1 hc2 x hx
          rcases List.mem_append.mp hy with hy | hy
          · exact ⟨y, List.mem_append_left _ (by simp [comps, hvu, hy]), hxy⟩
          · simp only [Gc, List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact ⟨z, List.mem_append_right _ (by simp [Gc]), hxy⟩
            · exact ⟨y, List.mem_append_left _ (by simp [comps, hvu, hy]), hxy⟩
        · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
    · simp at hx
  · exact ⟨x, List.mem_append_left _ (hsub x hx), le_refl _⟩

/-- **Collapse of the subscript** (the `sub` case of Lemma 3.5, with any allowance). -/
theorem lhd_sub_eta {η a' a : T} (hl : Lhd η a' a) : Lhd η (psi a' z z) (psi a z z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inl hl.1, fun u c h1 h2 => ?_⟩
  obtain ⟨v, c0, c1, rfl, hv1, hv2⟩ := between_sub h1 h2
  intro x hx
  simp only [comps, List.mem_append] at hx
  rcases hx with hx | hx
  · split at hx
    · simp at hx
    · rename_i hau
      have hvu : ¬ lt v u = true := fun h => hau (lt_of_le_of_lt hv1 h)
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨z, List.mem_append_right _ (by simp [Gc]), le_refl _⟩
      · simp at hx
      · rcases (le_iff _ _).mp hv1 with hv1 | rfl
        · obtain ⟨y, hy, hxy⟩ := hl.2 u v hv1 hv2 x hx
          refine ⟨y, ?_, hxy⟩
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ (by simp [comps, hvu, hy])
          · exact List.mem_append_right _ hy
        · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
  · simp at hx

theorem lhd_of_summands_eta {η X w : T} (hlt : X < w) (hle : ∀ t ∈ summands X, t ≤ X)
    (h : ∀ t ∈ summands X, Lhd η t w) : Lhd η X w := by
  refine ⟨hlt, fun u c h1 h2 g hg => ?_⟩
  obtain ⟨t, ht, hgt⟩ := comps_sub_summands u X g hg
  exact (h t ht).2 u c (lt_of_le_of_lt (hle t ht) h1) h2 g hgt

/-- **Sum with absorption, the allowance version**: `X + w′ ◁_η X + w` when `w′ ◁_η w` and the components of
`X` are components of `η` (no condition on the absorbed summands). -/
theorem lhd_add_eta {η s' y' s y : T} (hw : Lhd η (psi s' y' z) (psi s y z)) :
    ∀ (X : T), isOT X = true → isOT (add X (psi s' y' z)) = true →
      (∀ u, ∀ g ∈ comps u X, g ∈ comps u η) →
      Lhd η (add X (psi s' y' z)) (add X (psi s y z))
  | z, _, _, _ => by simpa using hw
  | psi a b c, hV, hot, hR => by
    have hle : psi s' y' z ≤ psi s y z := le_of_lt hw.1
    rw [add_psi_psi, add_psi_psi]
    by_cases h1 : psi a b z < psi s' y' z
    · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 hle)]; exact hw
    · rw [if_neg h1]
      by_cases h2 : psi a b z < psi s y z
      · rw [if_pos h2]
        have hot' : isOT (psi a b (add c (psi s' y' z))) = true := by
          rw [add_psi_psi, if_neg h1] at hot; exact hot
        have hcb : ∀ t ∈ summands c, t ≤ psi a b z := by
          intro t ht
          have := summands_le_head hV t (by simp [summands, ht])
          simpa [head] using this
        apply lhd_of_summands_eta
        · rw [psi_lt_psi_z_iff] at h2 ⊢; exact h2
        · intro t ht
          have := summands_le_head hot' t ht
          exact le_trans this (by simp only [head]; exact psi_le_psi_rest (z_le _))
        · intro t ht
          simp only [summands, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact lhd_of_compsSub h2 (fun u g hg => hR u g (comps_head_sub hg))
          · rcases summands_add_single c t ht with rfl | ⟨htc, htn⟩
            · exact hw
            · exact lhd_of_compsSub (lt_of_le_of_lt (hcb t htc) h2)
                (fun u g hg => hR u g (comps_rest_sub (comps_of_summand c t htc hg)))
      · rw [if_neg h2]
        have hc : isOT c = true := isOT_rest hV
        have hot' : isOT (add c (psi s' y' z)) = true := by
          rw [add_psi_psi, if_neg h1] at hot; exact isOT_rest hot
        have ih := lhd_add_eta hw c hc hot' (fun u g hg => hR u g (comps_rest_sub hg))
        exact lhd_app (psi a b z) ih

theorem v_bump_lhdV {M N : Mat} {ρ σ : Valn} {i j : Nat} {L : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = omega G) (hbjN : bumpTerm N σ i j = omega G')
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : BRelS G' G) (hlt : G' < G)
    (hTD : BumpTermDec M ρ) :
    Lhd (vOpt ρ (par M 1 i)) (σ.v i) (ρ.v i) := by
  set V := vOpt ρ (par M 1 i) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef]
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  set Lb := L.map (bumpTerm M ρ i) with hLb
  have hLbot : ∀ t ∈ Lb, isOT t = true := fun t ht => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hmapM : (children M i).map (bumpTerm M ρ i) = Lb ++ [omega G] := by
    rw [hchM, List.map_append, List.map_singleton, hbjM]
  have hmapN : (children N i).map (bumpTerm N σ i) = Lb ++ [omega G'] := by
    rw [hchN, List.map_append, List.map_singleton, hbjN, List.map_congr_left hbL]
  set Pl := nzs Lb with hPl
  have hsumM : sumN (one :: (Lb ++ [omega G])) = sumN (one :: Pl ++ [omega G]) := by
    rw [sumN_nzs (l := one :: (Lb ++ [omega G])) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · simp at ht; rw [ht]; exact isOT_omega hGot)]
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one, omega_ne_z G]
    rw [hPl, nzs]; simp
  have hsumN : sumN (one :: (Lb ++ [omega G'])) = sumN (one :: Pl ++ [omega G']) := by
    rw [sumN_nzs (l := one :: (Lb ++ [omega G'])) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · simp at ht; rw [ht]; exact isOT_omega hG'ot)]
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one, omega_ne_z G']
    rw [hPl, nzs]; simp
  have hsP : ∀ q ∈ Pl, Single q := by
    intro q hq
    rw [hPl, nzs, List.mem_filter] at hq
    obtain ⟨hq, hqz⟩ := hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    unfold bumpTerm at hqz ⊢
    by_cases hb : col M d = bump M i
    · rw [if_pos hb]
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    · rw [if_neg hb] at hqz; simp at hqz
  have hdecP := hTD i h1 h2
  rw [hmapM, nzs_append, nzs_single (omega_ne_z G)] at hdecP
  have hpre := List.pairwise_append.mp hdecP
  have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
  have hPt : ∀ q ∈ Pl, omega G ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
  have hPot : ∀ t ∈ one :: Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact (hsP t ht).1
  have hp'ot : isOT (sumN (one :: Pl ++ [omega G'])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot)
  have hpot : isOT (sumN (one :: Pl ++ [omega G])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact isOT_omega hGot)
  have ev : ρ.v i = add V (omega (sumN (one :: Pl ++ [omega G]))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hmapM, hsumM, sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev' : σ.v i = add V (omega (sumN (one :: Pl ++ [omega G']))) := by
    rw [(hCN i hiN).2]; unfold vRhs
    rw [he1, he2, if_neg h1, if_neg h2, hV, hmapN, hsumN, sf_ot (isOT_add hVot (isOT_omega hp'ot))]
  have hp := brelS_p hsP hpP hPt (single_omega hG'ot) (single_omega hGot) (brelS_omega hG'ot hGot hS)
  have hW := brelS_lhdE (brelS_omega hp'ot hpot hp)
  have hbW : bumpW M ρ i = omega (sumN (one :: Pl ++ [omega G])) := by
    unfold bumpW; rw [hmapM, hsumM]
  have hWl : Lhd z (omega (sumN (one :: Pl ++ [omega G']))) (omega (sumN (one :: Pl ++ [omega G]))) :=
    lhd_of_lhdE_lt hW (omega_lt_omega hp'ot hpot
      (sumN_snoc_lt hPot hPot (isOT_omega hG'ot) (isOT_omega hGot) (le_refl _) (omega_lt_omega hG'ot hGot hlt)))
  rw [ev', ev]
  obtain ⟨_, s', y', hs'⟩ := single_omega hp'ot
  obtain ⟨_, s, y, hs⟩ := single_omega hpot
  rw [hs', hs] at hWl ⊢
  exact lhd_add_eta (lhd_mono_eta hWl) V hVot
    (by rw [← hs']; exact isOT_add hVot (isOT_omega hp'ot)) (fun u g hg => hg)

/-- One step of `sp` on an argument-free summand. -/
theorem step_y0 (a b s c : T) : step a b s z c = add b (psi s z z) := by
  unfold step; rw [if_neg]; intro h; exact T.not_lt_z _ h.1

/-- **The parent `o` frame with the allowance discharged**: the counted children of `i` are `Lc ++ [c]` in
`M` and `N`, `v(i)` and the `o` of `Lc` do not change, the last child `c` has argument `0` in both and goes down
by `◁` with the allowance `v(i)`. Then `o(i)` goes down by `◁` (allowance `0`). -/
theorem o_frame_lhdV {M N : Mat} {ρ σ : Valn} {i c : Nat} {Lc : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : GoodOT N σ)
    (hiM : i < M.length) (hiN : i < N.length) (hv : σ.v i = ρ.v i)
    (hclN : CL N i = Lc ++ [c]) (hclM : CL M i = Lc ++ [c])
    (hsame : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hl : Lhd (ρ.v i) (σ.o c) (ρ.o c))
    (hs : ∃ s, ρ.o c = psi s z z) (hs' : ∃ s', σ.o c = psi s' z z)
    (hpN0 : ((CL N i).map σ.o).Pairwise (fun a b => b ≤ a)) :
    Lhd z (σ.o i) (ρ.o i) := by
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hclM]; simp))).2
  have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
  obtain ⟨s, hsy⟩ := hs
  obtain ⟨s', hs'y'⟩ := hs'
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  have hformM := o_last_form hC hiM hvot hclM (fun d hd => single_o hC hG
    (mem_children (cl_mem_children hd)).2) hpM hsy
  have hformN := o_last_form hCN hiN (by rw [hv]; exact hvot) hclN (fun d hd => single_oT hCN hGN
    (mem_children (cl_mem_children hd)).2) hpN0 hs'y'
  have hLm : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hsame
  rw [hLm, hv] at hformN
  rw [hformN, hformM, step_y0, step_y0]
  set a := ρ.v i
  set B := spArg a z (sumN (Lc.map ρ.o)) with hB
  rw [hclM] at hsM hpM
  have hpM' := hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hpM'
  have hsL : ∀ t ∈ Lc.map ρ.o, Single t := fun t ht =>
    hsM t (by simp only [List.map_append]; exact List.mem_append_left _ ht)
  have hp1 := List.pairwise_append.mp hpM'
  have hLs := sumN_dec (Lc.map ρ.o) hsL hp1.1
  have hBc : ∀ q ∈ summands B, psi s z z ≤ q := by
    intro q hq
    apply spArg_summands_ge ⟨s, z, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hsy]; exact hp1.2.2 q hq _ (by simp)
    · simp [summands]
    · exact hq
  have hlt' : psi s' z z < psi s z z := by rw [← hsy, ← hs'y']; exact hl.1
  rw [add_eq_app_of_ge ⟨s, z, rfl⟩ B hBc,
    add_eq_app_of_ge ⟨s', z, rfl⟩ B (fun q hq => le_trans (le_of_lt hlt') (hBc q hq))]
  rw [hsy, hs'y'] at hl
  exact lhd_psi_dis (lhd_app B hl)

/-- **The bad column, argument-free**: `o(i) = ψ_{v(i)}(0)` in `M` and `N` and `v(i)` goes down with the allowance
`V`, so `o(i)` does too. -/
theorem o_noarg_lhdV {V : T} {ρ σ : Valn} {i : Nat} (hl : Lhd V (σ.v i) (ρ.v i))
    (hoM : ρ.o i = psi (ρ.v i) z z) (hoN : σ.o i = psi (σ.v i) z z) : Lhd V (σ.o i) (ρ.o i) := by
  rw [hoM, hoN]; exact lhd_sub_eta hl

/-- **The parent of a bad absorption column**: at a bump-type column `i` whose absorption may fail, with
`m = P₀ i = P₁ i`, no counted children at `i` (in `M` and `N`), `i` the last counted child of `m` (in both), and `v(m)`
and the `o` of the earlier counted children of `m` unchanged, `o(m)` goes down by `◁`. No absorption hypothesis. -/
theorem bad_parent_lhd {M N : Mat} {ρ σ : Valn} {i j m : Nat} {L Lc : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : GoodOT N σ)
    (hiM : i < M.length) (hiN : i < N.length) (hmM : m < M.length) (hmN : m < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = omega G) (hbjN : bumpTerm N σ i j = omega G')
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : BRelS G' G) (hlt : G' < G)
    (hTD : BumpTermDec M ρ)
    (hp1 : par M 1 i = some m) (hclMi : CL M i = []) (hclNi : CL N i = [])
    (hclM : CL M m = Lc ++ [i]) (hclN : CL N m = Lc ++ [i]) (hvm : σ.v m = ρ.v m)
    (hsame : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hpN0 : ((CL N m).map σ.o).Pairwise (fun a b => b ≤ a)) :
    Lhd z (σ.o m) (ρ.o m) := by
  have hvl := v_bump_lhdV hC hG hCN hiM hiN h1 h2 he1 he2 hV hchM hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
  rw [hp1] at hvl
  have hoM : ρ.o i = psi (ρ.v i) z z :=
    o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclMi)
  have hoN : σ.o i = psi (σ.v i) z z :=
    o_of_no_counted hCN hiN (hGN.ot_v i hiN) (no_cnt_of_cl_nil hclNi)
  have hol := o_noarg_lhdV hvl hoM hoN
  exact o_frame_lhdV hC hG hCN hGN hmM hmN hvm hclN hclM hsame (by simpa [vOpt] using hol)
    ⟨_, hoM⟩ ⟨_, hoN⟩ hpN0

/-! ## The replacement field `AbsWNx` -/

/-- The weak absorption of `AbsWN` at one column `i`. -/
def AbsAt (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z → ¬ q < bumpW N σ i → q < bumpW M ρ i →
    Lhd z q (bumpW M ρ i)

/-- **The shape of a column where the absorption may fail** (measured: every failure of `AbsWN M M[n]` on the
t = 2 sets and the graft families around the 36-column matrix has this shape): `m = P₀ i = P₁ i`, `i` has no
counted children in `M` and `N`, `i` is the last counted child of `m` in both, the earlier counted children of `m`
and `v(m)` do not change, and no column upgrades to `i`. -/
def BadAbsShape (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  ∃ m Lc, par M 0 i = some m ∧ par M 1 i = some m ∧ CL M i = [] ∧ CL N i = [] ∧
    CL M m = Lc ++ [i] ∧ CL N m = Lc ++ [i] ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧ σ.v m = ρ.v m ∧
    (∀ j, upg M j ≠ some i)

/-- **The replacement of `AbsWN`**: at every bump-type column before `bnd`, the absorption or the bad shape. -/
def AbsWNx (M N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → AbsAt M N ρ σ i ∨ BadAbsShape M N ρ σ i

theorem AbsWN.toX {M N : Mat} {bnd : Nat} {ρ σ : Valn} (h : AbsWN M N bnd ρ σ) : AbsWNx M N bnd ρ σ :=
  fun i hi h1 h2 => Or.inl (h i hi h1 h2)

/-- **The two outcomes at a bump-type column under `AbsWNx`**: `v(i)` goes down by `◁` (absorption), or the
parent `m` of the bad shape has `o(m)` going down by `◁` and `v(i)`, `o(i)` go down with the allowance `v(m)`. -/
theorem bump_col_of_absWNx {M N : Mat} {ρ σ : Valn} {i j : Nat} {L : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : GoodOT N σ)
    (hiM : i < M.length) (hiN : i < N.length) (hlenN : M.length ≤ N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = omega G) (hbjN : bumpTerm N σ i j = omega G')
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : BRelS G' G) (hlt : G' < G)
    (hTD : BumpTermDec M ρ)
    (hpN : ∀ m, m < N.length → ((CL N m).map σ.o).Pairwise (fun a b => b ≤ a))
    (hA : AbsAt M N ρ σ i ∨ BadAbsShape M N ρ σ i) :
    Lhd z (σ.v i) (ρ.v i) ∨
      ∃ m, par M 0 i = some m ∧ par M 1 i = some m ∧ Lhd z (σ.o m) (ρ.o m) ∧
        Lhd (ρ.v m) (σ.v i) (ρ.v i) ∧ Lhd (ρ.v m) (σ.o i) (ρ.o i) := by
  rcases hA with hA | ⟨m, Lc, hp0, hp1, hclMi, hclNi, hclM, hclN, hsame, hvm, _⟩
  · exact Or.inl (v_bump_lhdW hC hG hCN hiM hiN h1 h2 he1 he2 hV hchM hchN hbL hbjM hbjN hGot hG'ot hS hlt
      hTD hA)
  · right
    have hmi : m < i := par_lt M 0 i m hp0
    have hvl := v_bump_lhdV hC hG hCN hiM hiN h1 h2 he1 he2 hV hchM hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
    rw [hp1] at hvl
    have hoM : ρ.o i = psi (ρ.v i) z z :=
      o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclMi)
    have hoN : σ.o i = psi (σ.v i) z z :=
      o_of_no_counted hCN hiN (hGN.ot_v i hiN) (no_cnt_of_cl_nil hclNi)
    refine ⟨m, hp0, hp1, ?_, by simpa [vOpt] using hvl, by simpa [vOpt] using o_noarg_lhdV hvl hoM hoN⟩
    exact bad_parent_lhd hC hG hCN hGN hiM hiN (by omega) (by omega) h1 h2 he1 he2 hV hchM hchN hbL hbjM hbjN
      hGot hG'ot hS hlt hTD hp1 hclMi hclNi hclM hclN hvm hsame (hpN m (by omega))

end Ytosk.WfAbsW
