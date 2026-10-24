/-
**弱い葉の節で v(r) > v(g) の場合（2026-10-25、Bad2・t = 0 の r = g 用）。**

旧の `weak_seed`（V3T0ArgB）は v(r) ≤ v(g) を仮定して、高い部分が同じ（A 型）ことから RClaim を出していた。
Bad2 の r = g では v(r) > v(g) で、引数 X′・X はどちらも低い部分がない（B0 型）。

- `copies_lhd_arg`: 写しだけの状態 `B′ = spArg a B (ψ_v(Y0)·m)` は引数の段で `B′ ◁ X`（基本列の項、`m ≥ 1`）。
- `weak_seed_hi`: `succ a ≤ w′` のとき、`ψ_a(X′)` は標準形、`ψ_a(X′) ◁ ψ_a(X)`（`s1_core_weak`）、RClaim は
  `relR_of_subU`（下の端を `B′` から `X′ = B′ + ψ_{w′}(0)` に上げる）で出る。`w′` の成分は WCS により `Ω_1` 未満
  （したがって `X′` 未満）か、`a` の成分以下（RClaim の前提で片づく）。引数の段の `X′ ◁ X` は使わない。
-/
import Ytosk.V3T0BadSeed

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The copies-only state drops by `◁` in the argument** (`m ≥ 1`): it is a term of the fundamental sequence of
`spArg a B (ψ_v(Y0 + 1))`. -/
theorem copies_lhd_arg {a B v Y0 : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q) :
    Lhd z (spArg a B (mulT (psi v Y0 z) m)) (spArg a B (psi v (app Y0 one) z)) := by
  have hArg : spArg a B (psi v (app Y0 one) z) ≠ z := by
    intro h
    have := lt_spArg a (b := B) hX (by simp)
    rw [h] at this; exact T.not_lt_z _ this
  have hfsM : ∃ k, psi a (spArg a B (mulT (psi v Y0 z) m)) z =
      fs (psi a (spArg a B (psi v (app Y0 one) z)) z) (natT k) := by
    by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
    · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
      · exact ⟨m - 1, (t0_frame_swallow (n := m) hm hX hO htr hbad.1 hbad.2).symm⟩
      · exact ⟨m, (t0_frame_trig (n := m) hm hOld hX hO htr hbad).symm⟩
    · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
        have h1 := isOT_arg hOld
        rw [spArg_single] at h1; unfold step at h1
        rw [if_neg htr, add_eq_app_of_ge ⟨_, _, rfl⟩ _ hBX] at h1
        exact h1
      exact ⟨m, (t0_frame_notrig m hXapp htr hBX).symm⟩
  obtain ⟨k, hk⟩ := hfsM
  obtain ⟨P, hP⟩ := step_succ_end (a := a) hX hBX
  rw [← spArg_single] at hP
  obtain ⟨hXz, hXs, hXc⟩ := cof_app_succ_end P v Y0
  rw [← hP] at hXz hXs hXc
  rw [fs_psi_omega hXz hXs hXc] at hk
  simp only [psi.injEq] at hk
  rw [hk.2.1]
  apply lhd_natT_z
  apply lhd_fs (isOT_arg hOld)
  unfold ValidLt; rw [hXc]; trivial

/-- **The weak seed at a node with `v > a`** (`succ a ≤ w′ < v`): standard, `◁`, and `RClaim` (class B0). -/
theorem weak_seed_hi {a B v Y0 w' : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hW : WkVA w' v) (hWC : WCS a w') (hc' : isOT (psi w' z z) = true) (haw : succ a ≤ w') :
    isOT (psi a (spArg a (spArg a B (mulT (psi v Y0 z) m)) (psi w' z z)) z) = true ∧
      Lhd z (psi a (spArg a (spArg a B (mulT (psi v Y0 z) m)) (psi w' z z)) z)
        (psi a (spArg a B (psi v (app Y0 one) z)) z) ∧
      ∀ (U : T → Prop) (ρ σ : Valn) (i : Nat), ρ.o i = psi a (spArg a B (psi v (app Y0 one) z)) z →
        σ.o i = psi a (spArg a (spArg a B (mulT (psi v Y0 z) m)) (psi w' z z)) z → RClaimU U ρ σ i := by
  have hlhd := s1_core_weak hm hOld hX hO hBX hW hWC hc'
  set O := psi v Y0 z with hOdef
  set B' := spArg a B (mulT O m) with hB'
  set X := spArg a B (psi v (app Y0 one) z) with hXdef
  have hOX : O < psi v (app Y0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  have hB'O : ∀ q ∈ summands B', O ≤ q :=
    spArg_summands_ge ⟨v, Y0, rfl⟩ _ B (isOT_mulT hO ⟨_, _, rfl⟩ m)
      (fun q hq => by rw [summands_mulT ⟨_, _, rfl⟩ m q hq])
      (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
  have hleafO : psi w' z z < O := psi_lt_psi_z_iff.mpr (Or.inl hW.1)
  have hB'leaf : ∀ q ∈ summands B', psi w' z z ≤ q := fun q hq => le_trans (le_of_lt hleafO) (hB'O q hq)
  have hnew : spArg a B' (psi w' z z) = app B' (psi w' z z) := by
    rw [spArg_single, step_leaf]; exact add_eq_app_of_ge ⟨w', z, rfl⟩ B' hB'leaf
  have hmid := T0ArgB.copies_ot hm hOld hX hO hBX
  change isOT (psi a B' z) = true at hmid
  have harg := isOT_app_of (isOT_arg hmid) hc' hB'leaf
  have haot : isOT a = true := isOT_sub hOld
  have hθw : psi (succ a) z z ≤ psi w' z z := psi_le_psi_z haw
  have hX'w : psi w' z z ≤ app B' (psi w' z z) := le_app_of_ge B' hB'leaf
  have hone : psi one z z ≤ psi (succ a) z z :=
    psi_le_psi_z (one_le_of_ne_z (fun h => T.not_lt_z a (h ▸ lt_succ_self a)))
  have hOm1 : Om one ≤ app B' (psi w' z z) := le_trans hone (le_trans hθw hX'w)
  have haθ : psi a z z < psi (succ a) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self a))
  have haw' : a < w' := lt_of_lt_of_le (lt_succ_self a) haw
  have hX'pos : z < app B' (psi w' z z) := lt_of_lt_of_le (T.z_lt_psi _ _ _) hX'w
  have hcz : ∀ u, comps u z = [] := fun _ => rfl
  have hot : isOT (psi a (app B' (psi w' z z)) z) = true := by
    rw [isOT_psi_iff]
    refine ⟨haot, harg, rfl, z_le _, ?_⟩
    intro g hg
    rw [comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact lt_of_lt_of_le (comps_lt hmid g hg) (le_app_self _ _)
    · rw [comps_psi_z_of_ge (not_lt.mpr (le_of_lt haw')), hcz, List.nil_append] at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hX'pos
      · rcases hWC a (fun h => lt_irrefl' _ (show a < a from h)) g hg with h | ⟨d, hd, _⟩
        · exact lt_of_lt_of_le h hOm1
        · rw [comps_self_nil haot] at hd; simp at hd
  refine ⟨by rw [hnew]; exact hot, hlhd, ?_⟩
  intro U ρ σ i hXi hX'i
  rw [hnew] at hX'i
  intro p y y' q hy hy' hpq hprem
  rw [hXi] at hy; rw [hX'i] at hy'
  simp only [psi.injEq] at hy hy'
  obtain ⟨rfl, rfl, -⟩ := hy
  obtain ⟨-, rfl, -⟩ := hy'
  have hXs : ∀ q ∈ summands X, psi v (app Y0 one) z ≤ q :=
    spArg_summands_ge ⟨v, app Y0 one, rfl⟩ (psi v (app Y0 one) z) B hX
      (fun q hq => by simp [summands] at hq; subst hq; exact le_refl _) hBX
  have hva : succ a ≤ v := le_trans haw (le_of_lt hW.1)
  have hloX : (split X (psi (succ a) z z)).2 = z :=
    split_snd_z_of_ge (fun q hq => not_lt.mpr (le_trans (psi_le_psi_z hva) (hXs q hq)))
  have hloX' : (split (app B' (psi w' z z)) (psi (succ a) z z)).2 = z := by
    apply split_snd_z_of_ge
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact not_lt.mpr (le_trans hθw (hB'leaf q hq))
    · simp [summands] at hq; subst hq; exact not_lt.mpr hθw
  have hHX := H_of_lo_z hOld hloX
  have hHX' := H_of_lo_z hot hloX'
  rw [hHX, hHX']
  have hR0 : RelRU U q B' X := by
    have := relR_prefix_lhdU (U := U) (q := q) (P := z) (copies_lhd_arg hm hOld hX hO hBX)
    simpa [app] using this
  apply relR_of_subU hR0 (le_app_self _ _)
  intro u hU hu g hg
  have hua : ¬ lt a u = true := fun h => hu (lt_of_le_of_lt (not_lt.mp hpq) (show a < u from h))
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inr (Or.inl hg)
  · rw [comps_psi_z_of_ge (fun h => hua (lt_trans haw' h)), hcz, List.nil_append] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Or.inl hX'pos
    · rcases hWC u hua g hg with h | ⟨d, hd, hgd⟩
      · exact Or.inl (lt_of_lt_of_le h hOm1)
      · rcases hprem u hU hu d hd with h | h | ⟨d', hd', hdd'⟩
        · exact Or.inl (lt_of_le_of_lt (le_trans hgd h) (lt_of_lt_of_le haθ (le_trans hθw hX'w)))
        · rw [hHX'] at h; exact Or.inl (lt_of_le_of_lt hgd h)
        · exact Or.inr (Or.inr ⟨d', hd', le_trans hgd hdd'⟩)

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN

/-- **The weak seed node when `v(r) > v(g)`** (as `t0_S1AW_node`, with `weak_seed_hi`): the changed subscript `w′` of
the leaf stays at least `Ω_{v(g)+1}` (`hvch`, from `t0_shape3C`). -/
theorem t0_S1AW_nodeHi {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hw : ∃ w', ρ'.o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ WCS (ρ.v g) w' ∧ isOT (psi w' z z) = true)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hrN : Counted (TRIO.gexp M r L 0 0 n) g r)
    (hav : ρ.v g < ρ.v r)
    (hvch : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z) :
    ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧
      isOT (psi (ρ.v g) X' z) = true ∧ Lhd z (psi (ρ.v g) X' z) (psi (ρ.v g) X z) ∧
      ∀ U : T → Prop, RClaimU U ρ σ g := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  -- the counted children in `M`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set Lc := F.filter (fun d => decide (Counted M g d)) with hLcdef
  have hclM : CL M g = Lc ++ [r] := by
    unfold CL; rw [hchM, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
    rfl
  -- the counted children in `N`
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hroots : [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) =
      (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
    have e1 : (List.range n).map f = [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [hfdef, Nat.add_sub_cancel]
    have e2 : (List.range n).map f = (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ, List.map_append]; simp [hfdef]
    rw [← e1, e2]
  set Cm := ((List.range (n - 1)).map f).filter
    (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) with hCmdef
  have hclN : CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] := by
    unfold CL
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
      List.filter_append]
    have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) = Lc := by
      apply List.filter_congr
      intro d hd
      have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
      simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hgr hdr]
    rw [hF', List.append_assoc]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hLast]
    rfl
  have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hσLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  have hLcv : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hσLc
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  have hsO0 : Single (omid M r L ρ) :=
    ⟨isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN, by
      rw [(o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG).2]; exact ⟨_, _, rfl⟩⟩
  have hsLr : Single (ρ'.o r) := single_o hC1 hGT (by rw [List.length_take]; omega)
  have hsCL : ∀ d ∈ CL (TRIO.gexp M r L 0 0 n) g, Single (σ.o d) := by
    intro d hd
    rw [hclN] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · have hdF := (List.mem_filter.mp hd).1
        have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
        rw [hσLc d hd]
        exact single_o hC hG (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
        rw [hσmid k (by have := List.mem_range.mp hk; omega)]; exact hsO0
    · simp at hd; rw [hd, hσlast]; exact hsLr
  have hsN : ∀ t ∈ (CL (TRIO.gexp M r L 0 0 n) g).map σ.o, Single t := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hsCL d hd
  rw [hclM] at hsM hpM
  rw [hclN] at hsN
  simp only [List.map_append, List.map_singleton] at hsM hpM hsN
  rw [hLcv, hCmv, hσlast] at hsN
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  -- the decrease at `g` in `N`
  have hpN : (Lc.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r]).Pairwise
      (fun a b => b ≤ a) := by
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hlo : ρ'.o r ≤ omid M r L ρ := by
      obtain ⟨w', hw', hWk, _, _⟩ := hw
      rw [hw', hom]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hWk.1))
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hp1.1,
      List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha b hb => ?_⟩, by simp, fun a ha b hb => ?_⟩
    · rw [(List.mem_replicate.mp hb).2]
      exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
    · simp at hb; rw [hb]
      rcases List.mem_append.mp ha with ha | ha
      · exact le_trans hlo (le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp)))
      · rw [(List.mem_replicate.mp ha).2]; exact hlo
  have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) g).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hclN]; simp only [List.map_append, List.map_singleton]; rw [hLcv, hCmv, hσlast]; exact hpN
  set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map
    (cnt M ρ r))) with hY0
  set v := ρ.v r with hv
  set a := ρ.v g with ha
  set Lv := Lc.map ρ.o with hLv
  set m := Cm.length with hm
  have hOv : omid M r L ρ = psi v Y0 z := hom
  -- the sums
  have hsO : Single (omid M r L ρ) := by
    exact hsO0
  have hsumN : sumN (Lv ++ List.replicate m (omid M r L ρ) ++ [ρ'.o r]) =
      app (app (sumN Lv) (mulT (omid M r L ρ) m)) (ρ'.o r) := by
    have hp1 := List.pairwise_append.mp hpN
    rw [sumN_append_dec hsN hpN, sumN_append_dec (fun t ht => hsN t (List.mem_append_left _ ht)) hp1.1,
      sumN_replicate hsO m, sumN_singleton (hsN _ (by simp))]
  have hsumM : sumN (Lv ++ [ρ.o r]) = app (sumN Lv) (ρ.o r) := by
    rw [sumN_append_dec hsM hpM, sumN_singleton (hsM _ (by simp))]
  have hoN : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (omid M r L ρ) m))
      (ρ'.o r)) z := by
    rw [o_cl_loc hCN hgN (by rw [hσvg]; exact hG.ot_v g hgM) hsCL hpN0, hclN]
    simp only [List.map_append, List.map_singleton]
    rw [hLcv, hCmv, hσlast, hsumN, spArg_app, spArg_app, hσvg]
  have hoM : ρ.o g = psi a (spArg a (spArg a z (sumN Lv)) (ρ.o r)) z := by
    rw [o_cl_eq hC hG hgM, hclM]
    simp only [List.map_append, List.map_singleton]
    rw [hsumM, spArg_app]
  have hLs := sumN_dec Lv (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  have hm1' : (∃ k, k + 1 < n ∧ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) → 1 ≤ m := by
    rintro ⟨k, hk, hkc⟩
    have : r + k * L ∈ Cm := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩,
      by simpa using hkc⟩
    rw [hm]; exact List.length_pos_of_mem this
  have hXot : isOT (ρ.o r) = true := hG.ot_o r (by omega)
  rw [hor] at hoM hXot
  have hOld : isOT (psi a (spArg a (spArg a z (sumN Lv)) (psi v (app Y0 one) z)) z) = true := by
    rw [← hoM]; exact hG.ot_o g hgM
  have hBXs : ∀ q ∈ summands (spArg a z (sumN Lv)), psi v (app Y0 one) z ≤ q := by
    apply spArg_summands_ge ⟨v, _, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq
      have := (List.pairwise_append.mp hpM).2.2 q hq (ρ.o r) (by simp)
      rwa [hor] at this
    · simp [summands]
  have hO0 : isOT (psi v Y0 z) = true := by rw [← hOv]; exact hsO.1
  have hOT' : isOT (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (psi v Y0 z) m)) (ρ'.o r)) = true :=
    isOT_spArg a _ _ (isOT_spArg a _ _ (isOT_spArg a _ _ rfl hLs.1) (isOT_mulT hO0 ⟨_, _, rfl⟩ m)) hsLr.1
  have hm : 1 ≤ m := hm1' ⟨0, by omega, by simpa using hrN⟩
  have hX'O : ρ'.o r ≤ psi v Y0 z := by
    have hp1 := List.pairwise_append.mp hpN
    rw [← hOv]
    exact hp1.2.2 (omid M r L ρ) (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
      (ρ'.o r) (by simp)
  have hoN' : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (psi v Y0 z) m)) (ρ'.o r)) z := by
    rw [hoN, hOv]
  obtain ⟨w',hw',hWk,hWC,hcw⟩ := hw
  have hres := hvch w' z hw' (ne_of_lt hWk.1) (not_lt.mpr (psi_le_psi_z (succ_le_of_lt hav)))
  have haw : succ a ≤ w' := not_lt.mp (fun h => hres (psi_lt_psi_z_iff.mpr (Or.inl h)))
  have hweak := weak_seed_hi hm hOld hXot hO0 hBXs hWk hWC hcw haw
  rw [← hw'] at hweak
  refine ⟨_,_,hoM,hoN',hweak.1,hweak.2.1,?_⟩
  intro U
  exact hweak.2.2 U ρ σ g hoM hoN'

end

/-- **Seed S1 as a node when `r ≠ x − 1`** (`Bad2`, `t = 0`), from the structural fact that the first copy root still
counts at `g` in `N`: the drop at `r` is `◁` (`t0_S1N_of`), a weak leaf with `v(r) ≤ v(g)` (`t0_S1N_of`), or a weak
leaf with `v(r) > v(g)` (`t0_S1AW_nodeHi`). -/
theorem t0_S1N_cnt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3C M ρ rk) (D : T0DropF M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {n : Nat} (hn2 : 2 ≤ n) {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
    (hcN : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r) :
    ∀ g, par M 0 r = some g → Counted M g r → ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧
      isOT (psi (ρ.v g) X' z) = true ∧ Lhd z (psi (ρ.v g) X' z) (psi (ρ.v g) X z) ∧
      ∀ U : T → Prop, RClaimU U ρ σ g := by
  intro g hg hcnt
  have K := t0NCtx_of I D hlen hL hp he1 hn2 hCN
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hgr : g < r := par_lt M 0 r g hg
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  have hDP := D.po
  rw [show M.length - 1 = r + L by omega] at hDP
  obtain ⟨hPO, hPV⟩ := hDP r (by omega)
  have hLast := fun hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hc
  have hvch := t0_shape3C hM hS I D hlen hL hp he1 g hg
  have hG0 := t0IVResC_holds M ρ rk r L hM hS I hlen hL hp he1 n hn2 g hg
  rcases po_lhd_or_weak I.cons I.good K.C1 (by omega) (by omega) hPO hPV hg K.nz K.lt with hl | ⟨_, hw⟩
  · exact t0_S1N_of hlen hL hp (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hg K.C1
      K.GT K.offD K.σmid K.σlast (Or.inl hl) K.y' hLast hvch hG0 hcnt
  by_cases hva : ρ.v r ≤ ρ.v g
  · exact t0_S1N_of hlen hL hp (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hg K.C1
      K.GT K.offD K.σmid K.σlast (Or.inr ⟨hw, hcN g hg, fun _ => hva⟩) K.y' hLast hvch hG0 hcnt
  · have hσvg : σ.v g = ρ.v g := (K.offD g hgr).2 (fun hd =>
      uncnt_of_depv hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp (by omega) hd hrg hcnt)
    exact t0_S1AW_nodeHi hlen hL hp (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hg
      hcnt (fun c hc hd => (K.offD c hc).1 hd) hσvg K.σmid K.σlast (hLast hcnt) hw K.y' K.C1 K.GT
      (hcN g hg hcnt) (lt_of_not_ge hva) hvch

/-- **Residual: the hard seeds of a `Bad2` matrix at `t = 0`, narrowed** (2026-10-25): for `r ≠ x − 1` the first copy
root still counts at `g` in `N` (a structural fact) and S2; S3 for every `r`. -/
def T0BadSeedsH2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      (r ≠ r + L - 1 → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r) ∧
      (r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g)) ∧
      (∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 → col M g = bump M pp →
        Lhd z (σ.v pp) (ρ.v pp))

theorem t0BadSeedsH_of (hDU : HDropU) (h2 : T0BadSeedsH2) : T0BadSeedsH := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1 n hn2 σ hCN
  have S := sInv_std hM hS
  have IC := I.toC S
  have D := T0DropF.of_U hDU hM hS (by omega) I
  have H := h2 M ρ rk hM hS hB I r L hlen hL hp he1 n hn2 σ hCN
  refine ⟨fun hrx g hg => ⟨t0_S1N_cnt hM hS IC D hlen hL hp he1 hn2 hCN (fun g' hg' => (H g' hg').1 hrx) g hg,
    (H g hg).2.1 hrx, (H g hg).2.2⟩, fun _ g hg => (H g hg).2.2⟩

end Ytosk
