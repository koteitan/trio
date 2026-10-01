/-
**3 行・t = 0: 展開 N の値（2）r より前の比較（D の呼び出しは ◁ で真に下がる）。**

N = M[n]（n ≥ 2、r に親 g がある）の r より前の列は、構造が g の子（コピーの根が並ぶ）を除いて M と同じ。
- B（[r, x)）の呼び出しで D = DepX M x に入るのは o(r) だけ（`nodep_B`）。
- D の呼び出しは N で ◁ で真に下がる（`t0_dep_lhd`、D の導出についての帰納法）。種は g の 2 か所:
  r が g で数えられるときの o(g)（S1）、r が g ののりしろの子のときの v(g)（S2）。g が P_0(g) ののりしろの子に
  なる場合は仮定で除く（実測 0 件）。
- 枠の補題 `o_frame_evalG` は `o_frame_eval` の M.take x を一般の行列 M′ にしたもの（証明は同じ）。
-/
import Ytosk.V3T0V

namespace Ytosk

open T

set_option linter.unusedSectionVars false


/-- **The `o` frame where `v` does not change**: the counted children of a matrix `M′` are those of `M`
up to a tail, and only the last one changes. -/
theorem o_frame_evalG {M M' : Mat} {ρ ρ' : Valn} {i cs : Nat} {Lc Tl : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ)
    (hC' : Cons M' ρ') (hiT : i < M'.length) (hiM : i < M.length)
    (hv : ρ'.v i = ρ.v i)
    (hclT : CL M' i = Lc ++ [cs]) (hcl : CL M i = Lc ++ [cs] ++ Tl)
    (hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d)
    (hcs' : Single (ρ'.o cs))
    (hrel : LhdE (ρ'.o cs) (ρ.o cs) ∨ (WkO (ρ'.o cs) (ρ.o cs) ∧ ∃ w, ρ.o cs = psi w z z))
    (hsub : ∀ s y, ρ.o cs = psi s y z →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      SubSmall (ρ.v i) s)
    (hsub' : ∀ s y s' y', ρ.o cs = psi s y z → ρ'.o cs = psi s' y' z →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true) ∨
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      SubSmall (ρ.v i) s') :
    LhdE (ρ'.o i) (ρ.o i) := by
  set a := ρ.v i with ha
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  rw [hcl] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  set Lv := Lc.map ρ.o with hLv
  set Tv := Tl.map ρ.o with hTv
  have hsL : ∀ t ∈ Lv, Single t := fun t ht => hsM t (by simp [ht])
  have hcsS : Single (ρ.o cs) := hsM _ (by simp)
  have hsT : ∀ t ∈ Tv, Single t := fun t ht => hsM t (by simp [ht])
  have hp1 := List.pairwise_append.mp hpM
  have hpL : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp1.1).1
  have hLc : ∀ t ∈ Lv, ρ.o cs ≤ t := fun t ht =>
    (List.pairwise_append.mp hp1.1).2.2 t ht _ (by simp)
  have hpcT : (ρ.o cs :: Tv).Pairwise (fun a b => b ≤ a) := by
    refine List.pairwise_cons.mpr ⟨fun t ht => hp1.2.2 _ (by simp) t ht, hp1.2.1⟩
  have hsC : ∀ t ∈ ρ.o cs :: Tv, Single t := fun t ht => by
    rcases List.mem_cons.mp ht with h | h
    · rw [h]; exact hcsS
    · exact hsT t h
  have hLC : ∀ u ∈ ρ.o cs :: Tv, u ≤ ρ.o cs := fun u hu => by
    rcases List.mem_cons.mp hu with h | h
    · rw [h]
    · exact hp1.2.2 _ (by simp) u h
  have hsLc : ∀ t ∈ Lv ++ [ρ.o cs], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsL t h
    · simp at h; rw [h]; exact hcsS
  have hpLc : (Lv ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by simp at hb; rw [hb]; exact hLc t ht⟩
  -- the value in `M.take x`
  have hmapT : (CL M' i).map ρ'.o = Lv ++ [ρ'.o cs] := by
    rw [hclT, List.map_append, List.map_singleton, hLv]
    congr 1
    exact List.map_congr_left hsame
  have hle' : ρ'.o cs ≤ ρ.o cs := by
    rcases hrel with h | ⟨h, _⟩
    · exact h.le
    · exact DRelO.le (Or.inr h)
  have hs' : ∀ t ∈ Lv ++ [ρ'.o cs], Single t := by
    intro t ht; rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · simp at ht; rw [ht]; exact hcs'
  have hp' : (Lv ++ [ρ'.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by
      simp at hb; rw [hb]; exact le_trans hle' (hLc t ht)⟩
  have hvot : isOT a = true := hG.ot_v i hiM
  have ho' : ρ'.o i = psi a (spArg a z (sumN (Lv ++ [ρ'.o cs]))) z := by
    have := o_cl_loc hC' hiT (by rw [hv]; exact hvot)
      (fun c hc => by
        have : ρ'.o c ∈ (CL M' i).map ρ'.o := List.mem_map_of_mem hc
        rw [hmapT] at this; exact hs' _ this)
      (by rw [hmapT]; exact hp')
    rw [this, hmapT, hv]
  have ho : ρ.o i = psi a (spArg a z (sumN (Lv ++ [ρ.o cs] ++ Tv))) z := by
    rw [o_spArg hC hG hiM, cvals_eq_map hC hG i, hcl]
    simp only [List.map_append, List.map_singleton]
    rfl
  rw [ho', ho]
  set B := spArg a z (sumN Lv) with hB
  have hLs := sumN_dec Lv hsL hpL
  -- the state before `cs` is above the children
  have hBge : ∀ t, Single t → t ≤ ρ.o cs → ∀ q ∈ summands B, t ≤ q := by
    intro t ht htc
    obtain ⟨s0, y0, rfl⟩ := ht.2
    apply spArg_summands_ge ⟨s0, y0, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq; exact le_trans htc (hLc q hq)
    · simp [summands]
  have hCL : CL M i = Lc ++ cs :: Tl := by rw [hcl]; simp
  obtain ⟨s, y, hsy⟩ := hcsS.2
  rcases hrel with hrel | hW
  · -- `⊴` child: one frame, then the tail
    obtain ⟨s', y', hs'y'⟩ := hcs'.2
    rw [hsy, hs'y'] at hrel
    have hc := hcsS.1; rw [hsy] at hc
    have hc' := hcs'.1; rw [hs'y'] at hc'
    have hN := node_lhd (a := a) (B := B) hc hc' hrel (hBge _ hcsS (le_refl _) |> fun h => by
        rw [hsy] at h; exact h) (hsub s y hsy) (hsub' s y s' y' hsy hs'y')
      (fun _ hr => hF i hiM Lc cs Tl hCL s y hsy hr)
    have hstate : spArg a z (sumN ((Lc ++ [cs]).map ρ.o)) = step a B s y z := by
      rw [List.map_append, List.map_singleton, ← hLv, sumN_append_dec hsLc hpLc,
        sumN_singleton hcsS, spArg_app, hsy, spArg_single]
    have hTcl := tailcl_of_frame hC hG hF hiM Tl (Lc ++ [cs]) (by rw [hcl])
    rw [hstate] at hTcl
    have hT := drop_tail a Tv (step a B s y z) hsT hp1.2.1
      (fun u hu q hq => by
        obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
        have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi s y z) B hc
          (by intro q2 hq2; simp [summands] at hq2; rw [hq2, ← hsy]; exact hp1.2.2 _ (by simp) u hu)
          (hBge u (hsT u hu) (hp1.2.2 _ (by simp) u hu))
        rw [spArg_single] at this
        exact this q hq) hTcl
    rw [hsy, hs'y']
    rw [hs'y'] at hs' hp'
    rw [hsy] at hsM hpM
    exact o_frame_term (L := Lv) (Tl := Tv) hsM hpM hs' hp' hN hT
  · -- weak child
    obtain ⟨⟨w', w, X, hw', hw, hWk⟩, w0, hw0⟩ := hW
    rw [hw] at hw0; simp only [psi.injEq] at hw0; obtain ⟨rfl, rfl, -⟩ := hw0
    have hF' : spArg a z (sumN (Lv ++ [ρ.o cs] ++ Tv)) = spArg a B (sumN (ρ.o cs :: Tv)) := by
      rw [List.append_assoc, show [ρ.o cs] ++ Tv = ρ.o cs :: Tv from rfl,
        sumN_append_dec (fun t ht => hsM t (by simpa using ht)) (by simpa using hpM), spArg_app]
    rw [hF']
    have hTcl := tailcl_of_frame hC hG hF hiM (cs :: Tl) Lc (by rw [hCL])
    have hdrop := drop_tail a (ρ.o cs :: Tv) B hsC hpcT
      (fun u hu q hq => hBge u (hsC u hu) (hLC u hu) q hq) (by simpa using hTcl)
    -- the old state after `cs` is `B + ψ_w(0)`, and the rest only grows
    have hstep : spArg a B (ρ.o cs) = app B (psi w z z) := by
      rw [hw, spArg_single, step_leaf]
      exact add_eq_app_of_ge ⟨w, z, rfl⟩ B (hBge _ hcsS (le_refl _) |> fun h => by rw [hw] at h; exact h)
    have hTcl2 := tailcl_of_frame hC hG hF hiM Tl (Lc ++ [cs]) (by rw [hcl])
    have hgrow : app B (psi w z z) ≤ spArg a B (sumN (ρ.o cs :: Tv)) := by
      have e : spArg a B (sumN (ρ.o cs :: Tv)) = spArg a (app B (psi w z z)) (sumN Tv) := by
        rw [sumN_cons_dec hsC hpcT, hw,
          show app (psi w z z) (sumN Tv) = psi w z (sumN Tv) from rfl, spArg_cons, step_rest a B w z (sumN Tv) z,
          step_leaf, add_eq_app_of_ge ⟨w, z, rfl⟩ B (hBge _ hcsS (le_refl _) |> fun h => by rw [hw] at h; exact h)]
      have hs2 : spArg a z (sumN ((Lc ++ [cs]).map ρ.o)) = app B (psi w z z) := by
        rw [List.map_append, List.map_singleton, ← hLv, sumN_append_dec hsLc hpLc,
          sumN_singleton hcsS, spArg_app, hstep]
      rw [hs2] at hTcl2
      have hd := drop_tail a Tv (app B (psi w z z)) hsT hp1.2.1
        (fun u hu q hq => by
          obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
          have hcw : isOT (psi w z z) = true := by rw [← hw]; exact hcsS.1
          have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi w z z) B hcw
            (by intro q2 hq2; simp [summands] at hq2; rw [hq2, ← hw]; exact hp1.2.2 _ (by simp) u hu)
            (hBge u (hsT u hu) (hp1.2.2 _ (by simp) u hu))
          rw [spArg_single, step_leaf, add_eq_app_of_ge ⟨w, z, rfl⟩ B
            (hBge _ hcsS (le_refl _) |> fun h => by rw [hw] at h; exact h)] at this
          exact this q hq) hTcl2
      rw [e]
      clear e
      have := hd.le
      rcases (le_iff _ _).mp this with h | h
      · rw [psi_lt_psi_z_iff] at h
        rcases h with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact le_of_lt h
      · simp only [psi.injEq] at h; exact (le_iff _ _).mpr (Or.inr h.2.1)
    have hlt : app B (psi w' z z) < spArg a B (sumN (ρ.o cs :: Tv)) := by
      apply lt_of_lt_of_le _ hgrow
      apply app_lt_app_left
      rw [psi_lt_psi_z_iff]; exact Or.inl hWk.1
    rw [hw'] at hs' hp'
    rw [hw']
    exact o_frame_weak hs' hp' hWk hdrop hlt


theorem lhd_of_lhdE_lt {a b : T} (h : LhdE a b) (hlt : a < b) : Lhd z a b := by
  rcases h with h | h
  · rw [h] at hlt; exact absurd hlt (lt_irrefl' _)
  · exact h

/-- **The `o` frame of two matrices with the same counted children at `i`**, where only the last one
changes by `◁`: the parent changes by `◁`. -/
theorem o_frame_lhd {M N : Mat} {ρ σ : Valn} {i c : Nat} {Lc : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ) (hCN : Cons N σ) (hGN : Good3 N σ)
    (hiM : i < M.length) (hiN : i < N.length) (hv : σ.v i = ρ.v i)
    (hclN : CL N i = Lc ++ [c]) (hclM : CL M i = Lc ++ [c])
    (hsame : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hl : Lhd z (σ.o c) (ρ.o c))
    (hsub : ∀ s y, ρ.o c = psi s y z →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      SubSmall (ρ.v i) s)
    (hsub' : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true) ∨
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      SubSmall (ρ.v i) s')
    (hy : ∀ s, ρ.o c = psi s z z → ∃ s', σ.o c = psi s' z z)
    (hss : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → y' ≠ z → s' = s) :
    Lhd z (σ.o i) (ρ.o i) := by
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hclN]; simp))).2
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hclM]; simp))).2
  have hcs' := single_o hCN hGN hcN
  have hE := o_frame_evalG hC hG hF hCN hiN hiM hv hclN (Tl := []) (by rw [hclM, List.append_nil]) hsame
    hcs' (Or.inl (Or.inr hl)) hsub hsub'
  apply lhd_of_lhdE_lt hE
  -- strictness
  have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
  set a := ρ.v i with ha
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  obtain ⟨hsN, hpN⟩ := cl_vals hCN hGN hiN
  rw [hclM] at hsM hpM
  have hpM' := hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hpM'
  obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
  obtain ⟨s', y', hs'y'⟩ := hcs'.2
  have hformM := o_last_form hC hiM hvot hclM (fun d hd => single_o hC hG
    (mem_children (cl_mem_children hd)).2) (by rw [hclM]; exact hpM) hsy
  have hformN := o_last_form hCN hiN (by rw [hv]; exact hvot) hclN (fun d hd => single_o hCN hGN
    (mem_children (cl_mem_children hd)).2) hpN hs'y'
  have hLm : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hsame
  rw [hLm, hv] at hformN
  rw [hformN, hformM]
  apply psi_lt_psi_z_iff.mpr; right; refine ⟨rfl, ?_⟩
  set B := spArg a z (sumN (Lc.map ρ.o)) with hB
  have hsL : ∀ t ∈ Lc.map ρ.o, Single t := fun t ht => hsM t (by simp only [List.map_append]; exact List.mem_append_left _ ht)
  have hp1 := List.pairwise_append.mp hpM'
  have hLs := sumN_dec (Lc.map ρ.o) hsL hp1.1
  have hc : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
  have hc' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hcs'.1
  apply step_lt hc hc'
  · left; rw [← hsy, ← hs'y']; exact hl
  · intro q hq
    apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hsy]; exact hp1.2.2 q hq _ (by simp)
    · simp [summands]
    · exact hq
  · intro ht' hlt
    have := hss s y s' y' hsy hs'y' (ne_z_of_lt ht'.1)
    rw [this] at hlt; exact absurd hlt (lt_irrefl' _)
  · intro hyz
    rw [hyz] at hsy
    obtain ⟨s'', h''⟩ := hy s hsy
    rw [hs'y'] at h''; simp only [psi.injEq] at h''; exact h''.2.1

/-- `v(x)` is not in `D` when row 1 of `x` is `0`. -/
theorem not_depX_v_x {M : Mat} {x : Nat} (he1 : entry M 1 x = 0) : ¬ DepX M x false x := by
  intro h
  cases h with
  | vpar h1 _ _ => exact h1 he1
  | vupg h1 _ _ _ => exact h1 he1
  | vbump h1 _ _ _ _ _ => exact h1 he1

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0)
include hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1

/-- **In `B`, only `o(r)` is in `D`.** -/
theorem nodep_B : ∀ b d, DepX M (r + L) b d → r ≤ d → d < r + L → b = true ∧ d = r := by
  intro b d h
  induction h with
  | leaf => intro _ h; omega
  | @ochild i c hc _ _ _ ih =>
    intro hri hix
    have hic := (mem_children hc).1
    have hcl := (mem_children hc).2
    by_cases hcx : c < r + L
    · have := ih (by omega) hcx; omega
    · have hce : c = r + L := by omega
      have hpc := (mem_children_iff.mp hc).2
      rw [hce, hp] at hpc
      exact ⟨rfl, (Option.some.inj hpc).symm⟩
  | ov _ ih =>
    intro h1 h2
    exact absurd (ih h1 h2).1 (by simp)
  | @vpar i m h1 hpm hdm ih =>
    intro hri hix
    have hmi := par_lt M 1 i m hpm
    by_cases hmr : r ≤ m
    · exact absurd (ih hmr (by omega)).1 (by simp)
    · exact absurd hdm (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB m i hri hix (Or.inl hpm))
  | @vupg i k h1 h2 hu hdk ih =>
    intro hri hix
    have hkl := upg_lt (by omega) hu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    by_cases hkx : k = r + L
    · subst hkx; exact absurd hdk (not_depX_v_x he1)
    · by_cases hkr : r ≤ k
      · exact absurd (ih hkr (by omega)).1 (by simp)
      · exact absurd hdk (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB k i hri hix
          (Or.inr ⟨hu, by rcases hcase with h | ⟨_, h⟩ <;> omega⟩))
  | @vbump i j k h1 h2 hj _ hk _ ih =>
    intro hri hix
    have hij := (mem_children hj).1
    have hjk := (mem_children hk).1
    have hkl := (mem_children hk).2
    by_cases hkx : k < r + L
    · have := ih (by omega) hkx; omega
    · have hke : k = r + L := by omega
      have hpk := (mem_children_iff.mp hk).2
      rw [hke, hp] at hpk
      have := Option.some.inj hpk; omega

theorem not_depX_v_r : ¬ DepX M (r + L) false r := fun h =>
  absurd (nodep_B hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 false r h (le_refl _) (by omega)).1 (by simp)

end

end Ytosk
