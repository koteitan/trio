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
import Ytosk.V3MainT1F

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

theorem foldl_nzs : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, isOT t = true) →
    l.foldl (fun a b => sf (add a b)) acc = (nzs l).foldl (fun a b => sf (add a b)) acc
  | [], _, _, _ => rfl
  | t :: l, acc, hacc, hl => by
    have hl' : ∀ u ∈ l, isOT u = true := fun u hu => hl u (by simp [hu])
    by_cases ht : t = z
    · have : nzs (t :: l) = nzs l := by simp [nzs, List.filter_cons, ht]
      rw [this, List.foldl_cons, ht, add_z_right, sf_ot hacc]
      exact foldl_nzs l acc hacc hl'
    · have : nzs (t :: l) = t :: nzs l := by simp [nzs, List.filter_cons, ht]
      rw [this, List.foldl_cons, List.foldl_cons]
      have hot : isOT (add acc t) = true := isOT_add hacc (hl t (by simp))
      exact foldl_nzs l _ (by rw [sf_ot hot]; exact hot) hl'

theorem sumN_nzs {l : List T} (hl : ∀ t ∈ l, isOT t = true) : sumN l = sumN (nzs l) :=
  foldl_nzs l z rfl hl

/-- **The bump-type `v` frame of two matrices** with the same children at `i` and at its last (bump)
child `j`, where the sum `G` of the children of `j` changes in the strong relation and strictly. -/
theorem v_bump_lhd {M N : Mat} {ρ σ : Valn} {i j : Nat} {L : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = omega G) (hbjN : bumpTerm N σ i j = omega G')
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : BRelS G' G) (hlt : G' < G)
    (hTD : BumpTermDec M ρ)
    (hAbs : ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z → q < bumpW M ρ i →
      Lhd z q (bumpW M ρ i)) :
    Lhd z (σ.v i) (ρ.v i) := by
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
  have hE : LhdE (σ.v i) (ρ.v i) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
    intro q hq hn hlt'
    by_cases hWE : omega (sumN (one :: Pl ++ [omega G])) < E0
    · exact lhd_lt_small (isOT_mem_summands hVot hq) hWE hlt'
    · rw [← hbW]
      apply hAbs q hq _ (by rw [hbW]; exact hlt')
      intro hq2
      apply hn
      have h2le : two ≤ sumN (one :: Pl ++ [omega G']) :=
        two_le_sumN_one_cons (by simp) (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hsP t h
          · simp at h; rw [h]; exact single_omega hG'ot)
      have hom : psi z two z ≤ omega (sumN (one :: Pl ++ [omega G'])) := by
        rw [← omega_small two_lt_E0]
        rcases (le_iff _ _).mp h2le with h' | h'
        · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
        · rw [h']
      exact lt_of_lt_of_le hq2 hom
  apply lhd_of_lhdE_lt hE
  rw [ev', ev]
  apply add_lt_add_left
  apply omega_lt_omega hp'ot hpot
  exact sumN_snoc_lt hPot hPot (isOT_omega hG'ot) (isOT_omega hGot) (le_refl _)
    (omega_lt_omega hG'ot hGot hlt)

/-- **The `G` level** (the children of the bump child): the last child changes by `◁`, either with the
same subscript or to `ψ_{w′}(0)` with `w′ ⊴ w`. -/
theorem g_brel {Kv : List T} {t' t : T} (hsK : ∀ u ∈ Kv, Single u)
    (hpK : (Kv ++ [t]).Pairwise (fun a b => b ≤ a)) (ht : Single t) (ht' : Single t')
    (hl : Lhd z t' t)
    (hform : (∃ s y y', t = psi s y z ∧ t' = psi s y' z) ∨
      (∃ w' w Y, t' = psi w' z z ∧ t = psi w Y z ∧ LhdE w' w ∧ one ≤ w')) :
    BRelS (sumN (Kv ++ [t'])) (sumN (Kv ++ [t])) ∧ sumN (Kv ++ [t']) < sumN (Kv ++ [t]) ∧
      isOT (sumN (Kv ++ [t'])) = true := by
  have hp1 := List.pairwise_append.mp hpK
  have hKt : ∀ u ∈ Kv, t ≤ u := fun u hu => hp1.2.2 u hu t (by simp)
  have hst : ∀ u ∈ Kv ++ [t], Single u := fun u hu => by
    rcases List.mem_append.mp hu with h | h
    · exact hsK u h
    · simp at h; rw [h]; exact ht
  have hst' : ∀ u ∈ Kv ++ [t'], Single u := fun u hu => by
    rcases List.mem_append.mp hu with h | h
    · exact hsK u h
    · simp at h; rw [h]; exact ht'
  have hpK' : (Kv ++ [t']).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hp1.1, by simp, fun a ha b hb => by
      simp at hb; rw [hb]; exact le_trans (le_of_lt hl.1) (hKt a ha)⟩
  have hKot : ∀ u ∈ Kv, isOT u = true := fun u hu => (hsK u hu).1
  refine ⟨?_, sumN_snoc_lt hKot hKot ht'.1 ht.1 (le_refl _) hl.1,
    isOT_sumN _ (fun u hu => (hst' u hu).1)⟩
  rw [sumN_snoc_dec hst' hpK', sumN_snoc_dec hst hpK]
  by_cases hK : Kv = []
  · subst hK
    simp only [sumN_nil, app_z]
    rcases hform with ⟨s, y, y', rfl, rfl⟩ | ⟨w', w, Y, rfl, rfl, hw, h1⟩
    · exact brelS_single_same z (Or.inr hl) ht'.1
    · exact brelS_fix hw h1
  · have hS0 : sumN Kv ≠ z := sumN_ne_z hsK hp1.1 hK
    have := brelS_app_same hS0 (Or.inr hl) z
    simpa using this

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

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

/-- **The counted children before `r` in `N`** are those of `M`, unless `r` is a counted child. -/
theorem cl_N_eq (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n) {i : Nat}
    (hi : i < r) (hb : par M 0 r = some i → col M r = bump M i) :
    CL (TRIO.gexp M r L 0 0 n) i = CL M i := by
  unfold CL
  by_cases hig : par M 0 r = some i
  · have hbr := hb hig
    rw [children_g0 hlen hL hp hn hig, List.filter_append]
    have hz : ((List.range (n - 1)).map (fun k => r + (k + 1) * L)).filter
        (fun c => decide (Counted (TRIO.gexp M r L 0 0 n) i c)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      have hk' := List.mem_range.mp hk
      simp only [decide_eq_true_eq]
      intro h
      apply h.1
      rw [col_root0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hbr
    rw [hz, List.append_nil]
    apply List.filter_congr
    intro c hc
    have hcr := children_g_le hlen hL hp hig hc
    rcases Nat.lt_or_ge c r with h | h
    · simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hi h]
    · rw [show c = r by omega]
      have h1 : ¬ Counted (TRIO.gexp M r L 0 0 n) i r := fun h' => h'.1 (by
        rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hbr)
      have h2 : ¬ Counted M i r := fun h' => h'.1 hbr
      rw [decide_eq_false h1, decide_eq_false h2]
  · rw [children_pre0 hlen hL hp hn hi hig]
    apply List.filter_congr
    intro c hc
    have hcr := children_lt_r hlen hL hp hi hig hc
    simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hi hcr]

end

/-- **Hypothesis on `N`** (as `VSmallNew` of the drop): a last counted child before `r` whose `v`
changes in `N`, in a rewriting frame of `M`, has a small subscript. -/
def VSmallNewN (M : Mat) (r : Nat) (ρ σ : Valn) : Prop :=
  ∀ i, i < r → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
    ∀ s y, ρ.o cs = psi s y z →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
      VSmallV (σ.v cs)

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : Good3 (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

theorem cl_nil_of_depv {c : Nat} (hc : c < r) (hv : DepX M (r + L) false c) : CL M c = [] := by
  unfold CL
  rw [List.filter_eq_nil_iff]
  intro d hd
  simp only [decide_eq_true_eq]
  exact uncnt_of_depv (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp
    (by omega) hv hd

theorem o_N_noc {c : Nat} (hc : c < r) (hcl : CL M c = []) : σ.o c = psi (σ.v c) z z := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hclN : CL (TRIO.gexp M r L 0 0 n) c = [] := by
    rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hc]
    · exact hcl
    · intro hg
      by_contra hb
      have hrc : r ∈ children M c := mem_children_iff.mpr ⟨by omega, hg⟩
      have : r ∈ CL M c := by
        unfold CL; rw [List.mem_filter]; refine ⟨hrc, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
      rw [hcl] at this; simp at this
  exact o_of_no_counted hCN hcN (hGN.ot_v c hcN) (no_cnt_of_cl_nil hclN)

/-- **Every call of `D` before `r` drops by `◁`** in `N` (`t = 0`, `n ≥ 2`, `r` has a parent `g`),
from the two seeds at `g`. -/
theorem t0_dep_lhd {g : Nat} (hg : par M 0 r = some g) {rk : Bool → Nat → Nat} (hRM : Rk M rk)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbs : BumpAbsC M (r + L) ρ) (hVNN : VSmallNewN M r ρ σ)
    (hE3 : ∀ p, par M 0 g = some p → entry M 1 p ≠ 0 → entry M 2 p ≠ 0 → col M g ≠ bump M p)
    (hS1 : Counted M g r → Lhd z (σ.o g) (ρ.o g))
    (hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g)) :
    ∀ b i, DepX M (r + L) b i → i < r → Lhd z (valB σ b i) (valB ρ b i) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hiN : ∀ i, i < r → i < (TRIO.gexp M r L 0 0 n).length := fun i hi => by rw [hlN]; omega
  have hAgx : Anc0 M g (r + L) := Anc0.step hp (Anc0.step hg (Anc0.refl g))
  have key : ∀ K, ∀ b i, rk b i ≤ K → DepX M (r + L) b i → i < r →
      Lhd z (valB σ b i) (valB ρ b i) := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hD hi
      have hiM : i < M.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      cases hD with
      | leaf => omega
      | @ochild _ c hc hcb hcu hdc =>
        show Lhd z (σ.o i) (ρ.o i)
        have hcnt : Counted M i c := ⟨hcb, hcu⟩
        have hvD : ¬ DepX M (r + L) false i := fun hv =>
          uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hv hc hcnt
        have hv' := (hoffD i hi).2 hvD
        have hci := (mem_children hc).1
        have hcl := (mem_children hc).2
        by_cases hcr : r ≤ c
        · have hcr' : c = r := by
            by_contra hne
            by_cases hig : par M 0 r = some i
            · have := children_g_le hlen hL hp hig hc; omega
            · have := children_lt_r hlen hL hp hi hig hc; omega
          rw [hcr'] at hc hcnt
          have hig : par M 0 r = some i := (mem_children_iff.mp hc).2
          have hgi : g = i := Option.some.inj (hg.symm.trans hig)
          rw [← hgi] at hcnt ⊢
          exact hS1 hcnt
        · have hcr : c < r := by omega
          rcases hOS_t1 hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp i (by omega) (DepX.ochild hc hcb hcu hdc) with
            ⟨hv, _⟩ | ⟨_, Lp, c0, R, hch, _, _, hR, hLnd⟩
          · exact absurd hv hvD
          · have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
              rcases hR d h with h' | h'
              · exact hd.1 h'
              · exact hd.2 h'
            have hcc0 : c = c0 := by
              have hc' := hc
              rw [hch] at hc'
              rcases List.mem_append.mp hc' with h | h
              · exact absurd hdc (hLnd c h hcnt)
              · rcases List.mem_cons.mp h with h | h
                · exact h
                · exact absurd hcnt (hcR c h)
            rw [← hcc0] at hch
            obtain ⟨hLs, hRs⟩ := sib_order (children_sorted M i) hch
            have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
              unfold CL
              rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
              have : R.filter (fun d => decide (Counted M i d)) = [] := by
                rw [List.filter_eq_nil_iff]; intro d hd; simpa using hcR d hd
              rw [this]
            set Lc := Lp.filter (fun d => decide (Counted M i d)) with hLc
            have hb : par M 0 r = some i → col M r = bump M i := by
              intro hig
              have hri : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
              have hrR : r ∈ R := by
                rw [hch] at hri
                rcases List.mem_append.mp hri with h | h
                · have := hLs r h; omega
                · rcases List.mem_cons.mp h with h | h
                  · omega
                  · exact h
              by_contra hb
              exact hcR r hrR ⟨hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
            have hclN : CL (TRIO.gexp M r L 0 0 n) i = Lc ++ [c] := by
              rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hi hb, hclM]
            have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => by
              have hd' := List.mem_filter.mp hd
              have hdc : Counted M i d := by simpa using hd'.2
              have := hLs d hd'.1
              exact (hoffD d (by omega)).1 (hLnd d hd'.1 hdc)
            have hIH : Lhd z (σ.o c) (ρ.o c) :=
              ih _ (by have := hRc c hc hcb hcu; omega) true c (le_refl _) hdc hcr
            have hfr := hVS i hiM Lc c [] (by rw [hclM])
            -- `c` with a changed `v` has argument `0` in `N`
            have hchv : σ.v c ≠ ρ.v c → σ.o c = psi (σ.v c) z z := by
              intro hne
              have hdv : DepX M (r + L) false c := by
                by_contra hn'; exact hne ((hoffD c hcr).2 hn')
              exact o_N_noc hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hcr
                (cl_nil_of_depv hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hcr hdv)
            have hsv : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → σ.v c = ρ.v c → s' = s := by
              intro s y s' y' hsy hs'y' hvc
              obtain ⟨y0, hy0⟩ := o_psi_sub hCN (hiN c hcr)
              rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
              obtain ⟨y1, hy1⟩ := o_psi_sub hC (show c < M.length by omega)
              rw [hsy] at hy1; simp only [psi.injEq] at hy1
              rw [hy0.1, hy1.1, sf_ot (hGN.ot_v c (hiN c hcr)), sf_ot (hG.ot_v c (by omega)), hvc]
            have hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c := by
              intro s y h
              obtain ⟨y0, hy0⟩ := o_psi_sub hC (show c < M.length by omega)
              rw [h] at hy0; simp only [psi.injEq] at hy0
              rw [hy0.1, sf_ot (hG.ot_v c (by omega))]
            apply o_frame_lhd hC hG hF hCN hGN hiM (hiN i hi) hv' hclN hclM hsame hIH
            · intro s y hsy hrw
              rw [hvM s y hsy]; exact (hfr.2 s y hsy hrw).subSmall _
            · intro s y s' y' hsy hs'y' hrw
              by_cases hvc : σ.v c = ρ.v c
              · have hss := hsv s y s' y' hsy hs'y' hvc
                subst hss
                have hle : psi s' y' z ≤ psi s' y z := by rw [← hs'y', ← hsy]; exact le_of_lt hIH.1
                have hold : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧
                    lt (psi (ρ.v i) z z) (psi s' y z) = true := by
                  rcases hrw with hn' | ho
                  · have hyy : y' ≤ y := by
                      rcases (le_iff _ _).mp hle with hl | hl
                      · rcases psi_lt_psi_z_iff.mp hl with hl | ⟨_, hl⟩
                        · exact absurd hl (lt_irrefl' _)
                        · exact le_of_lt hl
                      · simp only [psi.injEq] at hl; rw [hl.2.1]
                    exact ⟨lt_of_lt_of_le hn'.1 hyy, lt_of_lt_of_le hn'.2 hle⟩
                  · exact ho
                rw [hvM s' y hsy]; exact (hfr.2 s' y hsy hold).subSmall _
              · have ho0 := hchv hvc
                rw [hs'y'] at ho0; simp only [psi.injEq] at ho0
                rcases hrw with hn' | ho
                · exfalso; have := hn'.1; rw [ho0.2.1] at this; exact T.not_lt_z _ this
                · rw [ho0.1]; exact (hVNN i hi Lc c hclM hvc s y hsy ho).subSmall _
            · intro s hs
              have hclc : CL M c = [] := by
                by_contra hne
                have hlt := arg_lt_of_cl hC hG (show c < M.length by omega) hne
                rw [o_cl_eq hC hG (show c < M.length by omega)] at hs
                simp only [psi.injEq] at hs
                rw [hs.2.1] at hlt; exact lt_irrefl' _ hlt
              exact ⟨_, o_N_noc hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hcr hclc⟩
            · intro s y s' y' hsy hs'y' hy'
              apply hsv s y s' y' hsy hs'y'
              by_contra hvc
              have := hchv hvc
              rw [hs'y'] at this; simp only [psi.injEq] at this; exact hy' this.2.1
      | ov hv =>
        show Lhd z (σ.o i) (ρ.o i)
        have hIH : Lhd z (σ.v i) (ρ.v i) := ih _ (by omega) false i (le_refl _) hv hi
        have hclM := cl_nil_of_depv hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hi hv
        rw [o_N_noc hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hi hclM,
          o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclM)]
        exact lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hIH)) (psi_lt_psi_z_iff.mpr (Or.inl hIH.1))
      | vpar h1 hpm hdm =>
        exfalso
        have hm := par_lt M 1 i _ hpm
        exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i
          (by omega) hpm
      | @vupg _ k h1 h2 hu hdk =>
        show Lhd z (σ.v i) (ρ.v i)
        obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
        have hkr : k < r := by
          have hkle : k ≤ r := by rcases hcase with h | ⟨_, h⟩ <;> omega
          rcases Nat.lt_or_ge k r with h | h
          · exact h
          · exfalso
            have : k = r := by omega
            rw [this] at hdk
            exact not_depX_v_r hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 hdk
        have hIH : Lhd z (σ.v k) (ρ.v k) :=
          ih _ (by have := (hRr h1).2.1 h2 k hu; omega) false k (le_refl _) hdk hkr
        have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
          cases hpp : par M 1 i with
          | none => rfl
          | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
        have hVot' : isOT (vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i)) = true := by
          cases hpp : par (TRIO.gexp M r L 0 0 n) 1 i with
          | none => rfl
          | some m => exact hGN.ot_v m (by have := par_lt _ 1 i m hpp; have := hiN i hi; omega)
        have ek : ρ.v i = ρ.v k :=
          v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
        have huN : upg (TRIO.gexp M r L 0 0 n) i = some k := by
          rw [upg_pre0 hlen hL hp hn (by omega)]; exact hu
        have ek' : σ.v i = σ.v k :=
          v_upg_eq hCN (hiN i hi) (by rw [entry_pre0 hlen hn 1 (by omega)]; exact h1)
            (by rw [entry_pre0 hlen hn 2 (by omega)]; exact h2) huN hVot'
            (fun _ _ _ k' hk' => hGN.ot_o k' (mem_children hk').2)
        rw [ek, ek']; exact hIH
      | @vbump _ j k h1 h2 hj hjb hk hdk =>
        show Lhd z (σ.v i) (ρ.v i)
        have hij := (mem_children hj).1
        have hjk := (mem_children hk).1
        have hkl := (mem_children hk).2
        by_cases hkr : r ≤ k
        · by_cases hjr : r ≤ j
          · have hjr' : j = r := by
              by_contra hne
              by_cases hig : par M 0 r = some i
              · have := children_g_le hlen hL hp hig hj; omega
              · have := children_lt_r hlen hL hp hi hig hj; omega
            have hig : par M 0 r = some i := by rw [← hjr']; exact (mem_children_iff.mp hj).2
            have hgi : g = i := Option.some.inj (hg.symm.trans hig)
            have hkx : k = r + L := by
              by_contra hne
              have := nodep_B hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 true k hdk (by omega) (by omega)
              omega
            rw [hjr'] at hjb
            rw [← hgi] at hjb h1 h2 ⊢
            exact hS2 hjb h1 h2
          · have hjg : par M 0 r = some j := by
              by_contra hne
              have := children_lt_r hlen hL hp (by omega) hne hk; omega
            have hgj : g = j := Option.some.inj (hg.symm.trans hjg)
            exfalso
            apply hE3 i (by rw [hgj]; exact (mem_children_iff.mp hj).2) h1 h2
            rw [hgj]; exact hjb
        · have hkr' : k < r := by omega
          obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega)
            (DepX.vbump h1 h2 hj hjb hk hdk)
          rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
          · exact absurd h2' h2
          · have hjj : j = j' := by
              rw [hch] at hj
              rcases List.mem_append.mp hj with h | h
              · exact absurd hdk (hLnd j h k hk).2
              · exact List.mem_singleton.mp h
            subst hjj
            have hkk : k = k' := by
              rw [hchj] at hk
              rcases List.mem_append.mp hk with h | h
              · exact absurd hdk (hKnd k h)
              · exact List.mem_singleton.mp h
            subst hkk
            have hLj : ∀ d ∈ Lb, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
            have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
            have hig : par M 0 r ≠ some i := by
              intro hig
              have hri : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
              rw [hch] at hri
              rcases List.mem_append.mp hri with h | h
              · have := hLj r h; omega
              · simp at h; omega
            have hjg : par M 0 r ≠ some j := by
              intro hjg
              have hgj : g = j := Option.some.inj (hg.symm.trans hjg)
              exact hE3 i (by rw [hgj]; exact (mem_children_iff.mp hj).2) h1 h2 (by rw [hgj]; exact hjb)
            have hchN : children (TRIO.gexp M r L 0 0 n) i = Lb ++ [j] := by
              rw [children_pre0 hlen hL hp hn hi hig, hch]
            have hchjN : children (TRIO.gexp M r L 0 0 n) j = Kb ++ [k] := by
              rw [children_pre0 hlen hL hp hn (by omega) hjg, hchj]
            have hbL : ∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L 0 0 n) σ i d = bumpTerm M ρ i d := by
              intro d hd
              have hdj := hLj d hd
              have hdM : d ∈ children M i := by rw [hch]; simp [hd]
              have hdg : par M 0 r ≠ some d := by
                intro hdg
                have hgd : g = d := Option.some.inj (hg.symm.trans hdg)
                have hAj : Anc0 M g j := anc_between hAgx j (by omega) (by omega)
                have hAi := anc0_par hAj (by omega) (mem_children_iff.mp (show j ∈ children M i by
                  rw [hch]; simp)).2
                have := hAi.le
                have := (mem_children hdM).1
                omega
              apply bumpTerm_eq_of
              · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
              · intro _
                rw [children_pre0 hlen hL hp hn (by omega) hdg]
                apply List.map_congr_left
                intro e he
                have her := children_lt_r hlen hL hp (by omega) hdg he
                exact (hoffD e her).1 (hLnd d hd e he).2
            have hKv : Kb.map σ.o = Kb.map ρ.o := List.map_congr_left (fun d hd => by
              have := hKk d hd; exact (hoffD d (by omega)).1 (hKnd d hd))
            have hbjM : bumpTerm M ρ i j = omega (sumN (Kb.map ρ.o ++ [ρ.o k])) := by
              unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
            have hbjN : bumpTerm (TRIO.gexp M r L 0 0 n) σ i j = omega (sumN (Kb.map ρ.o ++ [σ.o k])) := by
              unfold bumpTerm
              rw [if_pos (by rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hjb),
                hchjN, List.map_append, List.map_singleton, hKv]
            have hIH : Lhd z (σ.o k) (ρ.o k) :=
              ih _ (by have := (hRr h1).2.2 h2 j hj hjb k hk; omega) true k (le_refl _) hdk hkr'
            have hdec := hKD i h1 h2 j hj hjb
            rw [hchj, List.map_append, List.map_singleton] at hdec
            have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
              obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
              exact single_o hC hG (by have := hKk d hd; omega)
            have hform : (∃ s y y', ρ.o k = psi s y z ∧ σ.o k = psi s y' z) ∨
                (∃ w' w Y, σ.o k = psi w' z z ∧ ρ.o k = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
              obtain ⟨y1, hy1⟩ := o_psi_sub hC (show k < M.length by omega)
              rw [sf_ot (hG.ot_v k (by omega))] at hy1
              by_cases hvk : σ.v k = ρ.v k
              · obtain ⟨y0, hy0⟩ := o_psi_sub hCN (hiN k hkr')
                rw [sf_ot (hGN.ot_v k (hiN k hkr')), hvk] at hy0
                exact Or.inl ⟨_, _, _, hy1, hy0⟩
              · have hdv : DepX M (r + L) false k := by
                  by_contra hn'; exact hvk ((hoffD k hkr').2 hn')
                have ho0 := o_N_noc hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hkr'
                  (cl_nil_of_depv hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hkr' hdv)
                have hvIH : Lhd z (σ.v k) (ρ.v k) :=
                  ih _ (by have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega)
                    false k (le_refl _) hdv hkr'
                have he1k : entry M 1 k ≠ 0 := by
                  intro he; apply hvk
                  rw [v_z_of_e1 hC (by omega) he, v_z_of_e1 hCN (hiN k hkr')
                    (by rw [entry_pre0 hlen hn 1 (by omega)]; exact he)]
                have hv0 : σ.v k ≠ z := v_ne_z_of_e1 hCN (hiN k hkr')
                  (by rw [entry_pre0 hlen hn 1 (by omega)]; exact he1k)
                exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
            obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG (by omega))
              (single_o hCN hGN (hiN k hkr')) hIH hform
            have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k])) = true := isOT_sumN _ (fun u hu => by
              rcases List.mem_append.mp hu with h | h
              · exact (hsK u h).1
              · simp at h; rw [h]; exact hG.ot_o k (by omega))
            have hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i) = vOpt ρ (par M 1 i) := by
              rw [par1_pre0 hlen hL hp hn hi]
              cases hpp : par M 1 i with
              | none => rfl
              | some m =>
                have := par_lt M 1 i m hpp
                exact (hoffD m (by omega)).2 (hpnd m hpp)
            exact v_bump_lhd hC hG hCN hiM (hiN i hi) h1 h2 (entry_pre0 hlen hn 1 (by omega))
              (entry_pre0 hlen hn 2 (by omega)) hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
              (hAbs i h1 h2 (fun _ _ _ _ => v_z_of_e1 hC (by omega) he1))
  exact fun b i hD hi => key _ b i (le_refl _) hD hi

end

end Ytosk
