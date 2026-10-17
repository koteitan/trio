/-
**t = 2: VSmallRAll を M[n] へ運ぶ骨組み（2026-10-17、t1）。**

clField_expand_t2S（V3T2VSR）と同じ 1 コピーごとの帰納法で、段の道つきの VSmallRAll を運ぶ。
枠ごとの主張は段 u を固定した `QVRAt a Lv cv u`（VSmallRAll の 1 つの枠・1 つの段の上限）。
- 接頭辞（k < x）で種の列でない枠: FrameShape（T2BelowXS）で M の枠と同じか最後の子が ◁ で下がる。
  段は M の段（名前つきの残り `T2VRAPre`）。M の VSmallRAll から `clField_of_shapeS`（Q を段 u で固定）。
- 写し（k = i + L ≥ x）: CopyFacts で P = M[n − 1] の枠の σ 像（守られた列）か等しい（守られない列）。
  意味のある段（書き換え・hi ≠ 0・成分あり）は P の段で u ≤ V（名前つきの残り `T2VRACopy`）。P の VSmallRAll
  （帰納法の仮定）と σ での移送 `QVRAshK K`（枠の条件 K のもと）から。K は守られた写しの枠の名前つきの残り
  `T2VRAK K M`。項だけの移送（K なし）は偽（V′ の成分が深い添字の f から入る、`QVRAshK` の注の反例）。
  `KStepVRA`（移送そのもの）なら `qVRAshK_step` で自明。
- 種の列の枠: 名前つきの残り `T2VRASeed`。
-/
import Ytosk.V3T2VSR
import Ytosk.V3ExpT2V2

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **One frame, one level of `VSmallRAll`.** -/
def QVRAt (a : T) (Lv : List T) (cv u : T) : Prop :=
  ∀ s y, cv = psi s y z →
    (lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z → ¬ lt a u = true →
    ∀ g ∈ comps u s, g ≤ psi s z z ∨ g ≤ spArg a z (sumN Lv) ∨ ∃ d ∈ comps u a, g ≤ d

/-- The levels at a column: its own `v` and the path levels. -/
def LevAt (N : Mat) (σ : Valn) (k : Nat) (u : T) : Prop := u = σ.v k ∨ PathLvAll N σ k u

theorem vsmallRAll_iff {N : Mat} {σ : Valn} :
    VSmallRAll N σ ↔ ∀ k (Lc : List Nat) c (R : List Nat), CL N k = Lc ++ c :: R →
      ∀ u, LevAt N σ k u → QVRAt (σ.v k) (Lc.map σ.o) (σ.o c) u := by
  constructor
  · intro h k Lc c R hcl u hu s y hsy ht hhz hku g hg
    exact h k c Lc R s y hcl hsy ht hhz u hu hku g hg
  · intro h k c Lc R s y hcl hsy ht hhz u hu hku g hg
    exact h k Lc c R hcl u hu s y hsy ht hhz hku g hg

/-- **`QVRAt` survives lowering the last child** (same subscript, or argument `0`). -/
theorem qVRAt_low : ∀ a Lv cv cv' u, QVRAt a Lv cv u → Lhd z cv' cv → isOT cv' = true →
    (∃ s y, cv = psi s y z) →
    (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → QVRAt a Lv cv' u := by
  intro a Lv cv cv' u hQ hl _ ⟨s, y, hcv⟩ hst s' y' hcv' htr hhi
  by_cases hss : s' = s
  · subst hss
    have hyy : y' < y := by
      have h := hl.1; rw [hcv', hcv] at h
      rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact h
    exact hQ s' y hcv ⟨lt_trans htr.1 hyy, lt_trans htr.2 (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩))⟩
      (split_fst_ne_of_le hhi (le_of_lt hyy))
  · have := hst s y s' y' hcv hcv' hss
    subst this
    exact absurd htr.1 (T.not_lt_z _)

/-- **The `σ`-transport of one frame at a level `u ≤ V`** under a frame condition `K`. Without a condition the
statement about terms only is false: a component of `V′` enters `f(s)` through a deep subscript of `s` and need
not be bounded in `f(a)` (V = Ω_2, V′ = Ω_3 + ψ_1(ψ_0(Ω_{Ω_{Ω_{Ω_9}}})), a = Ω_2 + Ω_2, u = 0,
cv = ψ_{Ω_{Ω_2+1}}(Ω_{Ω_{Ω_2+1}+1})). -/
def QVRAshK (K : T → T → T → List T → T → T → Prop) : Prop :=
  ∀ (V V' a : T) (Lv : List T) (cv u : T), isOT V = true → isOT V' = true → V < V' →
    isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
    (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
    u ≤ V → K V V' a Lv cv u → QVRAt a Lv cv u → QVRAt (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) u

/-- The frame condition that is the `σ`-transport itself. -/
def KStepVRA (V V' a : T) (Lv : List T) (cv u : T) : Prop :=
  QVRAt a Lv cv u → QVRAt (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) u

theorem qVRAshK_step : QVRAshK KStepVRA :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK hQ => hK hQ

/-- **A copy frame of `N`** from the frame of `P` at the level `u₁`, moved to the level `u`. -/
theorem copyFrame_VRA {K : T → T → T → List T → T → T → Prop} (hsh : QVRAshK K)
    {N P : Mat} {σ ρ : Valn} {r L : Nat} {V' : T} {g : Nat → Prop}
    (hF : CopyFacts N P σ ρ r L V' g) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hrP : r < P.length)
    (hV' : isOT V' = true) (hVV : ρ.v r < V')
    {i : Nat} (hri : r ≤ i) (hi : i < P.length) {u : T} (hgu : g i → u ≤ ρ.v r)
    (hK : g i → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL P i = Lc ++ c :: R →
      K (ρ.v r) V' (ρ.v i) (Lc.map ρ.o) (ρ.o c) u)
    (hQP : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL P i = Lc ++ c :: R →
      QVRAt (ρ.v i) (Lc.map ρ.o) (ρ.o c) u) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N (i + L) = Lc ++ c :: R →
      QVRAt (σ.v (i + L)) (Lc.map σ.o) (σ.o c) u := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  intro Lc c R h
  obtain ⟨hcl, hgc, hngc⟩ := hF i hri hi
  rw [hcl] at h
  obtain ⟨Lc0, rest, hsplit, hLc, hrest⟩ := List.map_eq_append_iff.mp h
  obtain ⟨c0, R0, hrest0, hc, _⟩ := List.map_eq_cons_iff.mp hrest
  rw [hrest0] at hsplit
  have hQ := hQP Lc0 c0 R0 hsplit
  subst hLc; subst hc
  obtain ⟨hsM, hpM⟩ := cl_vals hCP hGP hi
  rw [hsplit] at hsM hpM
  have hmem : ∀ d ∈ Lc0 ++ [c0], d ∈ CL P i := fun d hd => by
    rw [hsplit]
    rcases List.mem_append.mp hd with h | h
    · exact List.mem_append_left _ h
    · simp at h; rw [h]; simp
  have hS' : ∀ t ∈ Lc0.map ρ.o ++ [ρ.o c0], Single t := fun t ht => by
    apply hsM
    rw [List.map_append, List.map_cons]
    rcases List.mem_append.mp ht with h | h
    · exact List.mem_append_left _ h
    · simp at h; rw [h]; simp
  have hP' : (Lc0.map ρ.o ++ [ρ.o c0]).Pairwise (fun a b => b ≤ a) := by
    rw [List.map_append, List.map_cons] at hpM
    have h1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨h1.1, by simp, fun a ha b hb => ?_⟩
    simp at hb; rw [hb]; exact h1.2.2 a ha _ (by simp)
  rw [List.map_map]
  by_cases hg : g i
  · obtain ⟨hv, hVi, hlt, hd⟩ := hgc hg
    have hmap : Lc0.map (σ.o ∘ (· + L)) = (Lc0.map ρ.o).map (sh V V') := by
      rw [List.map_map]; apply List.map_congr_left; intro d hd'
      exact (hd d (hmem d (List.mem_append_left _ hd'))).1
    rw [hv, hmap, (hd c0 (hmem c0 (by simp))).1]
    have hlevel : V < ρ.v i ∨ ∀ t ∈ Lc0.map ρ.o ++ [ρ.o c0], V < lev t := by
      rcases Nat.lt_or_ge r i with h1 | h1
      · exact Or.inl (hlt h1)
      · have hir : i = r := by omega
        right
        intro t ht
        have hdl : ∀ d ∈ Lc0 ++ [c0], V < lev (ρ.o d) := by
          intro d hd'
          have hdC := hmem d hd'
          obtain ⟨y', hy'⟩ := o_form hCP hGP (mem_children (cl_mem_children hdC)).2
          rw [hy']; exact (hd d hdC).2 hir
        rcases List.mem_append.mp ht with h | h
        · obtain ⟨d, hd', rfl⟩ := List.mem_map.mp h
          exact hdl d (List.mem_append_left _ hd')
        · simp at h; rw [h]; exact hdl c0 (by simp)
    exact hsh V V' (ρ.v i) (Lc0.map ρ.o) (ρ.o c0) u hVo hV' hVV (hGP.ot_v i hi) hVi hS' hP' hlevel (hgu hg)
      (hK hg Lc0 c0 R0 hsplit) hQ
  · obtain ⟨hv, hd⟩ := hngc hg
    have hmap : Lc0.map (σ.o ∘ (· + L)) = Lc0.map ρ.o := by
      apply List.map_congr_left; intro d hd'; exact hd d (hmem d (List.mem_append_left _ hd'))
    rw [hv, hmap, hd c0 (hmem c0 (by simp))]
    exact hQ

/-- `M[n]` (`t = 2`) in the `gexp` form. -/
noncomputable abbrev G2 (M : Mat) (r L n : Nat) : Mat :=
  TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n

/-- **R-seed (VSmallRAll)**: the frames of the seed columns of `M[n]`. -/
def T2VRASeed (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
    ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ i, T2SeedCol M r L i → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) i = Lc ++ c :: R →
      ∀ u, LevAt (G2 M r L n) σ i u → QVRAt (σ.v i) (Lc.map σ.o) (σ.o c) u

/-- **R-pre (VSmallRAll)**: the path levels of `M[n]` before `x`, away from the seed columns, are levels of `M`. -/
def T2VRAPre (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
    ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ k, k < r + L → ¬ T2SeedCol M r L k → ∀ u, PathLvAll (G2 M r L n) σ k u → PathLvAll M ρ k u

/-- **R-copy (VSmallRAll)**: a level that matters at a copy frame of `M[n]` (rewriting, `hi ≠ 0`, at most the
parent's `v`, with a component) is a level of `M[n − 1]` at the copied column, and at most `V = v_P(r)`. -/
def T2VRACopy (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
    ∀ σ ρP, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    Cons (G2 M r L (n - 1)) ρP → Good3 (G2 M r L (n - 1)) ρP →
    ∀ i, r ≤ i → i < (G2 M r L (n - 1)).length →
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) (i + L) = Lc ++ c :: R →
    ∀ s y, σ.o c = psi s y z →
    (lt (spArg (σ.v (i + L)) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v (i + L)) z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, LevAt (G2 M r L n) σ (i + L) u → ¬ lt (σ.v (i + L)) u = true → comps u s ≠ [] →
      LevAt (G2 M r L (n - 1)) ρP i u ∧ u ≤ ρP.v r

/-- **R-copy-K (VSmallRAll)**: the frame condition `K` at the guarded copy frames of `M[n − 1]`, at its levels
`u ≤ V` (`V = v_P(r)`, `V′ = v_N(r + L)`). -/
def T2VRAK (K : T → T → T → List T → T → T → Prop) (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
    ∀ σ ρP, Cons (G2 M r L n) σ → Cons (G2 M r L (n - 1)) ρP → Good3 (G2 M r L (n - 1)) ρP →
    ∀ i, r ≤ i → i < (G2 M r L (n - 1)).length → TRIO.le1 (G2 M r L (n - 1)) r i →
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L (n - 1)) i = Lc ++ c :: R →
    ∀ u, LevAt (G2 M r L (n - 1)) ρP i u → u ≤ ρP.v r →
      K (ρP.v r) (σ.v (r + L)) (ρP.v i) (Lc.map ρP.o) (ρP.o c) u

/-- **VSmallRAll of every `M[n]`** (`t = 2`, `n ≥ 1`) from VSmallRAll of `M` and `M.take x` and the named
residuals. -/
theorem vsmallRAll_expand_t2 {K : T → T → T → List T → T → T → Prop} (hsh : QVRAshK K) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hVM : VSmallRAll M ρ)
    (hVT : ∀ τ, Cons (M.take (M.length - 1)) τ → VSmallRAll (M.take (M.length - 1)) τ)
    (hSeed : T2VRASeed M) (hPre : T2VRAPre M ρ) (hCopy : T2VRACopy M) (hKM : T2VRAK K M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → VSmallRAll (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr hVT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by omega
  have hd0 : 0 < entry M 0 (r + L) - entry M 0 r := by omega
  have hd1 : 0 < entry M 1 (r + L) - entry M 1 r := by omega
  have hexp : ∀ n, expand M n = G2 M r L n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (G2 M r L m) σ → Good3 (G2 M r L m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (G2 M r L m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBE : ∀ m, 1 ≤ m → BumpE2 (G2 M r L m) := fun m _ => by
    rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (G2 M r L n) σ → VSmallRAll (G2 M r L n) σ := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ
        unfold G2 at hσ ⊢
        rw [gexp_one_gen hlen] at hσ ⊢
        exact hVT σ hσ
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        set ρP := rhsIt (G2 M r L m) (rkBound (G2 M r L m) rkP) with hρP
        have hCP : Cons (G2 M r L m) ρP := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hQP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hSD
        have hF := copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (G2 M r L (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (G2 M r L m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (G2 M r L m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have hGN := hG (m + 1) (by omega) σ hCN
        apply vsmallRAll_iff.mpr
        intro k Lc c Rr hCL u hu
        rcases Nat.lt_or_ge k (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L k
          · exact hSeed r L hlen hr (m + 1) hn2 σ hCN hGN k hsc Lc c Rr hCL u hu
          · have hshp := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN
              (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) k hix).2.2.2.1 hsc
            have hlevM : LevAt M ρ k u := by
              rcases hu with hu | hu
              · left
                rw [hu]
                rcases hshp with ⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨hN, _⟩
                · exact hv
                · exact hv
                · rw [hN] at hCL; simp at hCL
              · exact Or.inr (hPre r L hlen hr (m + 1) hn2 σ hCN hGN k hix hsc u hu)
            exact clField_of_shapeS (Q := fun a Lv cv => QVRAt a Lv cv u)
              (fun a Lv cv cv' h1 h2 h3 h4 h5 => qVRAt_low a Lv cv cv' u h1 h2 h3 h4 h5)
              I.cons I.good hCN hGN hshp
              (fun Lc0 c0 R0 h => (vsmallRAll_iff.mp hVM) k Lc0 c0 R0 h u hlevM) Lc c Rr hCL
        · obtain ⟨a, rfl⟩ : ∃ a, k = r + a + L := ⟨k - L - r, by omega⟩
          have hia : r + a < (G2 M r L m).length := by
            have hkN : r + a + L < (G2 M r L (m + 1)).length :=
              (mem_children (cl_mem_children (show c ∈ CL _ (r + a + L) by rw [hCL]; simp))).1.trans
                (mem_children (cl_mem_children (show c ∈ CL _ (r + a + L) by rw [hCL]; simp))).2
            omega
          intro s y hsy ht hhi hku
          by_cases hcs : comps u s = []
          · intro g hg; rw [hcs] at hg; simp at hg
          obtain ⟨hu1, huV⟩ := hCopy r L hlen hr (m + 1) hn2 σ _ hCN hGN hCP hGP (r + a) (by omega) hia
            Lc c Rr hCL s y hsy ht hhi u hu hku hcs
          exact copyFrame_VRA hsh hF hCP hGP hrP hV' hVV (i := r + a) (by omega) hia (fun _ => huV)
            (fun hg Lc0 c0 R0 h => hKM r L hlen hr (m + 1) hn2 σ _ hCN hCP hGP (r + a) (by omega) hia hg
              Lc0 c0 R0 h u hu1 huV)
            (fun Lc0 c0 R0 h => (vsmallRAll_iff.mp hQP) (r + a) Lc0 c0 R0 h u hu1) Lc c Rr hCL
            s y hsy ht hhi hku
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

/-- Path levels do not depend on the valuation outside the matrix. -/
theorem pathLvAll_congr {N : Mat} {σ τ : Valn} (h : Agree N σ τ) {c : Nat} {u : T}
    (hp : PathLvAll N τ c u) : PathLvAll N σ c u := by
  induction hp with
  | @top k c Lc R s y hcl hsy ht =>
    have hcCL : c ∈ CL N k := by rw [hcl]; simp
    have hcc := (mem_children (cl_mem_children hcCL))
    have hkN : k < N.length := by omega
    have hLo : Lc.map σ.o = Lc.map τ.o := List.map_congr_left (fun d hd =>
      (h d (mem_children (cl_mem_children (show d ∈ CL N k by rw [hcl]; simp [hd]))).2).1)
    rw [← (h k hkN).2]
    exact PathLvAll.top hcl (by rw [(h c hcc.2).1]; exact hsy) (by rw [(h k hkN).2, hLo]; exact ht)
  | @step k c Lc R s y u hcl hsy ht _ ih =>
    have hcCL : c ∈ CL N k := by rw [hcl]; simp
    have hcc := (mem_children (cl_mem_children hcCL))
    have hkN : k < N.length := by omega
    have hLo : Lc.map σ.o = Lc.map τ.o := List.map_congr_left (fun d hd =>
      (h d (mem_children (cl_mem_children (show d ∈ CL N k by rw [hcl]; simp [hd]))).2).1)
    exact PathLvAll.step hcl (by rw [(h c hcc.2).1]; exact hsy) (by rw [(h k hkN).2, hLo]; exact ht) ih

/-- `VSmallRAll` does not depend on the valuation outside the matrix. -/
theorem vsmallRAll_congr {N : Mat} {σ τ : Valn} (h : Agree N σ τ) (hV : VSmallRAll N σ) : VSmallRAll N τ := by
  intro k c Lc R s y hcl hsy ht hhi u hu hku g hg
  have hcCL : c ∈ CL N k := by rw [hcl]; simp
  have hcc := (mem_children (cl_mem_children hcCL))
  have hkN : k < N.length := by omega
  have hLo : Lc.map σ.o = Lc.map τ.o := List.map_congr_left (fun d hd =>
    (h d (mem_children (cl_mem_children (show d ∈ CL N k by rw [hcl]; simp [hd]))).2).1)
  rw [← (h k hkN).2, ← hLo]
  rw [← (h k hkN).2, ← hLo] at ht
  rw [← (h k hkN).2] at hku
  refine hV k c Lc R s y hcl (by rw [(h c hcc.2).1]; exact hsy) ht hhi u ?_ hku g hg
  rcases hu with hu | hu
  · exact Or.inl (by rw [hu, (h k hkN).2])
  · exact Or.inr (pathLvAll_congr h hu)

/-- **T2VRAV2 from the named residuals.** -/
theorem t2VRAV2_of {K : T → T → T → List T → T → T → Prop} (hsh : QVRAshK K) (hB : T2BelowXResV2)
    (hSeedG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeed M)
    (hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ)
    (hCopyG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopy M)
    (hKG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK K M) : T2VRAV2 := by
  intro M ρ rk C hz h2 n hn σ rkN hCN _ _ _
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  have hl2 : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr; omega
  obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
  have hRk1 : Rk (M.take (M.length - 1)) rk := I1.rank
  have hC1 := I1.cons
  exact vsmallRAll_expand_t2 hsh (hB M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 C.I.vra
    (fun τ hτ => vsmallRAll_congr (agree_of_cons hC1 hτ hRk1) I1.vra)
    (hSeedG M ρ rk C hz h2) (hPreG M ρ rk C hz h2) (hCopyG M ρ rk C hz h2) (hKG M ρ rk C hz h2) n (by omega) σ hCN

end Ytosk
