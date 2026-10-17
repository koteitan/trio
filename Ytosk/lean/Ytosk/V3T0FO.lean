/-
**3 行・t = 0: 展開 N = M[n] の評価の FrameOT（枠の項が標準形）。**

枠の項 ψ_{v(i)}(spArg(v(i), Σ_{d ∈ Lc} o(d)))（Lc は数える子の並びの頭）:
- r より前の列（r の親 g で r が数えられる場合を除く）: 数える子の並びは M と同じ。枠の頭 Lc の子は
  最後の数える子でないので D に入らず（`p1_dep`）、値は M のもの。v も M のもの（v が変わる列は数える子が
  ない）。M の枠そのもの。
- r 以後のコピーの列: 中間のコピーは M の枠、最後のコピーは M.take x の枠（`cl_copy0`・`cl_take_B`）。
- g で r が数えられる場合（copy の根 omid が並ぶ枠）は仮定 hFOg（`frameOT_g0` で示す）。
-/
import Ytosk.V3T0Good

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **No rewriting in the rest, without standardness**: the summands of `R` are below every summand of `b`,
decreasing, and each has `y ≤ b` or `s < a`. -/
theorem spArg_eq_app_ge {a : T} : ∀ {b R : T},
    (∀ s y, psi s y z ∈ summands R → y ≤ b ∨ s < a) →
    (∀ q ∈ summands b, ∀ p ∈ summands R, p ≤ q) → (summands R).Pairwise (fun u v => v ≤ u) →
    spArg a b R = app b R
  | b, z, _, _, _ => by simp [spArg]
  | b, psi s y R, hR, hge, hdec => by
    rw [spArg_cons]
    have hst : step a b s y R = app b (psi s y z) := by
      unfold step
      have hno : ¬ (lt b y = true ∧ lt (psi a z z) (psi s y R) = true) := by
        rintro ⟨h1, h2⟩
        rcases hR s y (by simp [summands]) with h | h
        · exact absurd (show b < y from h1) (not_lt_of_ge h)
        · have h2' : psi a z z < psi s y R := h2
          rw [T.psi_lt_psi] at h2'
          rcases h2' with h3 | ⟨h3, _⟩ | ⟨h3, _, _⟩
          · exact lt_asymm h3 h
          · subst h3; exact lt_irrefl _ h
          · subst h3; exact lt_irrefl _ h
      rw [if_neg hno]
      exact add_eq_app_of_ge ⟨s, y, rfl⟩ b (fun q hq => hge q hq _ (by simp [summands]))
    rw [hst]
    simp only [summands, List.pairwise_cons] at hdec
    have hassoc : app (app b (psi s y z)) R = app b (psi s y R) := by rw [app_assoc]; simp
    rw [spArg_eq_app_ge (b := app b (psi s y z)) (R := R)
      (fun s' y' h => (hR s' y' (by simp [summands, h])).imp_left
        (fun h' => le_trans h' (le_app_self _ _)))
      (fun q hq p hp => by
        rw [summands_app] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hge q hq p (by simp [summands, hp])
        · simp [summands] at hq; rw [hq]; exact hdec.1 p hp)
      hdec.2, hassoc]

/-- A summand at most `Ω_a` reads nothing in the state: `y ≤ b` or `s < a`. -/
theorem le_or_lt_of_le_om {a s y b : T} (h : ¬ psi a z z < psi s y z) : y ≤ b ∨ s < a := by
  rcases lt_trichotomy' s a with h1 | rfl | h1
  · exact Or.inr h1
  · left
    rcases (le_iff _ _).mp (z_le y) with hy | hy
    · exact absurd (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hy⟩)) h
    · rw [← hy]; exact z_le _
  · exact absurd (psi_lt_psi_z_iff.mpr (Or.inl h1)) h

theorem mulT_add (t : T) : ∀ j k, mulT t (j + k) = app (mulT t j) (mulT t k)
  | 0, k => by simp [mulT]
  | j + 1, k => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    show app t (mulT t (j + k)) = app (app t (mulT t j)) (mulT t k)
    rw [mulT_add t j k, app_assoc]

/-- **A prefix of a standard `ψ_a` argument gives a standard `ψ_a`.** -/
theorem psi_ot_prefix {a S T' : T} (h : isOT (psi a (app S T') z) = true) : isOT (psi a S z) = true := by
  rw [isOT_psi_iff] at h ⊢
  obtain ⟨ha, hS, _, _, hc⟩ := h
  refine ⟨ha, isOT_app_left hS, rfl, z_le _, fun g hg => ?_⟩
  exact comps_lt_prefix hg (hc g (by rw [comps_app]; exact List.mem_append_left _ hg))

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **The frames of the valuation of `N = M[n]` are standard** (`t = 0`), given those at the parent `g`
of `r` when `r` counts there. -/
theorem frameOT_N_t0 {ρ' : Valn} (hFO : FrameOT M ρ) (hFOT : FrameOT (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hFOg : ∀ g, par M 0 r = some g → Counted M g r →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (TRIO.gexp M r L 0 0 n) g = Lc ++ c :: R →
        isOT (psi (σ.v g) (spArg (σ.v g) z (sumN (Lc.map σ.o))) z) = true) :
    FrameOT (TRIO.gexp M r L 0 0 n) σ := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  intro i hi Lc c R hCL
  rcases Nat.lt_or_ge i r with hir | hir
  · by_cases hgc : par M 0 r = some i ∧ Counted M i r
    · exact hFOg i hgc.1 hgc.2 Lc c R hCL
    have hb : par M 0 r = some i → col M r = bump M i := by
      intro hig
      by_contra hb
      exact hgc ⟨hig, hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
    rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hir hb] at hCL
    have hiM : i < M.length := by omega
    -- the counted children before `c` are not in `D`
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hccnt : Counted M i c := by
      have := hcCL; unfold CL at this; simpa using (List.mem_filter.mp this).2
    have hsort : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ (children_sorted M i)
    rw [hCL] at hsort
    have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
      intro d hd
      have hdc : d < c := (List.pairwise_append.mp hsort).2.2 d hd c (by simp)
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdr : d < r := by
        have hdch := cl_mem_children hdCL
        by_cases hig : par M 0 r = some i
        · have hle := children_g_le hlen hL hp hig hdch
          have hcle := children_g_le hlen hL hp hig (cl_mem_children hcCL)
          omega
        · exact children_lt_r hlen hL hp hir hig hdch
      apply (hoffD d hdr).1
      intro hD
      exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) (cl_mem_children hdCL)
        (cl_mem_children hcCL) hdc hD hccnt
    have hv : σ.v i = ρ.v i := by
      apply (hoffD i hir).2
      intro hD
      exact uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hD (cl_mem_children hcCL) hccnt
    rw [hv, List.map_congr_left hLc]
    exact hFO i hiM Lc c R hCL
  · -- a copy column
    have hk0 : (i - r) / L < n := by
      rw [hlN] at hi
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hq0 : (i - r) % L < L := Nat.mod_lt _ hL
    have hi' : i = r + ((i - r) / L * L + (i - r) % L) := by
      have := Nat.div_add_mod (i - r) L
      rw [Nat.mul_comm] at this; omega
    obtain ⟨k, q, hk, hq, rfl⟩ : ∃ k q, k < n ∧ q < L ∧ i = r + (k * L + q) :=
      ⟨_, _, hk0, hq0, hi'⟩
    rw [cl_copy0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hk hq] at hCL
    obtain ⟨G, hGdef⟩ : ∃ G, G = ((children M (r + q)).filter (fun c => decide (c < r + L))).filter
      (fun d => decide (Counted M (r + q) d)) := ⟨_, rfl⟩
    rw [← hGdef] at hCL
    obtain ⟨Lc', T', hGs, hLc', hT'⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', rfl, hc', hR'⟩ := List.map_eq_cons_iff.mp hT'
    have hGm : ∀ d ∈ G, r + q < d ∧ d < r + L := fun d hd => by
      rw [hGdef] at hd
      have h := List.mem_filter.mp (List.mem_filter.mp hd).1
      exact ⟨(mem_children h.1).1, by simpa using h.2⟩
    have hval : ∀ d ∈ Lc', σ.o (shk r (k * L) d) = if k + 1 < n then ρ.o d else ρ'.o d := by
      intro d hd
      obtain ⟨h1, h2⟩ := hGm d (by rw [hGs]; simp [hd])
      obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
      have hkL : k * L + L ≤ n * L := by
        have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
      simp only [shk, if_pos (show r ≤ r + q' by omega)]
      rw [show r + q' + k * L = r + (k * L + q') by omega, (hσB _ (by omega) (by rw [hlN]; omega)).1]
      split
      · rename_i hkn; exact tau_o_mid hkn (by omega) (by omega)
      · have hk' : k = n - 1 := by omega
        rw [hk']
        exact tau_o_last (by omega)
    rw [← hLc', List.map_map]
    have hLc'' : Lc'.map (σ.o ∘ shk r (k * L)) = Lc'.map (if k + 1 < n then ρ.o else ρ'.o) := by
      apply List.map_congr_left
      intro d hd
      simp only [Function.comp]
      rw [hval d hd]
      split <;> rfl
    rw [hLc'', (hσB _ (by omega) hi).2]
    by_cases hkn : k + 1 < n
    · rw [if_pos hkn, tau_v_mid hkn hq]
      -- the frame of `M` at `r + q`
      have hCLM : ∃ X, CL M (r + q) = G ++ X := by
        by_cases hxq : r + L ∈ children M (r + q)
        · refine ⟨((([r + L] : List Nat)).filter (fun d => decide (Counted M (r + q) d))), ?_⟩
          unfold CL
          rw [hGdef]
          conv_lhs => rw [children_split_x (x := r + L) hlen hxq]
          rw [List.filter_append]
        · refine ⟨[], ?_⟩
          unfold CL
          rw [hGdef, children_filter_x (x := r + L) hlen hxq, List.append_nil]
      obtain ⟨X, hX⟩ := hCLM
      exact hFO (r + q) (by omega) Lc' c' (R' ++ X) (by rw [hX, hGs]; simp)
    · rw [if_neg hkn]
      have hk' : k = n - 1 := by omega
      rw [show r + (k * L + q) = r + ((n - 1) * L + q) by rw [hk'], tau_v_last hq]
      exact hFOT (r + q) (by rw [List.length_take]; omega) Lc' c' R'
        (by rw [cl_take_B hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hq, ← hGdef, hGs])

/-- **The frames at the parent `g` of `r` when `r` counts there**, from the standard value `σ.o g`: after
the first copy root nothing rewrites, so the final argument extends every frame state. -/
theorem frameOT_g0 {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hl : ρ'.o r < ρ.o r)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hFO : FrameOT M ρ) (hOTg : isOT (σ.o g) = true) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (TRIO.gexp M r L 0 0 n) g = Lc ++ c :: R →
      isOT (psi (σ.v g) (spArg (σ.v g) z (sumN (Lc.map σ.o))) z) = true := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  obtain ⟨Lc0, Cm, hclM, hclN, hLcv, hCmv⟩ := g0_shape hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2
    hC hG hCN hGN hg hcnt hσG hσmid hσlast hLast hl
  have hdecN := dec_g0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hg hcnt hσG hσmid
    hσlast hLast hl
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hLcv' : ∀ d ∈ Lc0, σ.o d = ρ.o d := List.map_inj_left.mp hLcv
  have hCmv' : ∀ d ∈ Cm, σ.o d = omid M r L ρ := fun d hd =>
    (List.eq_replicate_iff.mp hCmv).2 _ (List.mem_map_of_mem hd)
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  rw [hclM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hOX : omid M r L ρ < ρ.o r := by
    rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
  have hOS : Single (omid M r L ρ) := by
    rw [← hσmid 0 (by omega)]
    exact single_oT hCN hGN (by rw [hlN]; omega)
  obtain ⟨Y0, hOY⟩ : ∃ Y0, omid M r L ρ = psi (ρ.v r) Y0 z := ⟨_, hom⟩
  have hsL : ∀ t ∈ Lc0.map ρ.o, Single t := fun t ht => hsM t (List.mem_append_left _ ht)
  have hpL := (List.pairwise_append.mp hpM).1
  have hLr : ∀ t ∈ Lc0.map ρ.o, ρ.o r ≤ t := fun t ht => (List.pairwise_append.mp hpM).2.2 t ht _ (by simp)
  -- the frame of `M` after a prefix of `Lc0`
  have hMfr : ∀ Lc c'' R'', CL M g = Lc ++ c'' :: R'' → (∀ d ∈ Lc, d ∈ Lc0) →
      isOT (psi (σ.v g) (spArg (σ.v g) z (sumN (Lc.map σ.o))) z) = true := by
    intro Lc c'' R'' hCLM hsub
    rw [hσvg, List.map_congr_left (fun d hd => hLcv' d (hsub d hd))]
    exact hFO g hgM Lc c'' R'' hCLM
  intro Lc c R hCL
  rw [hclN, List.append_assoc] at hCL
  rcases List.append_eq_append_iff.mp hCL with ⟨a', hLc, hrest⟩ | ⟨c', hLc0, hrest⟩
  swap
  · -- `Lc` is a prefix of `Lc0`
    obtain ⟨c'', R'', hcR⟩ : ∃ c'' R'', c' ++ [r] = c'' :: R'' := by
      cases h : c' ++ [r] with
      | nil => simp at h
      | cons c'' R'' => exact ⟨c'', R'', rfl⟩
    exact hMfr Lc c'' R'' (by rw [hclM, hLc0, List.append_assoc, hcR])
      (fun d hd => by rw [hLc0]; exact List.mem_append_left _ hd)
  -- `Lc = Lc0 ++ a'` with `a'` a prefix of the copy roots
  subst hLc
  have hsubC : a'.Sublist Cm := by
    rcases List.append_eq_append_iff.mp hrest.symm with ⟨b, hb, _⟩ | ⟨b, hb, hb2⟩
    · rw [hb]; exact List.sublist_append_left _ _
    · have := congrArg List.length hb2
      simp at this
      have hbz : b = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hb, hbz, List.append_nil]
  have ha' : ∀ d ∈ a', d ∈ Cm := fun d hd => hsubC.subset hd
  by_cases hj0 : a' = []
  · subst hj0
    rw [List.append_nil]
    exact hMfr Lc0 r [] (by rw [hclM]) (fun d hd => hd)
  set j := a'.length with hjdef
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact absurd (List.eq_nil_of_length_eq_zero h) hj0
    · exact h
  have ha'v : a'.map σ.o = List.replicate j (omid M r L ρ) :=
    List.eq_replicate_iff.mpr ⟨by simp [hjdef], fun b hb => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb; exact hCmv' d (ha' d hd)⟩
  have hjm : j ≤ Cm.length := hsubC.length_le
  rw [List.map_append, hLcv, ha'v, hσvg]
  -- sums
  have hsLO : ∀ k, ∀ t ∈ Lc0.map ρ.o ++ List.replicate k (omid M r L ρ), Single t := fun k t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsL t h
    · rw [(List.mem_replicate.mp h).2]; exact hOS
  have hpLO : ∀ k, (Lc0.map ρ.o ++ List.replicate k (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := fun k =>
    List.pairwise_append.mpr ⟨hpL, List.pairwise_replicate.mpr (Or.inr (le_refl _)),
      fun a ha b hb => by rw [(List.mem_replicate.mp hb).2]; exact le_trans (le_of_lt hOX) (hLr a ha)⟩
  have hsum : ∀ k, sumN (Lc0.map ρ.o ++ List.replicate k (omid M r L ρ)) =
      app (sumN (Lc0.map ρ.o)) (mulT (omid M r L ρ) k) := fun k => by
    rw [sumN_append_dec (hsLO k) (hpLO k), sumN_replicate hOS]
  rw [hsum j, spArg_app]
  -- the value at `g`
  have hog := o_cl_eqT hCN hGN hgN hdecN
  rw [hclN, hσvg] at hog
  simp only [List.map_append, List.map_singleton] at hog
  rw [hLcv, hCmv, hσlast] at hog
  have hpN : (Lc0.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r]).Pairwise
      (fun a b => b ≤ a) := by
    have := hdecN
    rw [hclN] at this; simp only [List.map_append, List.map_singleton] at this
    rwa [hLcv, hCmv, hσlast] at this
  have hsN : ∀ t ∈ Lc0.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r], Single t := by
    have := cl_valsT hCN hGN (i := g)
    rw [hclN] at this; simp only [List.map_append, List.map_singleton] at this
    rwa [hLcv, hCmv, hσlast] at this
  have hsfin : sumN (Lc0.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r]) =
      app (app (sumN (Lc0.map ρ.o)) (mulT (omid M r L ρ) Cm.length)) (ρ'.o r) := by
    rw [sumN_append_dec hsN hpN, hsum Cm.length, sumN_singleton (hsN _ (by simp))]
  rw [hsfin, spArg_app, spArg_app] at hog
  have hO' : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := hsN (ρ'.o r) (by simp)
    have h := hl
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hfin : spArg (ρ.v g) (spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o)))
      (mulT (omid M r L ρ) Cm.length)) (ρ'.o r) =
      spArg (ρ.v g) (spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) (mulT (omid M r L ρ) j))
        (app (mulT (omid M r L ρ) (Cm.length - j)) (ρ'.o r)) := by
    rw [← spArg_app, show Cm.length = j + (Cm.length - j) by omega, mulT_add, app_assoc, spArg_app,
      show j + (Cm.length - j) - j = Cm.length - j by omega]
  rw [hfin] at hog
  have hOot : isOT (psi (ρ.v r) Y0 z) = true := by rw [← hOY]; exact hOS.1
  have hnr := no_rw_after (a := ρ.v g) (B := spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) hOot hj1
  rw [← hOY] at hnr
  -- no rewriting after the frame state
  have hsumT : summands (app (mulT (omid M r L ρ) (Cm.length - j)) (ρ'.o r)) =
      List.replicate (Cm.length - j) (omid M r L ρ) ++ [ρ'.o r] := by
    rw [summands_app, summands_mulT_eq ⟨_, _, hOY⟩]
    obtain ⟨_, s', y', hs'⟩ := hsN (ρ'.o r) (by simp)
    rw [hs']; simp [summands]
  have hSjO : ∀ q ∈ summands (spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o)))
      (mulT (omid M r L ρ) j)), omid M r L ρ ≤ q := by
    apply spArg_summands_ge ⟨_, _, hOY⟩ (mulT (omid M r L ρ) j) _ (isOT_mulT hOS.1 hOS.2 j)
    · intro q hq; rw [summands_mulT hOS.2 j q hq]
    · apply spArg_summands_ge ⟨_, _, hOY⟩ (sumN (Lc0.map ρ.o)) z (sumN_dec _ hsL hpL).1
      · rw [(sumN_dec _ hsL hpL).2]; intro q hq; exact le_trans (le_of_lt hOX) (hLr q hq)
      · simp [summands]
  have happ := spArg_eq_app_ge (a := ρ.v g)
    (b := spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) (mulT (omid M r L ρ) j))
    (R := app (mulT (omid M r L ρ) (Cm.length - j)) (ρ'.o r)) (by
      intro s y hsy
      rw [hsumT] at hsy
      have hlow : ¬ Y0 ≤ spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) (mulT (omid M r L ρ) j) →
          ¬ psi (ρ.v g) z z < omid M r L ρ := fun h h' => hnr ⟨lt_of_not_ge h, h'⟩
      rcases List.mem_append.mp hsy with h | h
      · have hO2 := (List.mem_replicate.mp h).2
        rw [hOY] at hO2
        simp only [psi.injEq] at hO2
        obtain ⟨rfl, rfl, -⟩ := hO2
        by_cases hY : y ≤ spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) (mulT (omid M r L ρ) j)
        · exact Or.inl hY
        · exact le_or_lt_of_le_om (by rw [← hOY]; exact hlow hY)
      · simp at h
        by_cases hs : s = ρ.v r
        · have hyY : y ≤ Y0 := by
            have := hO'
            rw [← h, hOY, hs] at this
            rcases (le_iff _ _).mp this with h1 | h1
            · rcases psi_lt_psi_z_iff.mp h1 with h2 | ⟨_, h2⟩
              · exact absurd h2 (lt_irrefl' _)
              · exact le_of_lt h2
            · simp only [psi.injEq] at h1; rw [h1.2.1]
          by_cases hY : Y0 ≤ spArg (ρ.v g) (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) (mulT (omid M r L ρ) j)
          · exact Or.inl (le_trans hyY hY)
          · apply le_or_lt_of_le_om
            intro h'
            exact hlow hY (lt_of_lt_of_le h' (by rw [h]; exact hO'))
        · left; rw [hy' s y h.symm hs]; exact z_le _)
    (by
      intro q hq p hp
      rw [hsumT] at hp
      rcases List.mem_append.mp hp with hp | hp
      · rw [(List.mem_replicate.mp hp).2]; exact hSjO q hq
      · simp at hp; rw [hp]; exact le_trans hO' (hSjO q hq))
    (by
      rw [hsumT]
      exact List.pairwise_append.mpr ⟨List.pairwise_replicate.mpr (Or.inr (le_refl _)), by simp,
        fun a ha b hb => by simp at hb; rw [hb, (List.mem_replicate.mp ha).2]; exact hO'⟩)
  rw [happ] at hog
  rw [hog] at hOTg
  exact psi_ot_prefix hOTg

end

end Ytosk
