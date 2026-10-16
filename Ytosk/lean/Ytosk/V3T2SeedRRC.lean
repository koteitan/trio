/-
**3 行・t = 2: 種での RClaimU・REr（T2SeedRR）を 4 つの場合ごとに（2026-10-17、t2）。**

qr: X = B + Ω_s（s = v(x)）、X′ = B + ψ_{V+k+1}(σ^k W₁)（seqZ_form）。閉じた条件は残り T2SeedQRRes の dom の欄。
-/
import Ytosk.V3T2SeedRR
import Ytosk.V3T2BelowV2
import Ytosk.V3T2SeedRes

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem z_lt_of_ne_z {t : T} (h : t ≠ z) : z < t := by
  cases t with
  | z => exact absurd rfl h
  | psi _ _ _ => exact T.z_lt_psi _ _ _

/-- A component is not the term itself. -/
theorem lt_of_le_comps {u t g : T} (hg : g ∈ comps u t) (h : g ≤ t) : g < t := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact h
  · exact absurd (size_comps hg) (lt_irrefl _)

/-- **T2SeedRR at the seed `r`, `q = r` without an upgrade into `x`.** -/
theorem seedRR_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        isOT (σ.o r) = true → T2SeedRR M ρ σ r := by
  intro n hn hGlow σ hCN hot'
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  obtain ⟨hBc, _, hoM⟩ := qr_M_side I hlen hrx hCLM
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hVot := I.good.ot_v r hrM
  have hσN := seed_r_value_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨rk, hRk1⟩ n hn hGlow σ hCN
  have hform := seqZ_form (B := t2B (ρ.v r) ρ Lc) (W1 := t2W1 (M.take (r + L)) (ρ.v r) (rhsIt (M.take (r + L))
    (rkBound (M.take (r + L)) rk)) r) hVot (tame_sigmaB_std hM hS I hlen hr hq hXu hCLM) hBc hRes.ks (n - 2)
  rw [hσN] at hot'
  rw [hform] at hσN hot'
  have hot : isOT (psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + L)) z z)) z) = true := by
    rw [← hoM]; exact I.good.ot_o r hrM
  -- every summand is at least `Ω_{V+1}`
  have hsV : succ (ρ.v r) < ρ.v (r + L) := by rw [succ_eq_addN_one]; exact hRes.ks 1
  have hBhi : ∀ q ∈ summands (t2B (ρ.v r) ρ Lc), ¬ q < psi (succ (ρ.v r)) z z := by
    intro q hq hlt
    have h1 := hBc q hq
    have h2' : psi (succ (ρ.v r)) z z < psi (ρ.v (r + L)) z z := psi_lt_psi_z_iff.mpr (Or.inl hsV)
    exact lt_irrefl' _ (lt_of_le_of_lt h1 (lt_trans hlt h2'))
  have hall : ∀ q ∈ summands (app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + L)) z z)),
      ¬ q < psi (succ (ρ.v r)) z z := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hBhi q hq
    · simp [summands] at hq; rw [hq]
      intro hlt; rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with hlt | ⟨_, hlt⟩
      · exact lt_irrefl' _ (lt_trans hlt hsV)
      · exact T.not_lt_z _ hlt
  have hall' : ∀ q ∈ summands (app (t2B (ρ.v r) ρ Lc) (psi (addN (ρ.v r) (n - 2 + 1))
      (shN (ρ.v r) (n - 2) (t2W1 (M.take (r + L)) (ρ.v r) (rhsIt (M.take (r + L))
        (rkBound (M.take (r + L)) rk)) r)) z)), ¬ q < psi (succ (ρ.v r)) z z := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hBhi q hq
    · simp [summands] at hq; rw [hq]
      intro hlt; rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with hlt | ⟨_, hlt⟩
      · rw [succ_eq_addN_one] at hlt
        exact lt_irrefl' _ (lt_of_lt_of_le hlt (addN_le (by omega)))
      · exact T.not_lt_z _ hlt
  have hX'z : app (t2B (ρ.v r) ρ Lc) (psi (addN (ρ.v r) (n - 2 + 1))
      (shN (ρ.v r) (n - 2) (t2W1 (M.take (r + L)) (ρ.v r) (rhsIt (M.take (r + L))
        (rkBound (M.take (r + L)) rk)) r)) z) ≠ z := app_ne_z_right (by simp)
  refine ⟨fun U _ => rclaim_of_hiB0 hoM hσN hot hot' hall hall' hX'z
    (fun c h1 h2 => by obtain ⟨c0, e, _, _⟩ := between_app h1 h2; exact ⟨c0, e⟩) (fun u _ => ?_), ?_⟩
  · intro hu g hg
    rcases hRes.dom _ hC0 (n - 2) u hu g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl (lt_of_le_comps hg h)
    · rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_append.mp hd with hd | hd
        · exact Or.inr ⟨d, List.mem_append_left _ hd, hgd⟩
        · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩
      · rw [succ, comps_app] at hd
        rcases List.mem_append.mp hd with hd | hd
        · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩
        · rw [mem_comps_one hd] at hgd
          exact Or.inl (lt_of_le_of_lt hgd (z_lt_of_ne_z hX'z))
  · intro X X' hX hX' hne
    rw [hoM] at hX; rw [hσN] at hX'
    simp only [psi.injEq] at hX hX'
    rw [← hX.2.1, ← hX'.2.1]
    exact rEr_of_prefix (by simp)

/-- **The closedness residual of the seed `r`, `q ≠ r` with `q` the last counted child** (`M` and `M.take x`
only): the components of the subscript `t_k` of the new last summand `Ω_{t_k}` at the levels `u ≤ V` are below
`B + Ω_{t_k}` or below a component of `B` or of `V`. -/
def T2SeedQNCl (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
    ∀ k, 1 ≤ k → ∀ u, PathLvA M ρ r u → ¬ lt (ρ.v r) u = true →
      ∀ g ∈ comps u (tqN (ρ.v r) (qnS M ρ r L q) t1 k),
      g < app (t2B (ρ.v r) ρ Lc) (psi (tqN (ρ.v r) (qnS M ρ r L q) t1 k) z z) ∨
        ∃ d ∈ comps u (t2B (ρ.v r) ρ Lc) ++ comps u (ρ.v r), g ≤ d

/-- **T2SeedRR at the seed `r`, `q ≠ r` with `q` the last counted child of `r`.** -/
theorem seedRR_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
    (hCl : T2SeedQNCl M ρ r L q Lc) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ → isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map σ.o).Pairwise (fun a b => b ≤ a) →
      isOT (σ.o r) = true → T2SeedRR M ρ σ r := by
  intro n hn hGlow σ hCN hqOT hdecN hot'
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrM : r < M.length := by have := par_lt M 2 _ _ hr; omega
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hVq : ρ.v r < ρ.v q := lt_trans (qnS_gt M ρ r L q) (qn_vqlt hM hS I hlen hr hq hqr)
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  obtain ⟨_, _, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hoq : ρ.o (r + qp) = psi (ρ.v (r + qp)) z z := by
    rw [o_cl_eq I.cons I.good (show r + qp < M.length by omega), Tclq]; rfl
  obtain ⟨hBc, _, hoM⟩ := leaf_M_side I hrM hCLM hoq
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  obtain ⟨t1, ht1, hch⟩ := hRes.base _ hC0
  have hσN := seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 ⟨rk, hRk1⟩ hv0 ht1
    (fun k => ⟨(hch k).1, (hch k).2.1⟩) n hn hGlow σ hCN hqOT hdecN
  rw [hσN] at hot'
  have hot : isOT (psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + qp)) z z)) z) = true := by
    rw [← hoM]; exact I.good.ot_o r hrM
  have hVt := (hch (n - 1)).1
  -- every summand is at least `Ω_{V+1}`
  have hge : ∀ s, ρ.v r < s → ¬ psi s z z < psi (succ (ρ.v r)) z z := by
    intro s hs hlt
    rw [psi_lt_psi_z_iff] at hlt
    rcases hlt with hlt | ⟨_, hlt⟩
    · exact lt_irrefl' _ (lt_of_lt_of_le hlt (succ_le_of_lt hs))
    · exact T.not_lt_z _ hlt
  have hBhi : ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), ¬ g < psi (succ (ρ.v r)) z z :=
    fun g hg hlt => hge _ hVq (lt_of_le_of_lt (hBc g hg) hlt)
  have hall : ∀ g ∈ summands (app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + qp)) z z)),
      ¬ g < psi (succ (ρ.v r)) z z := by
    intro g hg
    rw [summands_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hBhi g hg
    · simp [summands] at hg; rw [hg]; exact hge _ hVq
  have hall' : ∀ g ∈ summands (app (t2B (ρ.v r) ρ Lc) (psi (tqN (ρ.v r) (qnS M ρ r L (r + qp)) t1 (n - 1)) z z)),
      ¬ g < psi (succ (ρ.v r)) z z := by
    intro g hg
    rw [summands_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hBhi g hg
    · simp [summands] at hg; rw [hg]; exact hge _ hVt
  have hX'z : app (t2B (ρ.v r) ρ Lc) (psi (tqN (ρ.v r) (qnS M ρ r L (r + qp)) t1 (n - 1)) z z) ≠ z :=
    app_ne_z_right (by simp)
  refine ⟨fun U hU => rclaim_of_hiB0 hoM hσN hot hot' hall hall' hX'z
    (fun c h1 h2 => by obtain ⟨c0, e, _, _⟩ := between_app h1 h2; exact ⟨c0, e⟩) (fun u hUu => ?_), ?_⟩
  · intro hu g hg
    have htu : ¬ tqN (ρ.v r) (qnS M ρ r L (r + qp)) t1 (n - 1) < u := fun h => hu (lt_trans' hVt h)
    rw [comps_app, comps_psi_z_of_ge htu] at hg
    simp only [comps, List.nil_append, List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact Or.inr ⟨g, List.mem_append_left _ hg, le_refl _⟩
    · exact Or.inl (z_lt_of_ne_z hX'z)
    · exact hCl _ hC0 t1 ht1 (n - 1) (by omega) u (hU u hUu) hu g hg
  · intro X X' hX hX' hne
    rw [hoM] at hX; rw [hσN] at hX'
    simp only [psi.injEq] at hX hX'
    rw [← hX.2.1, ← hX'.2.1]
    exact rEr_of_prefix (by simp)

/-- **The shape and closedness of an argument pair at a seed** (class B0, common prefix `P`, closed at the
levels `u ≤ V`). -/
def SeedClB0 (Lv : T → Prop) (V X X' : T) : Prop :=
  ∃ P b x T', X = app P (psi b x z) ∧ X' = app P T' ∧ T' ≠ z ∧
    (∀ q ∈ summands X, ¬ q < psi (succ V) z z) ∧ (∀ q ∈ summands X', ¬ q < psi (succ V) z z) ∧
    ∀ u, Lv u → ¬ lt V u = true → ∀ g ∈ comps u X', g < X' ∨ ∃ d ∈ comps u P ++ comps u V, g ≤ d

/-- **T2SeedRR from `SeedClB0`.** -/
theorem seedRR_of_clB0 {M : Mat} {ρ σ : Valn} {p : Nat} {X X' : T}
    (hX : ρ.o p = psi (ρ.v p) X z) (hX' : σ.o p = psi (ρ.v p) X' z)
    (hot : isOT (psi (ρ.v p) X z) = true) (hot' : isOT (psi (ρ.v p) X' z) = true)
    (h : SeedClB0 (PathLvA M ρ p) (ρ.v p) X X') : T2SeedRR M ρ σ p := by
  obtain ⟨P, b, x, T', rfl, rfl, hT, hall, hall', hcl⟩ := h
  refine ⟨fun U hU => rclaim_of_hiB0 hX hX' hot hot' hall hall' (app_ne_z_right hT)
    (fun c h1 h2 => by obtain ⟨c0, e, _, _⟩ := between_app h1 h2; exact ⟨c0, e⟩)
    (fun u hUu => hcl u (hU u hUu)), ?_⟩
  intro Y Y' hY hY' _
  rw [hX] at hY; rw [hX'] at hY'
  simp only [psi.injEq] at hY hY'
  rw [← hY.2.1, ← hY'.2.1]
  exact rEr_of_prefix hT

/-- **The closedness residual of the seed `r`, sv** (`M` and `M.take x` only). -/
def T2SeedSVCl (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k → ∀ X, ρ.o r = psi (ρ.v r) X z →
    SeedClB0 (PathLvA M ρ r) (ρ.v r) X (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)

/-- **The closedness residual of the seed `r`, C** (`M` and `M.take x` only). -/
def T2SeedCCl (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k → ∀ X, ρ.o r = psi (ρ.v r) X z →
    SeedClB0 (PathLvA M ρ r) (ρ.v r) X (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)

/-- The argument of `o(r)`. -/
theorem o_arg_form {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r : Nat}
    (hrM : r < M.length) : ∃ X, ρ.o r = psi (ρ.v r) X z := by
  exact ⟨_, o_spArg I.cons I.good hrM⟩

/-- **T2SeedRR at the seed `r`, sv.** -/
theorem seedRR_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L) (hCl : T2SeedSVCl M ρ r L) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ → ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map σ.o).Pairwise (fun a b => b ≤ a) →
      isOT (σ.o r) = true → T2SeedRR M ρ σ r := by
  intro n hn hGlow σ hCN hdecN hot'
  have hrM : r < M.length := by have := par_lt M 2 _ _ hr; omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hσN := seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hRk1 n hn hGlow σ hCN hdecN
  rw [hσN] at hot'
  obtain ⟨X, hoM⟩ := o_arg_form I hrM
  have hot : isOT (psi (ρ.v r) X z) = true := by rw [← hoM]; exact I.good.ot_o r hrM
  exact seedRR_of_clB0 hoM hσN hot hot' (hCl _ hC0 (n - 1) (by omega) X hoM)

/-- **T2SeedRR at the seed `r`, C.** -/
theorem seedRR_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q) (hCl : T2SeedCCl M ρ r L q) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ → isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map σ.o).Pairwise (fun a b => b ≤ a) →
      isOT (σ.o r) = true → T2SeedRR M ρ σ r := by
  intro n hn hGlow σ hCN hqOT hdecN hot'
  have hrM : r < M.length := by have := par_lt M 2 _ _ hr; omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hσN := seed_r_value_C hM hS I R hz h2 hlen hr hq hqr hncl hRes hC0 hRk1 n hn hGlow σ hCN hqOT hdecN
  rw [hσN] at hot'
  obtain ⟨X, hoM⟩ := o_arg_form I hrM
  have hot : isOT (psi (ρ.v r) X z) = true := by rw [← hoM]; exact I.good.ot_o r hrM
  exact seedRR_of_clB0 hoM hσN hot hot' (hCl _ hC0 (n - 1) (by omega) X hoM)

end Ytosk
