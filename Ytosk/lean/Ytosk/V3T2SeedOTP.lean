/-
**3 行・t = 2: 種の閉じた形の標準形 T2SeedQROT（q = r、x への上げなし）と T2SeedSVOT（sv）を証明する（2026-10-17、t2）。**

sv: ψ_V(σ^k X₁) の標準形は ψ_V(X₁)（M.take x の o(r)）から。σ = σ_{V,V+1} で ψ_V(X) の標準形は ψ_V(σX) に移る
（`isOT_psi_shSucc`: 段 V の成分は comps_sh_min で σ g・g・V + 1 の加数の成分に引き戻せる。V の成分は段 V で空、1 の成分は 0）。

X′ = B + ψ_{V+k+1}(σ^k W₁)（seqZ_form）。
- ψ_{V+k+1}(σ^k W₁) の標準形: M.take x の o(r) = ψ_{v′(r)}(X_T) の標準形から isOT_shTop を k + 1 回（v′(r) ≤ V は落とす補題の PV）。
- 段 V の成分: 残り T2SeedQRRes の dom の欄（u = V）で、X′ 以下（成分なので X′ 未満）、B の成分（M の o(r) の標準形で
  B 未満）、V の成分（標準形の V では段 V の成分はない）、V + 1 の成分（0 だけ）。
-/
import Ytosk.V3T2SeedRRC

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **T2SeedQROT** from the seed residual `T2SeedQRRes`. -/
theorem seedOT_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc) :
    T2SeedQROT M ρ r L Lc := by
  intro τ hτ k
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  obtain ⟨hBc, hBot, hoM⟩ := qr_M_side I hlen hrx hCLM
  -- the drop at `τ`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [show M.length - 1 = r + L by omega]; exact hτ
  have hag := agree_of_cons hC1 hτ' hRk1
  have hG1 := good3_take_any I R (by omega) hτ'
  rw [show M.length - 1 = r + L by omega] at hG1
  have hrT' : r < (M.take (M.length - 1)).length := by rw [List.length_take]; omega
  have hvle : τ.v r ≤ ρ.v r := by
    have h1 := PV.le (hdrop r (by omega)).2
    have h2 := (hag r hrT').2
    first | (rw [← h2]; exact h1) | (rw [h2] at h1; exact h1)
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hotT : isOT (psi (τ.v r) (spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o))) z) = true := by
    rw [← o_cl_eq hτ hG1 hrT]; exact hG1.ot_o r hrT
  -- the new summand is standard
  have hW : ∀ j, isOT (psi (addN (ρ.v r) (j + 1)) (shN (ρ.v r) j (t2W1 (M.take (r + L)) (ρ.v r) τ r)) z) = true := by
    intro j
    induction j with
    | zero =>
      have h := isOT_shTop (V := τ.v r) (V' := succ (ρ.v r)) (hG1.ot_v r hrT) (isOT_succ hVot)
        (lt_of_le_of_lt hvle (lt_succ_self _)) hotT (le_refl _)
      rw [shf_self] at h
      exact h
    | succ j ih =>
      have h := isOT_shTop (V := ρ.v r) (V' := succ (ρ.v r)) hVot (isOT_succ hVot) (lt_succ_self _) ih
        (le_of_lt (lt_addN (by omega)))
      rw [shf_addN hVot (by omega)] at h
      exact h
  have hform := seqZ_form (B := t2B (ρ.v r) ρ Lc) (W1 := t2W1 (M.take (r + L)) (ρ.v r) τ r) hVot
    (tame_sigmaB_std hM hS I hlen hr hq hXu hCLM) hBc hRes.ks k
  rw [hform]
  have hotM : isOT (psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + L)) z z)) z) = true := by
    rw [← hoM]; exact I.good.ot_o r hrM
  have hX'z : app (t2B (ρ.v r) ρ Lc) (psi (addN (ρ.v r) (k + 1))
      (shN (ρ.v r) k (t2W1 (M.take (r + L)) (ρ.v r) τ r)) z) ≠ z := app_ne_z_right (by simp)
  rw [isOT_psi_iff]
  refine ⟨hVot, isOT_app_of hBot (hW k) (fun q hq => ?_), rfl, z_le _, ?_⟩
  · exact le_trans (le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl (hRes.ks (k + 1))))) (hBc q hq)
  · intro g hg
    rcases hRes.dom τ hτ k (ρ.v r) (lt_irrefl' _) g hg with h | ⟨d, hd, hgd⟩
    · exact lt_of_le_comps hg h
    · rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_append.mp hd with hd | hd
        · have h1 : d < app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + L)) z z) :=
            comps_lt hotM d (by rw [comps_app]; exact List.mem_append_left _ hd)
          exact lt_of_le_of_lt hgd (lt_trans (comps_lt_prefix hd h1) (lt_app_of (by simp)))
        · rw [comps_self hVot] at hd; simp at hd
      · rw [succ, comps_app, comps_self hVot, List.nil_append] at hd
        rw [mem_comps_one hd] at hgd
        exact lt_of_le_of_lt hgd (z_lt_of_ne_z hX'z)


/-- The components of a summand are components of the sum. -/
theorem comps_mem_of_summand {u g : T} : ∀ {t q : T}, q ∈ summands t → g ∈ comps u q → g ∈ comps u t
  | z, _, hq, _ => by simp [summands] at hq
  | psi a b c, q, hq, hg => by
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp only [comps, List.mem_append] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inl hg
      · simp at hg
    · simp only [comps, List.mem_append]
      exact Or.inr (comps_mem_of_summand hq hg)

/-- **`ψ_V(X)` stays standard under `σ_{V, V+1}`.** -/
theorem isOT_psi_shSucc {V X : T} (hV : isOT V = true) (h : isOT (psi V X z) = true) :
    isOT (psi V (sh V (succ V) X) z) = true := by
  have hV' := isOT_succ hV
  have hVV : V < succ V := lt_succ_self V
  have hX := isOT_arg h
  rw [isOT_psi_iff]
  refine ⟨hV, isOT_sh hV hV' hVV hX, rfl, z_le _, ?_⟩
  intro g' hg'
  have hc := comps_sh_min V (succ V) V hg'
  simp only [le_refl, if_true] at hc
  rcases hc with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | ⟨q, hq, hgq⟩
  · rw [e]; exact sh_lt_sh hV hV' (le_of_lt hVV) (isOT_of_mem_comps V hX hg) hX (comps_lt h g hg)
  · rw [e]; exact lt_of_lt_of_le (comps_lt h g hg) (le_sh hV hV' (le_of_lt hVV) hX)
  · rw [succ, summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · have := comps_mem_of_summand hq hgq
      rw [comps_self hV] at this; simp at this
    · simp [one, summands] at hq
      subst hq
      have hg0 := mem_comps_one hgq
      subst hg0
      apply z_lt_of_ne_z
      intro hz0
      rw [hz0] at hg'; simp [comps] at hg'

/-- **The sv closed form is standard**: `ψ_V(σ^k X₁)` from `ψ_V(X₁)`. -/
theorem isOT_psi_shIt {V X : T} (hV : isOT V = true) (h : isOT (psi V X z) = true) :
    ∀ k, isOT (psi V (shIt V (succ V) X k) z) = true
  | 0 => h
  | k + 1 => isOT_psi_shSucc hV (isOT_psi_shIt hV h k)

/-- **T2SeedSVOT** (the sv closed forms are standard). -/
theorem seedOT_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L)) :
    T2SeedSVOT M ρ r L := by
  intro τ hτ k _
  obtain ⟨hG, hv, _⟩ := sv_children_ctx hM hS I R hlen hr hq hux hτ
  have hrT : r < (M.take (r + L)).length := by
    rw [List.length_take]; have := par_lt M 0 _ _ hq; omega
  have hot : isOT (psi (τ.v r) (t2X1 M r L τ) z) = true := by
    unfold t2X1; rw [← o_cl_eq hτ hG hrT]; exact hG.ot_o r hrT
  rw [hv] at hot
  exact isOT_psi_shIt (I.good.ot_v r (by omega)) hot k

/-- **The residual of the seed standard forms** (qn・C; qr and sv are proved). -/
def T2SeedOTRest (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNOT M ρ r L q Lc) ∧
    (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCOT M ρ r L q)

/-- **Residual (t2): `T2SeedOTRest` in the step context.** -/
def T2SeedOTRestV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedOTRest M ρ

/-- **`T2SeedOTV2` from the seed residuals and `T2SeedOTRestV2`** (qr and sv are proved). -/
theorem t2SeedOTV2_of (hP : T2SeedPResV2) (h : T2SeedOTRestV2) : T2SeedOTV2 := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨h1, h3⟩ := h M ρ rk C hz h2 r L hlen hr
  refine ⟨fun hqx Lc hCLM => ?_, h1, fun hsv => seedOT_sv C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩
    hlen hr hsv.1 hsv.2, h3⟩
  exact seedOT_qr C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hlen hr hqx.1 hqx.2 hCLM
    ((hP M ρ rk C hz h2).qr r L hlen hr hqx.1 hqx.2 Lc hCLM)

end Ytosk
