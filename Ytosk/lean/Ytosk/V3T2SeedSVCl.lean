/-
**3 行・t = 2: sv の種の閉じた条件 T2SeedSVCl を、k を含まない M・M.take x の性質に減らす（2026-10-17、lead）。**

sv（q = r、x − 1 が x へ上げる）の種の引数は X′ = σ^k X₁（σ = σ_{V,V+1}、X₁ は M.take x での r の引数）。
σ は添字 > V の項を上げ、段 u ≤ V の成分は「元の成分 g₀ か σ g₀」か V + 1 の成分（`comps_sh_low`）。
よって X₁ が段 u ≤ V で真に閉じていて（成分 < X₁）、V の成分も X₁ より小さければ、σ^k X₁ も真に閉じている
（`closed_shIt`）。類 B0（加数 ≥ Ω_{V+1}）も σ で保たれ（`b0_shIt`）、σ が共通の接頭辞 P を動かさなければ
X′ = P + σ^k T₁（`shIt_app`）。

残り `T2SeedSVBase`（k を含まない）: X = P + ψ_b(x)、X₁ = P + T₁（T₁ ≠ 0）、σ P = P、X・X₁ は類 B0、
段 u ≤ V で X₁ と V の成分は X₁ より小さい。実測（tmp/lead/probes/svcl.py）: d3s・deep2・Cprime・ext2 の sv の
種 1.9 万件で例外 0。
-/
import Ytosk.V3T2BelowR

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {V V' : T}

/-- **`σ^k` of `P + T₁` when `σ` fixes `P`.** -/
theorem shIt_app {P : T} (hP : sh V V' P = P) (T1 : T) :
    ∀ k, shIt V V' (app P T1) k = app P (shIt V V' T1 k)
  | 0 => rfl
  | k + 1 => by simp only [shIt]; rw [shIt_app hP T1 k, sh_app, hP]

theorem shIt_ne_z {T1 : T} (h : T1 ≠ z) : ∀ k, shIt V V' T1 k ≠ z
  | 0 => h
  | k + 1 => sh_ne_z (shIt_ne_z h k)

/-- **The summands of `σ t`** are the `σ`-images of the summands of `t`. -/
theorem summands_sh : ∀ t : T, summands (sh V V' t) = (summands t).map (sh V V')
  | z => by simp [summands]
  | psi s y c => by
    by_cases hs : V < s
    · rw [sh_psi_gt hs]; simp only [summands, List.map_cons]; rw [summands_sh c, sh_psi_gt hs, sh_z]
    · rw [sh_psi_le hs]; simp only [summands, List.map_cons]; rw [summands_sh c, sh_psi_le hs, sh_z]

theorem isOT_of_mem_summands : ∀ {t q : T}, isOT t = true → q ∈ summands t → isOT q = true
  | z, _, _, h => by simp [summands] at h
  | psi s y c, q, ht, hq => by
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact isOT_head ht
    · exact isOT_of_mem_summands (isOT_rest ht) hq

/-- The components of a summand are components of the whole term. -/
theorem comps_summand_sub (u : T) : ∀ {W q : T}, q ∈ summands W → ∀ g ∈ comps u q, g ∈ comps u W
  | z, _, h, _, _ => by simp [summands] at h
  | psi a b c, q, hq, g, hg => by
    simp only [summands, List.mem_cons] at hq
    simp only [comps, List.mem_append]
    rcases hq with rfl | hq
    · simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · exact Or.inl hg
      · simp at hg
    · exact Or.inr (comps_summand_sub u hq g hg)

theorem comps_sub_of_summands (u : T) : ∀ {P W : T}, (∀ q ∈ summands P, q ∈ summands W) →
    ∀ g ∈ comps u P, g ∈ comps u W
  | z, _, _, _, h => by simp [comps] at h
  | psi a b c, W, hP, g, hg => by
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · exact comps_summand_sub u (hP (psi a b z) (by simp [summands])) g
        (by simp only [comps, List.mem_append]; exact Or.inl hg)
    · exact comps_sub_of_summands u (fun q hq => hP q (by simp [summands, hq])) g hg

/-- **The components of `σ t` at a level `u ≤ V`**: a component `g₀` of `t` or its image `σ g₀`, or a component
of `V′`. -/
theorem comps_sh_low {u : T} (hVu : ¬ V < u) : ∀ n (t : T), size t ≤ n →
    ∀ g ∈ comps u (sh V V' t), (∃ g0 ∈ comps u t, g = g0 ∨ g = sh V V' g0) ∨ g ∈ comps u V'
  | 0, t, hn, g, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi => simp [size] at hn
  | n + 1, t, hn, g, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi v x c =>
      have hcsub : ∀ g ∈ comps u c, g ∈ comps u (psi v x c) := by
        intro g hg; simp only [comps, List.mem_append]; exact Or.inr hg
      have hcpart : g ∈ comps u (sh V V' c) →
          (∃ g0 ∈ comps u (psi v x c), g = g0 ∨ g = sh V V' g0) ∨ g ∈ comps u V' := by
        intro h
        rcases comps_sh_low hVu n c (by simp [size] at hn; omega) g h with ⟨g0, hg0, he⟩ | h
        · exact Or.inl ⟨g0, hcsub g0 hg0, he⟩
        · exact Or.inr h
      by_cases hv : V < v
      · have hvu : ¬ v < u := fun h => hVu (lt_trans hv h)
        have hmem : ∀ g, g = x ∨ g ∈ comps u x ∨ g ∈ comps u v → g ∈ comps u (psi v x c) := by
          intro g hg
          simp only [comps, List.mem_append]
          left; rw [if_neg (show ¬ lt v u = true from hvu)]; simp only [List.mem_cons, List.mem_append]; exact hg
        rw [sh_psi_gt hv] at hg
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · split at hg
          · simp at hg
          · simp only [List.mem_cons, List.mem_append] at hg
            rcases hg with rfl | hg | hg
            · exact Or.inl ⟨x, hmem x (Or.inl rfl), Or.inr rfl⟩
            · rcases comps_sh_low hVu n x (by simp [size] at hn; omega) g hg with ⟨g0, hg0, he⟩ | h
              · exact Or.inl ⟨g0, hmem g0 (Or.inr (Or.inl hg0)), he⟩
              · exact Or.inr h
            · rw [show shf V V' v = add V' (sh V V' (sub v V)) from rfl] at hg
              obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub v V))
              rw [hP, comps_app, List.mem_append] at hg
              rcases hg with hg | hg
              · exact Or.inr (comps_sub_of_summands u hPs g hg)
              · rcases comps_sh_low hVu n (sub v V) (by have := size_sub_le v V; simp [size] at hn; omega)
                  g hg with ⟨g0, hg0, he⟩ | h
                · exact Or.inl ⟨g0, hmem g0 (Or.inr (Or.inr (comps_sub_sub u v V hg0))), he⟩
                · exact Or.inr h
        · exact hcpart hg
      · rw [sh_psi_le hv] at hg
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · refine Or.inl ⟨g, ?_, Or.inl rfl⟩
          simp only [comps, List.mem_append]; exact Or.inl hg
        · exact hcpart hg

end

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **One step of `σ` keeps the strict closedness at a level `u ≤ V`** (with the components of `V′` below). -/
theorem closed_sh_step {u Y : T} (hVu : ¬ V < u) (hY : isOT Y = true)
    (hcl : ∀ g ∈ comps u Y, g < Y) (hc' : ∀ g ∈ comps u V', g < Y) :
    ∀ g ∈ comps u (sh V V' Y), g < sh V V' Y := by
  intro g hg
  have hle := le_sh hV hV' (le_of_lt hVV) hY
  rcases comps_sh_low hVu _ Y (Nat.le_refl _) g hg with ⟨g0, hg0, rfl | rfl⟩ | h
  · exact lt_of_lt_of_le (hcl _ hg0) hle
  · exact sh_lt_sh hV hV' (le_of_lt hVV) (isOT_of_mem_comps u hY hg0) hY (hcl _ hg0)
  · exact lt_of_lt_of_le (hc' _ h) hle

/-- **`σ^k` keeps the strict closedness at the levels `u ≤ V`.** -/
theorem closed_shIt {Y : T} (hY : isOT Y = true)
    (hcl : ∀ u, ¬ V < u → ∀ g ∈ comps u Y ++ comps u V', g < Y) :
    ∀ k, isOT (shIt V V' Y k) = true ∧
      ∀ u, ¬ V < u → ∀ g ∈ comps u (shIt V V' Y k) ++ comps u V', g < shIt V V' Y k
  | 0 => ⟨hY, hcl⟩
  | k + 1 => by
    obtain ⟨hk, hclk⟩ := closed_shIt hY hcl k
    simp only [shIt]
    refine ⟨isOT_sh hV hV' hVV hk, fun u hVu g hg => ?_⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact closed_sh_step hV hV' hVV hVu hk (fun g h => hclk u hVu g (List.mem_append_left _ h))
        (fun g h => hclk u hVu g (List.mem_append_right _ h)) g hg
    · exact lt_of_lt_of_le (hclk u hVu g (List.mem_append_right _ hg)) (le_sh hV hV' (le_of_lt hVV) hk)

theorem isOT_shIt_svc {Y : T} (hY : isOT Y = true) : ∀ k, isOT (shIt V V' Y k) = true
  | 0 => hY
  | k + 1 => isOT_sh hV hV' hVV (isOT_shIt_svc hY k)

/-- **`σ^k` keeps the class B0** (every summand at least `W`). -/
theorem b0_shIt {W Y : T} (hY : isOT Y = true) (hB : ∀ q ∈ summands Y, ¬ q < W) :
    ∀ k, ∀ q ∈ summands (shIt V V' Y k), ¬ q < W
  | 0 => hB
  | k + 1 => by
    intro q hq hqW
    simp only [shIt] at hq
    rw [summands_sh, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    have hq0t := isOT_of_mem_summands (isOT_shIt_svc hV hV' hVV hY k) hq0
    exact b0_shIt hY hB k q0 hq0 (lt_of_le_of_lt (le_sh hV hV' (le_of_lt hVV) hq0t) hqW)

end

/-- **`SeedClB0` for `σ^k X₁`** from the `k`-free facts on `X` and `X₁`. -/
theorem seedClB0_of_base {Lv : T → Prop} {V X X1 P b x T1 : T} (hV : isOT V = true)
    (hX : X = app P (psi b x z)) (hX1 : X1 = app P T1) (hT1 : T1 ≠ z) (hP : sh V (succ V) P = P)
    (hB0 : ∀ q ∈ summands X, ¬ q < psi (succ V) z z) (hB1 : ∀ q ∈ summands X1, ¬ q < psi (succ V) z z)
    (hot : isOT X1 = true) (hcl : ∀ u, ¬ lt V u = true → ∀ g ∈ comps u X1 ++ comps u V, g < X1) (k : Nat) :
    SeedClB0 Lv V X (shIt V (succ V) X1 k) := by
  have hV' := isOT_succ hV
  have hVV := lt_succ_self V
  have hX1z : X1 ≠ z := by rw [hX1]; exact app_ne_z_right hT1
  have hcl' : ∀ u, ¬ V < u → ∀ g ∈ comps u X1 ++ comps u (succ V), g < X1 := by
    intro u hVu g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hcl u hVu g (List.mem_append_left _ hg)
    · rw [succ, comps_app, List.mem_append] at hg
      rcases hg with hg | hg
      · exact hcl u hVu g (List.mem_append_right _ hg)
      · have hgz : g = z := by
          simp only [one, comps, List.append_nil] at hg
          split at hg
          · simp at hg
          · simpa using hg
        rw [hgz]; exact z_lt_of_ne_z hX1z
  obtain ⟨_, hk⟩ := closed_shIt hV hV' hVV hot hcl' k
  exact ⟨P, b, x, shIt V (succ V) T1 k, hX, by rw [hX1, shIt_app hP], shIt_ne_z hT1 k, hB0,
    b0_shIt hV hV' hVV hot hB1 k, fun u _ hVu g hg => Or.inl (hk u hVu g (List.mem_append_left _ hg))⟩

/-- **Residual (t2, sv): the `k`-free facts on the seed `r`** (`M` and `M.take x` only). `X` is the argument of
`o_M(r)`, `X₁ = t2X1` that of `o_{M.take x}(r)`, `V = v(r)`: `X = P + ψ_b(x)` and `X₁ = P + T₁` with `σ P = P`, both of
class B0, and at every level `u ≤ V` the components of `X₁` and of `V` are below `X₁`. -/
def T2SeedSVBase (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ X, ρ.o r = psi (ρ.v r) X z →
    ∃ P b x T1, X = app P (psi b x z) ∧ t2X1 M r L τ = app P T1 ∧ T1 ≠ z ∧
      sh (ρ.v r) (succ (ρ.v r)) P = P ∧
      (∀ q ∈ summands X, ¬ q < psi (succ (ρ.v r)) z z) ∧
      (∀ q ∈ summands (t2X1 M r L τ), ¬ q < psi (succ (ρ.v r)) z z) ∧
      isOT (t2X1 M r L τ) = true ∧
      ∀ u, ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (t2X1 M r L τ) ++ comps u (ρ.v r), g < t2X1 M r L τ

/-- **`T2SeedSVCl` from the `k`-free residual.** -/
theorem t2SeedSVCl_of_base {M : Mat} {ρ : Valn} {r L : Nat} (hV : isOT (ρ.v r) = true)
    (h : T2SeedSVBase M ρ r L) : T2SeedSVCl M ρ r L := by
  intro τ hC k _ X hX
  obtain ⟨P, b, x, T1, hXe, hX1, hT1, hP, hB0, hB1, hot, hcl⟩ := h τ hC X hX
  exact seedClB0_of_base hV hXe hX1 hT1 hP hB0 hB1 hot hcl k

/-- **Residual (t2)**: `T2SeedClV2` with the sv part replaced by the `k`-free `T2SeedSVBase`. -/
def T2SeedClV2B : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNCl M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVBase M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCCl M ρ r L q)

theorem t2SeedClV2_of_B (h : T2SeedClV2B) : T2SeedClV2 := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, hSV, hCC⟩ := h M ρ rk C hz h2 r L hlen hr
  have hrM : r < M.length := by omega
  exact ⟨hQN, fun hc => t2SeedSVCl_of_base ((Inv3W.ofV2 C.S C.I).good.ot_v r hrM) (hSV hc), hCC⟩

end Ytosk
