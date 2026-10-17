/-
**3 行・t = 2: sv・C の種の閉じた条件 T2SeedSVCl・T2SeedCCl を、k を含まない M・M.take x の性質に減らす（2026-10-17、lead）。**

sv（q = r、x − 1 が x へ上げる）と C の種の引数は X′ = σ^k X₁（σ = σ_{V,V′}、V′ は sv で V + 1、C で s′ = qnS、
X₁ は M.take x での r の引数）。σ は添字 > V の項を上げ、段 u ≤ V の成分は「元の成分 g₀ か σ g₀」か V′ の成分
（`comps_sh_low`）。よって段 u で X₁ と V′ の成分が X₁ より小さければ、σ^k X₁ も同じ（`closed_shIt`、段ごと）。
類 B0（加数 ≥ Ω_{V+1}）も σ で保たれ（`b0_shIt`）、σ が共通の接頭辞 P を動かさなければ X′ = P + σ^k T₁（`shIt_app`）。
段 u = V では C の ψ_V(σ^k X₁) の標準形も出る（`seedCOT1_of_base`）。

残り `T2SeedSVBase`・`T2SeedCBase`（k を含まない）: X = P + ψ_b(x)、X₁ = P + T₁（T₁ ≠ 0）、σ P = P、X・X₁ は類 B0、
段 V と道の段 u ≤ V で X₁ と V′（sv では V）の成分は X₁ より小さい。すべての段 u ≤ V では偽（expP に sv・C 各 2 件、
ext3s に sv 1 件）。実測は tmp/lead/probes/svcbase.py。
-/
import Ytosk.V3T2BelowR
import Ytosk.V3T2SeedOTP

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
theorem closed_shIt {Lv : T → Prop} {Y : T} (hY : isOT Y = true)
    (hcl : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u Y ++ comps u V', g < Y) :
    ∀ k, isOT (shIt V V' Y k) = true ∧
      ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u (shIt V V' Y k) ++ comps u V', g < shIt V V' Y k
  | 0 => ⟨hY, hcl⟩
  | k + 1 => by
    obtain ⟨hk, hclk⟩ := closed_shIt hY hcl k
    simp only [shIt]
    refine ⟨isOT_sh hV hV' hVV hk, fun u hu hVu g hg => ?_⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact closed_sh_step hV hV' hVV hVu hk (fun g h => hclk u hu hVu g (List.mem_append_left _ h))
        (fun g h => hclk u hu hVu g (List.mem_append_right _ h)) g hg
    · exact lt_of_lt_of_le (hclk u hu hVu g (List.mem_append_right _ hg)) (le_sh hV hV' (le_of_lt hVV) hk)

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

/-- **`SeedClB0` for `σ^k X₁`** (`σ = σ_{V,V′}`) from the `k`-free facts on `X` and `X₁`. -/
theorem seedClB0_of_baseG {Lv : T → Prop} {V V' X X1 P b x T1 : T} (hV : isOT V = true) (hV' : isOT V' = true)
    (hVV : V < V') (hX : X = app P (psi b x z)) (hX1 : X1 = app P T1) (hT1 : T1 ≠ z) (hP : sh V V' P = P)
    (hB0 : ∀ q ∈ summands X, ¬ q < psi (succ V) z z) (hB1 : ∀ q ∈ summands X1, ¬ q < psi (succ V) z z)
    (hot : isOT X1 = true) (hcl : ∀ u, (u = V ∨ Lv u) → ¬ V < u → ∀ g ∈ comps u X1 ++ comps u V', g < X1)
    (k : Nat) : SeedClB0 Lv V X (shIt V V' X1 k) := by
  obtain ⟨_, hk⟩ := closed_shIt hV hV' hVV hot hcl k
  exact ⟨P, b, x, shIt V V' T1 k, hX, by rw [hX1, shIt_app hP], shIt_ne_z hT1 k, hB0,
    b0_shIt hV hV' hVV hot hB1 k, fun u hu hVu g hg => Or.inl (hk u (Or.inr hu) hVu g (List.mem_append_left _ hg))⟩

/-- **`SeedClB0` for `σ^k X₁`** with `V′ = V + 1` (the components of `V + 1` are those of `V` and `0`). -/
theorem seedClB0_of_base {Lv : T → Prop} {V X X1 P b x T1 : T} (hV : isOT V = true)
    (hX : X = app P (psi b x z)) (hX1 : X1 = app P T1) (hT1 : T1 ≠ z) (hP : sh V (succ V) P = P)
    (hB0 : ∀ q ∈ summands X, ¬ q < psi (succ V) z z) (hB1 : ∀ q ∈ summands X1, ¬ q < psi (succ V) z z)
    (hot : isOT X1 = true)
    (hcl : ∀ u, (u = V ∨ Lv u) → ¬ lt V u = true → ∀ g ∈ comps u X1 ++ comps u V, g < X1) (k : Nat) :
    SeedClB0 Lv V X (shIt V (succ V) X1 k) := by
  have hX1z : X1 ≠ z := by rw [hX1]; exact app_ne_z_right hT1
  refine seedClB0_of_baseG hV (isOT_succ hV) (lt_succ_self V) hX hX1 hT1 hP hB0 hB1 hot
    (fun u hu hVu g hg => ?_) k
  rcases List.mem_append.mp hg with hg | hg
  · exact hcl u hu hVu g (List.mem_append_left _ hg)
  · rw [succ, comps_app, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hcl u hu hVu g (List.mem_append_right _ hg)
    · have hgz : g = z := by
        simp only [one, comps, List.append_nil] at hg
        split at hg
        · simp at hg
        · simpa using hg
      rw [hgz]; exact z_lt_of_ne_z hX1z

/-- **Residual (t2, sv): the `k`-free facts on the seed `r`** (`M` and `M.take x` only). `X` is the argument of
`o_M(r)`, `X₁ = t2X1` that of `o_{M.take x}(r)`, `V = v(r)`: `X = P + ψ_b(x)` and `X₁ = P + T₁` with `σ P = P`, both of
class B0, and at the level `V` and the path levels `u ≤ V` the components of `X₁` and of `V` are below `X₁`. -/
def T2SeedSVBase (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ X, ρ.o r = psi (ρ.v r) X z →
    ∃ P b x T1, X = app P (psi b x z) ∧ t2X1 M r L τ = app P T1 ∧ T1 ≠ z ∧
      sh (ρ.v r) (succ (ρ.v r)) P = P ∧
      (∀ q ∈ summands X, ¬ q < psi (succ (ρ.v r)) z z) ∧
      (∀ q ∈ summands (t2X1 M r L τ), ¬ q < psi (succ (ρ.v r)) z z) ∧
      isOT (t2X1 M r L τ) = true ∧
      ∀ u, (u = ρ.v r ∨ PathLvA M ρ r u) → ¬ lt (ρ.v r) u = true →
        ∀ g ∈ comps u (t2X1 M r L τ) ++ comps u (ρ.v r), g < t2X1 M r L τ

/-- **`T2SeedSVCl` from the `k`-free residual.** -/
theorem t2SeedSVCl_of_base {M : Mat} {ρ : Valn} {r L : Nat} (hV : isOT (ρ.v r) = true)
    (h : T2SeedSVBase M ρ r L) : T2SeedSVCl M ρ r L := by
  intro τ hC k _ X hX
  obtain ⟨P, b, x, T1, hXe, hX1, hT1, hP, hB0, hB1, hot, hcl⟩ := h τ hC X hX
  exact seedClB0_of_base hV hXe hX1 hT1 hP hB0 hB1 hot hcl k

/-- **Residual (t2, C): the `k`-free facts on the seed `r`**, as `T2SeedSVBase` with `V′ = s′ = qnS`. -/
def T2SeedCBase (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ X, ρ.o r = psi (ρ.v r) X z →
    ∃ P b x T1, X = app P (psi b x z) ∧ t2X1 M r L τ = app P T1 ∧ T1 ≠ z ∧
      sh (ρ.v r) (qnS M ρ r L q) P = P ∧
      (∀ q ∈ summands X, ¬ q < psi (succ (ρ.v r)) z z) ∧
      (∀ q ∈ summands (t2X1 M r L τ), ¬ q < psi (succ (ρ.v r)) z z) ∧
      isOT (t2X1 M r L τ) = true ∧
      ∀ u, (u = ρ.v r ∨ PathLvA M ρ r u) → ¬ lt (ρ.v r) u = true →
        ∀ g ∈ comps u (t2X1 M r L τ) ++ comps u (qnS M ρ r L q), g < t2X1 M r L τ

/-- **`T2SeedCCl` from the `k`-free residual.** -/
theorem t2SeedCCl_of_base {M : Mat} {ρ : Valn} {r L q : Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (h : T2SeedCBase M ρ r L q) : T2SeedCCl M ρ r L q := by
  intro τ hC k _ X hX
  obtain ⟨P, b, x, T1, hXe, hX1, hT1, hP, hB0, hB1, hot, hcl⟩ := h τ hC X hX
  exact seedClB0_of_baseG hV hs (qnS_gt M ρ r L q) hXe hX1 hT1 hP hB0 hB1 hot hcl k


/-! ## qn: X′_k = B + Ω_{t_k}、t_{k+1} = f(t_k) -/

/-- **The qn closed forms stay closed**: with `σ B = B` and `V < t₁`, `σ(B + Ω_{t_k}) = B + Ω_{t_{k+1}}`, so the
components of `t_{k+1} = V′ + σ(t_k − V)` are below `B + Ω_{t_{k+1}}` when those of `t₁` and `V′` are below `B + Ω_{t₁}`. -/
theorem qn_closed_tqN {Lv : T → Prop} {V V' B t1 : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hσB : sh V V' B = B) (hVt : V < t1) (hot : isOT (app B (psi t1 z z)) = true)
    (hcl : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u t1 ++ comps u V', g < app B (psi t1 z z)) :
    ∀ k, isOT (app B (psi (tqN V V' t1 k) z z)) = true ∧ V < tqN V V' t1 k ∧
      ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u (tqN V V' t1 k) ++ comps u V', g < app B (psi (tqN V V' t1 k) z z)
  | 0 => ⟨hot, hVt, hcl⟩
  | k + 1 => by
    obtain ⟨hk, hVk, hclk⟩ := qn_closed_tqN hV hV' hVV hσB hVt hot hcl k
    have hσ : sh V V' (app B (psi (tqN V V' t1 k) z z)) = app B (psi (tqN V V' t1 (k + 1)) z z) := by
      rw [sh_app, hσB, sh_psi_gt hVk, sh_z]; rfl
    have hle : app B (psi (tqN V V' t1 k) z z) ≤ app B (psi (tqN V V' t1 (k + 1)) z z) :=
      hσ ▸ le_sh hV hV' (le_of_lt hVV) hk
    have hot' : isOT (app B (psi (tqN V V' t1 (k + 1)) z z)) = true := hσ ▸ isOT_sh hV hV' hVV hk
    have htk : isOT (tqN V V' t1 k) = true := isOT_sub (isOT_app_right hk)
    refine ⟨hot', lt_trans hVV (lt_shf hV hV' (le_of_lt hVV) htk hVk), fun u hu hVu g hg => ?_⟩
    rcases List.mem_append.mp hg with hg | hg
    · change g ∈ comps u (add V' (sh V V' (sub (tqN V V' t1 k) V))) at hg
      obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub (tqN V V' t1 k) V))
      rw [hP, comps_app, List.mem_append] at hg
      rcases hg with hg | hg
      · exact lt_of_lt_of_le (hclk u hu hVu g (List.mem_append_right _ (comps_sub_of_summands u hPs g hg))) hle
      · rcases comps_sh_low hVu _ _ (Nat.le_refl _) g hg with ⟨g0, hg0, rfl | rfl⟩ | h
        · exact lt_of_lt_of_le (hclk u hu hVu _ (List.mem_append_left _ (comps_sub_sub u _ V hg0))) hle
        · rw [← hσ]
          exact sh_lt_sh hV hV' (le_of_lt hVV) (isOT_of_mem_comps u (isOT_sub_sfx htk V) hg0) hk
            (hclk u hu hVu _ (List.mem_append_left _ (comps_sub_sub u _ V hg0)))
        · exact lt_of_lt_of_le (hclk u hu hVu g (List.mem_append_right _ h)) hle
    · exact lt_of_lt_of_le (hclk u hu hVu g (List.mem_append_right _ hg)) hle


/-- **`σ^k (B + Ω_{t₁}) = B + Ω_{t_k}`** when `σ B = B` and `V < t₁`. -/
theorem tqN_shIt {V V' B t1 : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hσB : sh V V' B = B) (hVt : V < t1) (ht1 : isOT t1 = true) :
    ∀ k, isOT (tqN V V' t1 k) = true ∧ V < tqN V V' t1 k ∧
      shIt V V' (app B (psi t1 z z)) k = app B (psi (tqN V V' t1 k) z z)
  | 0 => ⟨ht1, hVt, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := tqN_shIt hV hV' hVV hσB hVt ht1 k
    refine ⟨isOT_shf hV hV' hVV h1, lt_trans hVV (lt_shf hV hV' (le_of_lt hVV) h1 h2), ?_⟩
    simp only [shIt]; rw [h3, sh_app, hσB, sh_psi_gt h2, sh_z]; rfl

/-- **The qn closed forms are standard** (`T2SeedQNOT`) from the standard form of `ψ_V(X₁)` and the components of
`V′` at the level `V`: `ψ_V(X_k)` by the closedness at the level `V`, and `ψ_{V′}(X_{k+1})` since the components of
`σ Y` at `V′ = f(V)` are the images of those of `Y` at `V`. -/
theorem qn_ot_of {V V' B t1 : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hσB : sh V V' B = B) (hVt : V < t1) (hot0 : isOT (psi V (app B (psi t1 z z)) z) = true)
    (hcV : ∀ g ∈ comps V V', g < app B (psi t1 z z)) :
    ∀ k, isOT (psi V (app B (psi (tqN V V' t1 k) z z)) z) = true ∧
      isOT (psi V' (app B (psi (tqN V V' t1 (k + 1)) z z)) z) = true := by
  have hX0 : isOT (app B (psi t1 z z)) = true := isOT_arg hot0
  have ht1 : isOT t1 = true := isOT_sub (isOT_app_right hX0)
  have hcl : ∀ u, u = V → ¬ V < u → ∀ g ∈ comps u (app B (psi t1 z z)) ++ comps u V', g < app B (psi t1 z z) := by
    rintro u rfl _ g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact (isOT_psi_iff.mp hot0).2.2.2.2 g hg
    · exact hcV g hg
  intro k
  obtain ⟨hk, hclk⟩ := closed_shIt (Lv := fun u => u = V) hV hV' hVV hX0 hcl k
  obtain ⟨_, _, he⟩ := tqN_shIt hV hV' hVV hσB hVt ht1 k
  obtain ⟨_, _, he1⟩ := tqN_shIt hV hV' hVV hσB hVt ht1 (k + 1)
  constructor
  · rw [← he, isOT_psi_iff]
    exact ⟨hV, hk, rfl, z_le _, fun g hg => hclk V rfl (lt_irrefl' _) g (List.mem_append_left _ hg)⟩
  · rw [← he1]
    show isOT (psi V' (sh V V' (shIt V V' (app B (psi t1 z z)) k)) z) = true
    rw [isOT_psi_iff]
    refine ⟨hV', isOT_sh hV hV' hVV hk, rfl, z_le _, fun g hg => ?_⟩
    have hcs := comps_sh hV hV' hVV hV (le_refl V) hk
    rw [shf_self] at hcs
    obtain ⟨g0, hg0, rfl⟩ := hcs g hg
    exact sh_lt_sh hV hV' (le_of_lt hVV) (isOT_of_mem_comps V hk hg0) hk
      (hclk V rfl (lt_irrefl' _) g0 (List.mem_append_left _ hg0))

/-- **Residual (t2, qn): the `k`-free facts on the seed `r`**: `X₁ = B + Ω_{t₁}` (`B = t2B`), `σ B = B`, `V < t₁`,
and at the path levels `u ≤ V` the components of `t₁` and `s′` are below `X₁`. -/
def T2SeedQNBase (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
    sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc ∧ ρ.v r < t1 ∧
      isOT (psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) z) = true ∧
      (∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) ∧
      ∀ u, PathLvA M ρ r u → ¬ lt (ρ.v r) u = true →
        ∀ g ∈ comps u t1 ++ comps u (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)

theorem t2SeedQNCl_of_base {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (h : T2SeedQNBase M ρ r L q Lc) : T2SeedQNCl M ρ r L q Lc := by
  intro τ hτ t1 ht1 k _ u hu hVu g hg
  obtain ⟨hσB, hVt, hot, -, hcl⟩ := h τ hτ t1 ht1
  exact Or.inl ((qn_closed_tqN hV hs (qnS_gt M ρ r L q) hσB hVt (isOT_arg hot) hcl k).2.2 u hu hVu g
    (List.mem_append_left _ hg))

theorem t2SeedQNOT_of_base {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (h : T2SeedQNBase M ρ r L q Lc) : T2SeedQNOT M ρ r L q Lc := by
  intro τ hτ t1 ht1 k hk
  obtain ⟨hσB, hVt, hot, hcV, -⟩ := h τ hτ t1 ht1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨(qn_ot_of hV hs (qnS_gt M ρ r L q) hσB hVt hot hcV (k' + 1)).1,
    (qn_ot_of hV hs (qnS_gt M ρ r L q) hσB hVt hot hcV k').2⟩

/-- **Residual (t2)**: `T2SeedClV2` with the qn, sv and C parts replaced by the `k`-free `T2SeedQNBase`,
`T2SeedSVBase` and `T2SeedCBase`. -/
def T2SeedClV2B : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNBase M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVBase M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCBase M ρ r L q)

theorem t2SeedClV2_of_B (h : T2SeedClV2B) : T2SeedClV2 := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, hSV, hCC⟩ := h M ρ rk C hz h2 r L hlen hr
  have hrM : r < M.length := by omega
  have IW := Inv3W.ofV2 C.S C.I
  exact ⟨fun q Lc hq hqr hCL => t2SeedQNCl_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (hQN q Lc hq hqr hCL),
    fun hc => t2SeedSVCl_of_base (IW.good.ot_v r hrM) (hSV hc),
    fun q hq hqr hncl => t2SeedCCl_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (hCC q hq hqr hncl)⟩

/-! ## C の種の標準形の前半 -/

/-- **The C closed forms `ψ_V(σ^k X₁)` are standard** from `T2SeedCBase` (the level `u = V` of the closedness). -/
theorem seedCOT1_of_base {M : Mat} {ρ : Valn} {r L q : Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (hXex : ∃ X, ρ.o r = psi (ρ.v r) X z) (h : T2SeedCBase M ρ r L q) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
      isOT (psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) z) = true := by
  intro τ hτ k
  obtain ⟨X, hX⟩ := hXex
  obtain ⟨_, _, _, _, -, -, -, -, -, -, hot, hcl⟩ := h τ hτ X hX
  obtain ⟨hk, hclk⟩ := closed_shIt hV hs (qnS_gt M ρ r L q) hot hcl k
  rw [isOT_psi_iff]
  exact ⟨hV, hk, rfl, z_le _, fun g hg => hclk _ (Or.inl rfl) (lt_irrefl' _) g (List.mem_append_left _ hg)⟩

/-- **The rest of the C seed standard forms**: the value of `q` in `M[n]`. -/
def T2SeedCOT2 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ →
    ∀ k, isOT (psi (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
      (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z) = true

/-- **Residual (t2)**: what remains of `T2SeedOTRest` (qn and the first half of C come from `T2SeedClV2B`): the value
of `q` in the C case, `T2SeedCOT2`. -/
def T2SeedOTRestB (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    ∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCOT2 M ρ r L q

def T2SeedOTRestV2B : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedOTRestB M ρ

/-- **`T2SeedOTRestV2` from `T2SeedClV2B` (its qn and C parts) and `T2SeedOTRestV2B`.** -/
theorem t2SeedOTRestV2_of_B (hCl : T2SeedClV2B) (h : T2SeedOTRestV2B) : T2SeedOTRestV2 := by
  intro M ρ rk C hz h2 r L hlen hr
  have hC2 := h M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, _, hCC⟩ := hCl M ρ rk C hz h2 r L hlen hr
  have hrM : r < M.length := by omega
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨fun q Lc hq hqr hCL => t2SeedQNOT_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (hQN q Lc hq hqr hCL),
    fun q hq hqr hncl τ hτ => ⟨fun k _ => ?_, hC2 q hq hqr hncl τ hτ⟩⟩
  exact seedCOT1_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (o_arg_form IW hrM) (hCC q hq hqr hncl) τ hτ k

end Ytosk
