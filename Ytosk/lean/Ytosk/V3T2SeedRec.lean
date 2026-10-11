/-
**3 行・t = 2・q = r: 種の値の漸化式と ◁（純粋な順序数の部分）。**

N = M[n] での r の引数 Y_{n−1} は、M.take x での r の引数 Y_0 から
  Y_{k+1} = step_V(B, V + 1, σ(Y_k))、σ = σ_{V, V+1}
で決まる（C′ 1 万行列の q = r の全件で一致、t2 の実測）。V = v(r)、B = x より前の r の数える子の状態。
σ(B) = B、σ(Y_0) ≤ B、B の加数 ≥ Ω_s、V + k < s のもとで、k ≥ 1 では
  Y_k = B + ψ_{V+k}(σ^k(Y_0))
（`seqY_form`: k = 1 は書き換えず足すだけ、k ≥ 2 は書き換えるが加数がすべて Ω_{V+2} 以上なので H は恒等）。
これと seed_frame_lhd で ψ_V(Y_k) ◁ ψ_V(B + Ω_s)（`seqY_lhd`）。
-/
import Ytosk.V3T2SeedLhd
import Ytosk.V3PSh

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- `V + k`. -/
def addN (V : T) (k : Nat) : T := app V (natT k)

/-- `σ^k` for `σ = σ_{V, V+1}`. -/
def shN (V : T) : Nat → T → T
  | 0, t => t
  | k + 1, t => sh V (succ V) (shN V k t)

/-- **The seed recursion** (`t = 2`, `q = r`). -/
def seqY (V B Y0 : T) : Nat → T
  | 0 => Y0
  | k + 1 => step V B (succ V) (sh V (succ V) (seqY V B Y0 k)) z

theorem natT_one : natT 1 = one := rfl

theorem app_one_natT (k : Nat) : app one (natT k) = natT (k + 1) := rfl

theorem natT_le : ∀ {j k : Nat}, j ≤ k → natT j ≤ natT k
  | 0, 0, _ => le_refl _
  | 0, k + 1, _ => le_of_lt (T.z_lt_psi _ _ _)
  | j + 1, 0, h => absurd h (by omega)
  | j + 1, k + 1, h => by
    have ih := natT_le (show j ≤ k by omega)
    show psi z z (natT j) ≤ psi z z (natT k)
    rcases (le_iff _ _).mp ih with h' | h'
    · apply le_of_lt; rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩)
    · rw [h']

theorem sh_natT {V V' : T} : ∀ k, sh V V' (natT k) = natT k
  | 0 => by simp [natT]
  | k + 1 => by
    show sh V V' (psi z z (natT k)) = psi z z (natT k)
    rw [sh_psi_le (T.not_lt_z V), sh_natT k]

theorem sub_app_prefix : ∀ (V X : T), sub (app V X) V = X
  | z, X => sub_z_right X
  | psi a b c, X => by
    show sub (psi a b (app c X)) (psi a b c) = X
    rw [sub_psi_self]; exact sub_app_prefix c X

theorem lt_addN {V : T} {k : Nat} (hk : 1 ≤ k) : V < addN V k := by
  unfold addN
  apply lt_app_of
  cases k with
  | zero => omega
  | succ k => simp [natT]

theorem addN_le {V : T} {j k : Nat} (h : j ≤ k) : addN V j ≤ addN V k :=
  app_le_app_left V (natT_le h)

theorem succ_eq_addN_one (V : T) : succ V = addN V 1 := rfl

/-- `f(V + k) = V + (k + 1)` for `σ = σ_{V, V+1}` and `k ≥ 1`. -/
theorem shf_addN {V : T} (hV : isOT V = true) {k : Nat} (hk : 1 ≤ k) :
    shf V (succ V) (addN V k) = addN V (k + 1) := by
  unfold shf addN
  rw [sub_app_prefix, sh_natT]
  rw [add_eq_app_of_last (isOT_succ hV)]
  · unfold succ; rw [app_assoc, app_one_natT]
  · cases k with
    | zero => omega
    | succ k =>
      show head (psi z z (natT k)) ≤ last (app V one)
      rw [last_app V (by simp [one])]
      show psi z z z ≤ psi z z z
      exact le_refl _

theorem sh_psi_addN {V : T} (hV : isOT V = true) {k : Nat} (hk : 1 ≤ k) (W : T) :
    sh V (succ V) (psi (addN V k) W z) = psi (addN V (k + 1)) (sh V (succ V) W) z := by
  rw [sh_psi_gt (lt_addN hk), shf_addN hV hk, sh_z]

/-- `split y t = (y, 0)` when every summand of `y` is at least `t`. -/
theorem split_all_ge {t : T} : ∀ {y : T}, (∀ q ∈ summands y, ¬ q < t) → split y t = (y, z)
  | z, _ => rfl
  | psi a b c, h => by
    have h1 : ¬ lt (psi a b z) t = true := h _ (by simp [summands])
    have ih := split_all_ge (y := c) (fun q hq => h q (by simp [summands, hq]))
    simp only [split, h1, if_false, ih]; rfl

theorem cut_all_ge {w : T} : ∀ {y : T}, (∀ q ∈ summands y, ¬ q < psi w z z) → cut w y = y
  | z, _ => rfl
  | psi a b c, h => by
    have h1 : ¬ lt (psi a b z) (psi w z z) = true := h _ (by simp [summands])
    have ih := cut_all_ge (y := c) (fun q hq => h q (by simp [summands, hq]))
    simp only [cut, ih, h1]
    simp

theorem sub_self_psi (a b : T) : sub (psi a b z) (psi a b z) = z := by
  rw [sub_psi_self]; rfl

/-- `H(s, y) = y` when every summand of `y` is at least `Ω_{s+1}`. -/
theorem H_of_high {s y : T} (hs : isOT s = true) (h : ∀ q ∈ summands y, ¬ q < psi (succ s) z z) :
    H s y = y := by
  unfold H
  rw [add_one_eq_succ hs, cut_all_ge h, sub_self_psi]
  cases y with
  | z => rfl
  | psi a b c => rfl

section
variable {V B Y0 s : T} (hV : isOT V = true) (hB : isOT B = true)
  (hσB : sh V (succ V) B = B) (hY0 : ¬ B < sh V (succ V) Y0)
  (hBc : ∀ q ∈ summands B, psi s z z ≤ q) (hks : ∀ k, addN V k < s)
include hV hB hσB hY0 hBc hks

/-- **The closed form** `Y_k = B + ψ_{V+k}(σ^k(Y_0))` for `k ≥ 1`. -/
theorem seqY_form : ∀ k, 1 ≤ k → seqY V B Y0 k = app B (psi (addN V k) (shN V k Y0) z) := by
  have hlastB : ∀ (a : T), a < psi s z z → B ≠ z → a ≤ last B := by
    intro a ha hBz
    have hl : last B ∈ summands B := last_mem_summands hBz
    exact le_of_lt (lt_of_lt_of_le ha (hBc _ hl))
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- `k = 0`: no rewrite
      show step V B (succ V) (sh V (succ V) Y0) z = _
      unfold step
      rw [if_neg (fun h => hY0 h.1)]
      by_cases hBz : B = z
      · subst hBz; rfl
      rw [add_eq_app_of_last hB]
      · rfl
      · apply hlastB _ _ hBz
        show psi (succ V) _ z < psi s z z
        rw [psi_lt_psi_z_iff]; left
        rw [succ_eq_addN_one]; exact hks 1
    · -- `k ≥ 1`: rewrite, and `H` is the identity
      have ihk := ih hk1
      show step V B (succ V) (sh V (succ V) (seqY V B Y0 k)) z = _
      rw [ihk, sh_app, hσB, sh_psi_addN hV hk1]
      have hne : psi (addN V (k + 1)) (sh V (succ V) (shN V k Y0)) z ≠ z := by simp
      unfold step
      rw [if_pos ⟨lt_app_of hne, by
        show psi V z z < psi (succ V) _ z
        rw [psi_lt_psi_z_iff]; left; exact lt_app_of (by simp [one])⟩]
      rw [H_of_high (isOT_succ hV)]
      · rfl
      · intro q hq
        rw [summands_app] at hq
        have hV2 : succ (succ V) = addN V 2 := by
          unfold succ addN; rw [app_assoc]; rfl
        rcases List.mem_append.mp hq with hq | hq
        · intro hlt
          have h1 := hBc q hq
          have h2 : psi (succ (succ V)) z z < psi s z z := by
            rw [psi_lt_psi_z_iff, hV2]; left; exact hks 2
          exact lt_irrefl' _ (lt_of_le_of_lt h1 (lt_trans hlt h2))
        · simp [summands] at hq; rw [hq]
          intro hlt
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with hlt | ⟨_, hlt2⟩
          · rw [hV2] at hlt
            exact lt_irrefl' _ (lt_of_lt_of_le hlt (addN_le (by omega)))
          · exact T.not_lt_z _ hlt2

/-- **The seed ◁** for `k ≥ 1`: `ψ_V(Y_k) ◁ ψ_V(B + Ω_s)`, from the closed form and `seed_frame_lhd`. The remaining
hypotheses are on `M` only: `V + 1 ◁ s` and the components of the closed forms. -/
theorem seqY_lhd (hVs : succ V = s ∨ Lhd z (succ V) s)
    (hdom : ∀ k, 1 ≤ k → ∀ u, ¬ lt V u = true →
      ∀ g ∈ comps u (app B (psi (addN V k) (shN V k Y0) z)),
        g ≤ app B (psi (addN V k) (shN V k Y0) z) ∨
        ∃ d ∈ comps u B ++ comps u V ++ comps u (succ V), g ≤ d) :
    ∀ k, 1 ≤ k → Lhd z (psi V (seqY V B Y0 k) z) (psi V (app B (psi s z z)) z) := by
  intro k hk
  rw [seqY_form hV hB hσB hY0 hBc hks k hk]
  apply seed_frame_lhd (s' := succ V) (lt_app_of (by simp [one]))
  · apply app_le_app_left
    rw [succ_eq_addN_one]
    exact le_trans (le_psi_sub (addN_le hk)) (le_psi_arg (z_le _))
  · exact app_lt_app_left B (psi_lt_psi_z_iff.mpr (Or.inl (hks k)))
  · exact hVs
  · exact hdom k hk

end

/-! ## 基点を M[2] にとる形（M.take x の v(r) が M と違う場合、L = 1 で起きる） -/

/-- **The seed recursion from `Y_1 = B + ψ_{V+1}(W_1)`.** -/
def seqZ (V B W1 : T) : Nat → T
  | 0 => app B (psi (succ V) W1 z)
  | k + 1 => step V B (succ V) (sh V (succ V) (seqZ V B W1 k)) z

section
variable {V B W1 s : T} (hV : isOT V = true)
  (hσB : sh V (succ V) B = B)
  (hBc : ∀ q ∈ summands B, psi s z z ≤ q) (hks : ∀ k, addN V k < s)
include hV hσB hBc hks

/-- **The closed form** `Y_{k+1} = B + ψ_{V+k+1}(σ^k(W_1))`. -/
theorem seqZ_form : ∀ k, seqZ V B W1 k = app B (psi (addN V (k + 1)) (shN V k W1) z) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show step V B (succ V) (sh V (succ V) (seqZ V B W1 k)) z = _
    rw [ih, sh_app, hσB, sh_psi_addN hV (by omega)]
    have hne : psi (addN V (k + 1 + 1)) (sh V (succ V) (shN V k W1)) z ≠ z := by simp
    unfold step
    rw [if_pos ⟨lt_app_of hne, by
      show psi V z z < psi (succ V) _ z
      rw [psi_lt_psi_z_iff]; left; exact lt_app_of (by simp [one])⟩]
    rw [H_of_high (isOT_succ hV)]
    · rfl
    · intro q hq
      rw [summands_app] at hq
      have hV2 : succ (succ V) = addN V 2 := by
        unfold succ addN; rw [app_assoc]; rfl
      rcases List.mem_append.mp hq with hq | hq
      · intro hlt
        have h1 := hBc q hq
        have h2 : psi (succ (succ V)) z z < psi s z z := by
          rw [psi_lt_psi_z_iff, hV2]; left; exact hks 2
        exact lt_irrefl' _ (lt_of_le_of_lt h1 (lt_trans hlt h2))
      · simp [summands] at hq; rw [hq]
        intro hlt
        rw [psi_lt_psi_z_iff] at hlt
        rcases hlt with hlt | ⟨_, hlt2⟩
        · rw [hV2] at hlt
          exact lt_irrefl' _ (lt_of_lt_of_le hlt (addN_le (by omega)))
        · exact T.not_lt_z _ hlt2

/-- **The seed ◁** for every level: `ψ_V(Y_{k+1}) ◁ ψ_V(B + Ω_s)`. -/
theorem seqZ_lhd (hVs : succ V = s ∨ Lhd z (succ V) s)
    (hdom : ∀ k u, ¬ lt V u = true →
      ∀ g ∈ comps u (app B (psi (addN V (k + 1)) (shN V k W1) z)),
        g ≤ app B (psi (addN V (k + 1)) (shN V k W1) z) ∨
        ∃ d ∈ comps u B ++ comps u V ++ comps u (succ V), g ≤ d) :
    ∀ k, Lhd z (psi V (seqZ V B W1 k) z) (psi V (app B (psi s z z)) z) := by
  intro k
  rw [seqZ_form hV hσB hBc hks k]
  apply seed_frame_lhd (s' := succ V) (lt_app_of (by simp [one]))
  · apply app_le_app_left
    rw [succ_eq_addN_one]
    exact le_trans (le_psi_sub (addN_le (by omega))) (le_psi_arg (z_le _))
  · exact app_lt_app_left B (psi_lt_psi_z_iff.mpr (Or.inl (hks (k + 1))))
  · exact hVs
  · exact hdom k

end

end Ytosk
