/-
**評価器を関係として書く: 値の割り当てと依存の順位。**

`eval2` は燃料と呼び出しの経路を持つので、行列についての補題（コピーの値など）が書きにくい。
ここでは列ごとの値の割り当て ρ（o と v）が `eval2` と同じ等式を満たし（`Cons`）、依存に順位がつく（`Rk`）ことを
「ρ は M の評価」とする。順位があれば割り当ては一意（`cons_unique`）。
展開 M[n] の評価は、M の評価から ρ′ を明示して等式を確かめる形で作れる。

停止性への還元 `terminates_of_desc2` は `BMS.lean` の `terminates_of_desc` と同じ形で、評価器をこの関係に替えたもの。
-/
import Ytosk.TwoRow
import Ytosk.BMS

namespace Ytosk

open T

/-- A valuation: the `o`- and `v`-value of each column. -/
structure Valn where
  o : Nat → T
  v : Nat → T

/-- `v` of an optional column (`0` for none). -/
def vOpt (ρ : Valn) : Option Nat → T
  | none => z
  | some m => ρ.v m

/-- What the child `c` of `i` contributes to the argument of `o(i)`. -/
def cnt (M : Mat) (ρ : Valn) (i c : Nat) : T :=
  if col M c = bump M i then z else if isUpg M c = true ∧ topped M c = true then z else ρ.o c

/-- What the child `j` of `i` contributes to the subscript of `i` (row 2 nonzero). -/
def bumpTerm (M : Mat) (ρ : Valn) (i j : Nat) : T :=
  if col M j = bump M i then omega (sumN ((children M j).map ρ.o)) else z

/-- The right side of the equation for `o(i)` (as `ord2`). -/
def oRhs (M : Mat) (ρ : Valn) (i : Nat) : T :=
  sf (psi (ρ.v i) (sumN ((children M i).map (cnt M ρ i))) z)

/-- The right side of the equation for `v(i)` (as `val2`). -/
def vRhs (M : Mat) (ρ : Valn) (i : Nat) : T :=
  if entry M 1 i = 0 then z
  else if entry M 2 i = 0 then
    sf (add (vOpt ρ (par M 1 i)) (match upg M i with
      | some k => last (ρ.v k)
      | none => one))
  else sf (add (vOpt ρ (par M 1 i)) (omega (sumN (one :: (children M i).map (bumpTerm M ρ i)))))

/-- `ρ` satisfies the equations of the evaluator at every column. -/
def Cons (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ρ.o i = oRhs M ρ i ∧ ρ.v i = vRhs M ρ i

/-- A ranking of the calls (`true` = `o`, `false` = `v`) that every used dependency decreases. -/
def Rk (M : Mat) (rk : Bool → Nat → Nat) : Prop :=
  ∀ i, i < M.length →
    rk false i < rk true i ∧
    (∀ c ∈ children M i, col M c ≠ bump M i → ¬ (isUpg M c = true ∧ topped M c = true) →
      rk true c < rk true i) ∧
    (entry M 1 i ≠ 0 →
      (∀ m, par M 1 i = some m → rk false m < rk false i) ∧
      (entry M 2 i = 0 → ∀ k, upg M i = some k → rk false k < rk false i) ∧
      (entry M 2 i ≠ 0 → ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j,
        rk true k < rk false i))

/-- The value of the matrix: the sum of `o` over the `(0,0,0)` columns (as `eval2`). -/
def root (M : Mat) (ρ : Valn) : T :=
  sumN ((List.range M.length).map fun i => if col M i = (0, 0, 0) then ρ.o i else z)

/-- `t` is the value of `M` under the evaluator. -/
def Val (M : Mat) (t : T) : Prop :=
  ∃ ρ rk, Cons M ρ ∧ Rk M rk ∧ root M ρ = t

/-! ## 列の番号の範囲 -/

theorem climb_le {step : Nat → Option Nat} (hs : ∀ q q', step q = some q' → q' < q)
    {ok : Nat → Bool} : ∀ (f q k : Nat), climb step ok f (some q) = some k → k ≤ q
  | 0, _, _, h => by simp [climb] at h
  | f + 1, q, k, h => by
    simp only [climb] at h
    split at h
    · cases h; exact Nat.le_refl _
    · cases hq : step q with
      | none => rw [hq] at h; cases f <;> simp [climb] at h
      | some q' =>
        rw [hq] at h
        exact Nat.le_of_lt (Nat.lt_of_le_of_lt (climb_le hs f q' k h) (hs q q' hq))

theorem upg_lt {M : Mat} {i k : Nat} (hi : i < M.length) (h : upg M i = some k) : k < M.length := by
  unfold upg at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · simp only at h
      split at h
      · cases h; omega
      · cases hq : par M 0 i with
        | none => rw [hq] at h; cases i <;> simp [climb] at h
        | some q =>
          rw [hq] at h
          have h1 := climb_le (par_lt M 0) (i + 1) q k h
          have h2 := par_lt M 0 i q hq
          omega

/-! ## 一意性 -/

/-- **Uniqueness.** Two valuations satisfying the equations agree when one ranking exists. -/
theorem cons_unique {M : Mat} {ρ₁ ρ₂ : Valn} {rk : Bool → Nat → Nat} (h₁ : Cons M ρ₁)
    (h₂ : Cons M ρ₂) (hr : Rk M rk) :
    ∀ i, i < M.length → ρ₁.o i = ρ₂.o i ∧ ρ₁.v i = ρ₂.v i := by
  have key : ∀ N, ∀ i, i < M.length → (rk true i ≤ N → ρ₁.o i = ρ₂.o i) ∧
      (rk false i ≤ N → ρ₁.v i = ρ₂.v i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hv : ∀ i, i < M.length → rk false i ≤ N → ρ₁.v i = ρ₂.v i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hr i hi
        rw [(h₁ i hi).2, (h₂ i hi).2]
        unfold vRhs
        by_cases h1 : entry M 1 i = 0
        · rw [if_pos h1, if_pos h1]
        · rw [if_neg h1, if_neg h1]
          obtain ⟨hp, hu, hb⟩ := hR h1
          have hpar : vOpt ρ₁ (par M 1 i) = vOpt ρ₂ (par M 1 i) := by
            cases hm : par M 1 i with
            | none => rfl
            | some m =>
              have hlt := hp m hm
              exact (ih _ (by omega) m (by have := par_lt M 1 i m hm; omega)).2 (Nat.le_refl _)
          rw [hpar]
          by_cases h2 : entry M 2 i = 0
          · rw [if_pos h2, if_pos h2]
            cases hk : upg M i with
            | none => rfl
            | some k =>
              have hlt := hu h2 k hk
              simp only
              rw [(ih _ (by omega) k (upg_lt hi hk)).2 (Nat.le_refl _)]
          · rw [if_neg h2, if_neg h2]
            congr 4
            congr 1
            apply List.map_congr_left
            intro j hj
            unfold bumpTerm
            split
            · rename_i hbj
              congr 2
              apply List.map_congr_left
              intro k hk
              have hlt := hb h2 j hj hbj k hk
              have hkl := (mem_children hk).2
              exact (ih _ (by omega) k hkl).1 (Nat.le_refl _)
            · rfl
      refine fun i hi => ⟨fun hN => ?_, hv i hi⟩
      obtain ⟨hvo, hc, _⟩ := hr i hi
      rw [(h₁ i hi).1, (h₂ i hi).1]
      unfold oRhs
      rw [hv i hi (by omega)]
      congr 3
      apply List.map_congr_left
      intro c hcm
      unfold cnt
      split
      · rfl
      · rename_i hbc
        split
        · rfl
        · rename_i huc
          have hlt := hc c hcm hbc huc
          exact (ih _ (by omega) c (mem_children hcm).2).1 (Nat.le_refl _)
  intro i hi
  exact ⟨(key _ i hi).1 (Nat.le_refl _), (key _ i hi).2 (Nat.le_refl _)⟩

theorem val_unique {M : Mat} {t t' : T} (h : Val M t) (h' : Val M t') : t = t' := by
  obtain ⟨ρ₁, rk, h₁, hr, rfl⟩ := h
  obtain ⟨ρ₂, _, h₂, _, rfl⟩ := h'
  have hu := cons_unique h₁ h₂ hr
  unfold root
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [(hu i (List.mem_range.mp hi)).1]

/-! ## SRO は値を持たない -/

/-- At SRO, `v(1) → o(3) → v(3) → v(1)` is a cycle, so there is no ranking. -/
theorem not_val_SRO (t : T) : ¬ Val SRO t := by
  rintro ⟨ρ, rk, _, hr, _⟩
  have hl : SRO.length = 5 := rfl
  obtain ⟨_, _, h1⟩ := hr 1 (by omega)
  obtain ⟨hvo3, _, _⟩ := hr 3 (by omega)
  obtain ⟨_, _, h3⟩ := hr 3 (by omega)
  have a := (h1 (by decide)).2.2 (by decide) 2 (by decide) (by decide) 3 (by decide)
  have b := (h3 (by decide)).2.1 (by decide) 1 (by decide)
  omega

/-! ## 停止性への還元 -/

/-- Step 1 with the relational evaluator. -/
def Desc2 : Prop :=
  ∀ M n, Std M → M ≠ SRO →
    ∃ t t', Val M t ∧ Val (expand M n) t' ∧ isOT t = true ∧ t' < t

theorem terminates_of_desc2 (hD : Desc2) : WellFounded Step := by
  have main : ∀ t, Acc (fun s t : T => isOT s = true ∧ isOT t = true ∧ s < t) t →
      ∀ M, Std M → M ≠ SRO → Val M t → Acc Step M := by
    intro t hacc
    induction hacc with
    | intro t _ ih =>
      intro M hM hne hev
      constructor
      rintro M' ⟨_, n, rfl⟩
      obtain ⟨t1, t', h1, h2, hot, hlt⟩ := hD M n hM hne
      cases val_unique hev h1
      have hM' : Std (expand M n) := Std.exp n hM
      have hne' : expand M n ≠ SRO := by
        intro h; rw [h] at h2; exact not_val_SRO _ h2
      obtain ⟨t2, _, h3, _, hot', _⟩ := hD (expand M n) 0 hM' hne'
      cases val_unique h2 h3
      exact ih t' ⟨hot', hot, hlt⟩ (expand M n) hM' hne' h2
  have accM : ∀ M, Std M → M ≠ SRO → Acc Step M := by
    intro M hM hne
    obtain ⟨t, _, h1, _, hot, _⟩ := hD M 0 hM hne
    exact main t (wf_OT.apply t) M hM hne h1
  constructor
  intro M
  by_cases hM : Std M
  · by_cases hne : M = SRO
    · subst hne
      constructor
      rintro M' ⟨_, n, rfl⟩
      apply accM _ (Std.exp n Std.sro)
      intro h
      have hlen := congrArg List.length h
      rw [expand_SRO_length] at hlen
      simp [SRO] at hlen
      omega
    · exact accM M hM hne
  · constructor
    rintro M' ⟨hM', _⟩
    exact absurd hM' hM

end Ytosk
