/-
**Ytosk の親 `par` と trio 本体の親 `TRIO.nextrel` の同値。**

trio 本体（`../../lean/Trio.lean`）は親を関係 `nextrel0/1/2` で、展開 `oper` を選択関数 `parent` で定義している。
Ytosk の `par`（`Eval.lean`）は同じ親を `climb` で計算する。ここでは

- `par M 0 b = some a ↔ nextrel0 M a b`（`par0_iff`）

などを示し、trio 本体の展開の補題（`Gtrans.lean` の `gexp` 系）を Ytosk の `expand` に使えるようにする。
-/
import Ytosk.Eval
import Trio

namespace Ytosk

open T

theorem entry_eq (M : Mat) (i j : Nat) : entry M i j = TRIO.entry M i j := rfl

/-! ## `climb` along `prev` -/

theorem climb_prev_iff (ok : Nat → Bool) (a : Nat) :
    ∀ q f, q < f → (climb prev ok f (some q) = some a ↔
      a ≤ q ∧ ok a = true ∧ ∀ j, a < j → j ≤ q → ok j = false)
  | q, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, f + 1, _ => by
    simp only [climb]
    by_cases h0 : ok 0 = true
    · simp only [h0, if_true, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨Nat.le_refl _, h0, fun j h1 h2 => absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)⟩
      · rintro ⟨h1, _, _⟩; omega
    · simp only [h0, Bool.false_eq_true, if_false, prev]
      constructor
      · intro h; cases f <;> simp [climb] at h
      · rintro ⟨h1, h2, _⟩
        have : a = 0 := by omega
        subst this; exact absurd h2 h0
  | q + 1, f + 1, hqf => by
    simp only [climb]
    by_cases h0 : ok (q + 1) = true
    · simp only [h0, if_true, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨Nat.le_refl _, h0, fun j h1 h2 => absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)⟩
      · rintro ⟨h1, h2, h3⟩
        by_contra hne
        have := h3 (q + 1) (by omega) (Nat.le_refl _)
        rw [h0] at this; exact Bool.noConfusion this
    · simp only [h0, Bool.false_eq_true, if_false, prev]
      rw [climb_prev_iff ok a q f (by omega)]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_ge j (q + 1) with h | h
        · exact h3 j hj1 (by omega)
        · have : j = q + 1 := by omega
          subst this; simpa using h0
      · rintro ⟨h1, h2, h3⟩
        have ha : a ≠ q + 1 := by rintro rfl; exact h0 h2
        exact ⟨by omega, h2, fun j hj1 hj2 => h3 j hj1 (by omega)⟩

theorem climb_prev_none (ok : Nat → Bool) :
    ∀ q f, q < f → (climb prev ok f (some q) = none ↔ ∀ j, j ≤ q → ok j = false)
  | q, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, f + 1, _ => by
    simp only [climb]
    by_cases h0 : ok 0 = true
    · simp only [h0, if_true]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; have := h 0 (Nat.le_refl _); rw [h0] at this; exact Bool.noConfusion this
    · simp only [h0, Bool.false_eq_true, if_false, prev]
      constructor
      · intro _ j hj; have : j = 0 := by omega
        subst this; simpa using h0
      · intro _; cases f <;> rfl
  | q + 1, f + 1, hqf => by
    simp only [climb]
    by_cases h0 : ok (q + 1) = true
    · simp only [h0, if_true]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; have := h (q + 1) (Nat.le_refl _); rw [h0] at this; exact Bool.noConfusion this
    · simp only [h0, Bool.false_eq_true, if_false, prev]
      rw [climb_prev_none ok q f (by omega)]
      constructor
      · intro h j hj
        rcases Nat.lt_or_ge j (q + 1) with h' | h'
        · exact h j (by omega)
        · have : j = q + 1 := by omega
          subst this; simpa using h0
      · intro h j hj; exact h j (by omega)

/-- **The row-0 parent.** -/
theorem par0_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    par M 0 b = some a ↔ TRIO.nextrel0 M a b := by
  unfold TRIO.nextrel0
  cases b with
  | zero =>
    simp only [par, prev]
    constructor
    · intro h; cases h' : (0 + 1) <;> simp [climb] at h
    · rintro ⟨_, _, h, _⟩; exact absurd h (Nat.not_lt_zero _)
  | succ c =>
    simp only [par, prev]
    rw [climb_prev_iff _ a c (c + 1 + 1) (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, hb, by omega, by simpa [entry_eq] using h2, fun j hj => ?_⟩
      have := h3 j hj.1 (by omega)
      simp only [decide_eq_false_iff_not, Nat.not_lt] at this
      simpa [entry_eq] using this
    · rintro ⟨_, _, h1, h2, h3⟩
      refine ⟨by omega, by simpa [entry_eq] using h2, fun j hj1 hj2 => ?_⟩
      simp only [decide_eq_false_iff_not, Nat.not_lt]
      simpa [entry_eq] using h3 j ⟨hj1, by omega⟩


/-! ## `climb` along a decreasing step -/

section chain
variable (s : Nat → Option Nat) (ok : Nat → Bool)

/-- One step of the chain: `R a b` iff `s b = some a`. -/
def StepRel (a b : Nat) : Prop := s b = some a

theorem stepRel_rtg_le (hs : ∀ q q', s q = some q' → q' < q) {j q : Nat}
    (h : Relation.ReflTransGen (StepRel s) j q) : j ≤ q := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ h2 ih => exact Nat.le_trans ih (Nat.le_of_lt (hs _ _ h2))

theorem climb_chain_iff (hs : ∀ q q', s q = some q' → q' < q) (a : Nat) :
    ∀ f q, q < f → (climb s ok f (some q) = some a ↔
      Relation.ReflTransGen (StepRel s) a q ∧ ok a = true ∧
      ∀ j, Relation.ReflTransGen (StepRel s) j q → a < j → ok j = false)
  | 0, q, h => absurd h (Nat.not_lt_zero _)
  | f + 1, q, hqf => by
    simp only [climb]
    by_cases h0 : ok q = true
    · simp only [h0, if_true, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨Relation.ReflTransGen.refl, h0, fun j hj h1 =>
          absurd (Nat.lt_of_lt_of_le h1 (stepRel_rtg_le s hs hj)) (Nat.lt_irrefl _)⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.lt_or_ge a q with h | h
        · have := h3 q Relation.ReflTransGen.refl h; rw [h0] at this; exact Bool.noConfusion this
        · exact Nat.le_antisymm (stepRel_rtg_le s hs h1) h |>.symm
    · simp only [h0, Bool.false_eq_true, if_false]
      cases hsq : s q with
      | none =>
        constructor
        · intro h; cases f <;> simp [climb] at h
        · rintro ⟨h1, h2, _⟩
          rcases Relation.ReflTransGen.cases_tail h1 with h | ⟨c, _, hc⟩
          · subst h; exact absurd h2 h0
          · unfold StepRel at hc; rw [hsq] at hc; cases hc
      | some q' =>
        have hq' : q' < q := hs q q' hsq
        rw [climb_chain_iff hs a f q' (by omega)]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨Relation.ReflTransGen.tail h1 hsq, h2, fun j hj hj2 => ?_⟩
          rcases Relation.ReflTransGen.cases_tail hj with h | ⟨c, hc1, hc2⟩
          · subst h; simpa using h0
          · unfold StepRel at hc2; rw [hsq] at hc2; cases hc2; exact h3 j hc1 hj2
        · rintro ⟨h1, h2, h3⟩
          rcases Relation.ReflTransGen.cases_tail h1 with h | ⟨c, hc1, hc2⟩
          · subst h; exact absurd h2 h0
          · unfold StepRel at hc2; rw [hsq] at hc2; cases hc2
            exact ⟨hc1, h2, fun j hj hj2 => h3 j (Relation.ReflTransGen.tail hj hsq) hj2⟩

end chain

theorem par_lt (M : Mat) : ∀ (r q q' : Nat), par M r q = some q' → q' < q := by
  intro r
  induction r with
  | zero =>
    intro q q' h
    have hb : q < q + 1 := Nat.lt_succ_self q
    cases q with
    | zero => simp [par, prev, climb] at h
    | succ c =>
      simp only [par, prev] at h
      have := (climb_prev_iff _ q' c (c + 1 + 1) (by omega)).mp h
      omega
  | succ r ih =>
    intro q q' h
    simp only [par] at h
    cases hp : par M r q with
    | none => rw [hp] at h; cases q <;> simp [climb] at h
    | some p =>
      rw [hp] at h
      have hpq := ih q p hp
      have := (climb_chain_iff (par M r) _ (fun a b => ih a b) q' (q + 1) p (by omega)).mp h
      exact Nat.lt_of_le_of_lt (stepRel_rtg_le (par M r) (fun a b => ih a b) this.1) hpq

/-- `StepRel (par M 0)` is `nextrel0`, inside the matrix. -/
theorem stepRel0_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    StepRel (par M 0) a b ↔ TRIO.nextrel0 M a b := par0_iff M hb

theorem rtg_step0_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    Relation.ReflTransGen (StepRel (par M 0)) a b ↔ Relation.ReflTransGen (TRIO.nextrel0 M) a b := by
  constructor
  · intro h
    revert hb
    induction h with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | tail _ h2 ih =>
      intro hd
      exact Relation.ReflTransGen.tail (ih (Nat.lt_trans (par_lt M 0 _ _ h2) hd)) ((par0_iff M hd).mp h2)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h2 ih => exact Relation.ReflTransGen.tail (ih h2.1) ((par0_iff M h2.2.1).mpr h2)


theorem climb_none (step : Nat → Option Nat) (ok : Nat → Bool) (f : Nat) : climb step ok f none = none := by
  cases f <;> rfl

/-- **The row-1 parent.** -/
theorem par1_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    par M 1 b = some a ↔ TRIO.nextrel1 M a b := by
  unfold TRIO.nextrel1 TRIO.le0
  have hpar : par M 1 b = climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 b)) (b + 1)
      (par M 0 b) := rfl
  rw [hpar]
  cases hp : par M 0 b with
  | none =>
    rw [climb_none]
    constructor
    · intro h; cases h
    · rintro ⟨_, _, hab, _, ⟨_, _, hrt⟩, _⟩
      rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, _, hc⟩
      · subst h; exact absurd hab (Nat.lt_irrefl _)
      · rw [(par0_iff M hb).mpr hc] at hp; cases hp
  | some p =>
    have hpb : p < b := par_lt M 0 b p hp
    have hpl : p < M.length := Nat.lt_trans hpb hb
    have hnp : TRIO.nextrel0 M p b := (par0_iff M hb).mp hp
    have huniq : ∀ c, TRIO.nextrel0 M c b → c = p := fun c hc => by
      have := (par0_iff M hb).mpr hc; rw [hp] at this; exact (Option.some.inj this).symm
    rw [climb_chain_iff (par M 0) _ (par_lt M 0) a (b + 1) p (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hap : a ≤ p := stepRel_rtg_le _ (par_lt M 0) h1
      have h1' := (rtg_step0_iff M hpl).mp h1
      refine ⟨by omega, hb, by omega, by simpa [entry_eq] using h2,
        ⟨by omega, hb, Relation.ReflTransGen.tail h1' hnp⟩, fun j ⟨hj1, _, _, hj2⟩ => ?_⟩
      rcases Relation.ReflTransGen.cases_tail hj2 with h | ⟨c, hc1, hc2⟩
      · subst h; exact Nat.le_refl _
      · rw [huniq c hc2] at hc1
        have hj3 := h3 j ((rtg_step0_iff M hpl).mpr hc1) hj1
        simp only [decide_eq_false_iff_not, Nat.not_lt] at hj3
        simpa [entry_eq] using hj3
    · rintro ⟨_, _, hab, h2, ⟨_, _, hrt⟩, h3⟩
      rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, hc1, hc2⟩
      · subst h; exact absurd hab (Nat.lt_irrefl _)
      · rw [huniq c hc2] at hc1
        refine ⟨(rtg_step0_iff M hpl).mpr hc1, by simpa [entry_eq] using h2, fun j hj hj2 => ?_⟩
        have hjp : j ≤ p := stepRel_rtg_le _ (par_lt M 0) hj
        have := h3 j ⟨hj2, by omega, hb, Relation.ReflTransGen.tail ((rtg_step0_iff M hpl).mp hj) hnp⟩
        simp only [decide_eq_false_iff_not, Nat.not_lt]
        simpa [entry_eq] using this

theorem rtg_step1_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    Relation.ReflTransGen (StepRel (par M 1)) a b ↔ Relation.ReflTransGen (TRIO.nextrel1 M) a b := by
  constructor
  · intro h
    revert hb
    induction h with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | tail _ h2 ih =>
      intro hd
      exact Relation.ReflTransGen.tail (ih (Nat.lt_trans (par_lt M 1 _ _ h2) hd)) ((par1_iff M hd).mp h2)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h2 ih => exact Relation.ReflTransGen.tail (ih h2.1) ((par1_iff M h2.2.1).mpr h2)

/-- **The row-2 parent.** -/
theorem par2_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    par M 2 b = some a ↔ TRIO.nextrel2 M a b := by
  unfold TRIO.nextrel2 TRIO.le1
  have hpar : par M 2 b = climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 b)) (b + 1)
      (par M 1 b) := rfl
  rw [hpar]
  cases hp : par M 1 b with
  | none =>
    rw [climb_none]
    constructor
    · intro h; cases h
    · rintro ⟨_, _, hab, _, ⟨_, _, hrt⟩, _⟩
      rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, _, hc⟩
      · subst h; exact absurd hab (Nat.lt_irrefl _)
      · rw [(par1_iff M hb).mpr hc] at hp; cases hp
  | some p =>
    have hpb : p < b := par_lt M 1 b p hp
    have hpl : p < M.length := Nat.lt_trans hpb hb
    have hnp : TRIO.nextrel1 M p b := (par1_iff M hb).mp hp
    have huniq : ∀ c, TRIO.nextrel1 M c b → c = p := fun c hc => by
      have := (par1_iff M hb).mpr hc; rw [hp] at this; exact (Option.some.inj this).symm
    rw [climb_chain_iff (par M 1) _ (par_lt M 1) a (b + 1) p (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hap : a ≤ p := stepRel_rtg_le _ (par_lt M 1) h1
      have h1' := (rtg_step1_iff M hpl).mp h1
      refine ⟨by omega, hb, by omega, by simpa [entry_eq] using h2,
        ⟨by omega, hb, Relation.ReflTransGen.tail h1' hnp⟩, fun j ⟨hj1, _, _, hj2⟩ => ?_⟩
      rcases Relation.ReflTransGen.cases_tail hj2 with h | ⟨c, hc1, hc2⟩
      · subst h; exact Nat.le_refl _
      · rw [huniq c hc2] at hc1
        have hj3 := h3 j ((rtg_step1_iff M hpl).mpr hc1) hj1
        simp only [decide_eq_false_iff_not, Nat.not_lt] at hj3
        simpa [entry_eq] using hj3
    · rintro ⟨_, _, hab, h2, ⟨_, _, hrt⟩, h3⟩
      rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, hc1, hc2⟩
      · subst h; exact absurd hab (Nat.lt_irrefl _)
      · rw [huniq c hc2] at hc1
        refine ⟨(rtg_step1_iff M hpl).mpr hc1, by simpa [entry_eq] using h2, fun j hj hj2 => ?_⟩
        have hjp : j ≤ p := stepRel_rtg_le _ (par_lt M 1) hj
        have := h3 j ⟨hj2, by omega, hb, Relation.ReflTransGen.tail ((rtg_step1_iff M hpl).mp hj) hnp⟩
        simp only [decide_eq_false_iff_not, Nat.not_lt]
        simpa [entry_eq] using this

theorem rtg_step2_iff (M : Mat) {a b : Nat} (hb : b < M.length) :
    Relation.ReflTransGen (StepRel (par M 2)) a b ↔ Relation.ReflTransGen (TRIO.nextrel2 M) a b := by
  constructor
  · intro h
    revert hb
    induction h with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | tail _ h2 ih =>
      intro hd
      exact Relation.ReflTransGen.tail (ih (Nat.lt_trans (par_lt M 2 _ _ h2) hd)) ((par2_iff M hd).mp h2)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h2 ih => exact Relation.ReflTransGen.tail (ih h2.1) ((par2_iff M h2.2.1).mpr h2)


end Ytosk
