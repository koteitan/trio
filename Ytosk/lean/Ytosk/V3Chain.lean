/-
**行 0 の祖先の列と、それに沿った探索。**

P_1（`par M 1`）と上げ（`upg` の後半）は、行 0 の祖先を近い方から順にたどって最初に条件を満たす列を返す（`climb`）。
これを祖先の列 `ancL M b` の上の `List.find?` と書き直す（`climb_eq_find`・`par1_find`・`upgClimb_find`）。
写しの列の P_1・上げを P の対応する列と比べるときは、祖先の列を「写しの中」「つなぎ目」「良い部分」に分けて比べる。
-/
import Ytosk.V3Dep
import Ytosk.ExpGexp

namespace Ytosk

/-- The list of the visited columns of `climb` (with the same fuel). -/
def chainF (step : Nat → Option Nat) : Nat → Option Nat → List Nat
  | 0, _ => []
  | _, none => []
  | f + 1, some q => q :: chainF step f (step q)

theorem climb_eq_find (step : Nat → Option Nat) (ok : Nat → Bool) :
    ∀ f o, climb step ok f o = (chainF step f o).find? ok
  | 0, _ => rfl
  | f + 1, none => by cases f <;> rfl
  | f + 1, some q => by
    simp only [climb, chainF, List.find?_cons]
    split <;> simp_all [climb_eq_find step ok f]

/-- The fuel does not matter once it exceeds the index (each step decreases the index). -/
theorem chainF_fuel {step : Nat → Option Nat} (hs : ∀ q q', step q = some q' → q' < q) :
    ∀ f f' q, q < f → q < f' → chainF step f (some q) = chainF step f' (some q)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, f' + 1, q, h1, h2 => by
    simp only [chainF]
    congr 1
    cases hq : step q with
    | none => cases f <;> cases f' <;> rfl
    | some q' =>
      have := hs q q' hq
      exact chainF_fuel hs f f' q' (by omega) (by omega)

/-- **The row-0 ancestors of `b`**, nearest first. -/
def ancL (M : Mat) (b : Nat) : List Nat := chainF (par M 0) (b + 1) (par M 0 b)

theorem ancL_eq {M : Mat} {b q : Nat} (h : par M 0 b = some q) :
    ancL M b = q :: ancL M q := by
  unfold ancL
  rw [h]
  simp only [chainF]
  congr 1
  cases hq : par M 0 q with
  | none =>
    have := par_lt M 0 b q h
    cases b with
    | zero => omega
    | succ b => simp [chainF]
  | some q' =>
    have h1 := par_lt M 0 b q h
    have h2 := par_lt M 0 q q' hq
    exact chainF_fuel (par_lt M 0) b (q + 1) q' (by omega) (by omega)

theorem ancL_none {M : Mat} {b : Nat} (h : par M 0 b = none) : ancL M b = [] := by
  unfold ancL; rw [h]; simp [chainF]

/-- **P_1 as a search along the ancestors.** -/
theorem par1_find (M : Mat) (b : Nat) :
    par M 1 b = (ancL M b).find? (fun q => decide (entry M 1 q < entry M 1 b)) := by
  show climb (par M 0) _ (b + 1) (par M 0 b) = _
  rw [climb_eq_find]
  rfl

/-- The second half of `upg`, as a search. -/
theorem upgClimb_find (M : Mat) (n : Nat) (ok : Nat → Bool) :
    climb (par M 0) ok (n + 1) (par M 0 n) = (ancL M n).find? ok := by
  rw [climb_eq_find]; rfl

/-! ## 祖先の列の性質 -/

theorem mem_ancL_lt {M : Mat} : ∀ {b q : Nat}, q ∈ ancL M b → q < b := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro q hq
    cases hp : par M 0 b with
    | none => rw [ancL_none hp] at hq; simp at hq
    | some p =>
      rw [ancL_eq hp] at hq
      have hpb := par_lt M 0 b p hp
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hpb
      · exact Nat.lt_trans (ih p hpb hq) hpb

theorem anc0_of_mem_ancL {M : Mat} : ∀ {b q : Nat}, q ∈ ancL M b → Anc0 M q b := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro q hq
    cases hp : par M 0 b with
    | none => rw [ancL_none hp] at hq; simp at hq
    | some p =>
      rw [ancL_eq hp] at hq
      have hpb := par_lt M 0 b p hp
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Anc0.step hp (Anc0.refl _)
      · exact (ih p hpb hq).trans (Anc0.step hp (Anc0.refl _))

/-- **Passing through an ancestor.** If `a` is a proper row-0 ancestor of `b`, the ancestor list of `b`
is the part strictly between, then `a`, then the ancestor list of `a`. -/
theorem ancL_through {M : Mat} {a b : Nat} (h : Anc0 M a b) (hne : a ≠ b) :
    ∃ S, ancL M b = S ++ a :: ancL M a ∧ ∀ s ∈ S, a < s ∧ s < b ∧ Anc0 M a s ∧ Anc0 M s b := by
  induction h with
  | refl => exact absurd rfl hne
  | @step b' c hp ha ih =>
    rw [ancL_eq hp]
    by_cases hab : a = b'
    · subst hab
      exact ⟨[], by simp, by simp⟩
    · obtain ⟨S, hS, hSp⟩ := ih hab
      refine ⟨b' :: S, by rw [hS]; rfl, ?_⟩
      intro s hs
      have hb'c := par_lt M 0 c b' hp
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨lt_of_le_of_ne ha.le hab, hb'c, ha, Anc0.step hp (Anc0.refl _)⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hSp s hs
        exact ⟨h1, Nat.lt_trans h2 hb'c, h3, h4.trans (Anc0.step hp (Anc0.refl _))⟩

end Ytosk
