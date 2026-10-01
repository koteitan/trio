/-
**BM4 の展開（3 行）と、段 1・段 2 から停止性への還元（段 3）。**

- `expand M n`: BM4 の展開 M[n]（悪い部分のコピーを n 個、上昇行列つき）。`tools/trio.py` の `expand` と同じ。
- `Std M`: SRO = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0) から展開でたどり着く行列。
- `terminates_of_desc`: 段 1（`Std` の行列で SRO 以外なら、翻訳は標準形の値を持ち、展開で下がる）を仮定すると、
  SRO から始めた展開の列は必ず止まる。段 2（`wf_OT`）を使う。
-/
import Ytosk.Eval
import Ytosk.WF

namespace Ytosk

open T

/-- `isAnc M y r j`: `r = P_y^a(j)` for some `a ≥ 0` (fuel `j + 1`). -/
def isAnc (M : Mat) (y r : Nat) : Nat → Option Nat → Bool
  | 0, _ => false
  | _, none => false
  | f + 1, some j => if j = r then true else isAnc M y r f (par M y j)

/-- BM4 expansion `M[n]` of a three-row matrix: `n` copies of the bad part. -/
def expand (M : Mat) (n : Nat) : Mat :=
  match M with
  | [] => []
  | _ =>
    let x := M.length - 1
    if col M x = (0, 0, 0) then M.take x else
    let t := if entry M 2 x > 0 then 2 else if entry M 1 x > 0 then 1 else 0
    match par M t x with
    | none => M.take x
    | some r =>
      let d : Nat → Nat := fun y => if y < t then entry M y x - entry M y r else 0
      let up : Nat → Nat → Nat → Nat := fun a k y =>
        entry M y (r + k) + (if isAnc M y r (r + k + 1) (some (r + k)) then a * d y else 0)
      M.take r ++ (List.range n).flatMap (fun a =>
        (List.range (x - r)).map (fun k => (up a k 0, up a k 1, up a k 2)))

/-- The limit of the extended Buchholz function, the sheet's psi(I). -/
def SRO : Mat := [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (2,0,0)]

/-- The matrices reached from SRO by expansion. -/
inductive Std : Mat → Prop
  | sro : Std SRO
  | exp {M : Mat} (n : Nat) : Std M → Std (expand M n)

theorem sum_map_const_range (c n : Nat) : (List.map (fun _ => c) (List.range n)).sum = c * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [Nat.mul_succ]

theorem expand_SRO_length (n : Nat) : (expand SRO n).length = 1 + 3 * n := by
  have hc : col SRO 4 = (2, 0, 0) := by decide
  have hp : par SRO 0 4 = some 1 := by decide
  have he2 : entry SRO 2 4 = 0 := by decide
  have he1 : entry SRO 1 4 = 0 := by decide
  simp only [expand, SRO] at *
  simp [hc, hp, he2, he1, List.length_flatMap, sum_map_const_range]
  omega

/-- One expansion step inside `Std`. -/
def Step (M' M : Mat) : Prop := Std M ∧ ∃ n, M' = expand M n

/-- Step 1, as a hypothesis: away from SRO, the evaluator has a standard value, which drops under
expansion. -/
def Desc : Prop :=
  ∀ M n, Std M → M ≠ SRO →
    ∃ t t', eval M = some t ∧ eval (expand M n) = some t' ∧ isOT t = true ∧ t' < t

/-- **Step 3.** Step 1 and step 2 give termination below SRO. -/
theorem terminates_of_desc (hD : Desc) : WellFounded Step := by
  have hSRO : eval SRO = none := by decide
  -- matrices other than SRO
  have main : ∀ t, Acc (fun s t : T => isOT s = true ∧ isOT t = true ∧ s < t) t →
      ∀ M, Std M → M ≠ SRO → eval M = some t → Acc Step M := by
    intro t hacc
    induction hacc with
    | intro t _ ih =>
      intro M hM hne hev
      constructor
      rintro M' ⟨_, n, rfl⟩
      obtain ⟨t1, t', h1, h2, hot, hlt⟩ := hD M n hM hne
      rw [hev] at h1; cases h1
      have hM' : Std (expand M n) := Std.exp n hM
      have hne' : expand M n ≠ SRO := by
        intro h; rw [h, hSRO] at h2; cases h2
      obtain ⟨t2, _, h3, _, hot', _⟩ := hD (expand M n) 0 hM' hne'
      rw [h2] at h3; cases h3
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
