/-
**3 行: 先頭部分 M.take k の順位。**

M の順位は、先頭部分で数える子が M でも数える子なら、そのまま M.take k の順位になる（`rk_take`）。
最後の列を落とす（k = |M| − 1）とき、数える子が増えないことは構造の不変条件から出る（`counted_take_last`）:
- 兄弟は辞書順で減る（SibDec）・行 2 が 1 の列の子の行 1 は親以下（Z1C）なら、x を落としても topped で
  上げられる列は増えない。
- 祖先への上げ（行き先が次の列でない上げ）の行き先は topped でない（UAT）なら、x − 1 の上げが消えても
  数える子は増えない。
-/
import Ytosk.V3Root

namespace Ytosk

open T

/-- Lexicographic order on columns. -/
def colLe (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2)))

/-- Consecutive siblings do not increase. -/
def SibDec (M : Mat) : Prop :=
  ∀ p (l₁ l₂ : List Nat) (a b : Nat), children M p = l₁ ++ a :: b :: l₂ → colLe (col M b) (col M a)

/-- A child of a column with row 2 equal to `1` has row 1 at most that of the column. -/
def Z1C (M : Mat) : Prop :=
  ∀ p c, entry M 2 p = 1 → c ∈ children M p → entry M 1 c ≤ entry M 1 p

/-- An upgrade to an ancestor never lands on a topped column. -/
def UAT (M : Mat) : Prop := ∀ i c, upg M i = some c → c ≠ i + 1 → topped M c = false

/-- **The ranking of a prefix**, when the prefix counts no new children. -/
theorem rk_take {M : Mat} {k : Nat} {rk : Bool → Nat → Nat} (hk : k ≤ M.length) (hR : Rk M rk)
    (hcnt : ∀ i c, i < k → c ∈ children (M.take k) i → Counted (M.take k) i c → Counted M i c) :
    Rk (M.take k) rk := by
  intro i hi
  have hik : i < k := by rw [List.length_take] at hi; omega
  have hiM : i < M.length := by omega
  obtain ⟨h1, h2, h3⟩ := hR i hiM
  refine ⟨h1, ?_, ?_⟩
  · intro c hc hcb hcu
    have hcM : c ∈ children M i := by
      rw [children_take, List.mem_filter] at hc; exact hc.1
    have := hcnt i c hik hc ⟨hcb, hcu⟩
    exact h2 c hcM this.1 this.2
  · intro he1
    rw [entry_take M 1 hik] at he1
    obtain ⟨hp, hu, hb⟩ := h3 he1
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      rw [par_take M 1 i hik] at hm
      exact hp m hm
    · intro he2 c hc
      rw [entry_take M 2 hik] at he2
      by_cases hik1 : i + 1 < k
      · rw [upg_take M hik1] at hc; exact hu he2 c hc
      · have : i = k - 1 := by omega
        subst this
        rw [upg_take_last M hk (by omega)] at hc; cases hc
    · intro he2 j hj hjb c hc
      rw [entry_take M 2 hik] at he2
      have hjM : j ∈ children M i := by rw [children_take, List.mem_filter] at hj; exact hj.1
      have hjk : j < k := by
        rw [children_take, List.mem_filter] at hj; simpa using hj.2
      have hcM : c ∈ children M j := by rw [children_take, List.mem_filter] at hc; exact hc.1
      rw [col_take M hjk, bump_take M hik] at hjb
      exact hb he2 j hjM hjb c hcM

/-- Row 0 of a child is one more than that of its parent. -/
def R0P (M : Mat) : Prop := ∀ c p, par M 0 c = some p → entry M 0 c = entry M 0 p + 1

/-- Row 2 is at most `1`. -/
def Z2 (M : Mat) : Prop := ∀ i, entry M 2 i ≤ 1

/-- An upgrade target has row 2 at least `1`. -/
theorem upg_target_e2 {M : Mat} {k c : Nat} (h : upg M k = some c) : 1 ≤ entry M 2 c := by
  unfold upg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i m hm
      simp only at h
      split at h
      · rename_i hcl
        have hc : k + 1 = c := Option.some.inj h
        subst hc
        have : entry M 2 (k + 1) = (col M (k + 1)).2.2 := rfl
        rw [this, hcl.2]; simp
      · rw [upgClimb_find] at h
        have hp := List.find?_some h
        simp only [decide_eq_true_eq] at hp
        have : entry M 2 c = (col M c).2.2 := rfl
        rw [this, hp.2.1]; simp

/-- **Dropping the last column counts no new children** (structural invariants). -/
theorem counted_take_last {M : Mat} (hM : 1 ≤ M.length) (hR0 : R0P M) (hZ2 : Z2 M)
    (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) :
    ∀ i c, i < M.length - 1 → c ∈ children (M.take (M.length - 1)) i →
      Counted (M.take (M.length - 1)) i c → Counted M i c := by
  intro i c hi hc hcnt
  have hcx : c < M.length - 1 := by rw [children_take, List.mem_filter] at hc; simpa using hc.2
  have hcM : c ∈ children M i := by rw [children_take, List.mem_filter] at hc; exact hc.1
  obtain ⟨hcb, hcu⟩ := hcnt
  rw [col_take M hcx, bump_take M hi] at hcb
  refine ⟨hcb, ?_⟩
  rintro ⟨hiu, htop⟩
  apply hcu
  -- the upgrade into `c`
  unfold isUpg at hiu
  rw [List.any_eq_true] at hiu
  obtain ⟨k, hk, hkk⟩ := hiu
  have hk' := List.mem_range.mp hk
  have hu : upg M k = some c := of_decide_eq_true hkk
  rcases Nat.lt_or_ge (k + 1) (M.length - 1) with hk1 | hk1
  · -- the upgrade survives in the prefix
    have hiuT : isUpg (M.take (M.length - 1)) c = true :=
      (isUpg_take M (by omega) c).mpr ⟨k, hk1, hu⟩
    refine ⟨hiuT, ?_⟩
    -- topped survives unless `x` is the last child of `c`
    unfold topped at htop ⊢
    rw [children_take]
    by_cases hxc : M.length - 1 ∈ children M c
    · -- `x` is the last child of `c`
      have hsplit : children M c = (children M c).filter (fun d => decide (d < M.length - 1)) ++
          [M.length - 1] := by
        apply split_last_max _ _ (children_sorted M c) hxc
        intro d hd; have := (mem_children hd).2; omega
      have hlastM : (children M c).getLast? = some (M.length - 1) := by rw [hsplit]; simp
      rw [hlastM] at htop
      simp only [decide_eq_true_eq] at htop
      have hc2 : entry M 2 c = 1 := by have := upg_target_e2 hu; have := hZ2 c; omega
      cases hd : ((children M c).filter (fun d => decide (d < M.length - 1))).getLast? with
      | none => rfl
      | some d =>
        simp only [decide_eq_true_eq]
        have hdm := List.mem_of_getLast? hd
        rw [List.mem_filter] at hdm
        have hdx : d < M.length - 1 := by simpa using hdm.2
        rw [col_take M hdx, bump_take M hcx]
        by_contra hdb
        obtain ⟨l₁, hl₁⟩ := List.getLast?_eq_some_iff.mp hd
        have hcons : children M c = l₁ ++ d :: (M.length - 1) :: [] := by
          rw [hsplit, hl₁]; simp
        have hle := hSD c l₁ [] d (M.length - 1) hcons
        have hpd := (mem_children_iff.mp hdm.1).2
        have hpx := (mem_children_iff.mp hxc).2
        have h0d := hR0 d c hpd
        have h1d := hZ1 c d hc2 hdm.1
        have h2d := hZ2 d
        unfold colLe at hle
        rw [htop] at hle
        unfold bump at hle
        have hd0 : (col M d).1 = entry M 0 d := rfl
        have hd1 : (col M d).2.1 = entry M 1 d := rfl
        have hd2 : (col M d).2.2 = entry M 2 d := rfl
        rw [hd0, hd1, hd2] at hle
        simp only at hle
        apply hdb
        rw [col_eq_entries]
        unfold bump
        rcases hle with h | ⟨_, h | ⟨h1, h2⟩⟩
        · omega
        · omega
        · simp only [Prod.mk.injEq]; omega
    · have : (children M c).filter (fun d => decide (d < M.length - 1)) = children M c := by
        rw [List.filter_eq_self]
        intro d hd
        have := (mem_children hd).2
        simp only [decide_eq_true_eq]
        by_contra h
        have : d = M.length - 1 := by omega
        rw [this] at hd; exact hxc hd
      rw [this]
      cases hlc : (children M c).getLast? with
      | none => rw [hlc] at htop
      | some d =>
        rw [hlc] at htop
        have hdm := List.mem_of_getLast? hlc
        have hdx : d < M.length - 1 := by
          have := (mem_children hdm).2
          rcases Nat.lt_or_ge d (M.length - 1) with h | h
          · exact h
          · have : d = M.length - 1 := by omega
            rw [this] at hdm; exact absurd hdm hxc
        simp only [col_take M hdx, bump_take M hcx]
        exact htop
  · -- the upgrade comes from `x − 1` (an ancestor upgrade, not topped) or `x` (none)
    exfalso
    rcases Nat.lt_or_ge k (M.length - 1) with hk2 | hk2
    · have hkx : k = M.length - 2 := by omega
      have hne : c ≠ k + 1 := by omega
      have := hUAT k c hu hne
      rw [this] at htop; cases htop
    · unfold upg at hu
      rw [if_pos (Or.inr (Or.inr (by omega)))] at hu
      cases hu

end Ytosk
