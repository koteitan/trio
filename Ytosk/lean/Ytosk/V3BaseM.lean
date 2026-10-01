/-
**基底 SRO[n] = (0,0,0)((1,1,1)(2,1,1)(3,1,0))^n とその接頭辞の形。**

列 i ≥ 1 は ((i−1)%3 + 1, 1, [(i−1)%3 ≠ 2])。長さ L の接頭辞を `Mlen L` と書く（SRO[n] = Mlen (1 + 3n)、
落とした行列 SRO[n].take (3n) = Mlen (3n)）。列の種類は 3 つ:
- A（(i−1)%3 = 0, (1,1,1)）: 行 0 の親は 0。子は i+1（B）。
- B（(i−1)%3 = 1, (2,1,1)）: 親は i−1（A、のりしろの子）。子は i+1（D）。
- D（(i−1)%3 = 2, (3,1,0)）: 親は i−1。子はない。上げ（upg）は i+1（次の A）。
行 1 の親は 0 以外のすべての列で 0。
-/
import Ytosk.V3InvExpand

namespace Ytosk

open T

/-- The column `i` of `SRO[n]`. -/
def bcol (i : Nat) : Nat × Nat × Nat :=
  if i = 0 then (0, 0, 0) else ((i - 1) % 3 + 1, 1, if (i - 1) % 3 = 2 then 0 else 1)

/-- The prefix of length `L` of the base family. -/
def Mlen (L : Nat) : Mat := (List.range L).map bcol

section
variable {L : Nat}

@[simp] theorem Mlen_length : (Mlen L).length = L := by simp [Mlen]

theorem Mlen_getD {i : Nat} (hi : i < L) : (Mlen L).getD i (0, 0, 0) = bcol i := by
  simp [Mlen, List.getD_eq_getElem?_getD, hi]

theorem Mlen_take {L' : Nat} (h : L' ≤ L) : (Mlen L).take L' = Mlen L' := by
  unfold Mlen; rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem Mlen_col {i : Nat} (hi : i < L) : col (Mlen L) i = bcol i := Mlen_getD hi

theorem Mlen_e0 {i : Nat} (hi : i < L) : entry (Mlen L) 0 i = if i = 0 then 0 else (i - 1) % 3 + 1 := by
  rw [entry0_getD, Mlen_getD hi]; unfold bcol; split_ifs <;> rfl

theorem Mlen_e1 {i : Nat} (hi : i < L) : entry (Mlen L) 1 i = if i = 0 then 0 else 1 := by
  rw [entry1_getD, Mlen_getD hi]; unfold bcol; split_ifs <;> rfl

theorem Mlen_e2 {i : Nat} (hi : i < L) :
    entry (Mlen L) 2 i = if i = 0 then 0 else if (i - 1) % 3 = 2 then 0 else 1 := by
  rw [entry2_getD, Mlen_getD hi]; unfold bcol; split_ifs <;> rfl

theorem Mlen_e0_pos {i : Nat} (hi : i < L) (h1 : 1 ≤ i) : 1 ≤ entry (Mlen L) 0 i := by
  rw [Mlen_e0 hi, if_neg (by omega)]; omega

/-! ## 行 0 の親 -/

theorem Mlen_par0_A {i : Nat} (hi : i < L) (h1 : 1 ≤ i) (hk : (i - 1) % 3 = 0) :
    par (Mlen L) 0 i = some 0 := by
  rw [par0_spec]
  refine ⟨by omega, ?_, fun j h1' h2 => ?_⟩
  · rw [Mlen_e0 (by omega), Mlen_e0 hi, if_pos rfl, if_neg (by omega)]; omega
  · rw [Mlen_e0 hi, if_neg (by omega), hk]; exact Mlen_e0_pos (by omega) (by omega)

theorem Mlen_par0_BD {i : Nat} (hi : i < L) (h1 : 1 ≤ i) (hk : (i - 1) % 3 ≠ 0) :
    par (Mlen L) 0 i = some (i - 1) := by
  rw [par0_spec]
  refine ⟨by omega, ?_, fun j h1' h2 => by omega⟩
  rw [Mlen_e0 (by omega), Mlen_e0 hi, if_neg (by omega)]
  split_ifs with h
  · omega
  · omega

theorem Mlen_anc0 : ∀ {i : Nat}, i < L → Anc0 (Mlen L) 0 i
  | 0, _ => Anc0.refl 0
  | i + 1, hi => by
    by_cases hk : (i + 1 - 1) % 3 = 0
    · exact Anc0.step (Mlen_par0_A hi (by omega) hk) (Anc0.refl 0)
    · exact Anc0.step (Mlen_par0_BD hi (by omega) hk) (Mlen_anc0 (by omega))

/-! ## 行 1 の親 -/

theorem Mlen_par1 {i : Nat} (hi : i < L) (h1 : 1 ≤ i) : par (Mlen L) 1 i = some 0 := by
  rw [par1_iff _ (by simpa using hi)]
  refine ⟨by simp; omega, by simpa using hi, h1, ?_, ⟨by simp; omega, by simpa using hi,
    rtg0_of_anc0 (Mlen_anc0 hi) (by simpa using hi)⟩, fun j ⟨hj, hjl⟩ => ?_⟩
  · show entry (Mlen L) 1 0 < entry (Mlen L) 1 i
    rw [Mlen_e1 (by omega), Mlen_e1 hi, if_pos rfl, if_neg (by omega)]; omega
  · have hjL : j < L := by have := hjl.1; simpa using this
    show entry (Mlen L) 1 i ≤ entry (Mlen L) 1 j
    rw [Mlen_e1 hi, Mlen_e1 hjL, if_neg (by omega), if_neg (by omega)]

theorem Mlen_par1_0 : par (Mlen L) 1 0 = none := par_zero_none _ 1

/-! ## 上げ -/

theorem Mlen_upg_D {i : Nat} (hi : i + 1 < L) (h1 : 1 ≤ i) (hk : (i - 1) % 3 = 2) :
    upg (Mlen L) i = some (i + 1) := by
  have hiL : i < L := by omega
  unfold upg
  rw [if_neg (by
    rw [Mlen_e1 hiL, Mlen_e2 hiL, if_neg (by omega), if_neg (by omega), if_pos hk, Mlen_length]
    omega)]
  rw [Mlen_par1 hiL h1]
  simp only
  have h3 : (i + 1 - 1) % 3 = 0 := by omega
  rw [if_pos ⟨Mlen_par1 hi (by omega), by
    rw [Mlen_col hi, Mlen_e0 (by omega), Mlen_e1 hiL, Mlen_e2 (by omega)]
    simp [bcol, show i ≠ 0 by omega]; omega⟩]

theorem Mlen_upg_none {i : Nat} (h : ¬ (i + 1 < L ∧ 1 ≤ i ∧ (i - 1) % 3 = 2)) :
    upg (Mlen L) i = none := by
  unfold upg
  rw [if_pos]
  rcases Nat.lt_or_ge i L with hiL | hiL
  · rw [Mlen_e1 hiL, Mlen_e2 hiL, Mlen_length]
    split_ifs <;> omega
  · left; exact entry_out (by simpa using hiL) 1

theorem Mlen_upg_iff {i k : Nat} :
    upg (Mlen L) i = some k ↔ i + 1 < L ∧ 1 ≤ i ∧ (i - 1) % 3 = 2 ∧ k = i + 1 := by
  by_cases h : i + 1 < L ∧ 1 ≤ i ∧ (i - 1) % 3 = 2
  · rw [Mlen_upg_D h.1 h.2.1 h.2.2]
    constructor
    · intro e; cases e; exact ⟨h.1, h.2.1, h.2.2, rfl⟩
    · rintro ⟨_, _, _, rfl⟩; rfl
  · rw [Mlen_upg_none h]
    constructor
    · intro e; cases e
    · rintro ⟨h1, h2, h3, _⟩; exact absurd ⟨h1, h2, h3⟩ h

/-! ## 子の並び -/

/-- Two strictly increasing lists with the same members are equal. -/
theorem list_eq_of_sorted_mem : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: t₁, b :: t₂, h₁, h₂, h => by
    have h₁' := List.pairwise_cons.mp h₁
    have h₂' := List.pairwise_cons.mp h₂
    have hab : a = b := by
      have ha := (h a).mp (by simp)
      have hb := (h b).mpr (by simp)
      rcases List.mem_cons.mp ha with e | ha
      · exact e
      rcases List.mem_cons.mp hb with e | hb
      · exact e.symm
      have := h₁'.1 b hb; have := h₂'.1 a ha; omega
    subst hab
    rw [list_eq_of_sorted_mem h₁'.2 h₂'.2 (fun x => ?_)]
    constructor
    · intro hx
      have hne : x ≠ a := by have := h₁'.1 x hx; omega
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd e hne
      · exact e
    · intro hx
      have hne : x ≠ a := by have := h₂'.1 x hx; omega
      rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd e hne
      · exact e

theorem children_eq_of {M : Mat} {p : Nat} {l : List Nat} (hl : l.Pairwise (· < ·))
    (h : ∀ c, c < M.length ∧ par M 0 c = some p ↔ c ∈ l) : children M p = l :=
  list_eq_of_sorted_mem (children_sorted M p) hl (fun c => by rw [mem_children_iff]; exact h c)

theorem Mlen_children_AB {i : Nat} (hi : i + 1 < L) (h1 : 1 ≤ i) (hk : (i - 1) % 3 ≠ 2) :
    children (Mlen L) i = [i + 1] := by
  apply children_eq_of (by simp)
  intro c
  simp only [Mlen_length, List.mem_singleton]
  constructor
  · rintro ⟨hc, hp⟩
    by_cases hck : (c - 1) % 3 = 0
    · have hc1 : 1 ≤ c := by have := par_lt _ 0 c i hp; omega
      rw [Mlen_par0_A hc hc1 hck] at hp; cases hp; omega
    · have hc1 : 1 ≤ c := by have := par_lt _ 0 c i hp; omega
      rw [Mlen_par0_BD hc hc1 hck] at hp; cases hp; omega
  · rintro rfl
    exact ⟨hi, by rw [Mlen_par0_BD hi (by omega) (by omega)]; rfl⟩

theorem Mlen_children_nil {i : Nat} (h : i + 1 = L ∨ (1 ≤ i ∧ (i - 1) % 3 = 2) ∨ L ≤ i) :
    children (Mlen L) i = [] := by
  apply nil_of_none
  intro c hc
  obtain ⟨hcL, hp⟩ := mem_children_iff.mp hc
  rw [Mlen_length] at hcL
  have hic := par_lt _ 0 c i hp
  by_cases hck : (c - 1) % 3 = 0
  · rw [Mlen_par0_A hcL (by omega) hck] at hp; cases hp
    rcases h with h | h | h <;> omega
  · rw [Mlen_par0_BD hcL (by omega) hck] at hp; cases hp
    rcases h with h | h | h <;> omega

/-- The root's children: `1` first, then the other `A` columns. -/
theorem Mlen_children_0 (hL : 2 ≤ L) : ∃ t, children (Mlen L) 0 = 1 :: t ∧
    ∀ c ∈ t, 4 ≤ c ∧ c < L ∧ (c - 1) % 3 = 0 := by
  have h1 : 1 ∈ children (Mlen L) 0 :=
    mem_children_iff.mpr ⟨by simp; omega, Mlen_par0_A (by omega) le_rfl rfl⟩
  have hmem : ∀ c ∈ children (Mlen L) 0, 1 ≤ c ∧ c < L ∧ (c - 1) % 3 = 0 := by
    intro c hc
    obtain ⟨hcL, hp⟩ := mem_children_iff.mp hc
    rw [Mlen_length] at hcL
    have := par_lt _ 0 c 0 hp
    refine ⟨by omega, hcL, ?_⟩
    by_contra hck
    rw [Mlen_par0_BD hcL (by omega) hck] at hp; have := Option.some.inj hp; omega
  have hs := children_sorted (Mlen L) 0
  cases hl : children (Mlen L) 0 with
  | nil => rw [hl] at h1; simp at h1
  | cons a t =>
    rw [hl] at hs hmem h1
    have ha := hmem a (by simp)
    have ha1 : a = 1 := by
      rcases List.mem_cons.mp h1 with e | e
      · exact e.symm
      · have := (List.pairwise_cons.mp hs).1 1 e; omega
    subst ha1
    refine ⟨t, rfl, fun c hc => ?_⟩
    have := (List.pairwise_cons.mp hs).1 c hc
    have hc' := hmem c (List.mem_cons_of_mem _ hc)
    exact ⟨by omega, hc'.2.1, hc'.2.2⟩

/-! ## のりしろ・上げの的・頭打ち -/

theorem Mlen_bump {i : Nat} (hi : i < L) :
    bump (Mlen L) i = (entry (Mlen L) 0 i + 1, entry (Mlen L) 1 i, 1) := rfl

/-- The bump child: `B` under `A`. -/
theorem Mlen_col_eq_bump {i j : Nat} (hj : j < L) (hi1 : 1 ≤ i) (hij : j = i + 1) :
    col (Mlen L) j = bump (Mlen L) i ↔ (i - 1) % 3 = 0 := by
  subst hij
  rw [Mlen_col hj, Mlen_bump (by omega), Mlen_e0 (by omega), Mlen_e1 (by omega)]
  unfold bcol
  simp only [show i + 1 ≠ 0 by omega, show i ≠ 0 by omega, if_false, Nat.add_sub_cancel,
    Prod.mk.injEq]
  simp only [true_and]
  split_ifs <;> constructor <;> intro h <;> first | omega | exact absurd h.2 id

theorem Mlen_bump_root : col (Mlen L) 1 ≠ bump (Mlen L) 0 := by
  intro h
  rcases Nat.lt_or_ge 1 L with hL | hL
  · rw [Mlen_col hL, Mlen_bump (by omega), Mlen_e0 (by omega), Mlen_e1 (by omega)] at h
    unfold bcol at h; simp at h
  · unfold col bump at h
    rw [getD_out (by simpa using hL)] at h
    simp at h

theorem Mlen_isUpg {c : Nat} : isUpg (Mlen L) c = true ↔ 4 ≤ c ∧ c < L ∧ (c - 1) % 3 = 0 := by
  unfold isUpg
  rw [List.any_eq_true]
  constructor
  · rintro ⟨k, _, hk⟩
    have := Mlen_upg_iff.mp (by simpa using hk)
    omega
  · intro h
    refine ⟨c - 1, by simp; omega, ?_⟩
    simp only [decide_eq_true_eq]
    rw [Mlen_upg_iff]; omega

theorem Mlen_topped_A {c : Nat} (hc : c < L) (h1 : 1 ≤ c) (hk : (c - 1) % 3 = 0) :
    topped (Mlen L) c = true := by
  unfold topped
  by_cases hc1 : c + 1 < L
  · rw [Mlen_children_AB hc1 h1 (by omega)]
    simp only [List.getLast?_singleton, decide_eq_true_eq]
    exact (Mlen_col_eq_bump hc1 h1 rfl).mpr hk
  · rw [Mlen_children_nil (Or.inl (by omega))]; rfl

/-- Which children count. -/
theorem Mlen_counted {i c : Nat} (hc : c ∈ children (Mlen L) i) :
    Counted (Mlen L) i c ↔ (i = 0 ∧ c = 1) ∨ (1 ≤ i ∧ (i - 1) % 3 = 1) := by
  obtain ⟨hcL, hp⟩ := mem_children_iff.mp hc
  rw [Mlen_length] at hcL
  have hic := par_lt _ 0 c i hp
  unfold Counted
  by_cases hck : (c - 1) % 3 = 0
  · rw [Mlen_par0_A hcL (by omega) hck] at hp; cases hp
    rw [Mlen_isUpg]
    by_cases hc1 : c = 1
    · subst hc1
      exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => ⟨Mlen_bump_root, by omega⟩⟩
    · have ht := Mlen_topped_A hcL (by omega) hck
      constructor
      · rintro ⟨_, h⟩; exact absurd ⟨⟨by omega, hcL, hck⟩, ht⟩ h
      · intro h; omega
  · rw [Mlen_par0_BD hcL (by omega) hck] at hp; cases hp
    have hbump := Mlen_col_eq_bump (i := c - 1) hcL (by omega) (by omega)
    have hnu : ¬ (isUpg (Mlen L) c = true) := by rw [Mlen_isUpg]; omega
    by_cases hk : (c - 1 - 1) % 3 = 0
    · constructor
      · rintro ⟨h, _⟩; exact absurd (hbump.mpr hk) h
      · intro h; omega
    · constructor
      · intro _; right; omega
      · intro _; exact ⟨fun h => hk (hbump.mp h), fun h => hnu h.1⟩

theorem Mlen_roots (hL : 1 ≤ L) : roots (Mlen L) = [0] := by
  apply list_eq_of_sorted_mem (List.Pairwise.filter _ List.pairwise_lt_range) (by simp)
  intro c
  simp only [List.mem_filter, List.mem_range, Mlen_length, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro ⟨hc, h⟩
    rw [Mlen_col hc] at h
    unfold bcol at h
    by_contra hne
    rw [if_neg hne] at h
    simp at h
  · rintro rfl
    exact ⟨hL, by rw [Mlen_col hL]; rfl⟩

end

/-! ## SRO[n] は Mlen (1 + 3n) -/

theorem expand_SRO_eq (n : Nat) : expand SRO n = Mlen (1 + 3 * n) := by
  have hp : par SRO (TRIO.srow SRO (SRO.length - 1)) (SRO.length - 1) = some 1 := by decide
  have he := expand_eq_gexp SRO n (by decide) (by decide) hp
  have he' : expand SRO n = TRIO.gexp SRO 1 3 0 0 n := by rw [he]; rfl
  rw [he']
  have hlen : 1 + 3 + 1 = SRO.length := rfl
  apply List.ext_getElem
  · rw [TRIO.gexp_length hlen, Mlen_length]; omega
  · intro i h1 h2
    rw [Mlen_length] at h2
    have key : (TRIO.gexp SRO 1 3 0 0 n).getD i (0, 0, 0) = (Mlen (1 + 3 * n)).getD i (0, 0, 0) := by
      rw [Mlen_getD h2]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; rw [TRIO.gexp_getD_low hlen (by omega)]; rfl
      · have hc : (i - 1) / 3 < n := by omega
        have hq : (i - 1) % 3 < 3 := Nat.mod_lt _ (by omega)
        have hi' : i = 1 + ((i - 1) / 3 * 3 + (i - 1) % 3) := by omega
        rw [hi', TRIO.gexp_getD_mir hlen hc hq]
        unfold bcol
        rw [if_neg (show 1 + ((i - 1) / 3 * 3 + (i - 1) % 3) ≠ 0 by omega)]
        have e1 : (1 + ((i - 1) / 3 * 3 + (i - 1) % 3) - 1) % 3 = (i - 1) % 3 := by omega
        rw [e1]
        have : (i - 1) % 3 = 0 ∨ (i - 1) % 3 = 1 ∨ (i - 1) % 3 = 2 := by omega
        rcases this with h | h | h <;> rw [h] <;> simp [TRIO.entry, SRO]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem (by rw [Mlen_length]; exact h2)] at key
    simpa using key

end Ytosk
