/-
KlA.lean: 段 o の持ち上げ量 κ つきの持ち上げ klift（notes 追記506・508・509）。

    lamK A o j K y = 0（行1 < o、または行1 = o で z ≠ 0）、min (K y) j（行1 = o で z = 0）、j（行1 > o）
    Lk A o j K c   = c の行 0 の祖先 y（c を含む）の lamK の最小
    klift A o j K  = 列 c を行 1 で Lk c だけ上げる

行 1 の親子で Lk が等しい（Lk_parent）ので、klift は行 0〜2 の親子関係を保つ（hasParent_klift）。
κ に条件は要らない（道の最小を取るので、印なしの段 o の祖先の下の κ は効かない）。
-/
import Aexp

namespace TRIO
namespace KlA

open Classical Wset

def lamK (A : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) (y : ℕ) : ℕ :=
  if entry A 1 y < o then 0
  else if entry A 1 y = o then (if entry A 2 y = 0 then min (K y) j else 0)
  else j

theorem lamK_le (A : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) (y : ℕ) : lamK A o j K y ≤ j := by
  unfold lamK; split_ifs <;> omega

theorem lamK_low {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {y : ℕ} (h : entry A 1 y < o) :
    lamK A o j K y = 0 := by
  unfold lamK; rw [if_pos h]

theorem lamK_high {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {y : ℕ} (h : o < entry A 1 y) :
    lamK A o j K y = j := by
  unfold lamK; rw [if_neg (by omega), if_neg (by omega)]

/-- 行 0 の祖先（自身を含む）の lamK の最小。 -/
noncomputable def Lk (A : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) (c : ℕ) : ℕ :=
  sInf {m | ∃ y, Relation.ReflTransGen (nextrel0 A) y c ∧ lamK A o j K y = m}

section Basic

variable {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ}

theorem Lk_le {c y : ℕ} (h : Relation.ReflTransGen (nextrel0 A) y c) :
    Lk A o j K c ≤ lamK A o j K y :=
  Nat.sInf_le ⟨y, h, rfl⟩

theorem Lk_mem (c : ℕ) :
    ∃ y, Relation.ReflTransGen (nextrel0 A) y c ∧ lamK A o j K y = Lk A o j K c := by
  have hne : {m | ∃ y, Relation.ReflTransGen (nextrel0 A) y c ∧ lamK A o j K y = m}.Nonempty :=
    ⟨lamK A o j K c, c, Relation.ReflTransGen.refl, rfl⟩
  exact Nat.sInf_mem hne

theorem Lk_mono {c y : ℕ} (h : Relation.ReflTransGen (nextrel0 A) y c) :
    Lk A o j K c ≤ Lk A o j K y := by
  obtain ⟨w, hw, hew⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K) y
  rw [← hew]
  exact Lk_le (hw.trans h)

theorem Lk_le_j (c : ℕ) : Lk A o j K c ≤ j :=
  le_trans (Lk_le Relation.ReflTransGen.refl) (lamK_le A o j K c)

theorem Lk_low {c : ℕ} (h : entry A 1 c < o) : Lk A o j K c = 0 := by
  have := Lk_le (A := A) (o := o) (j := j) (K := K) (c := c) Relation.ReflTransGen.refl
  rw [lamK_low h] at this
  omega

/-- 行 1 の親 j0 から b への行 0 の鎖の途中（j0 を含む）の列 x の Lk は、b の Lk 以下。 -/
theorem Lk_up {j0 b x : ℕ} (h : nextrel1 A j0 b) (hx0 : Relation.ReflTransGen (nextrel0 A) j0 x)
    (_hxb : le0 A x b) : Lk A o j K x ≤ Lk A o j K b := by
  obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K) b
  have hyb : le0 A y b := ⟨by have := rtg0_le hy; have := h.2.1; omega, h.2.1, hy⟩
  rcases Nat.lt_or_ge j0 y with hlt | hge
  · have hbet := h.2.2.2.2.2 y ⟨hlt, hyb⟩
    have hlt1 := h.2.2.2.1
    by_cases hj0o : entry A 1 j0 < o
    · have h0 : Lk A o j K x ≤ 0 := by
        have := Lk_le (A := A) (o := o) (j := j) (K := K) hx0
        rwa [lamK_low hj0o] at this
      omega
    · rw [← hey, lamK_high (by omega)]
      exact Lk_le_j x
  · have hyj0 : Relation.ReflTransGen (nextrel0 A) y j0 := by
      rcases Nat.eq_or_lt_of_le hge with heq | hlt
      · subst heq; exact Relation.ReflTransGen.refl
      · exact (le0_of_le0_le0 hyb h.2.2.2.2.1 hlt).2.2
    rw [← hey]
    exact Lk_le (hyj0.trans hx0)

/-- ★ 行 1 の親子で Lk は等しい。 -/
theorem Lk_parent {j0 b : ℕ} (h : nextrel1 A j0 b) : Lk A o j K j0 = Lk A o j K b :=
  le_antisymm (Lk_up h Relation.ReflTransGen.refl h.2.2.2.2.1) (Lk_mono h.2.2.2.2.1.2.2)

theorem Lk_between {j0 b x : ℕ} (h : nextrel1 A j0 b) (hx : j0 < x) (hxb : le0 A x b) :
    Lk A o j K x = Lk A o j K b := by
  have hj0x : le0 A j0 x := le0_of_le0_le0 h.2.2.2.2.1 hxb hx
  exact le_antisymm (Lk_up h hj0x.2.2 hxb) (Lk_mono hxb.2.2)

end Basic

/-- ★ κ つきの持ち上げ。 -/
noncomputable def klift (A : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) : TrioSeq :=
  (List.range A.length).map fun c =>
    ((entry A 0 c, entry A 1 c + Lk A o j K c, entry A 2 c) : ℕ × ℕ × ℕ)

section Klift

variable {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ}

@[simp] theorem klift_length (A : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) :
    (klift A o j K).length = A.length := by simp [klift]

theorem klift_getD {i : ℕ} (hi : i < A.length) :
    (klift A o j K).getD i (0, 0, 0)
      = ((entry A 0 i, entry A 1 i + Lk A o j K i, entry A 2 i) : ℕ × ℕ × ℕ) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [klift_length]; exact hi)]
  unfold klift
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem entry0_klift (i : ℕ) : entry (klift A o j K) 0 i = entry A 0 i := by
  show ((klift A o j K).getD i (0, 0, 0)).1 = ((A.getD i (0, 0, 0)).1 : ℕ)
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [klift_getD hi]; rfl
  · rw [getD_out (by rw [klift_length]; omega), getD_out hi]

theorem entry2_klift (i : ℕ) : entry (klift A o j K) 2 i = entry A 2 i := by
  show ((klift A o j K).getD i (0, 0, 0)).2.2 = ((A.getD i (0, 0, 0)).2.2 : ℕ)
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [klift_getD hi]; rfl
  · rw [getD_out (by rw [klift_length]; omega), getD_out hi]

theorem entry1_klift {i : ℕ} (hi : i < A.length) :
    entry (klift A o j K) 1 i = entry A 1 i + Lk A o j K i := by
  show ((klift A o j K).getD i (0, 0, 0)).2.1 = _
  rw [klift_getD hi]

theorem nextrel0_klift {a b : ℕ} : nextrel0 (klift A o j K) a b ↔ nextrel0 A a b := by
  unfold nextrel0
  rw [klift_length]
  simp only [entry0_klift]

theorem rtg0_klift {a b : ℕ} :
    Relation.ReflTransGen (nextrel0 (klift A o j K)) a b
      ↔ Relation.ReflTransGen (nextrel0 A) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel0_klift.1 hyw)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel0_klift.2 hyw)

theorem le0_klift {a b : ℕ} : le0 (klift A o j K) a b ↔ le0 A a b := by
  unfold le0
  rw [klift_length, rtg0_klift]

/-- 持ち上げた側の行 1 の親子でも、元の列の Lk は等しい。 -/
theorem Lk_eq_of_nextrel1_klift {a b : ℕ} (h : nextrel1 (klift A o j K) a b) :
    Lk A o j K a = Lk A o j K b := by
  have hal : a < A.length := by have := h.1; rwa [klift_length] at this
  have hbl : b < A.length := by have := h.2.1; rwa [klift_length] at this
  have hab : le0 A a b := le0_klift.1 h.2.2.2.2.1
  have hmono : Lk A o j K b ≤ Lk A o j K a := Lk_mono hab.2.2
  have hlt : entry A 1 a + Lk A o j K a < entry A 1 b + Lk A o j K b := by
    have := h.2.2.2.1; rwa [entry1_klift hal, entry1_klift hbl] at this
  obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K) b
  have hyb : le0 A y b := ⟨by have := rtg0_le hy; omega, hbl, hy⟩
  rcases Nat.lt_or_ge a y with hay | hya
  · have hyl : y < A.length := hyb.1
    have hbet := h.2.2.2.2.2 y ⟨hay, le0_klift.2 hyb⟩
    rw [entry1_klift hbl, entry1_klift hyl] at hbet
    have hLy : Lk A o j K y ≤ lamK A o j K y := Lk_le Relation.ReflTransGen.refl
    rcases Nat.lt_trichotomy (entry A 1 y) o with hy1 | hy1 | hy1
    · rw [lamK_low hy1] at hey hLy
      have ha0 : entry A 1 a < o := by omega
      have := Lk_low (A := A) (o := o) (j := j) (K := K) ha0
      omega
    · by_cases ha0 : entry A 1 a < o
      · have := Lk_low (A := A) (o := o) (j := j) (K := K) ha0
        omega
      · omega
    · rw [lamK_high hy1] at hey
      have := Lk_le_j (A := A) (o := o) (j := j) (K := K) a
      omega
  · have hya' : Relation.ReflTransGen (nextrel0 A) y a := by
      rcases Nat.eq_or_lt_of_le hya with heq | hlt
      · subst heq; exact Relation.ReflTransGen.refl
      · exact (le0_of_le0_le0 hyb hab hlt).2.2
    have := Lk_le (A := A) (o := o) (j := j) (K := K) hya'
    omega

/-- ★ klift は行 1 の辺関係を保つ。 -/
theorem nextrel1_klift {a b : ℕ} : nextrel1 (klift A o j K) a b ↔ nextrel1 A a b := by
  constructor
  · intro h
    have hal : a < A.length := by have := h.1; rwa [klift_length] at this
    have hbl : b < A.length := by have := h.2.1; rwa [klift_length] at this
    have hab : le0 A a b := le0_klift.1 h.2.2.2.2.1
    have hLab := Lk_eq_of_nextrel1_klift h
    have hlt : entry A 1 a < entry A 1 b := by
      have h4 := h.2.2.2.1
      rw [entry1_klift hal, entry1_klift hbl, hLab] at h4
      omega
    refine ⟨hal, hbl, h.2.2.1, hlt, hab, ?_⟩
    intro x hx
    have hxl : x < A.length := hx.2.1
    have hax : le0 A a x := le0_of_le0_le0 hab hx.2 hx.1
    have hLx : Lk A o j K x = Lk A o j K b :=
      le_antisymm (by rw [← hLab]; exact Lk_mono hax.2.2) (Lk_mono hx.2.2.2)
    have h5 := h.2.2.2.2.2 x ⟨hx.1, le0_klift.2 hx.2⟩
    rw [entry1_klift hxl, entry1_klift hbl, hLx] at h5
    omega
  · intro h
    have hal : a < A.length := h.1
    have hbl : b < A.length := h.2.1
    have hLab : Lk A o j K a = Lk A o j K b := Lk_parent h
    refine ⟨by rw [klift_length]; exact hal, by rw [klift_length]; exact hbl, h.2.2.1, ?_,
      le0_klift.2 h.2.2.2.2.1, ?_⟩
    · rw [entry1_klift hal, entry1_klift hbl, hLab]; have := h.2.2.2.1; omega
    · intro x hx
      have hxb : le0 A x b := le0_klift.1 hx.2
      have hxl : x < A.length := hxb.1
      have hLx := Lk_between (o := o) (j := j) (K := K) h hx.1 hxb
      have h5 := h.2.2.2.2.2 x ⟨hx.1, hxb⟩
      rw [entry1_klift hxl, entry1_klift hbl, hLx]
      omega

theorem le1_klift {a b : ℕ} : le1 (klift A o j K) a b ↔ le1 A a b := by
  unfold le1
  rw [klift_length]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel1_klift.1 hyw)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel1_klift.2 hyw)

theorem entry1_klift_pos (ho : 1 ≤ o) {c : ℕ} (hc : c < A.length) :
    0 < entry (klift A o j K) 1 c ↔ 0 < entry A 1 c := by
  rw [entry1_klift hc]
  constructor
  · intro h
    by_contra hn
    have := Lk_low (A := A) (o := o) (j := j) (K := K) (c := c) (by omega)
    omega
  · omega

theorem srow_klift (ho : 1 ≤ o) {c : ℕ} (hc : c < A.length) :
    srow (klift A o j K) c = srow A c := by
  unfold srow
  rw [entry2_klift]
  by_cases h2 : 0 < entry A 2 c
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2, if_congr (entry1_klift_pos ho hc) rfl rfl]

theorem nextrel2_klift {a b : ℕ} : nextrel2 (klift A o j K) a b ↔ nextrel2 A a b := by
  unfold nextrel2
  rw [klift_length]
  simp only [entry2_klift, le1_klift]

theorem nextR_klift {i a b : ℕ} : nextR (klift A o j K) i a b ↔ nextR A i a b := by
  unfold nextR
  split
  · exact nextrel0_klift
  · split
    · exact nextrel1_klift
    · exact nextrel2_klift

theorem hasParent_klift {i b : ℕ} : hasParent (klift A o j K) i b ↔ hasParent A i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, huniq⟩
    exact ⟨j0, nextR_klift.1 hj0, fun y hy => huniq y (nextR_klift.2 hy)⟩
  · rintro ⟨j0, hj0, huniq⟩
    exact ⟨j0, nextR_klift.2 hj0, fun y hy => huniq y (nextR_klift.1 hy)⟩

theorem parent_klift {i b : ℕ} : parent (klift A o j K) i b = parent A i b := by
  unfold parent
  exact congrArg _ (funext fun j0 => propext nextR_klift)

end Klift

end KlA
end TRIO
