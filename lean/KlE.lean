/-
KlE.lean: klift の分配（シフト・連結・根の下・節点の下）。

    klift_shift0 / klift_append / klift_app（κ の添字をずらす）
    klift_node_high（節点の段 > o）/ klift_node_low（段 < o）/ klift_node_mid（段 = o、z = 0、上限 min (K 0) j）
-/
import KlD

namespace TRIO
namespace KlE

open Classical Wset KlA KlB GxP GxJ

/-! ## シフト -/

theorem Lk_shift0 {d o j : ℕ} {K : ℕ → ℕ} (Z : TrioSeq) (c : ℕ) :
    Lk (shiftr01 d 0 Z) o j K c = Lk Z o j K c := by
  have hlam : ∀ y, lamK (shiftr01 d 0 Z) o j K y = lamK Z o j K y :=
    fun y => lamK_congr (entry1_shiftr01 Z y) (entry2_shiftr01 Z y) rfl
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := Z) (o := o) (j := j) (K := K) c
    rw [← hey, ← hlam y]; exact Lk_le (rtg0_shiftr01.mpr hy)
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := shiftr01 d 0 Z) (o := o) (j := j) (K := K) c
    rw [← hey, hlam y]; exact Lk_le (rtg0_shiftr01.mp hy)

theorem klift_shift0 (d : ℕ) (Z : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) :
    klift (shiftr01 d 0 Z) o j K = shiftr01 d 0 (klift Z o j K) := by
  refine list_ext_getD (by rw [klift_length, shiftr01_length, shiftr01_length, klift_length]) ?_
  intro i hi
  rw [klift_length, shiftr01_length] at hi
  rw [klift_getD (by rw [shiftr01_length]; exact hi),
    shiftr01_getD (by rw [klift_length]; exact hi), klift_getD hi,
    entry0_shiftr01 hi, entry1_shiftr01, entry2_shiftr01, Lk_shift0]
  simp

/-! ## 連結 -/

theorem Lk_append_left {A B : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {c : ℕ} (hc : c < A.length) :
    Lk (A ++ B) o j K c = Lk A o j K c := by
  have h := Lk_take (X := A ++ B) (o := o) (j := j) (K := K) (l := A.length) (by simp) hc
  rw [List.take_left] at h
  exact h.symm

theorem Lk_append_right {A B : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {q : ℕ} (hq : q < B.length)
    (hrs : ∀ x ∈ A, entry B 0 0 ≤ x.1) :
    Lk (A ++ B) o j K (A.length + q) = Lk B o j (fun i => K (A.length + i)) q := by
  have hlam : ∀ y, lamK (A ++ B) o j K (A.length + y)
      = lamK B o j (fun i => K (A.length + i)) y :=
    fun y => lamK_congr (entry_append_right A B 1 y) (entry_append_right A B 2 y) rfl
  have hnoA : ∀ y, Relation.ReflTransGen (nextrel0 (A ++ B)) y (A.length + q) → A.length ≤ y := by
    intro y hy
    by_contra hyA
    push_neg at hyA
    have hw := window_of_rtg0 hy (by simp; omega) A.length hyA (by omega)
    rw [Small.entry_append_left hyA, show A.length = A.length + 0 from rfl,
      entry_append_right] at hw
    have hmem := GxF.getD_mem_P hyA (P := fun x => entry B 0 0 ≤ x.1) hrs
    have : entry B 0 0 ≤ entry A 0 y := hmem
    omega
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ :=
      Lk_mem (A := B) (o := o) (j := j) (K := fun i => K (A.length + i)) q
    rw [← hey, ← hlam y]; exact Lk_le (rtg_nextrel0_lift A B hy)
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := A ++ B) (o := o) (j := j) (K := K) (A.length + q)
    have hyA := hnoA y hy
    have h1 := rtg0_append_unlift hyA hy q rfl
    rw [← hey, show y = A.length + (y - A.length) from by omega, hlam]
    exact Lk_le h1

theorem klift_append {A B : TrioSeq} (hrs : ∀ x ∈ A, entry B 0 0 ≤ x.1) (o j : ℕ) (K : ℕ → ℕ) :
    klift (A ++ B) o j K = klift A o j K ++ klift B o j (fun i => K (A.length + i)) := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [klift_length, List.length_append] at hi
  rw [klift_getD (by rw [List.length_append]; omega)]
  rcases Nat.lt_or_ge i A.length with hiA | hiA
  · have eg : (klift A o j K ++ klift B o j (fun i => K (A.length + i))).getD i (0, 0, 0)
        = (klift A o j K).getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [klift_length]; exact hiA)]
    rw [eg, klift_getD hiA, Small.entry_append_left hiA, Small.entry_append_left hiA,
      Small.entry_append_left hiA, Lk_append_left hiA]
  · obtain ⟨q, rfl⟩ : ∃ q, i = A.length + q := ⟨i - A.length, by omega⟩
    have hq : q < B.length := by omega
    rw [getD_app_right _ _ (by rw [klift_length]; omega), klift_length,
      show A.length + q - A.length = q from by omega, klift_getD hq,
      entry_append_right, entry_append_right, entry_append_right, Lk_append_right hq hrs]

theorem klift_app {W U : TrioSeq} (hW : Fr W) (hU : Hd U) (o j : ℕ) (K : ℕ → ℕ) :
    klift (W ++ U) o j K = klift W o j K ++ klift U o j (fun i => K (W.length + i)) := by
  refine klift_append (fun x hx => ?_) _ _ _
  by_cases hUn : U = []
  · subst hUn; simp [entry]
  · rw [hU hUn]; exact hW x hx

theorem klift_nil (o j : ℕ) (K : ℕ → ℕ) : klift [] o j K = [] := by simp [klift]

theorem Fr_klift {X : TrioSeq} (hX : Fr X) (o j : ℕ) (K : ℕ → ℕ) : Fr (klift X o j K) := by
  intro y hy
  simp only [klift, List.mem_map, List.mem_range] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  show 1 ≤ entry X 0 c
  have hmem : X.getD c (0, 0, 0) ∈ X := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; exact List.getElem_mem hc
  exact hX _ hmem

theorem Hd_klift {U : TrioSeq} (hU : Hd U) (o j : ℕ) (K : ℕ → ℕ) : Hd (klift U o j K) := by
  intro hne
  have hUne : U ≠ [] := by intro h; apply hne; subst h; exact klift_nil o j K
  have := hU hUne
  rw [entry0_klift]; exact this

/-! ## 根の下 -/

theorem Lk_idx0 (A : TrioSeq) (o j : ℕ) (K : ℕ → ℕ) : Lk A o j K 0 = lamK A o j K 0 := by
  refine le_antisymm (Lk_le Relation.ReflTransGen.refl) ?_
  obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K) 0
  have h0 : y = 0 := by have := rtg0_le hy; omega
  subst h0
  rw [hey]

theorem Lk_cons_root {S : TrioSeq} (hS : Fr S) (r z : ℕ) {o j : ℕ} {K : ℕ → ℕ} {c : ℕ}
    (hc : c < S.length) :
    Lk (((0, r, z) : ℕ × ℕ × ℕ) :: S) o j K (1 + c)
      = min (lamK (((0, r, z) : ℕ × ℕ × ℕ) :: S) o j K 0) (Lk S o j (fun i => K (1 + i)) c) := by
  set N : TrioSeq := ((0, r, z) : ℕ × ℕ × ℕ) :: S with hN
  have hlam : ∀ y, lamK N o j K (1 + y) = lamK S o j (fun i => K (1 + i)) y := by
    intro y
    refine lamK_congr ?_ ?_ rfl
    · rw [hN, show 1 + y = y + 1 from by omega, entry_cons]
    · rw [hN, show 1 + y = y + 1 from by omega, entry_cons]
  have h0 : Relation.ReflTransGen (nextrel0 N) 0 (1 + c) := by
    refine rtg0_of_window (by rw [hN]; simp; omega) (by omega) ?_
    intro l hl0 hl1
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have h00 : entry N 0 0 = 0 := by rw [hN]; exact based_cons r z S
    rw [h00, hN, entry_cons]
    exact hS _ (entry_pair_mem (by omega))
  refine le_antisymm ?_ ?_
  · refine le_min (Lk_le h0) ?_
    obtain ⟨y, hy, hey⟩ := Lk_mem (A := S) (o := o) (j := j) (K := fun i => K (1 + i)) c
    rw [← hey, ← hlam y]
    exact Lk_le (rtg0_cons_lift hy)
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := N) (o := o) (j := j) (K := K) (1 + c)
    rw [← hey]
    rcases Nat.eq_zero_or_pos y with rfl | hypos
    · exact min_le_left _ _
    · have h1 := rtg0_cons_unlift hypos hy c rfl
      have h2 := Lk_le (A := S) (o := o) (j := j) (K := fun i => K (1 + i)) h1
      rw [← hlam (y - 1), show 1 + (y - 1) = y from by omega] at h2
      exact le_trans (min_le_right _ _) h2

theorem klift_cons_root {S : TrioSeq} (hS : Fr S) (r z : ℕ) {o j j' : ℕ} {K K' : ℕ → ℕ}
    (hmin : ∀ c, c < S.length →
      min (lamK (((0, r, z) : ℕ × ℕ × ℕ) :: S) o j K 0) (Lk S o j (fun i => K (1 + i)) c)
        = Lk S o j' K' c) :
    klift (((0, r, z) : ℕ × ℕ × ℕ) :: S) o j K
      = ((0, r + lamK (((0, r, z) : ℕ × ℕ × ℕ) :: S) o j K 0, z) : ℕ × ℕ × ℕ) :: klift S o j' K' := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [klift_length] at hi
  rw [klift_getD hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [Lk_idx0]; rfl
  · obtain ⟨c, rfl⟩ : ∃ c, i = 1 + c := ⟨i - 1, by omega⟩
    have hc : c < S.length := by simp at hi; omega
    have e : ∀ t, entry (((0, r, z) : ℕ × ℕ × ℕ) :: S) t (1 + c) = entry S t c := by
      intro t; rw [show 1 + c = c + 1 by omega, entry_cons]
    rw [e 0, e 1, e 2, Lk_cons_root hS r z hc, hmin c hc]
    have eg : (((0, r + lamK (((0, r, z) : ℕ × ℕ × ℕ) :: S) o j K 0, z) : ℕ × ℕ × ℕ) ::
        klift S o j' K').getD (1 + c) (0, 0, 0) = (klift S o j' K').getD c (0, 0, 0) := by
      rw [show 1 + c = c + 1 by omega]; rfl
    rw [eg, klift_getD hc]

theorem lamK_cap (A : TrioSeq) (o j k : ℕ) (K : ℕ → ℕ) (y : ℕ) :
    min k (lamK A o j K y) = lamK A o (min k j) K y := by
  unfold lamK; split_ifs <;> omega

theorem Lk_cap (A : TrioSeq) (o j k : ℕ) (K : ℕ → ℕ) (c : ℕ) :
    min k (Lk A o j K c) = Lk A o (min k j) K c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := min k j) (K := K) c
    rw [← hey, ← lamK_cap]
    have := Lk_le (A := A) (o := o) (j := j) (K := K) hy
    omega
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K) c
    rw [← hey, lamK_cap]
    exact Lk_le hy

theorem klift_zero_j (X : TrioSeq) (o : ℕ) (K : ℕ → ℕ) : klift X o 0 K = X := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [klift_length] at hi
  have h0 : Lk X o 0 K i = 0 := by have := Lk_le_j (A := X) (o := o) (j := 0) (K := K) i; omega
  rw [klift_getD hi, h0, Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  exact entry_triple hi

/-! ## 節点の下 -/

theorem node_shift_eq (r z : ℕ) (V : TrioSeq) :
    ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V = shiftr01 1 0 (((0, r, z) : ℕ × ℕ × ℕ) :: V) := by
  simp [shiftr01]

/-- ★ 段 > o の節点（字・F）の下の子の並びは、同じ κ の持ち上げ（添字を 1 ずらす）。 -/
theorem klift_node_high {V : TrioSeq} (hV : Fr V) {r z o j : ℕ} {K : ℕ → ℕ} (hr : o < r) :
    klift (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) o j K
      = ((1, r + j, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (klift V o j (fun i => K (1 + i))) := by
  have hl : lamK (((0, r, z) : ℕ × ℕ × ℕ) :: V) o j K 0 = j := lamK_high (by show o < r; exact hr)
  rw [node_shift_eq, klift_shift0, klift_cons_root hV r z (j' := j) (K' := fun i => K (1 + i))
    (fun c _ => by rw [hl]; exact min_eq_right (Lk_le_j c)), hl]
  simp [shiftr01]

/-- ★ 段 < o の節点の下は動かない。 -/
theorem klift_node_low {V : TrioSeq} (hV : Fr V) {r z o j : ℕ} {K : ℕ → ℕ} (hr : r < o) :
    klift (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) o j K
      = ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V := by
  have hl : lamK (((0, r, z) : ℕ × ℕ × ℕ) :: V) o j K 0 = 0 := lamK_low (by show r < o; exact hr)
  rw [node_shift_eq, klift_shift0, klift_cons_root hV r z (j' := 0) (K' := K)
    (fun c _ => by
      rw [hl]
      have := Lk_le_j (A := V) (o := o) (j := 0) (K := K) c
      omega), hl, klift_zero_j, Nat.add_zero]
  try simp [shiftr01]

/-- ★ 段 = o・z = 0 の節点は κ(0) で上がり、子の並びは上限 min (K 0) j の κ の持ち上げ。 -/
theorem klift_node_mid {V : TrioSeq} (hV : Fr V) {o j : ℕ} {K : ℕ → ℕ} :
    klift (((1, o, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) o j K
      = ((1, o + min (K 0) j, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (klift V o (min (K 0) j) (fun i => K (1 + i))) := by
  have hl : lamK (((0, o, 0) : ℕ × ℕ × ℕ) :: V) o j K 0 = min (K 0) j := by
    unfold lamK; simp [entry]
  rw [node_shift_eq, klift_shift0, klift_cons_root hV o 0 (j' := min (K 0) j)
    (K' := fun i => K (1 + i)) (fun c _ => by rw [hl, Lk_cap, show min (min (K 0) j) j = min (K 0) j by omega]), hl]
  simp [shiftr01]

end KlE
end TRIO
