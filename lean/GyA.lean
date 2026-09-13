/-
GyA.lean: 階段リフト slift の汎用の部品（連結・シフト・根・入れ子の底に足した単位）。
-/
import GxY

namespace TRIO
namespace GyA

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN
open GxP
open GxR
open GxT
open GxV
open GxW
open GxY

/-! ## slift の部品 -/

theorem amin_shift0 {d : ℕ} (Z : TrioSeq) (j : ℕ) : amin (shiftr01 d 0 Z) j = amin Z j :=
  nat_eq_of_lt_iff fun v => by rw [← coneV_iff_amin, ← coneV_iff_amin]; exact coneV_shift0

theorem amin_append_left {A B : TrioSeq} {j : ℕ} (hj : j < A.length) :
    amin (A ++ B) j = amin A j :=
  nat_eq_of_lt_iff fun v => by
    rw [← coneV_iff_amin, ← coneV_iff_amin]; exact coneV_append_left hj

theorem amin_append_right {A B : TrioSeq} {q : ℕ} (hq : q < B.length)
    (hrs : ∀ x ∈ A, entry B 0 0 ≤ x.1) : amin (A ++ B) (A.length + q) = amin B q :=
  nat_eq_of_lt_iff fun v => by
    rw [← coneV_iff_amin, ← coneV_iff_amin]; exact coneV_append_right hq hrs

theorem slift_shift0 (d : ℕ) (Z : TrioSeq) (φ : ℕ → ℕ) :
    slift (shiftr01 d 0 Z) φ = shiftr01 d 0 (slift Z φ) := by
  refine list_ext_getD (by rw [slift_length, shiftr01_length, shiftr01_length, slift_length]) ?_
  intro i hi
  rw [slift_length, shiftr01_length] at hi
  rw [slift_getD (by rw [shiftr01_length]; exact hi),
    shiftr01_getD (by rw [slift_length]; exact hi), slift_getD hi,
    entry0_shiftr01 hi, entry1_shiftr01, entry2_shiftr01, amin_shift0]
  simp

theorem slift_append {A B : TrioSeq} (hrs : ∀ x ∈ A, entry B 0 0 ≤ x.1) (φ : ℕ → ℕ) :
    slift (A ++ B) φ = slift A φ ++ slift B φ := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length, List.length_append] at hi
  rw [slift_getD (by rw [List.length_append]; omega)]
  rcases Nat.lt_or_ge i A.length with hiA | hiA
  · have eg : (slift A φ ++ slift B φ).getD i (0, 0, 0) = (slift A φ).getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [slift_length]; exact hiA)]
    rw [eg, slift_getD hiA, Small.entry_append_left hiA, Small.entry_append_left hiA,
      Small.entry_append_left hiA, amin_append_left hiA]
  · obtain ⟨q, rfl⟩ : ∃ q, i = A.length + q := ⟨i - A.length, by omega⟩
    have hq : q < B.length := by omega
    rw [getD_app_right _ _ (by rw [slift_length]; omega), slift_length,
      show A.length + q - A.length = q from by omega, slift_getD hq,
      entry_append_right, entry_append_right, entry_append_right, amin_append_right hq hrs]

theorem slift_id (X : TrioSeq) : slift X (fun m => m) = X := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length] at hi
  rw [slift_getD hi, Nat.sub_self, Nat.add_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]
  exact entry_triple hi

theorem slift_nil (φ : ℕ → ℕ) : slift [] φ = [] := by simp [slift]

theorem Fr_slift {X : TrioSeq} (hX : Fr X) (φ : ℕ → ℕ) : Fr (slift X φ) := by
  intro y hy
  simp only [slift, List.mem_map, List.mem_range] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  show 1 ≤ entry X 0 j
  have hmem : X.getD j (0, 0, 0) ∈ X := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  exact hX _ hmem

theorem Hd_slift {U : TrioSeq} (hU : Hd U) (φ : ℕ → ℕ) : Hd (slift U φ) := by
  intro hne
  have hUne : U ≠ [] := by intro h; apply hne; subst h; exact slift_nil φ
  have := hU hUne
  rw [entry0_slift]; exact this

theorem slift_app {W U : TrioSeq} (hW : Fr W) (hU : Hd U) (φ : ℕ → ℕ) :
    slift (W ++ U) φ = slift W φ ++ slift U φ := by
  refine slift_append (fun x hx => ?_) _
  by_cases hUn : U = []
  · subst hUn; simp [entry]
  · rw [hU hUn]; exact hW x hx

/-! ## 根の持ち上げ -/

theorem amin_cons_root {S : TrioSeq} (hS : Fr S) (B z : ℕ) {j : ℕ} (hj : j < S.length) :
    amin (((0, B, z) : ℕ × ℕ × ℕ) :: S) (1 + j) = min B (amin S j) :=
  nat_eq_of_lt_iff fun v => by
    rw [← coneV_iff_amin, coneV_cons_iff (fun p hp => by have := hS p hp; omega) hj,
      coneV_iff_amin, lt_min_iff]

theorem slift_cons_root {S : TrioSeq} (hS : Fr S) (B z : ℕ) {φ : ℕ → ℕ} (hφ : Stair φ) :
    slift (((0, B, z) : ℕ × ℕ × ℕ) :: S) φ
      = ((0, φ B, z) : ℕ × ℕ × ℕ) :: slift S (fun m => m + (φ (min B m) - min B m)) := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length] at hi
  rw [slift_getD hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have e0 : entry (((0, B, z) : ℕ × ℕ × ℕ) :: S) 0 0 = 0 := rfl
    have e1 : entry (((0, B, z) : ℕ × ℕ × ℕ) :: S) 1 0 = B := rfl
    have e2 : entry (((0, B, z) : ℕ × ℕ × ℕ) :: S) 2 0 = z := rfl
    rw [amin_zero, e0, e1, e2, show B + (φ B - B) = φ B by have := hφ.ge B; omega]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    have hj : j < S.length := by simp at hi; omega
    have e : ∀ r, entry (((0, B, z) : ℕ × ℕ × ℕ) :: S) r (1 + j) = entry S r j := by
      intro r; rw [show 1 + j = j + 1 by omega, entry_cons]
    rw [e 0, e 1, e 2, amin_cons_root hS B z hj]
    have eg : (((0, φ B, z) : ℕ × ℕ × ℕ) ::
        slift S (fun m => m + (φ (min B m) - min B m))).getD (1 + j) (0, 0, 0)
        = (slift S (fun m => m + (φ (min B m) - min B m))).getD j (0, 0, 0) := by
      rw [show 1 + j = j + 1 by omega]; rfl
    rw [eg, slift_getD hj]
    simp

theorem slift_congr_amin {A : TrioSeq} {φ ψ : ℕ → ℕ}
    (h : ∀ k, k < A.length → φ (amin A k) = ψ (amin A k)) : slift A φ = slift A ψ := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length] at hi
  rw [slift_getD hi, slift_getD hi, h i hi]

/-- 節点 (1, r, z) :: V↑1 の階段リフト（子の並びは節点の値で切った階段）。 -/
theorem slift_node {V : TrioSeq} (hV : Fr V) (r z : ℕ) {φ : ℕ → ℕ} (hφ : Stair φ) :
    slift (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) φ
      = ((1, φ r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (slift V (fun m => m + (φ (min r m) - min r m))) := by
  have e1 : ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V
      = shiftr01 1 0 (((0, r, z) : ℕ × ℕ × ℕ) :: V) := by simp [shiftr01]
  rw [e1, slift_shift0, slift_cons_root hV r z hφ]
  simp [shiftr01]

/-! ## 入れ子の底に足した単位の持ち上げ -/

/-- 位置 P.length に行 0 が d の列を足したとき、P の中のその行 0 の祖先の行 1 がすべて v 以上。 -/
def BotGe (P : TrioSeq) (d v : ℕ) : Prop :=
  ∀ (c : ℕ × ℕ × ℕ) (y : ℕ), c.1 = d → y < P.length →
    Relation.ReflTransGen (nextrel0 (P ++ [c])) y P.length → v ≤ entry P 1 y

theorem BotGe_mono {P : TrioSeq} {d v w : ℕ} (h : BotGe P d v) (hwv : w ≤ v) : BotGe P d w :=
  fun c y hc hy hr => le_trans hwv (h c y hc hy hr)

theorem exists_last_small (d : ℕ) (P : TrioSeq) (h : ∃ x ∈ P, x.1 < d) :
    ∃ y, y < P.length ∧ entry P 0 y < d ∧ ∀ l, y < l → l < P.length → d ≤ entry P 0 l := by
  induction P using List.reverseRecOn with
  | nil => simp at h
  | append_singleton P x ih =>
      by_cases hx : x.1 < d
      · refine ⟨P.length, by simp, ?_, fun l hl1 hl2 => by simp at hl2; omega⟩
        rw [show P.length = P.length + 0 from rfl, entry_append_right]
        exact hx
      · have h' : ∃ x ∈ P, x.1 < d := by
          obtain ⟨x', hx', hx'd⟩ := h
          rcases List.mem_append.mp hx' with h1 | h1
          · exact ⟨x', h1, hx'd⟩
          · simp only [List.mem_singleton] at h1; subst h1; exact absurd hx'd hx
        obtain ⟨y, hy, hy0, hyl⟩ := ih h'
        refine ⟨y, by simp; omega, by rw [Small.entry_append_left hy]; exact hy0,
          fun l hl1 hl2 => ?_⟩
        rcases Nat.lt_or_ge l P.length with hlP | hlP
        · rw [Small.entry_append_left hlP]; exact hyl l hl1 hlP
        · have hl : l = P.length := by simp at hl2; omega
          subst hl
          rw [show P.length = P.length + 0 from rfl, entry_append_right]
          exact Nat.le_of_not_lt hx

theorem exists_anc {P : TrioSeq} (c : ℕ × ℕ × ℕ) (h : ∃ x ∈ P, x.1 < c.1) :
    ∃ y, y < P.length ∧ Relation.ReflTransGen (nextrel0 (P ++ [c])) y P.length := by
  obtain ⟨y, hy, hy0, hyl⟩ := exists_last_small c.1 P h
  refine ⟨y, hy, rtg0_of_window (by simp) (by omega) (fun l hl1 hl2 => ?_)⟩
  rw [Small.entry_append_left hy]
  rcases Nat.lt_or_ge l P.length with hlP | hlP
  · rw [Small.entry_append_left hlP]; have := hyl l hl1 hlP; omega
  · have hl : l = P.length := by omega
    subst hl
    rw [show P.length = P.length + 0 from rfl, entry_append_right]
    exact hy0

theorem slift_snoc_dropLast (P : TrioSeq) (c : ℕ × ℕ × ℕ) (φ : ℕ → ℕ) :
    (slift (P ++ [c]) φ).dropLast = slift P φ := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  rw [List.getElem_dropLast]
  rw [slift_length] at h2
  have h3 : i < (P ++ [c]).length := by simp; omega
  rw [← entry_triple (by rw [slift_length]; exact h3), ← entry_triple (by rw [slift_length]; exact h2),
    entry0_slift, entry2_slift, entry0_slift, entry2_slift,
    entry1_slift h3, entry1_slift h2,
    Small.entry_append_left h2, Small.entry_append_left h2, Small.entry_append_left h2,
    amin_append_left h2]

theorem amin_le_root {S : TrioSeq} (hS : Fr S) (B z k : ℕ)
    (hk : k < (((0, B, z) : ℕ × ℕ × ℕ) :: S).length) :
    amin (((0, B, z) : ℕ × ℕ × ℕ) :: S) k ≤ B := by
  have hr : Relation.ReflTransGen (nextrel0 (((0, B, z) : ℕ × ℕ × ℕ) :: S)) 0 k := by
    refine rtg0_zero (fun l hl0 hl => ?_) hk
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [entry_cons]
    have hl' : l' < S.length := by simp at hl; omega
    have := getD_row0_ge hS hl'
    show 0 < entry S 0 l'
    omega
  exact amin_le hr

/-- ★ 入れ子の底に足した単位の持ち上げ（単位の根の行 1 は底の祖先の行 1 以下）。 -/
theorem slift_bottom_unit {P S : TrioSeq} (hS : Fr S) {d B z : ℕ}
    (hbot : BotGe P d B) {φ : ℕ → ℕ} (hφ : Stair φ) :
    slift (P ++ shiftr01 d 0 (((0, B, z) : ℕ × ℕ × ℕ) :: S)) φ
      = slift P φ ++ shiftr01 d 0 (slift (((0, B, z) : ℕ × ℕ × ℕ) :: S) φ) := by
  by_cases hsm : ∃ x ∈ P, x.1 < d
  · obtain ⟨y0, hy0, hr0⟩ := exists_anc ((d, B, z) : ℕ × ℕ × ℕ) hsm
    have hM2 : 2 ≤ (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length := by
      obtain ⟨x, hx, -⟩ := hsm
      have := List.length_pos_of_mem hx
      simp; omega
    have hne : ∃ y, y < (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length - 1 ∧
        Relation.ReflTransGen (nextrel0 (P ++ [((d, B, z) : ℕ × ℕ × ℕ)])) y
          ((P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length - 1) :=
      ⟨y0, by simp; omega, by simpa using hr0⟩
    have elast : entry (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]) 0
        ((P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length - 1) = d := by
      rw [show (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length - 1 = P.length + 0 by simp,
        entry_append_right]
      rfl
    have hcap : B ≤ capV (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]) := by
      have hSne : {m | ∃ y, y < (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length - 1 ∧
          Relation.ReflTransGen (nextrel0 (P ++ [((d, B, z) : ℕ × ℕ × ℕ)])) y
            ((P ++ [((d, B, z) : ℕ × ℕ × ℕ)]).length - 1) ∧
          entry (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]) 1 y = m}.Nonempty := by
        obtain ⟨y, hy, hr⟩ := hne
        exact ⟨_, y, hy, hr, rfl⟩
      obtain ⟨y, hy, hr, hey⟩ := Nat.sInf_mem hSne
      unfold capV
      rw [← hey]
      have hyP : y < P.length := by simp at hy; omega
      rw [Small.entry_append_left hyP]
      exact hbot _ y rfl hyP (by simpa using hr)
    have eg : P ++ shiftr01 d 0 (((0, B, z) : ℕ × ℕ × ℕ) :: S)
        = graft (P ++ [((d, B, z) : ℕ × ℕ × ℕ)]) (((0, B, z) : ℕ × ℕ × ℕ) :: S) := by
      rw [graft_eq_shift, List.dropLast_concat, elast]
    rw [eg, slift_graft rfl (by simp) hM2 hne hφ, graft_eq_shift, slift_snoc_dropLast,
      entry0_slift, slift_length, elast]
    congr 2
    refine slift_congr_amin (fun k hk => ?_)
    have h1 := amin_le_root hS B z k hk
    have h2 := hφ.ge (amin (((0, B, z) : ℕ × ℕ × ℕ) :: S) k)
    rw [min_eq_right (le_trans h1 hcap)]
    omega
  · have hrs : ∀ x ∈ P, entry (shiftr01 d 0 (((0, B, z) : ℕ × ℕ × ℕ) :: S)) 0 0 ≤ x.1 := by
      intro x hx
      rw [entry0_shiftr01 (by simp)]
      show 0 + d ≤ x.1
      have : ¬ x.1 < d := fun h => hsm ⟨x, hx, h⟩
      omega
    rw [slift_append hrs, slift_shift0]

/-- ★ 入れ子の底に足した節点と子の並びの持ち上げ（階段の形のまま）。 -/
theorem slift_bottom_node {P L : TrioSeq} (hL : Fr L) {d r z : ℕ} (hd : 1 ≤ d)
    (hbot : BotGe P d r) {φ : ℕ → ℕ} (hφ : Stair φ) :
    slift (P ++ shiftr01 (d - 1) 0 (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) φ
      = slift P φ ++ shiftr01 (d - 1) 0 (((1, φ r, z) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (slift L (fun m => m + (φ (min r m) - min r m)))) := by
  have e0 : ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L
      = shiftr01 1 0 (((0, r, z) : ℕ × ℕ × ℕ) :: L) := by simp [shiftr01]
  have e1 : shiftr01 (d - 1) 0 (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
      = shiftr01 d 0 (((0, r, z) : ℕ × ℕ × ℕ) :: L) := by
    rw [e0, shiftr01_add0, show 1 + (d - 1) = d by omega]
  rw [← slift_node hL r z hφ, e1, e0, slift_shift0, shiftr01_add0, show 1 + (d - 1) = d by omega]
  exact slift_bottom_unit hL hbot hφ

end GyA
end TRIO
