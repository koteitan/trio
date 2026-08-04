/-
Lcone.lean: 根の行 1 錐 `le1 X 0 ·` の展開輸送。

`Wset.LiftInner`（B2a のリフト同変性）の核。悪根 `j0` が引数ブロックの内部に
ある（`j0 ≥ 1`）とき、根 `0` の錐は展開で位置対応どおりに移る。

鍵は二つ:
* `le1_iff_chain_window`: 根が行 0 で狭義に最浅なら `le1 A 0 j` は「`j` の行 0
  祖先 `y ≠ 0` がすべて `entry A 1 0 < entry A 1 y` を満たす」に同値。
  `le1` の極小性条項が消えて、鎖の窓だけの条件になる。
* `Gtrans.gexp_chain_inversion`: `gexp` の行 0 祖先鎖の逆転。`j0` 以上の祖先は
  すべて鏡像で、同じコピー内（`M` 側で目標オフセットへ降りる鎖）か、より前の
  コピー（`M` 側で `lp = j0 + Lb` へ降りる鎖）にある。

後者の「より前のコピー」分は `le1 M j0 (j0 + Lb)` の窓が押さえる。
-/
import Wset

namespace TRIO

open Wset

/-! ## 最浅根の錐 -/

/-- If the root is strictly the shallowest column, it is a row-0 ancestor of
everything. -/
theorem rtg0_zero {A : TrioSeq}
    (hr : ∀ l, 0 < l → l < A.length → entry A 0 0 < entry A 0 l)
    {j : ℕ} (hj : j < A.length) :
    Relation.ReflTransGen (nextrel0 A) 0 j :=
  rtg0_of_window hj (Nat.zero_le j) (fun l hl0 hl1 => hr l hl0 (by omega))

/-- **The root cone is a pure window condition.**  With the root strictly the
shallowest column, `le1 A 0 j` says exactly that every row-0 ancestor of `j`
other than the root sits strictly above the root in row 1. -/
theorem le1_zero_iff {A : TrioSeq}
    (hr : ∀ l, 0 < l → l < A.length → entry A 0 0 < entry A 0 l)
    {j : ℕ} (hj : j < A.length) :
    le1 A 0 j ↔ ∀ y, Relation.ReflTransGen (nextrel0 A) y j → y ≠ 0 →
      entry A 1 0 < entry A 1 y := by
  rw [le1_iff_chain_window hj (rtg0_zero hr hj)]
  constructor
  · intro h y hyj hy0
    have hylt : y < A.length := by
      have := nextrel0_rtrancl_index_le hyj
      omega
    exact h y (rtg0_zero hr hylt) hyj hy0
  · intro h y _ hyj hy0
    exact h y hyj hy0

section Cone

variable {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}

theorem gexp_entry_low {y p : ℕ} (hlen : j0 + Lb + 1 = M.length) (hp : p < j0) :
    entry (gexp M j0 Lb d0 d1 n) y p = entry M y p := by
  unfold entry
  rw [gexp_getD_low hlen hp]

theorem gexp_entry0_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) :
    entry (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + q))
      = entry M 0 (j0 + q) + k * d0 := by
  show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).1 = _
  rw [gexp_getD_mir hlen hk hq]

open Classical in
theorem gexp_entry1_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) :
    entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + q))
      = entry M 1 (j0 + q) + (if le1 M j0 (j0 + q) then k * d1 else 0) := by
  show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).2.1 = _
  rw [gexp_getD_mir hlen hk hq]

/-- The expansion keeps the root strictly the shallowest column. -/
theorem gexp_root_shallow (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0)
    (hLb : 0 < Lb)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) :
    ∀ l, 0 < l → l < (gexp M j0 Lb d0 d1 n).length →
      entry (gexp M j0 Lb d0 d1 n) 0 0 < entry (gexp M j0 Lb d0 d1 n) 0 l := by
  intro l hl0 hl1
  rw [gexp_length hlen] at hl1
  rw [gexp_entry_low hlen hj0]
  rcases Nat.lt_or_ge l j0 with hlj | hlj
  · rw [gexp_entry_low hlen hlj]
    exact hr0 l hl0 (by omega)
  · obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hlj hl1
    rw [gexp_entry0_mir hlen hk hq]
    have := hr0 (j0 + q) (by omega) (by omega)
    omega

/-- The prefix of the expansion carries the same root cone. -/
theorem gexp_cone_low (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hn : 0 < n) {p : ℕ} (hp : p < j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 p ↔ le1 M 0 p := by
  have hnLb : 0 < n * Lb := Nat.mul_pos hn hLb
  have hpX : p < (gexp M j0 Lb d0 d1 n).length := by
    rw [gexp_length hlen]; omega
  have hpM : p < M.length := by omega
  constructor
  · exact le1_of_agree (M := gexp M j0 Lb d0 d1 n) (X := M) hpM hpX
      (fun x _ => (gexp_getD_low hlen (by omega)).symm)
  · exact le1_of_agree (M := M) (X := gexp M j0 Lb d0 d1 n) hpX hpM
      (fun x _ => gexp_getD_low hlen (by omega))

/-- **Root-cone transport.**  At a mirror position the root cone of the
expansion agrees with the root cone of the host at the source offset. -/
theorem gexp_cone_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0)
    (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M j0 (j0 + Lb)) :
    le1 (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + q) < (gexp M j0 Lb d0 d1 n).length := by
    rw [hXlen]; omega
  have hqlt : j0 + q < M.length := by omega
  have hrX := gexp_root_shallow (d0 := d0) (d1 := d1) (n := n) hlen hj0 hLb hr0
  have h10 : entry (gexp M j0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
    gexp_entry_low hlen hj0
  have hroot0 : entry (gexp M j0 Lb d0 d1 n) 0 j0 = entry M 0 j0 :=
    gexp_entry_root hlen hn hLb
  have hroot1 : entry (gexp M j0 Lb d0 d1 n) 1 j0 = entry M 1 j0 :=
    gexp_entry_root hlen hn hLb
  have hMj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
    rtg0_of_window (by omega) (by omega) (fun l hl0 hl1 => hup l hl0 (by omega))
  have hXj0p : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0
      (j0 + (k * Lb + q)) :=
    gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  rw [le1_zero_iff hrX hplt, le1_zero_iff hr0 hqlt, h10]
  constructor
  · -- the expansion's window forces the host's window
    intro hXw y hyq hy0
    have hyle : y ≤ j0 + q := nextrel0_rtrancl_index_le hyq
    have hj0val : entry M 1 0 < entry M 1 j0 := by
      have h := hXw j0 hXj0p (by omega)
      rwa [hroot1] at h
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · -- prefix ancestor: transport the chain into the expansion
      have hle0My : le0 M y (j0 + q) := ⟨by omega, hqlt, hyq⟩
      have hle0Mj : le0 M j0 (j0 + q) := ⟨by omega, hqlt, hMj0q⟩
      have hMyj0 := (le0_of_le0_le0 hle0My hle0Mj hyj).2.2
      have hXyj0 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y j0 :=
        rtg0_of_agree_last (M := M) (X := gexp M j0 Lb d0 d1 n)
          (by rw [hXlen]; omega)
          (fun x hx => gexp_getD_low hlen (by omega)) hroot0 hMyj0
      have h := hXw y (hXyj0.trans hXj0p) hy0
      rwa [gexp_entry_low hlen hyj] at h
    · -- mirror ancestor in the same copy
      obtain ⟨q', hq'e⟩ : ∃ q', y = j0 + q' := ⟨y - j0, by omega⟩
      subst hq'e
      have hq'lt : q' < Lb := by omega
      have hmir : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hyq q rfl hq
      have h := hXw (j0 + (k * Lb + q')) hmir (by omega)
      rw [gexp_entry1_mir hlen hk hq'lt] at h
      by_cases hg : le1 M j0 (j0 + q')
      · rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
        · simpa using hj0val
        · have := le1_entry1_lt hg (by omega)
          omega
      · rw [if_neg hg] at h
        omega
  · -- the host's window forces the expansion's window
    intro hMw y hyp hy0
    have hj0valM : entry M 1 0 < entry M 1 j0 := hMw j0 hMj0q (by omega)
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hle0X : le0 (gexp M j0 Lb d0 d1 n) y (j0 + (k * Lb + q)) :=
        ⟨by rw [hXlen]; omega, hplt, hyp⟩
      have hle0j : le0 (gexp M j0 Lb d0 d1 n) j0 (j0 + (k * Lb + q)) :=
        ⟨by rw [hXlen]; omega, hplt, hXj0p⟩
      have hXyj0 := (le0_of_le0_le0 hle0X hle0j hyj).2.2
      have hMyj0 : Relation.ReflTransGen (nextrel0 M) y j0 :=
        rtg0_of_agree_last (M := gexp M j0 Lb d0 d1 n) (X := M)
          (by omega) (fun x hx => (gexp_getD_low hlen (by omega)).symm)
          hroot0.symm hXyj0
      have h := hMw y (hMyj0.trans hMj0q) hy0
      rwa [gexp_entry_low hlen hyj]
    · obtain ⟨k', q', hk', hq', hye, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e y hyp hyj
      subst hye
      rw [gexp_entry1_mir hlen (by omega) hq']
      have hbase : entry M 1 0 < entry M 1 (j0 + q') := by
        rcases hcase with ⟨-, hM⟩ | ⟨-, hM⟩
        · exact hMw (j0 + q') hM (by omega)
        · rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
          · simpa using hj0valM
          · have hchain : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q') :=
              rtg0_of_window (by omega) (by omega)
                (fun l hl0 hl1 => hup l hl0 (by omega))
            have := le1_chain_window hlp.2.2 (j0 + q') hchain hM (by omega)
            omega
      split_ifs <;> omega

end Cone

end TRIO
