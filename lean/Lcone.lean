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
theorem gexp_cone_low (hlen : j0 + Lb + 1 = M.length) {p : ℕ} (hp : p < j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 p ↔ le1 M 0 p := by
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

/-! ## 平坦コピー（`d0 = d1 = 0`）の錐輸送

`srow = 0` の展開ではコピーがそのまま複製され、コピーの根はどれも宿主の根と
同じ深さに並ぶ。したがって `j0` は他コピーの行 0 祖先にはならず、鎖は
「コピー `k` の内部 → その根 → 前置」としか降りない。`Gtrans` の鎖逆転は
`hd0e`（根が `d0` だけ深くなる）を使うのでここでは使えず、平坦版を別に立てる。 -/

section ConeFlat

variable {M : TrioSeq} {j0 Lb n : ℕ}

theorem gexp_flat_getD {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) :
    (gexp M j0 Lb 0 0 n).getD (j0 + (k * Lb + q)) (0, 0, 0)
      = M.getD (j0 + q) (0, 0, 0) := by
  classical
  rw [gexp_getD_mir hlen hk hq]
  simp only [Nat.mul_zero, Nat.add_zero, ite_self]
  rw [getD_eq_entries]

theorem gexp_flat_entry {y k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) :
    entry (gexp M j0 Lb 0 0 n) y (j0 + (k * Lb + q)) = entry M y (j0 + q) := by
  unfold entry
  rw [gexp_flat_getD hlen hk hq]

theorem gexp_flat_root_entry {y k : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hLb : 0 < Lb) :
    entry (gexp M j0 Lb 0 0 n) y (j0 + k * Lb) = entry M y j0 := by
  have h := gexp_flat_entry (M := M) (n := n) (y := y) (k := k) (q := 0)
    hlen hk hLb
  simpa using h

/-- Nothing in the copies region is shallower than the host root. -/
theorem gexp_flat_ge (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    ∀ l, j0 ≤ l → l < j0 + n * Lb →
      entry M 0 j0 ≤ entry (gexp M j0 Lb 0 0 n) 0 l := by
  intro l hl0 hl1
  obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hl0 hl1
  rw [gexp_flat_entry hlen hk hq]
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp
  · exact le_of_lt (hup (j0 + q) (by omega) (by omega))

/-- The chain from a copy root to a copy-interior position. -/
theorem gexp_flat_rtg0_root {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb) (hn : 0 < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) (j0 + k * Lb)
      (j0 + (k * Lb + q)) := by
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  refine rtg0_of_window (by rw [gexp_length hlen]; omega) (by omega) ?_
  intro l hl0 hl1
  obtain ⟨q', hq'0, hq'1, rfl⟩ : ∃ q', 0 < q' ∧ q' ≤ q ∧ l = j0 + (k * Lb + q') :=
    ⟨l - j0 - k * Lb, by omega, by omega, by omega⟩
  rw [gexp_flat_root_entry hlen hk hLb, gexp_flat_entry hlen hk (by omega)]
  exact hup (j0 + q') (by omega) (by omega)

/-- Below `j0` the expansion and the host share their row-0 chains. -/
theorem gexp_flat_rtg0_low {a b : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hn : 0 < n) (hb : b < j0) :
    Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) a b
      ↔ Relation.ReflTransGen (nextrel0 M) a b := by
  have hnLb : 0 < n * Lb := Nat.mul_pos hn hLb
  constructor
  · exact rtg0_of_agree_last (M := gexp M j0 Lb 0 0 n) (X := M) (by omega)
      (fun x hx => (gexp_getD_low hlen (by omega)).symm)
      (by rw [gexp_getD_low hlen hb])
  · exact rtg0_of_agree_last (M := M) (X := gexp M j0 Lb 0 0 n)
      (by rw [gexp_length hlen]; omega)
      (fun x hx => gexp_getD_low hlen (by omega))
      (by rw [gexp_getD_low hlen hb])

/-- A copy root has exactly the host root's row-0 parents. -/
theorem nextrel0_flat_root {k y : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hy : y < j0)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    nextrel0 (gexp M j0 Lb 0 0 n) y (j0 + k * Lb) ↔ nextrel0 M y j0 := by
  have hnLb : 0 < n * Lb := by
    have : 0 < n := by omega
    exact Nat.mul_pos this hLb
  have hbnd : k * Lb < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hey : entry (gexp M j0 Lb 0 0 n) 0 y = entry M 0 y :=
    gexp_entry_low hlen hy
  have her : entry (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb) = entry M 0 j0 :=
    gexp_flat_root_entry hlen hk hLb
  constructor
  · rintro ⟨-, -, -, h4, h5⟩
    refine ⟨by omega, by omega, hy, ?_, ?_⟩
    · rw [← hey, ← her]; exact h4
    · intro l hl
      have := h5 l ⟨hl.1, by omega⟩
      rwa [her, gexp_entry_low hlen (by omega)] at this
  · rintro ⟨-, -, -, h4, h5⟩
    refine ⟨by rw [gexp_length hlen]; omega, by rw [gexp_length hlen]; omega,
      by omega, ?_, ?_⟩
    · rw [hey, her]; exact h4
    · intro l hl
      rw [her]
      rcases Nat.lt_or_ge l j0 with hlj | hlj
      · rw [gexp_entry_low hlen hlj]
        exact h5 l ⟨hl.1, hlj⟩
      · exact gexp_flat_ge hlen hLb hup l hlj (by omega)

/-- **Flat chain inversion**: every row-0 ancestor at or above `j0` of a
copy-`k` mirror is a copy-`k` mirror over a host chain. -/
theorem gexp_flat_chain_inversion {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    ∀ y, Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) y
        (j0 + (k * Lb + q)) → j0 ≤ y →
      ∃ q', q' < Lb ∧ y = j0 + (k * Lb + q') ∧
        Relation.ReflTransGen (nextrel0 M) (j0 + q') (j0 + q) := by
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  intro y hy
  induction hy using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact ⟨q, hq, rfl, .refl⟩
  | @head x' y' hxy hyt ih =>
      intro hx0
      have hxy' : x' < y' := nextrel0_index_less hxy
      obtain ⟨q', hq', rfl, hM⟩ := ih (by omega)
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · exfalso
        have hlt : entry (gexp M j0 Lb 0 0 n) 0 x'
            < entry (gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + 0)) := hxy.2.2.2.1
        rw [gexp_flat_entry hlen hk hLb] at hlt
        have hge := gexp_flat_ge (n := n) hlen hLb hup x' hx0 (by omega)
        simp only [Nat.add_zero] at hlt
        omega
      · have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q') :=
          rtg0_of_window (by omega) (by omega)
            (fun l hl0 hl1 => hup l hl0 (by omega))
        rcases hrtg.cases_tail with heq | ⟨pa, hpa1, hpa2⟩
        · exact absurd heq (by omega)
        · have hpa0 : j0 ≤ pa := nextrel0_rtrancl_index_le hpa1
          have hpaq : pa < j0 + q' := nextrel0_index_less hpa2
          obtain ⟨qa, rfl⟩ : ∃ qa, pa = j0 + qa := ⟨pa - j0, by omega⟩
          have hstep := gexp_nextrel0_mir (n := n) (d0 := 0) (d1 := 0) (k := k)
            hlen hk hq' hpa2
          have hxe : x' = j0 + (k * Lb + qa) := nextrel0_src_unique hxy hstep
          exact ⟨qa, by omega, hxe, hM.head hpa2⟩

/-- **Root-cone transport, flat case.** -/
theorem gexp_cone_mir_flat {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hj0 : 0 < j0) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) :
    le1 (gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M j0 Lb 0 0 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + q) < (gexp M j0 Lb 0 0 n).length := by
    rw [hXlen]; omega
  have hqlt : j0 + q < M.length := by omega
  have hrX := gexp_root_shallow (d0 := 0) (d1 := 0) (n := n) hlen hj0 hLb hr0
  have h10 : entry (gexp M j0 Lb 0 0 n) 1 0 = entry M 1 0 :=
    gexp_entry_low hlen hj0
  have hMj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
    rtg0_of_window (by omega) (by omega) (fun l hl0 hl1 => hup l hl0 (by omega))
  have hXrp : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) (j0 + k * Lb)
      (j0 + (k * Lb + q)) := gexp_flat_rtg0_root hlen hLb hk hq hn hup
  -- the copy root's prefix ancestors are the host root's
  have hlowX : ∀ y, y < j0 →
      (Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) y (j0 + k * Lb)
        ↔ Relation.ReflTransGen (nextrel0 M) y j0) := by
    intro y hy
    constructor
    · intro h
      rcases h.cases_tail with heq | ⟨w, hw1, hw2⟩
      · exact absurd heq (by omega)
      · have hwj : w < j0 := by
          by_contra hcon
          have hlt : entry (gexp M j0 Lb 0 0 n) 0 w
              < entry (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb) := hw2.2.2.2.1
          rw [gexp_flat_root_entry hlen hk hLb] at hlt
          have hge := gexp_flat_ge (n := n) hlen hLb hup w (by omega)
            (by have := nextrel0_index_less hw2; omega)
          omega
        exact ((gexp_flat_rtg0_low hlen hLb hn hwj).1 hw1).tail
          ((nextrel0_flat_root hlen hLb hk hwj hup).1 hw2)
    · intro h
      rcases h.cases_tail with heq | ⟨w, hw1, hw2⟩
      · exact absurd heq (by omega)
      · have hwj : w < j0 := nextrel0_index_less hw2
        exact ((gexp_flat_rtg0_low hlen hLb hn hwj).2 hw1).tail
          ((nextrel0_flat_root hlen hLb hk hwj hup).2 hw2)
  rw [le1_zero_iff hrX hplt, le1_zero_iff hr0 hqlt, h10]
  constructor
  · intro hXw y hyq hy0
    have hyle : y ≤ j0 + q := nextrel0_rtrancl_index_le hyq
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hle0My : le0 M y (j0 + q) := ⟨by omega, hqlt, hyq⟩
      have hle0Mj : le0 M j0 (j0 + q) := ⟨by omega, hqlt, hMj0q⟩
      have hMyj0 := (le0_of_le0_le0 hle0My hle0Mj hyj).2.2
      have h := hXw y (((hlowX y hyj).2 hMyj0).trans hXrp) hy0
      rwa [gexp_entry_low hlen hyj] at h
    · obtain ⟨q', hq'e⟩ : ∃ q', y = j0 + q' := ⟨y - j0, by omega⟩
      subst hq'e
      have hq'lt : q' < Lb := by omega
      have hmir : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hyq q rfl hq
      have h := hXw (j0 + (k * Lb + q')) hmir (by omega)
      rwa [gexp_flat_entry hlen hk hq'lt] at h
  · intro hMw y hyp hy0
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hle0X : le0 (gexp M j0 Lb 0 0 n) y (j0 + (k * Lb + q)) :=
        ⟨by rw [hXlen]; omega, hplt, hyp⟩
      have hle0r : le0 (gexp M j0 Lb 0 0 n) (j0 + k * Lb) (j0 + (k * Lb + q)) :=
        ⟨by rw [hXlen]; omega, hplt, hXrp⟩
      have hXyr := (le0_of_le0_le0 hle0X hle0r (by omega)).2.2
      have h := hMw y (((hlowX y hyj).1 hXyr).trans hMj0q) hy0
      rwa [gexp_entry_low hlen hyj]
    · obtain ⟨q', hq', hye, hM⟩ :=
        gexp_flat_chain_inversion hlen hLb hk hq hup y hyp hyj
      subst hye
      rw [gexp_flat_entry hlen hk hq']
      exact hMw (j0 + q') hM (by omega)

theorem gexp_entry2_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) (d0' d1' : ℕ) :
    entry (gexp M j0 Lb d0' d1' n) 2 (j0 + (k * Lb + q)) = entry M 2 (j0 + q) := by
  show ((gexp M j0 Lb d0' d1' n).getD (j0 + (k * Lb + q)) (0, 0, 0)).2.2 = _
  rw [gexp_getD_mir hlen hk hq]

end ConeFlat

/-! ## `Wset.LiftInner` の組み立て -/

theorem rtg0_entry0_lt {A : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 A) a b) (hne : a ≠ b) :
    entry A 0 a < entry A 0 b := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail y w hay hyw ih =>
      rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hay) with heq | hlt
      · rw [heq]; exact hyw.2.2.2.1
      · exact lt_trans (ih (by omega)) hyw.2.2.2.1

theorem window_of_rtg0 {A : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 A) a b) (hb : b < A.length) :
    ∀ l, a < l → l ≤ b → entry A 0 a < entry A 0 l := fun l hl0 hl1 =>
  rtg0_entry0_lt (le0_interval_desc h hb l (by omega) hl1) (by omega)

/-- Row-1 ancestors of a common target are linearly ordered. -/
theorem le1_of_le1_le1 {X : TrioSeq} {a k b : ℕ}
    (ha : le1 X a b) (hk : le1 X k b) (hak : a < k) : le1 X a k := by
  obtain ⟨-, -, ha⟩ := ha
  obtain ⟨hkl, -, hk⟩ := hk
  have key : ∀ {c : ℕ}, Relation.ReflTransGen (nextrel1 X) k c →
      Relation.ReflTransGen (nextrel1 X) a c →
      Relation.ReflTransGen (nextrel1 X) a k := by
    intro c hkc
    induction hkc with
    | refl => intro h; exact h
    | @tail y w hky hyw ih =>
        intro hac
        cases hac with
        | refl =>
            have h1 : k ≤ y := rtg1_le hky
            have h2 : y < a := hyw.2.2.1
            exact absurd h1 (by omega)
        | @tail y' _ hay' hy'w =>
            have hyy : y' = y := nextrel1_uniq_src hy'w hyw
            subst hyy
            exact ih hay'
  exact ⟨by have := rtg1_le (key hk ha); omega, hkl, key hk ha⟩

open Classical in
/-- The expansion as a `gexp`, for an arbitrary bad root. -/
theorem oper_eq_gexp_gen {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    M⟦n⟧ = gexp M (parent M (srow M (M.length - 1)) (M.length - 1))
      (M.length - 1 - parent M (srow M (M.length - 1)) (M.length - 1))
      (if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1)
        - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1)) else 0)
      (if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1)
        - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1)) else 0) n := by
  rw [oper_gcopies n hL hz hp]
  unfold gexp
  rfl


open Classical in
/-- **`LiftInner` holds.**  When the bad root lies inside the argument block the
guarded row-1 lift commutes with the expansion: the root cone transports, and
everything else about the expansion (`srow`, the parent, `d0`, `d1`) is
invariant under the lift. -/
theorem liftInner_holds : Wset.LiftInner := by
  classical
  intro v z t n R hR hRne hp
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = srow R (R.length - 1) := by
    rw [hMlen, hMdef, srow_cons_last hRne]
  set q0 := parent R (srow R (R.length - 1)) (R.length - 1) with hq0def
  have hnrR : nextR R (srow R (R.length - 1)) q0 (R.length - 1) := parent_nextR hp
  have hq0lt : q0 < R.length - 1 := nextR_index_lt hnrR
  have hnrM : nextR M (srow R (R.length - 1)) (q0 + 1) R.length :=
    (nextR_cons_last hRne _ q0).mpr hnrR
  have hpM : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen]
    exact ⟨q0 + 1, hnrM, nextR_cons_uniq hR hRne hp⟩
  have hparM : parent M (srow M (M.length - 1)) (M.length - 1) = q0 + 1 := by
    have h := parent_nextR hpM
    rw [hsrM, hMlen] at h ⊢
    exact nextR_cons_uniq hR hRne hp _ h
  set j0 := q0 + 1 with hj0def
  set Lb := R.length - j0 with hLbdef
  have hj0pos : 0 < j0 := by omega
  have hLbpos : 0 < Lb := by omega
  have hlenM : j0 + Lb + 1 = M.length := by omega
  have hj0x : j0 + Lb = R.length := by omega
  have hLbe : M.length - 1 - j0 = Lb := by omega
  -- the lifted block
  set N : TrioSeq := Lift1 M t with hNdef
  have hNlen : N.length = M.length := by rw [hNdef]; exact Lift1_length M t
  have hNe0 : ∀ y, entry N 0 y = entry M 0 y := fun y => by
    rw [hNdef]; exact entry0_Lift1 M t y
  have hNe2 : ∀ y, entry N 2 y = entry M 2 y := fun y => by
    rw [hNdef]; exact entry2_Lift1 M t y
  have hNe1 : ∀ y, y < M.length →
      entry N 1 y = entry M 1 y + (if le1 M 0 y then t else 0) := by
    intro y hy; rw [hNdef, entry1_Lift1 hy]
  have hNlen1 : N.length - 1 = M.length - 1 := by rw [hNlen]
  have hLN : N.length - 1 ≠ 0 := by rw [hNlen1]; exact hL
  have hzN : ¬ (entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0 ∧
      entry N 2 (N.length - 1) = 0) := by
    rintro ⟨h1, -, -⟩
    rw [hNlen1, hNe0, hMlen, hE 0] at h1
    omega
  have hsrN : srow N (N.length - 1) = srow M (M.length - 1) := by
    rw [hNlen1, hNdef]
    exact srow_Lift1 (by rw [hMlen]; omega)
  have hpN : hasParent N (srow N (N.length - 1)) (N.length - 1) := by
    rw [hsrN, hNlen1, hNdef]
    exact hasParent_Lift1.mpr hpM
  have hparN : parent N (srow N (N.length - 1)) (N.length - 1) = j0 := by
    rw [hsrN, hNlen1, hNdef, parent_Lift1]
    exact hparM
  have hlenN : j0 + Lb + 1 = N.length := by rw [hNlen]; exact hlenM
  -- the deltas
  set D0 : ℕ := (if 0 < srow M (M.length - 1)
    then entry M 0 (M.length - 1) - entry M 0 j0 else 0) with hD0
  set D1 : ℕ := (if 1 < srow M (M.length - 1)
    then entry M 1 (M.length - 1) - entry M 1 j0 else 0) with hD1
  -- the root is strictly the shallowest column
  have hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l := by
    intro l hl0 hl1
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have h0 : entry M 0 0 = 0 := by rw [hMdef]; simp [entry, hp0]
    rw [h0, hMdef, entry_cons]
    exact hR _ (entry_pair_mem (B := R) (by omega))
  -- the block window
  have hrtgx : Relation.ReflTransGen (nextrel0 M) j0 (M.length - 1) := by
    have hnr := parent_nextR hpM
    rw [hparM] at hnr
    unfold nextR at hnr
    by_cases h0 : srow M (M.length - 1) = 0
    · rw [if_pos h0] at hnr
      exact Relation.ReflTransGen.single hnr
    · by_cases h1 : srow M (M.length - 1) = 1
      · rw [if_neg h0, if_pos h1] at hnr
        exact hnr.2.2.2.2.1.2.2
      · rw [if_neg h0, if_neg h1] at hnr
        exact rtg1_rtg0 hnr.2.2.2.2.1.2.2
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l := by
    intro l hl0 hl1
    exact window_of_rtg0 hrtgx (by omega) l hl0 (by omega)
  -- `d1` is invariant under the lift
  have hD1N : (if 1 < srow N (N.length - 1)
      then entry N 1 (N.length - 1) - entry N 1 j0 else 0) = D1 := by
    rw [hsrN, hNlen1, hD1]
    by_cases h2 : 1 < srow M (M.length - 1)
    · rw [if_pos h2, if_pos h2]
      have hnr := parent_nextR hpM
      rw [hparM] at hnr
      unfold nextR at hnr
      rw [if_neg (by omega), if_neg (by omega)] at hnr
      have hle1jx : le1 M j0 (M.length - 1) := hnr.2.2.2.2.1
      have hiff : le1 M 0 (M.length - 1) ↔ le1 M 0 j0 :=
        ⟨fun h => le1_of_le1_le1 h hle1jx hj0pos, fun h => le1_trans h hle1jx⟩
      have hlt := le1_entry1_lt hle1jx (by omega)
      rw [hNe1 _ (by omega), hNe1 _ (by omega)]
      by_cases hc : le1 M 0 j0
      · rw [if_pos hc, if_pos (hiff.mpr hc)]; omega
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h))]; omega
    · rw [if_neg h2, if_neg h2]
  have hD0N : (if 0 < srow N (N.length - 1)
      then entry N 0 (N.length - 1) - entry N 0 j0 else 0) = D0 := by
    rw [hsrN, hNlen1, hD0]
    by_cases h0 : 0 < srow M (M.length - 1)
    · rw [if_pos h0, if_pos h0, hNe0, hNe0]
    · rw [if_neg h0, if_neg h0]
  -- both expansions as guarded copies
  have hMe : M⟦n⟧ = gexp M j0 Lb D0 D1 n := by
    have h := oper_eq_gexp_gen (M := M) n hL hz hpM
    rw [hparM, hLbe] at h
    rw [h, hD0, hD1]
  have hNe : N⟦n⟧ = gexp N j0 Lb D0 D1 n := by
    have h := oper_eq_gexp_gen (M := N) n hLN hzN hpN
    rw [hparN, show N.length - 1 - j0 = Lb from by rw [hNlen1]; omega] at h
    rw [h, hD0N, hD1N]
  -- the root cone transports
  have htrans : ∀ k q, k < n → q < Lb →
      (le1 (gexp M j0 Lb D0 D1 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q)) := by
    intro k q hk hq
    by_cases h0 : 0 < srow M (M.length - 1)
    · have hlt0 : entry M 0 j0 < entry M 0 (M.length - 1) :=
        hup (M.length - 1) (by omega) (by omega)
      have hd0pos : 0 < D0 := by rw [hD0, if_pos h0]; omega
      have hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + D0 := by
        rw [hD0, if_pos h0, show j0 + Lb = M.length - 1 from by omega]
        omega
      have hlp : le1 M j0 (j0 + Lb) := by
        rw [show j0 + Lb = M.length - 1 from by omega]
        have hnr := parent_nextR hpM
        rw [hparM] at hnr
        unfold nextR at hnr
        by_cases h1 : srow M (M.length - 1) = 1
        · rw [if_neg (by omega), if_pos h1] at hnr
          exact ⟨hnr.1, hnr.2.1, Relation.ReflTransGen.single hnr⟩
        · rw [if_neg (by omega), if_neg h1] at hnr
          exact hnr.2.2.2.2.1
      exact gexp_cone_mir hlenM hj0pos hLbpos hk hq hup hd0pos hd0e hr0 hlp
    · have hD0z : D0 = 0 := by rw [hD0, if_neg h0]
      have hD1z : D1 = 0 := by rw [hD1, if_neg (by omega)]
      rw [hD0z, hD1z]
      exact gexp_cone_mir_flat hlenM hj0pos hLbpos hk hq hup hr0
  -- elementwise comparison
  rw [hNe, hMe]
  have hXlenM : (gexp M j0 Lb D0 D1 n).length = j0 + n * Lb := gexp_length hlenM
  have hXlenN : (gexp N j0 Lb D0 D1 n).length = j0 + n * Lb := gexp_length hlenN
  refine list_ext_getD (by rw [hXlenN, Lift1_length, hXlenM]) ?_
  intro i hi
  rw [hXlenN] at hi
  rw [Lift1_getD (by rw [hXlenM]; exact hi)]
  rcases Nat.lt_or_ge i j0 with hij | hij
  · rw [gexp_getD_low hlenN hij, hNdef, Lift1_getD (by omega),
      gexp_entry_low hlenM hij, gexp_entry_low hlenM hij,
      gexp_entry_low hlenM hij]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    dsimp only
    rw [if_congr (gexp_cone_low hlenM hij) rfl rfl]
  · obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLbpos hij hi
    rw [gexp_getD_mir hlenN hk hq, gexp_entry0_mir hlenM hk hq,
      gexp_entry1_mir hlenM hk hq, gexp_entry2_mir hlenM hk hq,
      hNe0, hNe2, hNe1 _ (by omega)]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    dsimp only
    rw [if_congr (le1_Lift1 (X := M) (d := t) (a := j0) (b := j0 + q)) rfl rfl,
      if_congr (htrans k q hk hq) rfl rfl]
    omega


/-- **Everything now rests on `GraftAll` alone.** -/
theorem Wstar2_closed_of_graftAll (hga : Wset.GraftAll) :
    ∀ (u0 : ℕ) (R : TrioSeq), Wset.Aop Wset.W u0 Wset.Wstar2 R → R ∈ Wset.Wstar2 :=
  Wset.Wstar2_closed liftInner_holds (Wset.liftTower1_of_graftAll hga)
    (Wset.liftTowerExp2_of_graftAll hga)

end TRIO
