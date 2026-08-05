/-
Aexp.lean: 展開による `amin` の転送 (A2)。

`Cgraft.lean` の階段リフト `slift A φ` は列 `j` を `φ (amin A j) - amin A j`
だけ持ち上げる。展開との可換性 (G2)

    slift (A⟦n⟧) φ = (slift A φ)⟦n⟧

は、分岐データ（`srow` / 親 / `le1` ガード / `d0` / `d1`）がすべて `slift` で
保存されること（Cgraft）に加えて、**コピー列が元の列と同じ `amin` をもつ**

    (A1)  amin (M⟦n⟧) i                 = amin M i        (i < j0)
    (A2)  amin (M⟦n⟧) (j0 + (k*Lb + q)) = amin M (j0 + q)

に還元される。(A1) は `Cgraft.amin_oper_prefix`。本ファイルは (A2)。

(A2) は `Lcone` の錐輸送 `gexp_cone_mir` / `gexp_cone_mir_flat` の閾値版:
あちらは「宿主の根 `0` の錐」（閾値 `entry M 1 0`）を運ぶが、`amin` は
**すべての閾値 `v` について同時に**錐が対応することと同値
（`coneV_iff_amin` + `nat_eq_of_lt_iff`）。したがって根 `0` を経由せずに済み、
`hj0 : 0 < j0` も `hr0`（根が最浅）も不要になる。

展開の 2 相はそのまま（tools/probe_a2_branch.py）:

* `i1 ≥ 1`（`d0 > 0`）: コピーの根は行 0 で上昇するので鎖は全コピーを貫いて
  `j0` に降りる。途中のコピーが最小値を下げないことは
  `amin M j0 ≤ amin M (j0+Lb)`（hrow1、`i1 ≥ 1` で常に真: 22272/22272）。
* `i1 = 0`（`d0 = d1 = 0`）: コピーは完全に同一で、コピー `k` の根の親は
  `j0` の親（接頭辞）。hrow1 は偽（4387/5967）なので平坦版を使う。

probe: tools/probe_a2_branch.py (A2) 0/28239。
-/
import Cgraft

namespace TRIO

open Classical
open Wset

section GexpAmin

variable {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}

/-- 接頭辞（`j0` を含む）では `gexp` の値は `M` の値。 -/
theorem gexp_entry_le {i p : ℕ} (hlen : j0 + Lb + 1 = M.length) (hn : 0 < n)
    (hLb : 0 < Lb) (hp : p ≤ j0) :
    entry (gexp M j0 Lb d0 d1 n) i p = entry M i p := by
  rcases Nat.lt_or_ge p j0 with hlt | hge
  · exact gexp_entry_low hlen hlt
  · have hpe : p = j0 := by omega
    rw [hpe]
    exact gexp_entry_root hlen hn hLb

/-! ## 上昇コピー相（`d0 > 0`） -/

/-- **(A2), 上昇コピー相**: 鏡映位置は元の列と同じ `amin` をもつ。側条件
`hrow1` は「ブロックの行 0 鎖が根より行 1 の最小値を下げない」。 -/
theorem amin_gexp_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hrow1 : amin M j0 ≤ amin M (j0 + Lb)) :
    amin (gexp M j0 Lb d0 d1 n) (j0 + (k * Lb + q)) = amin M (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + q) < (gexp M j0 Lb d0 d1 n).length := by
    rw [hXlen]; omega
  have hroot0 : entry (gexp M j0 Lb d0 d1 n) 0 j0 = entry M 0 j0 :=
    gexp_entry_root hlen hn hLb
  have hMj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
    rtg0_of_window (by omega) (by omega) fun l hl0 hl1 => hup l hl0 (by omega)
  have hXj0p : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0
      (j0 + (k * Lb + q)) :=
    gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  refine nat_eq_of_lt_iff fun v => ?_
  rw [← coneV_iff_amin, ← coneV_iff_amin]
  constructor
  · intro h y hy
    have hyle : y ≤ j0 + q := nextrel0_rtrancl_index_le hy
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · -- 接頭辞の祖先: 鎖を展開側に移す
      have hMyj0 := (le0_of_le0_le0 (X := M) ⟨by omega, by omega, hy⟩
        ⟨by omega, by omega, hMj0q⟩ hyj).2.2
      have hXyj0 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y j0 :=
        rtg0_of_agree_last (M := M) (X := gexp M j0 Lb d0 d1 n)
          (by rw [hXlen]; omega)
          (fun x hx => gexp_getD_low hlen (by omega)) hroot0 hMyj0
      have hval := h y (hXyj0.trans hXj0p)
      rwa [gexp_entry_low hlen hyj] at hval
    · -- 同じコピー内の鏡映祖先
      obtain ⟨q', rfl⟩ : ∃ q', y = j0 + q' := ⟨y - j0, by omega⟩
      have hq'lt : q' < Lb := by omega
      have hmir : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hy q rfl hq
      have hval := h _ hmir
      rw [gexp_entry1_mir hlen hk hq'lt] at hval
      by_cases hg : le1 M j0 (j0 + q')
      · have hj0v := h j0 hXj0p
        rw [gexp_entry_root (y := 1) hlen hn hLb] at hj0v
        rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
        · simpa using hj0v
        · have hge : entry M 1 j0 ≤ entry M 1 (j0 + q') :=
            le_of_lt (le1_entry1_lt hg (by omega))
          omega
      · rw [if_neg hg] at hval
        omega
  · intro h y hy
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hXyj0 := (le0_of_le0_le0 (X := gexp M j0 Lb d0 d1 n)
        ⟨by rw [hXlen]; omega, hplt, hy⟩ ⟨by rw [hXlen]; omega, hplt, hXj0p⟩
        hyj).2.2
      have hMyj0 : Relation.ReflTransGen (nextrel0 M) y j0 :=
        rtg0_of_agree_last (M := gexp M j0 Lb d0 d1 n) (X := M) (by omega)
          (fun x hx => (gexp_getD_low hlen (by omega)).symm) hroot0.symm hXyj0
      rw [gexp_entry_low hlen hyj]
      exact h y (hMyj0.trans hMj0q)
    · obtain ⟨k', q', hk', hq', rfl, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e y hy hyj
      rw [gexp_entry1_mir hlen (by omega) hq']
      rcases hcase with ⟨rfl, hM⟩ | ⟨hlt, hM⟩
      · have := h _ hM
        split_ifs <;> omega
      · have h1 : v < amin M (j0 + q) := coneV_iff_amin.1 h
        have h2 : amin M (j0 + q) ≤ amin M j0 := amin_mono hMj0q
        have h3 : amin M (j0 + Lb) ≤ entry M 1 (j0 + q') := amin_le hM
        split_ifs <;> omega

/-! ## 平坦コピー相（`d0 = d1 = 0`） -/

/-- **(A2), 平坦相**: コピーが完全に同一のとき、鏡映位置は元の列と同じ `amin`
をもつ。コピー `k` の根の接頭辞側の祖先は宿主の根 `j0` の祖先そのもの。 -/
theorem amin_gexp_mir_flat {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    amin (gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) = amin M (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M j0 Lb 0 0 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + q) < (gexp M j0 Lb 0 0 n).length := by
    rw [hXlen]; omega
  have hMj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
    rtg0_of_window (by omega) (by omega) fun l hl0 hl1 => hup l hl0 (by omega)
  have hXrp : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n))
      (j0 + k * Lb) (j0 + (k * Lb + q)) :=
    gexp_flat_rtg0_root hlen hLb hk hq hn hup
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
  refine nat_eq_of_lt_iff fun v => ?_
  rw [← coneV_iff_amin, ← coneV_iff_amin]
  constructor
  · intro h y hy
    have hyle : y ≤ j0 + q := nextrel0_rtrancl_index_le hy
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hMyj0 := (le0_of_le0_le0 (X := M) ⟨by omega, by omega, hy⟩
        ⟨by omega, by omega, hMj0q⟩ hyj).2.2
      have hval := h y (((hlowX y hyj).2 hMyj0).trans hXrp)
      rwa [gexp_entry_low hlen hyj] at hval
    · obtain ⟨q', rfl⟩ : ∃ q', y = j0 + q' := ⟨y - j0, by omega⟩
      have hq'lt : q' < Lb := by omega
      have hmir : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hy q rfl hq
      have hval := h _ hmir
      rwa [gexp_flat_entry hlen hk hq'lt] at hval
  · intro h y hy
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hXyr := (le0_of_le0_le0 (X := gexp M j0 Lb 0 0 n)
        ⟨by rw [hXlen]; omega, hplt, hy⟩ ⟨by rw [hXlen]; omega, hplt, hXrp⟩
        (by omega)).2.2
      rw [gexp_entry_low hlen hyj]
      exact h y (((hlowX y hyj).1 hXyr).trans hMj0q)
    · obtain ⟨q', hq', rfl, hM⟩ :=
        gexp_flat_chain_inversion hlen hLb hk hq hup y hy hyj
      rw [gexp_flat_entry hlen hk hq']
      exact h _ hM

end GexpAmin

/-! ## `oper` 版 (A2)

`Lcone.oper_eq_gexp_gen` で展開を `gexp` に直し、`srow` の値で 2 相に分ける。 -/

theorem rtg0_of_rtg1 {X : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 X) a b) :
    Relation.ReflTransGen (nextrel0 X) a b := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih => exact ih.trans hyz.2.2.2.2.1.2.2

open Classical in
/-- **(A2)**: 展開のコピー列は元の列と同じ `amin` をもつ。 -/
theorem amin_oper_mir {M : TrioSeq} {n j0 Lb k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (hk : k < n) (hq : q < Lb) :
    amin (M⟦n⟧) (j0 + (k * Lb + q)) = amin M (j0 + q) := by
  classical
  have hL : M.length - 1 ≠ 0 := by omega
  have hj1 : M.length - 1 = j0 + Lb := by omega
  have hnr : nextR M (srow M (M.length - 1)) j0 (M.length - 1) := by
    rw [← hj0]; exact parent_nextR hp
  have hsr2 : srow M (M.length - 1) = 0 ∨ srow M (M.length - 1) = 1
      ∨ srow M (M.length - 1) = 2 := by
    unfold srow; split_ifs <;> omega
  have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + Lb) := by
    rw [← hj1]
    rcases hsr2 with hs | hs | hs <;> rw [hs] at hnr <;> unfold nextR at hnr
    · rw [if_pos rfl] at hnr
      exact Relation.ReflTransGen.single hnr
    · rw [if_neg (by omega), if_pos rfl] at hnr
      exact hnr.2.2.2.2.1.2.2
    · rw [if_neg (by omega), if_neg (by omega)] at hnr
      exact rtg0_of_rtg1 hnr.2.2.2.2.1.2.2
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l :=
    window_of_rtg0 hrtg (by omega)
  rw [oper_eq_gexp_gen n hL hz hp, hj0,
    show M.length - 1 - j0 = Lb from by omega, hj1]
  by_cases h0 : 0 < srow M (j0 + Lb)
  · -- `i1 ≥ 1`: 行 0 が上昇するコピー
    have hd0pos : 0 < entry M 0 (j0 + Lb) - entry M 0 j0 := by
      have := hup (j0 + Lb) (by omega) (le_refl _); omega
    have hd0e : entry M 0 (j0 + Lb) = entry M 0 j0
        + (entry M 0 (j0 + Lb) - entry M 0 j0) := by omega
    have hle1 : le1 M j0 (j0 + Lb) := by
      rw [hj1] at hsr2
      rcases hsr2 with hs | hs | hs
      · exact absurd hs (by omega)
      · rw [hj1, hs] at hnr
        unfold nextR at hnr
        rw [if_neg (by omega), if_pos rfl] at hnr
        exact ⟨hnr.1, hnr.2.1, Relation.ReflTransGen.single hnr⟩
      · rw [hj1, hs] at hnr
        unfold nextR at hnr
        rw [if_neg (by omega), if_neg (by omega)] at hnr
        exact hnr.2.2.2.2.1
    rw [if_pos h0]
    exact amin_gexp_mir hlen hLb hk hq hup hd0pos hd0e
      (le_of_eq (amin_le1 hle1))
  · -- `i1 = 0`: 完全に同一のコピー
    rw [if_neg h0, if_neg (by omega)]
    exact amin_gexp_mir_flat hlen hLb hk hq hup

end TRIO
