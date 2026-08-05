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

/-! ## (G2): 階段リフトは展開と可換 -/

theorem slift_take {A : TrioSeq} {φ : ℕ → ℕ} {l : ℕ} (hl : l ≤ A.length) :
    slift (A.take l) φ = (slift A φ).take l := by
  refine List.ext_getElem (by simp) ?_
  intro i hi1 hi2
  rw [slift_length, List.length_take] at hi1
  have hiA : i < A.length := by omega
  have hil : i < l := by omega
  rw [← entry_triple (X := slift (A.take l) φ)
      (by rw [slift_length, List.length_take]; omega),
    ← entry_triple (X := (slift A φ).take l)
      (by rw [List.length_take, slift_length]; omega)]
  have hL : ∀ y, entry ((slift A φ).take l) y i = entry (slift A φ) y i :=
    fun y => Wset.entry_take (X := slift A φ) (l := l) (i := y) (j := i) hil
  have hR : ∀ y, entry (A.take l) y i = entry A y i :=
    fun y => Wset.entry_take (X := A) (l := l) (i := y) (j := i) hil
  rw [hL 0, hL 1, hL 2, entry0_slift, entry0_slift, entry2_slift, entry2_slift,
    entry1_slift (by rw [List.length_take]; omega), entry1_slift hiA, hR 0,
    hR 1, hR 2, amin_take hl hil]

theorem slift_dropLast {A : TrioSeq} {φ : ℕ → ℕ} :
    slift A.dropLast φ = (slift A φ).dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, slift_length,
    slift_take (by omega)]

open Classical in
/-- **(G2) の主分岐**: 展開が `gexp` になる場合。分岐データ `j0 / Lb / d0 / d1`
は両辺で共通（呼び出し側が `hAn` / `hBn` で供給する）。 -/
theorem slift_oper_main {A : TrioSeq} {φ : ℕ → ℕ} {n j0 Lb d0 d1 : ℕ}
    (hφ : Stair φ)
    (hlen : j0 + Lb + 1 = A.length) (hLb : 0 < Lb) (hn : 0 < n)
    (hz : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0 ∧
      entry A 2 (A.length - 1) = 0))
    (hp : hasParent A (srow A (A.length - 1)) (A.length - 1))
    (hj0 : parent A (srow A (A.length - 1)) (A.length - 1) = j0)
    (hAn : A⟦n⟧ = gexp A j0 Lb d0 d1 n)
    (hBn : (slift A φ)⟦n⟧ = gexp (slift A φ) j0 Lb d0 d1 n) :
    slift (A⟦n⟧) φ = (slift A φ)⟦n⟧ := by
  classical
  have hBlen : (slift A φ).length = A.length := slift_length A φ
  have hlenB : j0 + Lb + 1 = (slift A φ).length := by rw [hBlen]; exact hlen
  have hlenA : (A⟦n⟧).length = j0 + n * Lb := by rw [hAn]; exact gexp_length hlen
  have hlenBn : ((slift A φ)⟦n⟧).length = j0 + n * Lb := by
    rw [hBn]; exact gexp_length hlenB
  refine List.ext_getElem (by rw [slift_length, hlenA, hlenBn]) ?_
  intro i hi1 _
  rw [slift_length, hlenA] at hi1
  rw [← entry_triple (X := slift (A⟦n⟧) φ) (by rw [slift_length, hlenA]; omega),
    ← entry_triple (X := (slift A φ)⟦n⟧) (by rw [hlenBn]; omega)]
  rcases Nat.lt_or_ge i j0 with hlo | hhi
  · -- 接頭辞: (A1)
    have hiA : i < A.length := by omega
    have hA0 : entry (A⟦n⟧) 0 i = entry A 0 i := by
      rw [hAn]; exact gexp_entry_low hlen hlo
    have hA1 : entry (A⟦n⟧) 1 i = entry A 1 i := by
      rw [hAn]; exact gexp_entry_low hlen hlo
    have hA2 : entry (A⟦n⟧) 2 i = entry A 2 i := by
      rw [hAn]; exact gexp_entry_low hlen hlo
    have hamin : amin (A⟦n⟧) i = amin A i :=
      amin_oper_prefix (by omega) hn (by omega)
    have hB0 : entry ((slift A φ)⟦n⟧) 0 i = entry A 0 i := by
      rw [hBn, gexp_entry_low hlenB hlo, entry0_slift]
    have hB1 : entry ((slift A φ)⟦n⟧) 1 i
        = entry A 1 i + (φ (amin A i) - amin A i) := by
      rw [hBn, gexp_entry_low hlenB hlo, entry1_slift hiA]
    have hB2 : entry ((slift A φ)⟦n⟧) 2 i = entry A 2 i := by
      rw [hBn, gexp_entry_low hlenB hlo, entry2_slift]
    rw [entry0_slift, entry2_slift, entry1_slift (by rw [hlenA]; omega),
      hA0, hA1, hA2, hamin, hB0, hB1, hB2]
  · -- コピー: (A2)
    obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hhi hi1
    have hqA : j0 + q < A.length := by omega
    have hA0 : entry (A⟦n⟧) 0 (j0 + (k * Lb + q))
        = entry A 0 (j0 + q) + k * d0 := by
      rw [hAn]; exact gexp_entry0_mir hlen hk hq
    have hA1 : entry (A⟦n⟧) 1 (j0 + (k * Lb + q))
        = entry A 1 (j0 + q) + (if le1 A j0 (j0 + q) then k * d1 else 0) := by
      rw [hAn]; exact gexp_entry1_mir hlen hk hq
    have hA2 : entry (A⟦n⟧) 2 (j0 + (k * Lb + q)) = entry A 2 (j0 + q) := by
      rw [hAn]; exact gexp_entry2_mir hlen hk hq d0 d1
    have hamin : amin (A⟦n⟧) (j0 + (k * Lb + q)) = amin A (j0 + q) :=
      amin_oper_mir hlen hLb hn hz hp hj0 hk hq
    have hB0 : entry ((slift A φ)⟦n⟧) 0 (j0 + (k * Lb + q))
        = entry A 0 (j0 + q) + k * d0 := by
      rw [hBn, gexp_entry0_mir hlenB hk hq, entry0_slift]
    have hB1 : entry ((slift A φ)⟦n⟧) 1 (j0 + (k * Lb + q))
        = entry A 1 (j0 + q) + (φ (amin A (j0 + q)) - amin A (j0 + q))
          + (if le1 A j0 (j0 + q) then k * d1 else 0) := by
      rw [hBn, gexp_entry1_mir hlenB hk hq, entry1_slift hqA]
      congr 1
      exact if_congr (le1_slift hφ) rfl rfl
    have hB2 : entry ((slift A φ)⟦n⟧) 2 (j0 + (k * Lb + q))
        = entry A 2 (j0 + q) := by
      rw [hBn, gexp_entry2_mir hlenB hk hq d0 d1, entry2_slift]
    rw [entry0_slift, entry2_slift, entry1_slift (by rw [hlenA]; omega),
      hA0, hA1, hA2, hamin, hB0, hB1, hB2]
    have he : entry A 1 (j0 + q) + (if le1 A j0 (j0 + q) then k * d1 else 0)
          + (φ (amin A (j0 + q)) - amin A (j0 + q))
        = entry A 1 (j0 + q) + (φ (amin A (j0 + q)) - amin A (j0 + q))
          + (if le1 A j0 (j0 + q) then k * d1 else 0) := by omega
    rw [he]

open Classical in
/-- `n = 0` の展開はバッドルートまでの切り詰め。 -/
theorem oper_zero_take {X : TrioSeq} (hL : X.length - 1 ≠ 0)
    (hz : ¬ (entry X 0 (X.length - 1) = 0 ∧ entry X 1 (X.length - 1) = 0 ∧
      entry X 2 (X.length - 1) = 0))
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1)) :
    X⟦0⟧ = X.take (parent X (srow X (X.length - 1)) (X.length - 1)) := by
  rw [oper_eq_gexp_gen 0 hL hz hp]
  unfold gexp gcopies
  simp

open Classical in
/-- **(G2)**: 階段リフトは展開と可換（無条件、probe 0/28239）。 -/
theorem slift_oper {A : TrioSeq} {φ : ℕ → ℕ} (hφ : Stair φ) (n : ℕ) :
    slift (A⟦n⟧) φ = (slift A φ)⟦n⟧ := by
  classical
  have hBlen : (slift A φ).length = A.length := slift_length A φ
  have hj1 : (slift A φ).length - 1 = A.length - 1 := by rw [hBlen]
  by_cases hL : A.length - 1 = 0
  · rw [oper_eq_self_of_short n hL,
      oper_eq_self_of_short n (by rw [hj1]; exact hL)]
  · have hAlen : 1 < A.length := by omega
    have hj1lt : A.length - 1 < A.length := by omega
    have hLB : (slift A φ).length - 1 ≠ 0 := by rw [hj1]; exact hL
    have hpred : Pred (slift A φ) = (slift A φ).dropLast := by
      unfold Pred; rw [if_neg (by rw [hBlen]; omega)]
    have hpredA : Pred A = A.dropLast := by
      unfold Pred; rw [if_neg (by omega)]
    have hzero : (entry (slift A φ) 0 ((slift A φ).length - 1) = 0 ∧
        entry (slift A φ) 1 ((slift A φ).length - 1) = 0 ∧
        entry (slift A φ) 2 ((slift A φ).length - 1) = 0)
        ↔ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0 ∧
          entry A 2 (A.length - 1) = 0) := by
      rw [hj1, entry0_slift, entry2_slift]
      have h1 := entry1_slift_pos hφ hj1lt
      omega
    have hsrB : srow (slift A φ) ((slift A φ).length - 1)
        = srow A (A.length - 1) := by
      rw [hj1]; exact srow_slift hφ hj1lt
    by_cases hz0 : entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0 ∧
        entry A 2 (A.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz0,
        oper_eq_pred_of_zero n hLB (hzero.2 hz0), hpred, hpredA]
      exact slift_dropLast
    · by_cases hp : hasParent A (srow A (A.length - 1)) (A.length - 1)
      · -- 主分岐
        have hnr := parent_nextR hp
        have hj0lt : parent A (srow A (A.length - 1)) (A.length - 1)
            < A.length - 1 := nextR_index_lt hnr
        have hparB : parent (slift A φ)
            (srow (slift A φ) ((slift A φ).length - 1))
            ((slift A φ).length - 1)
            = parent A (srow A (A.length - 1)) (A.length - 1) := by
          rw [hsrB, hj1, parent_slift hφ]
        have hpB : hasParent (slift A φ)
            (srow (slift A φ) ((slift A φ).length - 1))
            ((slift A φ).length - 1) := by
          rw [hsrB, hj1]; exact (hasParent_slift hφ).2 hp
        have hzB : ¬ (entry (slift A φ) 0 ((slift A φ).length - 1) = 0 ∧
            entry (slift A φ) 1 ((slift A φ).length - 1) = 0 ∧
            entry (slift A φ) 2 ((slift A φ).length - 1) = 0) :=
          fun h => hz0 (hzero.1 h)
        have hd1eq : (if 1 < srow A (A.length - 1)
              then entry (slift A φ) 1 (A.length - 1)
                - entry (slift A φ) 1
                  (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0)
            = (if 1 < srow A (A.length - 1)
              then entry A 1 (A.length - 1)
                - entry A 1 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0) := by
          split_ifs with h2
          · have hn2 : nextrel2 A
                (parent A (srow A (A.length - 1)) (A.length - 1))
                (A.length - 1) := by
              have h := hnr
              unfold nextR at h
              rw [if_neg (by omega), if_neg (by omega)] at h
              exact h
            rw [entry1_slift hj1lt, entry1_slift (by omega),
              amin_le1 hn2.2.2.2.2.1]
            omega
          · rfl
        have hBn : (slift A φ)⟦n⟧ = gexp (slift A φ)
            (parent A (srow A (A.length - 1)) (A.length - 1))
            (A.length - 1 - parent A (srow A (A.length - 1)) (A.length - 1))
            (if 0 < srow A (A.length - 1) then entry A 0 (A.length - 1)
              - entry A 0 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0)
            (if 1 < srow A (A.length - 1) then entry A 1 (A.length - 1)
              - entry A 1 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0) n := by
          rw [oper_eq_gexp_gen n hLB hzB hpB, hparB, hsrB, hj1, entry0_slift,
            entry0_slift, hd1eq]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [oper_zero_take hL hz0 hp, oper_zero_take hLB hzB hpB, hparB,
            slift_take (by omega)]
        · exact slift_oper_main hφ (by omega) (by omega) hn hz0 hp rfl
            (oper_eq_gexp_gen n hL hz0 hp) hBn
      · have hpB : ¬ hasParent (slift A φ)
            (srow (slift A φ) ((slift A φ).length - 1))
            ((slift A φ).length - 1) := by
          rw [hsrB, hj1]
          exact fun h => hp ((hasParent_slift hφ).1 h)
        rw [oper_eq_pred_of_noParent n hL hz0 hp,
          oper_eq_pred_of_noParent n hLB (fun h => hz0 (hzero.1 h)) hpB,
          hpred, hpredA]
        exact slift_dropLast

/-! ## 環境マスクは根リフトに吸収される

`Lift1 X d` は根の錐をちょうど `d` だけ上げるので、`d > 0` なら錐の中の列は
どれも祖先最小値が `v + d > v` になり、錐の外の列は行 1 が `v` 以下の祖先を
もつ。したがって **`Lift1 X d` の閾値 `v` の環境マスクは `X` の根の錐そのもの**
で、マスクリフトは根リフトに吸収される:

    mlift (Lift1 X d) v e = Lift1 X (d + e)        （`X = (0,v,z) :: R`, `0 < d`）

probe: tools/probe_mliftlift.py 0/132781（`d = 0` では偽 44631/67219 — 根が
閾値ちょうどでマスクから外れる）。塔の帰納を `∀ s, Lift1 (Nb⟦j⟧) (d1+s) ∈ GX`
に強めれば、塔のデータ側は `CoreMaskLift` なしで閉じる。 -/

theorem rtg0_Lift1 {X : TrioSeq} {d a b : ℕ} :
    Relation.ReflTransGen (nextrel0 (Lift1 X d)) a b
      ↔ Relation.ReflTransGen (nextrel0 X) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel0_Lift1.1 hyw)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel0_Lift1.2 hyw)

theorem argOK_mlift {R : TrioSeq} (hR : argOK R) (v d : ℕ) :
    argOK (mlift R v d) := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  have hi' : i < R.length := by rw [mlift_length] at hi; exact hi
  have hpe : p = (mlift R v d).getD i (0, 0, 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, ← hpi]
    rfl
  rw [hpe, mlift_getD hi']
  show 0 < entry R 0 i
  exact hR _ (entry_pair_mem hi')

open Classical in
/-- **リフト済みブロックの環境マスクは根の錐**（`0 < d`）。 -/
theorem coneV_Lift1_cons {R : TrioSeq} (hR : argOK R) {v z d j : ℕ} (hd : 0 < d)
    (hj : j < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length) :
    coneV (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) v j
      ↔ le1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 j := by
  set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: R with hN
  have hNlen : N.length = R.length + 1 := by rw [hN]; simp
  have hshal : ∀ l, 0 < l → l < N.length → entry N 0 0 < entry N 0 l := by
    intro l hl0 hlN
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have h0 : entry N 0 0 = 0 := by rw [hN]; exact based_cons v z R
    rw [h0, hN, entry_cons]
    exact hR _ (entry_pair_mem (by omega))
  have hN1 : entry N 1 0 = v := by
    show ((((0, v, z) : ℕ × ℕ × ℕ) :: R).getD 0 (0, 0, 0)).2.1 = v
    rfl
  rw [le1_zero_iff hshal hj, hN1]
  constructor
  · intro h y hy hy0
    have hylt : y < N.length := by have := rtg0_le hy; omega
    have hval := h y (rtg0_Lift1.2 hy)
    rw [entry1_Lift1 hylt] at hval
    by_cases hg : le1 N 0 y
    · have := le1_entry1_lt hg (Ne.symm hy0)
      rw [hN1] at this
      exact this
    · rw [if_neg hg] at hval
      exact hval
  · intro h y hy
    have hylt : y < N.length := by have := rtg0_le hy; omega
    rw [entry1_Lift1 hylt]
    rcases Nat.eq_zero_or_pos y with rfl | hy0
    · rw [if_pos (le1_refl (by omega)), hN1]
      omega
    · have := h y (rtg0_Lift1.1 hy) (by omega)
      split_ifs <;> omega

open Classical in
/-- **(ML)**: 環境マスクリフトは根リフトに吸収される。 -/
theorem mlift_Lift1_cons {R : TrioSeq} (hR : argOK R) {v z d e : ℕ} (hd : 0 < d) :
    mlift (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) v e
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) (d + e) := by
  set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: R with hN
  refine List.ext_getElem (by simp) ?_
  intro i hi1 hi2
  rw [mlift_length, Lift1_length] at hi1
  rw [← entry_triple (X := mlift (Lift1 N d) v e)
      (by rw [mlift_length, Lift1_length]; exact hi1),
    ← entry_triple (X := Lift1 N (d + e)) (by rw [Lift1_length]; exact hi1)]
  have e0 : entry (mlift (Lift1 N d) v e) 0 i = entry N 0 i := by
    rw [entry0_mlift, entry0_Lift1]
  have e2 : entry (mlift (Lift1 N d) v e) 2 i = entry N 2 i := by
    rw [entry2_mlift, entry2_Lift1]
  have e1 : entry (mlift (Lift1 N d) v e) 1 i
      = entry N 1 i + (if le1 N 0 i then d + e else 0) := by
    rw [entry1_mlift (by rw [Lift1_length]; exact hi1), entry1_Lift1 hi1,
      if_congr (coneV_Lift1_cons hR hd hi1) rfl rfl]
    split_ifs <;> omega
  rw [e0, e1, e2, entry0_Lift1, entry2_Lift1, entry1_Lift1 hi1]

end TRIO
