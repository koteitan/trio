/-
Cgraft.lean: 接ぎ木ブロックにおける「根の行 1 錐」の輸送と、そこから従う
リフト計算則。

`Lift1 X d` は根 `0` の行 1 錐 `le1 X 0 ·` の上だけで行 1 を持ち上げる。よって
`Lift1 (graft E A) d` を `graft (Lift1 E d) ?` の形に落とすには、複合ブロック
`graft E A` の錐が引数 `A` の上でどう見えるかを知ればよい。

**主定理** (`cone_graft_high`): `E`（植えたブロック: 根が狭義に最浅）と
`A`（同じく単一木）について、`A` の**根以外の行 1 孤児がすべて `E` の根の行 1
値 `v` 以下**（`HighPar A v`）ならば、`s = |E| - 1` として

    le1 (graft E A) 0 (s + j) ↔ le1 (graft E A) 0 s ∧ le1 A 0 j

すなわち複合の錐は `A` の上では「接ぎ木点が錐に入っていれば `A` 自身の錐、
入っていなければ空」。ゆえに (`lift_graft_plant`)

    Lift1 (graft E A) d
      = graft (Lift1 E d) (if 接ぎ木点が錐 then Lift1 A d else A)

`HighPar` はちょうど必要な条件（tools/probe_calc2.py: 両枝 0/241816 違反、
条件を外すと 54978/58184 違反）。接ぎ木点のガードも必須（tools/probe_lowcalc.py:
素朴な「A の根が `v` より上」では 7814/102572 違反 — 文脈の低い列が
行 1 の親を横取りする）。
-/
import Lcone
import Xbar

namespace TRIO

open Wset

/-! ## 高い列は親をもつ（＝根以外の行 1 孤児は低い） -/

/-- 根を除く各列は、行 1 で `v` を超えるなら行 1 の親をもつ。同値に、`A` の
根以外の行 1 孤児はすべて行 1 で `v` 以下。 -/
def HighPar (A : TrioSeq) (v : ℕ) : Prop :=
  ∀ j, 0 < j → j < A.length → v < entry A 1 j → ∃ p, nextrel1 A p j

/-- 根が狭義に最浅なブロック（単一木）では、根より行 1 で高い列は必ず行 1 の
親をもつ。 -/
theorem highPar_of_shallow {A : TrioSeq} (hA0 : entry A 0 0 = 0)
    (hAs : ∀ l, 0 < l → l < A.length → 0 < entry A 0 l) :
    HighPar A (entry A 1 0) := by
  intro j hj0 hjA hlt
  obtain ⟨c, hc, -⟩ := nextrel1_exists hjA
    ⟨by omega, hjA, rtg0_zero (fun l hl0 hl1 => by rw [hA0]; exact hAs l hl0 hl1) hjA⟩
    hj0 hlt
  exact ⟨c, hc⟩

/-- `HighPar` はリフトで保たれる: 錐の中の列は親をもち、錐の外の列は行 1 の値が
変わらない。 -/
theorem highPar_Lift1 {A : TrioSeq} {v d : ℕ} (h : HighPar A v) :
    HighPar (Lift1 A d) v := by
  intro j hj0 hjA hlt
  rw [Lift1_length] at hjA
  by_cases hc : le1 A 0 j
  · obtain ⟨-, -, hr⟩ := hc
    cases hr with
    | refl => exact absurd hj0 (Nat.lt_irrefl 0)
    | @tail c _ _ hcj => exact ⟨c, nextrel1_Lift1.2 hcj⟩
  · rw [entry1_Lift1 hjA, if_neg hc] at hlt
    obtain ⟨p, hp⟩ := h j hj0 hjA (by omega)
    exact ⟨p, nextrel1_Lift1.2 hp⟩

/-! ## 接ぎ木の成分 -/

section Graft

variable {E A : TrioSeq}

theorem entry_graft_low {y i : ℕ} (hi : i < E.length - 1) :
    entry (graft E A) y i = entry E y i := by
  rw [← Wset.entry_take (X := graft E A) (l := E.length - 1) (i := y) (j := i) hi,
    take_graft_low (le_refl _), Wset.entry_take hi]

theorem entry1_graft_high (E A : TrioSeq) (k : ℕ) :
    entry (graft E A) 1 (E.length - 1 + k) = entry A 1 k := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd, entry_append_right, entry1_shiftr01]

theorem entry2_graft_high (E A : TrioSeq) (k : ℕ) :
    entry (graft E A) 2 (E.length - 1 + k) = entry A 2 k := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd, entry_append_right, entry2_shiftr01]

theorem entry0_graft_high {k : ℕ} (hk : k < A.length) :
    entry (graft E A) 0 (E.length - 1 + k)
      = entry A 0 k + entry E 0 (E.length - 1) := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd, entry_append_right, entry0_shiftr01 hk]

theorem nextrel1_graft_high (E A : TrioSeq) (a b : ℕ) :
    nextrel1 (graft E A) (E.length - 1 + a) (E.length - 1 + b) ↔ nextrel1 A a b := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd, nextrel1_append_right, nextrel1_shiftr01]

theorem le0_graft_high (E A : TrioSeq) (a b : ℕ) :
    le0 (graft E A) (E.length - 1 + a) (E.length - 1 + b) ↔ le0 A a b := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd, le0_append_right, le0_shiftr01]

theorem le1_graft_high (E A : TrioSeq) (a b : ℕ) :
    le1 (graft E A) (E.length - 1 + a) (E.length - 1 + b) ↔ le1 A a b := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd, le1_append_right, le1_shiftr01]

theorem le1_graft_low {i : ℕ} (hi : i < E.length - 1) :
    le1 (graft E A) 0 i ↔ le1 E 0 i := by
  have h1 : (graft E A).take (E.length - 1) = E.take (E.length - 1) :=
    take_graft_low (le_refl _)
  rw [← le1_take (X := graft E A) (l := E.length - 1)
      (by rw [graft_length]; omega) hi, h1,
    le1_take (by omega) hi]

/-- 接ぎ木ブロックでも根は狭義に最浅。 -/
theorem shallow_graft (hEs : ∀ l, 0 < l → l < E.length → 0 < entry E 0 l)
    (hE2 : 2 ≤ E.length) :
    ∀ l, 0 < l → l < (graft E A).length → 0 < entry (graft E A) 0 l := by
  intro l hl0 hlG
  rw [graft_length] at hlG
  rcases Nat.lt_or_ge l (E.length - 1) with hlow | hhigh
  · rw [entry_graft_low hlow]
    exact hEs l hl0 (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, l = E.length - 1 + k := ⟨l - (E.length - 1), by omega⟩
    rw [entry0_graft_high (by omega)]
    have := hEs (E.length - 1) (by omega) (by omega)
    omega

end Graft

/-! ## 錐の輸送 -/

/-- **接ぎ木の錐輸送**: `A` の根以外の行 1 孤児が `E` の根より高くないなら、
複合ブロックの錐は引数の上で「接ぎ木点が錐に入るなら `A` 自身の錐、
入らないなら空」になる。 -/
theorem cone_graft_high {E A : TrioSeq} (hE2 : 2 ≤ E.length)
    (hA0 : entry A 0 0 = 0)
    (hAs : ∀ l, 0 < l → l < A.length → 0 < entry A 0 l)
    (hlow : HighPar A (entry E 1 0)) {j : ℕ} (hj : j < A.length) :
    le1 (graft E A) 0 (E.length - 1 + j)
      ↔ (le1 (graft E A) 0 (E.length - 1) ∧ le1 A 0 j) := by
  set s := E.length - 1 with hs
  set G := graft E A with hGdef
  have hs1 : 1 ≤ s := by omega
  have hGlen : G.length = s + A.length := graft_length E A
  have hAroot : ∀ l, 0 < l → l < A.length → entry A 0 0 < entry A 0 l := by
    intro l hl0 hl1
    rw [hA0]
    exact hAs l hl0 hl1
  have hG1root : entry G 1 0 = entry E 1 0 := by
    rw [hGdef, entry_graft_low (by omega)]
  constructor
  · rintro ⟨-, -, hchain⟩
    have key : ∀ b : ℕ, Relation.ReflTransGen (nextrel1 G) 0 b →
        ∀ k, b = s + k → k < A.length →
        le1 G 0 s ∧ Relation.ReflTransGen (nextrel1 A) 0 k := by
      intro b hb
      induction hb with
      | refl => intro k hk _; omega
      | @tail y w hy hyw ih =>
          intro k hk hkA
          subst hk
          rcases Nat.lt_or_ge y s with hys | hys
          · -- the step enters the argument: it must land on the graft point
            rcases Nat.eq_zero_or_pos k with rfl | hk0
            · refine ⟨⟨by omega, by rw [hGlen]; omega, ?_⟩, Relation.ReflTransGen.refl⟩
              simpa using hy.tail hyw
            · exfalso
              have hle0A : le0 A 0 k := ⟨by omega, hkA, rtg0_zero hAroot hkA⟩
              have hle0G : le0 G (s + 0) (s + k) :=
                (le0_graft_high E A 0 k).2 hle0A
              have hmin := hyw.2.2.2.2.2 s ⟨by omega, by simpa using hle0G⟩
              have hsk : entry G 1 (s + k) = entry A 1 k := entry1_graft_high E A k
              have hs0 : entry G 1 s = entry A 1 0 := by
                have h := entry1_graft_high E A 0
                simpa using h
              rw [hsk, hs0] at hmin
              have hcone : le1 G 0 (s + k) :=
                ⟨by omega, by rw [hGlen]; omega, hy.tail hyw⟩
              have hgt := le1_entry1_lt hcone (by omega)
              rw [hG1root, hGdef, entry1_graft_high] at hgt
              obtain ⟨p, hp⟩ := hlow k hk0 hkA hgt
              have hpG : nextrel1 G (s + p) (s + k) :=
                (nextrel1_graft_high E A p k).2 hp
              have := nextrel1_uniq_src hyw hpG
              omega
          · obtain ⟨y', rfl⟩ : ∃ y', y = s + y' := ⟨y - s, by omega⟩
            have hy'A : y' < A.length := by
              have := hyw.1
              rw [hGlen] at this
              omega
            obtain ⟨h1, h2⟩ := ih y' rfl hy'A
            exact ⟨h1, h2.tail ((nextrel1_graft_high E A y' k).1 hyw)⟩
    obtain ⟨h1, h2⟩ := key (s + j) hchain j rfl hj
    exact ⟨h1, ⟨by omega, hj, h2⟩⟩
  · rintro ⟨h1, h2⟩
    refine le1_trans h1 ?_
    have := (le1_graft_high E A 0 j).2 h2
    simpa using this

/-! ## リフト計算則 -/

open Classical in
/-- **接ぎ木リフト計算則**: 単一木 `A`（根以外の行 1 孤児が `E` の根の行 1 値
以下）を接ぎ木したブロックをリフトすると、リフトは文脈側にだけ効き、引数側には
「接ぎ木点が錐に入るときにかぎり」引数自身のリフトとして効く。 -/
theorem lift_graft_cone {E A : TrioSeq} (hE2 : 2 ≤ E.length)
    (hA0 : entry A 0 0 = 0)
    (hAs : ∀ l, 0 < l → l < A.length → 0 < entry A 0 l)
    (hlow : HighPar A (entry E 1 0)) (d : ℕ) :
    Lift1 (graft E A) d
      = graft (Lift1 E d)
        (if le1 (graft E A) 0 (E.length - 1) then Lift1 A d else A) := by
  set B : TrioSeq := if le1 (graft E A) 0 (E.length - 1) then Lift1 A d else A
    with hB
  have hBlen : B.length = A.length := by
    rw [hB]; split <;> simp
  have hLElen : (Lift1 E d).length = E.length := Lift1_length E d
  have hLE1 : (Lift1 E d).length - 1 = E.length - 1 := by rw [hLElen]
  have hlen : (Lift1 (graft E A) d).length = (graft (Lift1 E d) B).length := by
    rw [Lift1_length, graft_length, graft_length, hLElen, hBlen]
  have hB0 : ∀ k, entry B 0 k = entry A 0 k := by
    intro k; rw [hB]; split
    · exact entry0_Lift1 A d k
    · rfl
  have hB2 : ∀ k, entry B 2 k = entry A 2 k := by
    intro k; rw [hB]; split
    · exact entry2_Lift1 A d k
    · rfl
  have hB1 : ∀ k, k < A.length → entry B 1 k
      = entry A 1 k + (if le1 (graft E A) 0 (E.length - 1 + k) then d else 0) := by
    intro k hk
    by_cases hg : le1 (graft E A) 0 (E.length - 1)
    · rw [hB, if_pos hg, entry1_Lift1 hk,
        if_congr (cone_graft_high hE2 hA0 hAs hlow hk) rfl rfl]
      by_cases hc : le1 A 0 k
      · rw [if_pos hc, if_pos ⟨hg, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · rw [hB, if_neg hg,
        if_neg (fun h => hg ((cone_graft_high hE2 hA0 hAs hlow hk).1 h).1)]
      omega
  refine List.ext_getElem hlen ?_
  intro i hi1 hi2
  rw [Lift1_length, graft_length] at hi1
  rw [← entry_triple (by rw [Lift1_length, graft_length]; omega),
    ← entry_triple (by rw [graft_length, hLElen, hBlen]; omega)]
  rcases Nat.lt_or_ge i (E.length - 1) with hlo | hhi
  · have hEi : i < E.length := by omega
    have e0 : entry (Lift1 (graft E A) d) 0 i = entry E 0 i := by
      rw [entry0_Lift1, entry_graft_low hlo]
    have e2 : entry (Lift1 (graft E A) d) 2 i = entry E 2 i := by
      rw [entry2_Lift1, entry_graft_low hlo]
    have e1 : entry (Lift1 (graft E A) d) 1 i
        = entry E 1 i + (if le1 E 0 i then d else 0) := by
      rw [entry1_Lift1 (by rw [graft_length]; omega), entry_graft_low hlo,
        if_congr (le1_graft_low hlo) rfl rfl]
    have f0 : entry (graft (Lift1 E d) B) 0 i = entry E 0 i := by
      rw [entry_graft_low (by omega), entry0_Lift1]
    have f2 : entry (graft (Lift1 E d) B) 2 i = entry E 2 i := by
      rw [entry_graft_low (by omega), entry2_Lift1]
    have f1 : entry (graft (Lift1 E d) B) 1 i
        = entry E 1 i + (if le1 E 0 i then d else 0) := by
      rw [entry_graft_low (by omega), entry1_Lift1 hEi]
    rw [e0, e1, e2, f0, f1, f2]
  · obtain ⟨k, rfl⟩ : ∃ k, i = E.length - 1 + k := ⟨i - (E.length - 1), by omega⟩
    have hkA : k < A.length := by omega
    have e0 : entry (Lift1 (graft E A) d) 0 (E.length - 1 + k)
        = entry A 0 k + entry E 0 (E.length - 1) := by
      rw [entry0_Lift1, entry0_graft_high hkA]
    have e2 : entry (Lift1 (graft E A) d) 2 (E.length - 1 + k) = entry A 2 k := by
      rw [entry2_Lift1, entry2_graft_high]
    have e1 : entry (Lift1 (graft E A) d) 1 (E.length - 1 + k)
        = entry A 1 k + (if le1 (graft E A) 0 (E.length - 1 + k) then d else 0) := by
      rw [entry1_Lift1 (by rw [graft_length]; omega), entry1_graft_high]
    have f0 : entry (graft (Lift1 E d) B) 0 (E.length - 1 + k)
        = entry A 0 k + entry E 0 (E.length - 1) := by
      rw [← hLE1, entry0_graft_high (by rw [hBlen]; exact hkA), hB0, entry0_Lift1]
    have f2 : entry (graft (Lift1 E d) B) 2 (E.length - 1 + k) = entry A 2 k := by
      rw [← hLE1, entry2_graft_high, hB2]
    have f1 : entry (graft (Lift1 E d) B) 1 (E.length - 1 + k)
        = entry A 1 k + (if le1 (graft E A) 0 (E.length - 1 + k) then d else 0) := by
      rw [← hLE1, entry1_graft_high, hB1 k hkA, hLE1]
    rw [e0, e1, e2, f0, f1, f2]

end TRIO
