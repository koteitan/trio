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
/-- **組み立て補題**: 引数側の置換ブロック `B` が「行 0・行 2 はそのまま、行 1 は
複合ブロックの錐の上でだけ `d` 上がる」なら、複合ブロックのリフトは
`graft (Lift1 E d) B` に等しい。 -/
theorem lift_graft_of_entries {E A B : TrioSeq} {d : ℕ} (hE2 : 2 ≤ E.length)
    (hBlen : B.length = A.length)
    (hB0 : ∀ k, entry B 0 k = entry A 0 k) (hB2 : ∀ k, entry B 2 k = entry A 2 k)
    (hB1 : ∀ k, k < A.length → entry B 1 k
      = entry A 1 k + (if le1 (graft E A) 0 (E.length - 1 + k) then d else 0)) :
    Lift1 (graft E A) d = graft (Lift1 E d) B := by
  have hLElen : (Lift1 E d).length = E.length := Lift1_length E d
  have hLE1 : (Lift1 E d).length - 1 = E.length - 1 := by rw [hLElen]
  have hlen : (Lift1 (graft E A) d).length = (graft (Lift1 E d) B).length := by
    rw [Lift1_length, graft_length, graft_length, hLElen, hBlen]
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

open Classical in
/-- **接ぎ木リフト計算則（単一木版）**: 単一木 `A`（根以外の行 1 孤児が `E` の根の
行 1 値以下）を接ぎ木したブロックをリフトすると、リフトは文脈側にだけ効き、
引数側には「接ぎ木点が錐に入るときにかぎり」引数自身のリフトとして効く。 -/
theorem lift_graft_cone {E A : TrioSeq} (hE2 : 2 ≤ E.length)
    (hA0 : entry A 0 0 = 0)
    (hAs : ∀ l, 0 < l → l < A.length → 0 < entry A 0 l)
    (hlow : HighPar A (entry E 1 0)) (d : ℕ) :
    Lift1 (graft E A) d
      = graft (Lift1 E d)
        (if le1 (graft E A) 0 (E.length - 1) then Lift1 A d else A) := by
  refine lift_graft_of_entries hE2 (by split <;> simp) (fun k => ?_) (fun k => ?_)
    (fun k hk => ?_)
  · split
    · exact entry0_Lift1 A d k
    · rfl
  · split
    · exact entry2_Lift1 A d k
    · rfl
  · by_cases hg : le1 (graft E A) 0 (E.length - 1)
    · rw [if_pos hg, entry1_Lift1 hk,
        if_congr (cone_graft_high hE2 hA0 hAs hlow hk) rfl rfl]
      by_cases hc : le1 A 0 k
      · rw [if_pos hc, if_pos ⟨hg, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · rw [if_neg hg,
        if_neg (fun h => hg ((cone_graft_high hE2 hA0 hAs hlow hk).1 h).1)]
      omega


/-! ## 一般形: 環境マスクリフト

単一木の仮定 `HighPar` を落とすと、複合ブロックの錐は引数の上で**行 0 祖先鎖が
すべて環境の根より高い列**（`coneV`）になる。したがって一般には、リフトは引数側
に「環境しきい値 `v` のマスクリフト `mlift`」として効く（tools/probe_maskcalc.py:
錐輸送・計算則ともに 0/200000 違反。マスクが引数自身の錐と食い違う場合が
131887/200000 あるので、これは真に一般な形）。 -/

/-- 行 0 の祖先（自身を含む）がすべて行 1 で `v` を超える列。 -/
def coneV (A : TrioSeq) (v j : ℕ) : Prop :=
  ∀ y, Relation.ReflTransGen (nextrel0 A) y j → v < entry A 1 y

/-- 接ぎ木点の**手前の**行 0 祖先がすべて根より行 1 で高い。接ぎ木点そのものは
引数の根の行 1 値を担うので除く。 -/
def SiteHigh (E : TrioSeq) : Prop :=
  ∀ y, y ≠ 0 → y < E.length - 1 →
    Relation.ReflTransGen (nextrel0 E) y (E.length - 1) → entry E 1 0 < entry E 1 y

open Classical in
/-- 環境しきい値 `v` のマスクリフト。 -/
noncomputable def mlift (A : TrioSeq) (v d : ℕ) : TrioSeq :=
  (List.range A.length).map fun j =>
    ((entry A 0 j, entry A 1 j + (if coneV A v j then d else 0),
      entry A 2 j) : ℕ × ℕ × ℕ)

@[simp] theorem mlift_length (A : TrioSeq) (v d : ℕ) :
    (mlift A v d).length = A.length := by simp [mlift]

open Classical in
theorem mlift_getD {A : TrioSeq} {v d i : ℕ} (hi : i < A.length) :
    (mlift A v d).getD i (0, 0, 0)
      = ((entry A 0 i, entry A 1 i + (if coneV A v i then d else 0),
          entry A 2 i) : ℕ × ℕ × ℕ) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [mlift_length]; exact hi)]
  unfold mlift
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem entry0_mlift (A : TrioSeq) (v d i : ℕ) :
    entry (mlift A v d) 0 i = entry A 0 i := by
  show ((mlift A v d).getD i (0, 0, 0)).1 = ((A.getD i (0, 0, 0)).1 : ℕ)
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [mlift_getD hi]; rfl
  · rw [getD_out (by rw [mlift_length]; omega), getD_out hi]

theorem entry2_mlift (A : TrioSeq) (v d i : ℕ) :
    entry (mlift A v d) 2 i = entry A 2 i := by
  show ((mlift A v d).getD i (0, 0, 0)).2.2 = ((A.getD i (0, 0, 0)).2.2 : ℕ)
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [mlift_getD hi]; rfl
  · rw [getD_out (by rw [mlift_length]; omega), getD_out hi]

open Classical in
theorem entry1_mlift {A : TrioSeq} {v d i : ℕ} (hi : i < A.length) :
    entry (mlift A v d) 1 i = entry A 1 i + (if coneV A v i then d else 0) := by
  show ((mlift A v d).getD i (0, 0, 0)).2.1 = _
  rw [mlift_getD hi]

/-! ### 行 0 の鎖: 接ぎ木点までは文脈と同じ、接ぎ木点からは引数の中 -/

theorem entry0_graft_le {E A : TrioSeq} (hA0 : entry A 0 0 = 0) (hA : 0 < A.length)
    {i : ℕ} (hi : i ≤ E.length - 1) :
    entry (graft E A) 0 i = entry E 0 i := by
  rcases Nat.lt_or_ge i (E.length - 1) with h | h
  · exact entry_graft_low h
  · have h0 := entry0_graft_high (E := E) (A := A) (k := 0) hA
    rw [hA0, Nat.zero_add] at h0
    have hie : i = E.length - 1 := by omega
    rw [hie]
    simpa using h0

theorem nextrel0_graft_le {E A : TrioSeq} (hA0 : entry A 0 0 = 0) (hA : 0 < A.length)
    (hE2 : 2 ≤ E.length) {a b : ℕ} (hb : b ≤ E.length - 1) :
    nextrel0 (graft E A) a b ↔ nextrel0 E a b := by
  have hGlen : (graft E A).length = E.length - 1 + A.length := graft_length E A
  have eb : entry (graft E A) 0 b = entry E 0 b := entry0_graft_le hA0 hA hb
  unfold nextrel0
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have ea : entry (graft E A) 0 a = entry E 0 a := entry0_graft_le hA0 hA (by omega)
    refine ⟨by omega, by omega, h3, by omega, ?_⟩
    intro j hj
    have ej : entry (graft E A) 0 j = entry E 0 j :=
      entry0_graft_le hA0 hA (by omega)
    have := h5 j hj
    omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have ea : entry (graft E A) 0 a = entry E 0 a := entry0_graft_le hA0 hA (by omega)
    refine ⟨by omega, by omega, h3, by omega, ?_⟩
    intro j hj
    have ej : entry (graft E A) 0 j = entry E 0 j :=
      entry0_graft_le hA0 hA (by omega)
    have := h5 j hj
    omega

theorem rtg0_graft_le {E A : TrioSeq} (hA0 : entry A 0 0 = 0) (hA : 0 < A.length)
    (hE2 : 2 ≤ E.length) {y b : ℕ} (hb : b ≤ E.length - 1) :
    Relation.ReflTransGen (nextrel0 (graft E A)) y b
      ↔ Relation.ReflTransGen (nextrel0 E) y b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail w c hw hwc ih =>
        exact (ih (by have := hwc.2.2.1; omega)).tail
          ((nextrel0_graft_le hA0 hA hE2 hb).1 hwc)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail w c hw hwc ih =>
        exact (ih (by have := hwc.2.2.1; omega)).tail
          ((nextrel0_graft_le hA0 hA hE2 hb).2 hwc)

theorem rtg0_graft_embed {E A : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 A) a b) :
    Relation.ReflTransGen (nextrel0 (graft E A)) (E.length - 1 + a) (E.length - 1 + b) := by
  have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
  rw [graft_eq_shift, ← hd]
  exact rtg_nextrel0_lift _ _ (rtg0_shiftr01.2 h)

/-- 行 0 の孤児（深さ 0 の列）は必ずどの列の祖先鎖の末端にある。 -/
theorem exists_root_anc {A : TrioSeq} (hA0 : entry A 0 0 = 0) {j : ℕ}
    (hj : j < A.length) :
    ∃ o, o < A.length ∧ entry A 0 o = 0 ∧
      Relation.ReflTransGen (nextrel0 A) o j := by
  classical
  have hspec : entry A 0 (Nat.findGreatest (fun k => entry A 0 k = 0) j) = 0 :=
    Nat.findGreatest_spec (P := fun k => entry A 0 k = 0) (Nat.zero_le j) hA0
  have hle : Nat.findGreatest (fun k => entry A 0 k = 0) j ≤ j :=
    Nat.findGreatest_le j
  refine ⟨_, by omega, hspec, rtg0_of_window hj hle ?_⟩
  intro l hl0 hl1
  have hnp : ¬ (entry A 0 l = 0) :=
    Nat.findGreatest_is_greatest (P := fun k => entry A 0 k = 0) hl0 hl1
  rw [hspec]
  omega

/-- 接ぎ木点への行 0 の一歩は、引数の任意の深さ 0 の列への一歩と同値。 -/
theorem nextrel0_graft_site {E A : TrioSeq} (hA0 : entry A 0 0 = 0)
    (hE2 : 2 ≤ E.length) {w o : ℕ} (ho : o < A.length) (hoz : entry A 0 o = 0)
    (hw : w < E.length - 1) :
    nextrel0 (graft E A) w (E.length - 1 + o)
      ↔ nextrel0 (graft E A) w (E.length - 1) := by
  have hGlen : (graft E A).length = E.length - 1 + A.length := graft_length E A
  have hA : 0 < A.length := by omega
  have hso : entry (graft E A) 0 (E.length - 1 + o) = entry (graft E A) 0 (E.length - 1) := by
    rw [entry0_graft_high ho, hoz, Nat.zero_add, entry0_graft_le hA0 hA (le_refl _)]
  unfold nextrel0
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, by omega, hw, by rw [← hso]; exact h4, ?_⟩
    intro j hj
    rw [← hso]
    exact h5 j ⟨hj.1, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, by omega, by omega, by rw [hso]; exact h4, ?_⟩
    intro j hj
    rw [hso]
    rcases Nat.lt_or_ge j (E.length - 1) with hjs | hjs
    · exact h5 j ⟨hj.1, hjs⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = E.length - 1 + k := ⟨j - (E.length - 1), by omega⟩
      have hk : k < A.length := by omega
      have e1 : entry (graft E A) 0 (E.length - 1 + k)
          = entry A 0 k + entry E 0 (E.length - 1) := entry0_graft_high hk
      have e2 : entry (graft E A) 0 (E.length - 1) = entry E 0 (E.length - 1) :=
        entry0_graft_le hA0 hA (le_refl _)
      omega

/-- 複合ブロックでの行 0 祖先鎖の分解: 引数の中の祖先か、接ぎ木点より手前の
（＝接ぎ木点の）祖先か。 -/
theorem rtg0_graft_split {E A : TrioSeq} (hA0 : entry A 0 0 = 0) (hE2 : 2 ≤ E.length)
    {j : ℕ} (hj : j < A.length) {y : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (graft E A)) y (E.length - 1 + j)) :
    (∃ y', y = E.length - 1 + y' ∧ y' < A.length ∧
        Relation.ReflTransGen (nextrel0 A) y' j)
      ∨ (y < E.length - 1 ∧
        Relation.ReflTransGen (nextrel0 (graft E A)) y (E.length - 1)) := by
  have hGlen : (graft E A).length = E.length - 1 + A.length := graft_length E A
  have hA : 0 < A.length := by omega
  have key : ∀ b : ℕ, Relation.ReflTransGen (nextrel0 (graft E A)) y b →
      ∀ k, b = E.length - 1 + k → k < A.length →
      (∃ y', y = E.length - 1 + y' ∧ y' < A.length ∧
          Relation.ReflTransGen (nextrel0 A) y' k)
        ∨ (y < E.length - 1 ∧
          Relation.ReflTransGen (nextrel0 (graft E A)) y (E.length - 1)) := by
    intro b hb
    induction hb with
    | refl => intro k hk hkA; exact Or.inl ⟨k, hk, hkA, Relation.ReflTransGen.refl⟩
    | @tail w c hw hwc ih =>
        intro k hk hkA
        subst hk
        rcases Nat.lt_or_ge w (E.length - 1) with hws | hws
        · -- the step comes from the context: it factors through the graft point
          have hdip := hwc.2.2.2.2
          have hlow : entry A 0 k = 0 := by
            rcases Nat.eq_zero_or_pos k with rfl | hk0
            · rw [← Nat.add_zero (E.length - 1)] at hwc
              have e1 : entry (graft E A) 0 (E.length - 1 + 0)
                  = entry A 0 0 + entry E 0 (E.length - 1) := entry0_graft_high hA
              rw [hA0] at e1
              omega
            · have hmid := hdip (E.length - 1) ⟨hws, by omega⟩
              have e1 : entry (graft E A) 0 (E.length - 1 + k)
                  = entry A 0 k + entry E 0 (E.length - 1) := entry0_graft_high hkA
              have e2 : entry (graft E A) 0 (E.length - 1) = entry E 0 (E.length - 1) :=
                entry0_graft_le hA0 hA (le_refl _)
              omega
          exact Or.inr ⟨by have := rtg0_le hw; omega,
            hw.tail ((nextrel0_graft_site hA0 hE2 hkA hlow hws).1 hwc)⟩
        · obtain ⟨w', rfl⟩ : ∃ w', w = E.length - 1 + w' := ⟨w - (E.length - 1), by omega⟩
          have hw'A : w' < A.length := by have := hwc.1; omega
          have hstep : nextrel0 A w' k := by
            have hd : E.dropLast.length = E.length - 1 := List.length_dropLast
            rw [graft_eq_shift, ← hd, nextrel0_append_right, nextrel0_shiftr01] at hwc
            exact hwc
          rcases ih w' rfl hw'A with ⟨y', hy1, hy2, hy3⟩ | hr
          · exact Or.inl ⟨y', hy1, hy2, hy3.tail hstep⟩
          · exact Or.inr hr
  exact key _ h j rfl hj

/-- 逆向き: 接ぎ木点の（手前の）祖先は、引数のどの列の祖先でもある。 -/
theorem rtg0_graft_join {E A : TrioSeq} (hA0 : entry A 0 0 = 0) (hE2 : 2 ≤ E.length)
    {j y : ℕ} (hj : j < A.length) (hy : y < E.length - 1)
    (h : Relation.ReflTransGen (nextrel0 (graft E A)) y (E.length - 1)) :
    Relation.ReflTransGen (nextrel0 (graft E A)) y (E.length - 1 + j) := by
  obtain ⟨o, hoA, hoz, hoj⟩ := exists_root_anc hA0 hj
  have hend : Relation.ReflTransGen (nextrel0 (graft E A)) (E.length - 1 + o)
      (E.length - 1 + j) := rtg0_graft_embed hoj
  refine Relation.ReflTransGen.trans ?_ hend
  cases h with
  | refl => omega
  | @tail w _ hyw hws =>
      exact hyw.tail ((nextrel0_graft_site hA0 hE2 hoA hoz
        (by have := hws.2.2.1; omega)).2 hws)

/-! ### 一般の錐輸送とリフト計算則 -/

/-- **一般の錐輸送**: 複合ブロックの錐は引数の上で「接ぎ木点の手前がすべて高い
（`SiteHigh`）ならば環境マスク `coneV`、そうでなければ空」。 -/
theorem cone_graft_mask {E A : TrioSeq} (hE0 : entry E 0 0 = 0)
    (hEs : ∀ l, 0 < l → l < E.length → 0 < entry E 0 l) (hE2 : 2 ≤ E.length)
    (hA0 : entry A 0 0 = 0) {j : ℕ} (hj : j < A.length) :
    le1 (graft E A) 0 (E.length - 1 + j)
      ↔ (SiteHigh E ∧ coneV A (entry E 1 0) j) := by
  have hGlen : (graft E A).length = E.length - 1 + A.length := graft_length E A
  have hA : 0 < A.length := by omega
  have hG0 : entry (graft E A) 0 0 = 0 := by
    rw [entry_graft_low (by omega)]; exact hE0
  have hshal : ∀ l, 0 < l → l < (graft E A).length →
      entry (graft E A) 0 0 < entry (graft E A) 0 l := by
    intro l h1 h2
    rw [hG0]
    exact shallow_graft hEs hE2 l h1 h2
  have hG1 : entry (graft E A) 1 0 = entry E 1 0 := entry_graft_low (by omega)
  rw [le1_zero_iff hshal (by omega)]
  constructor
  · intro h
    refine ⟨fun y hy0 hys hchain => ?_, fun y hchain => ?_⟩
    · have hGy := (rtg0_graft_le hA0 hA hE2 (le_refl _)).2 hchain
      have := h y (rtg0_graft_join hA0 hE2 hj hys hGy) hy0
      rwa [hG1, entry_graft_low hys] at this
    · have hy' : y < A.length := by
        have := rtg0_le hchain
        omega
      have := h (E.length - 1 + y) (rtg0_graft_embed hchain) (by omega)
      rwa [hG1, entry1_graft_high] at this
  · rintro ⟨hs, hc⟩ y hchain hy0
    rw [hG1]
    rcases rtg0_graft_split hA0 hE2 hj hchain with ⟨y', rfl, hy'A, hy'⟩ | ⟨hys, hGy⟩
    · rw [entry1_graft_high]
      exact hc y' hy'
    · rw [entry_graft_low hys]
      exact hs y hy0 hys ((rtg0_graft_le hA0 hA hE2 (le_refl _)).1 hGy)

open Classical in
/-- **一般のリフト計算則**: 引数が森でも構わない。リフトは文脈側に効き、引数側
には環境しきい値 `entry E 1 0` のマスクリフトとして効く（接ぎ木点の手前が
高くないなら引数はまったく動かない）。 -/
theorem lift_graft_mask {E A : TrioSeq} (hE0 : entry E 0 0 = 0)
    (hEs : ∀ l, 0 < l → l < E.length → 0 < entry E 0 l) (hE2 : 2 ≤ E.length)
    (hA0 : entry A 0 0 = 0) (d : ℕ) :
    Lift1 (graft E A) d
      = graft (Lift1 E d) (if SiteHigh E then mlift A (entry E 1 0) d else A) := by
  refine lift_graft_of_entries hE2 (by split <;> simp) (fun k => ?_) (fun k => ?_)
    (fun k hk => ?_)
  · split
    · exact entry0_mlift A (entry E 1 0) d k
    · rfl
  · split
    · exact entry2_mlift A (entry E 1 0) d k
    · rfl
  · by_cases hg : SiteHigh E
    · rw [if_pos hg, entry1_mlift hk,
        if_congr (cone_graft_mask hE0 hEs hE2 hA0 hk) rfl rfl]
      by_cases hc : coneV A (entry E 1 0) k
      · rw [if_pos hc, if_pos ⟨hg, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · rw [if_neg hg, if_neg (fun h => hg ((cone_graft_mask hE0 hEs hE2 hA0 hk).1 h).1)]
      omega


/-! ## マスクリフトの接ぎ木分配則と `ltail` との一致

`Lift1` はブロックごとに閾値を根の行 1 値へリセットするので「接ぎ木の内側で
リフトする」が言語の外に出る（(e)-壁）。`mlift` の閾値は定数なので接ぎ木に
分配し（`mlift_graft`）、しかも機械の環境リフトはちょうど尾部のマスクリフト
である（`ltail_eq_mlift`）。 -/

/-- 接ぎ木点の手前の行 0 祖先がすべて `v` より上（マスク版の窓条件）。 -/
def SiteV (M : TrioSeq) (v : ℕ) : Prop :=
  ∀ y, y < M.length - 1 →
    Relation.ReflTransGen (nextrel0 M) y (M.length - 1) → v < entry M 1 y

theorem coneV_graft_low {M A : TrioSeq} {v i : ℕ} (hA0 : entry A 0 0 = 0)
    (hA : 0 < A.length) (hM2 : 2 ≤ M.length) (hi : i < M.length - 1) :
    coneV (graft M A) v i ↔ coneV M v i := by
  constructor
  · intro h y hy
    have hyi : y ≤ i := rtg0_le hy
    rw [← entry_graft_low (A := A) (by omega)]
    exact h y ((rtg0_graft_le hA0 hA hM2 (by omega)).2 hy)
  · intro h y hy
    have hyi : y ≤ i := rtg0_le hy
    rw [entry_graft_low (A := A) (by omega)]
    exact h y ((rtg0_graft_le hA0 hA hM2 (by omega)).1 hy)

theorem coneV_graft_high {M A : TrioSeq} {v k : ℕ} (hA0 : entry A 0 0 = 0)
    (hM2 : 2 ≤ M.length) (hk : k < A.length) :
    coneV (graft M A) v (M.length - 1 + k) ↔ (SiteV M v ∧ coneV A v k) := by
  have hA : 0 < A.length := by omega
  constructor
  · intro h
    refine ⟨fun y hys hchain => ?_, fun y hy => ?_⟩
    · have hGy := (rtg0_graft_le hA0 hA hM2 (le_refl _)).2 hchain
      have := h y (rtg0_graft_join hA0 hM2 hk hys hGy)
      rwa [entry_graft_low hys] at this
    · have := h (M.length - 1 + y) (rtg0_graft_embed hy)
      rwa [entry1_graft_high] at this
  · rintro ⟨hs, hc⟩ y hchain
    rcases rtg0_graft_split hA0 hM2 hk hchain with ⟨y', rfl, hy'A, hy'⟩ | ⟨hys, hGy⟩
    · rw [entry1_graft_high]
      exact hc y' hy'
    · rw [entry_graft_low hys]
      exact hs y hys ((rtg0_graft_le hA0 hA hM2 (le_refl _)).1 hGy)

open Classical in
/-- **マスクリフトは接ぎ木に分配する（閾値は定数のまま）**。 -/
theorem mlift_graft {M A : TrioSeq} (hA0 : entry A 0 0 = 0) (hA : 0 < A.length)
    (hM2 : 2 ≤ M.length) (v d : ℕ) :
    mlift (graft M A) v d
      = graft (mlift M v d) (if SiteV M v then mlift A v d else A) := by
  set B : TrioSeq := if SiteV M v then mlift A v d else A with hB
  have hBlen : B.length = A.length := by rw [hB]; split <;> simp
  have hMLlen : (mlift M v d).length = M.length := mlift_length M v d
  have hML1 : (mlift M v d).length - 1 = M.length - 1 := by rw [hMLlen]
  have hlen : (mlift (graft M A) v d).length = (graft (mlift M v d) B).length := by
    rw [mlift_length, graft_length, graft_length, hMLlen, hBlen]
  have hB0 : ∀ k, entry B 0 k = entry A 0 k := by
    intro k; rw [hB]; split
    · exact entry0_mlift A v d k
    · rfl
  have hB2 : ∀ k, entry B 2 k = entry A 2 k := by
    intro k; rw [hB]; split
    · exact entry2_mlift A v d k
    · rfl
  have hB1 : ∀ k, k < A.length → entry B 1 k
      = entry A 1 k + (if coneV (graft M A) v (M.length - 1 + k) then d else 0) := by
    intro k hk
    by_cases hs : SiteV M v
    · rw [hB, if_pos hs, entry1_mlift hk,
        if_congr (coneV_graft_high hA0 hM2 hk) rfl rfl]
      by_cases hc : coneV A v k
      · rw [if_pos hc, if_pos ⟨hs, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · rw [hB, if_neg hs,
        if_neg (fun h => hs ((coneV_graft_high hA0 hM2 hk).1 h).1)]
      omega
  refine List.ext_getElem hlen ?_
  intro i hi1 hi2
  rw [mlift_length, graft_length] at hi1
  rw [← entry_triple (by rw [mlift_length, graft_length]; omega),
    ← entry_triple (by rw [graft_length, hMLlen, hBlen]; omega)]
  rcases Nat.lt_or_ge i (M.length - 1) with hlo | hhi
  · have hMi : i < M.length := by omega
    have e0 : entry (mlift (graft M A) v d) 0 i = entry M 0 i := by
      rw [entry0_mlift, entry_graft_low hlo]
    have e2 : entry (mlift (graft M A) v d) 2 i = entry M 2 i := by
      rw [entry2_mlift, entry_graft_low hlo]
    have e1 : entry (mlift (graft M A) v d) 1 i
        = entry M 1 i + (if coneV M v i then d else 0) := by
      rw [entry1_mlift (by rw [graft_length]; omega), entry_graft_low hlo,
        if_congr (coneV_graft_low hA0 hA hM2 hlo) rfl rfl]
    have f0 : entry (graft (mlift M v d) B) 0 i = entry M 0 i := by
      rw [entry_graft_low (by omega), entry0_mlift]
    have f2 : entry (graft (mlift M v d) B) 2 i = entry M 2 i := by
      rw [entry_graft_low (by omega), entry2_mlift]
    have f1 : entry (graft (mlift M v d) B) 1 i
        = entry M 1 i + (if coneV M v i then d else 0) := by
      rw [entry_graft_low (by omega), entry1_mlift hMi]
    rw [e0, e1, e2, f0, f1, f2]
  · obtain ⟨k, rfl⟩ : ∃ k, i = M.length - 1 + k := ⟨i - (M.length - 1), by omega⟩
    have hkA : k < A.length := by omega
    have e0 : entry (mlift (graft M A) v d) 0 (M.length - 1 + k)
        = entry A 0 k + entry M 0 (M.length - 1) := by
      rw [entry0_mlift, entry0_graft_high hkA]
    have e2 : entry (mlift (graft M A) v d) 2 (M.length - 1 + k) = entry A 2 k := by
      rw [entry2_mlift, entry2_graft_high]
    have e1 : entry (mlift (graft M A) v d) 1 (M.length - 1 + k)
        = entry A 1 k
          + (if coneV (graft M A) v (M.length - 1 + k) then d else 0) := by
      rw [entry1_mlift (by rw [graft_length]; omega), entry1_graft_high]
    have f0 : entry (graft (mlift M v d) B) 0 (M.length - 1 + k)
        = entry A 0 k + entry M 0 (M.length - 1) := by
      rw [← hML1, entry0_graft_high (by rw [hBlen]; exact hkA), hB0, entry0_mlift]
    have f2 : entry (graft (mlift M v d) B) 2 (M.length - 1 + k) = entry A 2 k := by
      rw [← hML1, entry2_graft_high, hB2]
    have f1 : entry (graft (mlift M v d) B) 1 (M.length - 1 + k)
        = entry A 1 k
          + (if coneV (graft M A) v (M.length - 1 + k) then d else 0) := by
      rw [← hML1, entry1_graft_high, hB1 k hkA, hML1]
    rw [e0, e1, e2, f0, f1, f2]

/-! ### 環境リフトはマスクリフト -/

theorem rtg0_cons_unlift {p : ℕ × ℕ × ℕ} {R : TrioSeq} {y b : ℕ} (hy : 1 ≤ y)
    (h : Relation.ReflTransGen (nextrel0 (p :: R)) y b) :
    ∀ b', b = 1 + b' → Relation.ReflTransGen (nextrel0 R) (y - 1) b' := by
  induction h with
  | refl => intro b' hb'; rw [show y - 1 = b' from by omega]
  | @tail w c hw hwc ih =>
      intro b' hb'
      subst hb'
      have hwy : y ≤ w := rtg0_le hw
      obtain ⟨w', rfl⟩ : ∃ w', w = 1 + w' := ⟨w - 1, by omega⟩
      have hstep : nextrel0 R w' b' := by
        have h := nextrel0_append_right [p] R w' b'
        simp only [List.length_singleton, List.singleton_append] at h
        exact h.1 hwc
      exact (ih w' rfl).tail hstep

theorem rtg0_cons_lift {p : ℕ × ℕ × ℕ} {R : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 R) a b) :
    Relation.ReflTransGen (nextrel0 (p :: R)) (1 + a) (1 + b) := by
  have := rtg_nextrel0_lift [p] R h
  simpa using this

/-- **植えた根の錐は尾部の環境マスク**: `argOK` な尾部の上では、根の行 1 錐は
閾値 `v` のマスク `coneV` にほかならない。 -/
theorem le1_cons_iff_coneV {v z : ℕ} {R : TrioSeq} (hR : argOK R) {j : ℕ}
    (hj : j < R.length) :
    le1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 (1 + j) ↔ coneV R v j := by
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
  rw [le1_zero_iff hshal (by omega), hN1]
  constructor
  · intro h y hy
    have hy1 : entry N 1 (1 + y) = entry R 1 y := by
      rw [hN, show 1 + y = y + 1 from by omega, entry_cons]
    rw [← hy1]
    exact h (1 + y) (rtg0_cons_lift hy) (by omega)
  · intro h y hchain hy0
    obtain ⟨y', rfl⟩ : ∃ y', y = 1 + y' := ⟨y - 1, by omega⟩
    have hy1 : entry N 1 (1 + y') = entry R 1 y' := by
      rw [hN, show 1 + y' = y' + 1 from by omega, entry_cons]
    rw [hy1]
    have hun := rtg0_cons_unlift (y := 1 + y') (by omega) hchain j rfl
    rw [show 1 + y' - 1 = y' from by omega] at hun
    exact h y' hun

open Classical in
/-- **機械の環境リフトはマスクリフト**: `Lift1 ((0,v,z) :: R) t` は根を `t` 上げ、
尾部を閾値 `v` でマスクリフトしたものに等しい（`argOK R` が必要: 尾部に深さ 0 の
列があると破れる — tools/probe_ltailmask.py）。ゆえに機械の義務言語は
**「植えた根 + マスクリフトした尾部」**であり、`mlift_graft` によって
接ぎ木で閉じる。 -/
theorem lift_cons_eq_mlift {v z t : ℕ} {R : TrioSeq} (hR : argOK R) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t
      = ((0, v + t, z) : ℕ × ℕ × ℕ) :: mlift R v t := by
  set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: R with hN
  have hNlen : N.length = R.length + 1 := by rw [hN]; simp
  have hRlen : (((0, v + t, z) : ℕ × ℕ × ℕ) :: mlift R v t).length
      = R.length + 1 := by simp
  have hn0 : entry N 0 0 = 0 := based_cons v z R
  have hn1 : entry N 1 0 = v := rfl
  have hn2 : entry N 2 0 = z := rfl
  refine List.ext_getElem (by rw [Lift1_length, hNlen, hRlen]) ?_
  intro i hi1 hi2
  rw [Lift1_length, hNlen] at hi1
  rw [← entry_triple (X := Lift1 N t) (by rw [Lift1_length, hNlen]; omega),
    ← entry_triple (X := ((0, v + t, z) : ℕ × ℕ × ℕ) :: mlift R v t)
      (by rw [hRlen]; omega)]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hc : le1 N 0 0 := ⟨by rw [hNlen]; omega, by rw [hNlen]; omega, .refl⟩
    have e0 : entry (Lift1 N t) 0 0 = 0 := by rw [entry0_Lift1, hn0]
    have e2 : entry (Lift1 N t) 2 0 = z := by rw [entry2_Lift1, hn2]
    have e1 : entry (Lift1 N t) 1 0 = v + t := by
      rw [entry1_Lift1 (by rw [hNlen]; omega), if_pos hc, hn1]
    rw [e0, e1, e2]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    have hjR : j < R.length := by omega
    have hidx : (1 : ℕ) + j = j + 1 := by omega
    have hc := le1_cons_iff_coneV (v := v) (z := z) hR hjR
    have e0 : entry (Lift1 N t) 0 (1 + j) = entry R 0 j := by
      rw [entry0_Lift1, hN, hidx, entry_cons]
    have e2 : entry (Lift1 N t) 2 (1 + j) = entry R 2 j := by
      rw [entry2_Lift1, hN, hidx, entry_cons]
    have e1 : entry (Lift1 N t) 1 (1 + j)
        = entry R 1 j + (if coneV R v j then t else 0) := by
      rw [entry1_Lift1 (by rw [hNlen]; omega), if_congr hc rfl rfl, hN, hidx,
        entry_cons]
    have f0 : entry (((0, v + t, z) : ℕ × ℕ × ℕ) :: mlift R v t) 0 (1 + j)
        = entry R 0 j := by rw [hidx, entry_cons, entry0_mlift]
    have f2 : entry (((0, v + t, z) : ℕ × ℕ × ℕ) :: mlift R v t) 2 (1 + j)
        = entry R 2 j := by rw [hidx, entry_cons, entry2_mlift]
    have f1 : entry (((0, v + t, z) : ℕ × ℕ × ℕ) :: mlift R v t) 1 (1 + j)
        = entry R 1 j + (if coneV R v j then t else 0) := by
      rw [hidx, entry_cons, entry1_mlift hjR]
    rw [e0, e1, e2, f0, f1, f2]


open Classical in
/-- **機械の義務言語のマスク表示**: 植えた根の下の接ぎ木ブロックのリフトは、
「根を上げ、文脈をマスクリフトし、引数をマスクリフトする」に等しい。
`Lift1` が閉じなかった操作（接ぎ木の内側のリフト）が、マスク表示では
そのまま閉じている。 -/
theorem lift_plant_graft {M y : TrioSeq} {v z t : ℕ} (hM : argOK M) (hMne : M ≠ [])
    (hM2 : 2 ≤ M.length) (hby : based y) (hyne : y ≠ []) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t
      = ((0, v + t, z) : ℕ × ℕ × ℕ)
        :: graft (mlift M v t) (if SiteV M v then mlift y v t else y) := by
  rw [lift_cons_eq_mlift (argOK_graft hMne hM y),
    mlift_graft hby (List.length_pos_iff.mpr hyne) hM2]

end TRIO
