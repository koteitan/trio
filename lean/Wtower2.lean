/-
Wtower2.lean: **行 2 塔をリフト無し `Wstar` のまま解く** — (WL) を法として。

`towerGraft2_holds`（Wset.lean）は塔の帰納を「すべてのリフト量 `s` について」
強めて回している。そのために `Wstar2`（リフト閉）が要り、そこから `GraftAll`
→ `GX` → `CoreCap` の全体が生えた。

しかし塔が実際に消費するのは **1 つの具体的なリフト `d1 = 行1(末尾) - v`** だけ
であり、段の勘定は

```
prev ∈ W (2v+z)  --(WL)-->  Lift1 prev d1 ∈ W (2v+z+2*d1) = W (2w+z) ⊆ W m
                              （w = 行1(末尾), z < 行2(末尾) ⟹ 2w+z ≤ m）
```

でちょうど閉じる。したがって **(WL) さえあれば `Wstar`（リフト無し）のままで
`TowerGraft2` が証明でき、`Wstar2` / `GX` / `CoreCap` は不要**になる。

(WL) は `tools/probe_lift.py` で 18300 例すべて**等号**で成立
（`minstage (Lift1 X d) = minstage X + 2d`）。階段リフト版
（`Wslift.slift_mem_W_tight` / `mlift_mem_W`）は核なしで証明済み。
-/
import Wset
import Wslift

namespace TRIO

open Wset
open Classical

/-- **(WL)**: the ambient root lift costs exactly `2 * d` stages.  Measured with
equality on 18300 instances (`tools/probe_lift.py`); the staircase-lift version
is proved (`Wslift.mlift_mem_W`). -/
def LiftStage : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), X ∈ W m → Lift1 X d ∈ W (m + 2 * d)

/-! ## (WL) を「親のある場合」だけに縮める

`oper` の `Pred` 分岐（末尾列が全零、または親なし）は根リフトと**可換**である:
`Lift1` は行 2 を動かさず、行 1 も錐の列しか動かさないので `srow` を保ち
（`srow_Lift1`）、`hasParent` も保つ（`hasParent_Lift1`）。したがって
`Aop` の節 3（`domT` ⟹ 親なし）と節 2 の親なし枝は自動で流れ、(WL) は
**末尾列に親がある場合**だけに縮む。 -/

theorem Lift1_of_length_one {X : TrioSeq} (h1 : X.length = 1) (d : ℕ) :
    Lift1 X d = [((entry X 0 0, entry X 1 0 + d, entry X 2 0) : ℕ × ℕ × ℕ)] := by
  have hle : le1 X 0 0 := le1_refl (by omega)
  unfold Lift1
  rw [h1, show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil, if_pos hle]

/-- **The `Pred` branches commute with the root lift.** -/
theorem lift_oper_of_noParent {X : TrioSeq} {d n : ℕ} (h2 : 2 ≤ X.length)
    (hnp : ¬ hasParent X (srow X (X.length - 1)) (X.length - 1)) :
    (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d := by
  classical
  have hlen : (Lift1 X d).length = X.length := Lift1_length X d
  have hL : X.length - 1 ≠ 0 := by omega
  have hnp' : ¬ hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlen, srow_Lift1 hL, hasParent_Lift1]
    exact hnp
  have hpredX : X⟦n⟧ = Pred X := by
    by_cases hz : entry X 0 (X.length - 1) = 0 ∧ entry X 1 (X.length - 1) = 0 ∧
        entry X 2 (X.length - 1) = 0
    · exact oper_eq_pred_of_zero n hL hz
    · exact oper_eq_pred_of_noParent n hL hz hnp
  have hpredL : (Lift1 X d)⟦n⟧ = Pred (Lift1 X d) := by
    by_cases hz : entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
        entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
        entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0
    · exact oper_eq_pred_of_zero n (by rw [hlen]; exact hL) hz
    · exact oper_eq_pred_of_noParent n (by rw [hlen]; exact hL) hz hnp'
  rw [hpredX, hpredL]
  unfold Pred
  rw [if_neg (by rw [hlen]; omega), if_neg (by omega), Lift1_dropLast]

/-- **(WL), parented residue**: the only case the lift law still needs. -/
def LiftStageParented : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), 2 ≤ X.length →
    hasParent X (srow X (X.length - 1)) (X.length - 1) →
    (∀ n, 1 ≤ n → Lift1 (X⟦n⟧) d ∈ W (m + 2 * d)) →
    ∀ n, 1 ≤ n → (Lift1 X d)⟦n⟧ ∈ W (m + 2 * d)

/-- **(WL) reduces to the parented case.**  Clause 1 and the one-column roots
are stage arithmetic, clause 3 forces `¬ hasParent` (`domT`), and the parentless
branch of clause 2 commutes by `lift_oper_of_noParent`. -/
theorem liftStage_of_parented (h : LiftStageParented) : LiftStage := by
  intro m d
  have hsub : W m ⊆ {X : TrioSeq | Lift1 X d ∈ W (m + 2 * d)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hdom, hgr⟩)
    · rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show Lift1 ([] : TrioSeq) d ∈ W (m + 2 * d)
        simpa using W_nil (m + 2 * d)
      · have h1 : X.length = 1 := by omega
        show Lift1 X d ∈ W (m + 2 * d)
        rw [Lift1_of_length_one h1 d]
        have hbc : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hbc.1, hbc.2]
        exact singleton_mem_W (by omega)
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show Lift1 X d ∈ W (m + 2 * d)
        by_cases hp : hasParent X (srow X (X.length - 1)) (X.length - 1)
        · exact mem_of_oper_mem (h m d X hbig hp (fun n hn => hop n hn))
        · refine mem_of_oper_mem (fun n hn => ?_)
          rw [lift_oper_of_noParent hbig hp]
          exact hop n hn
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hdom
          exact not_domT_nil m' hdom
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlv := hdom.1
        rw [show X.length - 1 = 0 from by omega] at hlv
        unfold lev at hlv
        show Lift1 X d ∈ W (m + 2 * d)
        rw [Lift1_of_length_one h1 d]
        exact singleton_mem_W (by omega)
      · show Lift1 X d ∈ W (m + 2 * d)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [lift_oper_of_noParent hbig hdom.2]
        exact aop_clause3_to_clause2 hbig hdom hgr n hn
  exact fun X hX => hsub hX

/-! ## 親ありの残差の 4 分割

計測（`GRAFTALL-PLAN` §1.9.51）では `Lift1` と `oper` の非可換は
**バッドルートの親 `j0` が `0` かつ崩壊行 `i1 ≤ 1`** の場合だけであった。
以下はその場合分けを Lean 側で固定するもので、各枝を個別に埋めれば
`LiftStageParented`、したがって (WL) が得られる。 -/

/-- The parented residue restricted to a class `C` of sequences. -/
def LSPOn (C : TrioSeq → Prop) : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), 2 ≤ X.length →
    hasParent X (srow X (X.length - 1)) (X.length - 1) → C X →
    (∀ n, 1 ≤ n → Lift1 (X⟦n⟧) d ∈ W (m + 2 * d)) →
    ∀ n, 1 ≤ n → (Lift1 X d)⟦n⟧ ∈ W (m + 2 * d)

theorem srow_cases (X : TrioSeq) (j : ℕ) :
    srow X j = 0 ∨ srow X j = 1 ∨ srow X j = 2 := by
  unfold srow
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

/-- The bad root's parent index of `X`. -/
noncomputable def badPar (X : TrioSeq) : ℕ :=
  parent X (srow X (X.length - 1)) (X.length - 1)

/-- **The four branches cover the parented residue.**  `1 ≤ badPar X` (the
window misses the head) and `badPar X = 0` with each of the three collapse rows.
Measurement says the first two branches commute with the lift; the open ones are
`badPar X = 0` with `srow ≤ 1`. -/
theorem liftStageParented_of_cases
    (hpos : LSPOn (fun X => 1 ≤ badPar X))
    (hs2 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 2))
    (hs0 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 0))
    (hs1 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 1)) :
    LiftStageParented := by
  intro m d X h2 hp hop n hn
  rcases Nat.eq_zero_or_pos (badPar X) with h0 | hposX
  · rcases srow_cases X (X.length - 1) with hsr | hsr | hsr
    · exact hs0 m d X h2 hp ⟨h0, hsr⟩ hop n hn
    · exact hs1 m d X h2 hp ⟨h0, hsr⟩ hop n hn
    · exact hs2 m d X h2 hp ⟨h0, hsr⟩ hop n hn
  · exact hpos m d X h2 hp hposX hop n hn

/-! ### 枝 `badPar = 0, i1 = 0`: コピーが同一なので可換性が要らない

`i1 = 0` では `d0 = d1 = 0` なので `oper` のコピーは**完全に同一**であり、
`X⟦n⟧` は `X.dropLast` を `n` 個並べたもの、`(Lift1 X d)⟦n⟧` は
`Lift1 (X.dropLast) d = Lift1 (X⟦1⟧) d` を `n` 個並べたものになる。よって
`W_flatMap_copies` がそのまま効く（`rsum` 条件は `nextrel0` の no-dip 節から）。 -/

theorem gcopy_flat (M : TrioSeq) (r L k : ℕ) : gcopy M r L 0 0 k = seg M r L := by
  unfold gcopy seg
  refine List.map_congr_left ?_
  intro j _
  simp

theorem gcopies_flat (M : TrioSeq) (r L n : ℕ) :
    gcopies M r L 0 0 n = (List.range n).flatMap fun _ => seg M r L := by
  unfold gcopies
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_flat M r L k

open Classical in
/-- The expansion of a length-`≥ 2` block whose bad root sits in row 0 with the
head as its parent: `n` literal copies of the peel. -/
theorem oper_of_srow0_par0 {X : TrioSeq} (h2 : 2 ≤ X.length)
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1))
    (hbp : parent X (srow X (X.length - 1)) (X.length - 1) = 0)
    (hsr : srow X (X.length - 1) = 0) (n : ℕ) :
    X⟦n⟧ = (List.range n).flatMap fun _ => X.dropLast := by
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn0 : nextrel0 X 0 (X.length - 1) := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  have hpos : 0 < entry X 0 (X.length - 1) := by
    have := hn0.2.2.2.1
    omega
  have hz : ¬ (entry X 0 (X.length - 1) = 0 ∧ entry X 1 (X.length - 1) = 0 ∧
      entry X 2 (X.length - 1) = 0) := by
    rintro ⟨h0, -, -⟩; omega
  have hseg : seg X 0 (X.length - 1) = X.dropLast := by
    rw [seg_zero_eq_take X (show X.length - 1 ≤ X.length by omega),
      ← List.dropLast_eq_take]
  rw [oper_gcopies n (by omega) hz hp, hbp, hsr]
  rw [if_neg (by omega), if_neg (by omega), List.take_zero, Nat.sub_zero,
    gcopies_flat, List.nil_append, hseg]

open Classical in
/-- **Branch `badPar = 0`, collapse row `0`.** -/
theorem lspOn_srow0 :
    LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 0) := by
  classical
  rintro m d X h2 hp ⟨hbp, hsr⟩ hop n hn
  unfold badPar at hbp
  -- the peel is a `W`-member at the bumped stage
  have hQ : Lift1 X.dropLast d ∈ W (m + 2 * d) := by
    have h1 := hop 1 le_rfl
    rwa [oper_of_srow0_par0 h2 hp hbp hsr 1, show
      ((List.range 1).flatMap fun _ => X.dropLast) = X.dropLast from by simp] at h1
  -- the head is the shallowest column of the peel
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn0 : nextrel0 X 0 (X.length - 1) := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  have hdeep : ∀ i, i < X.length - 1 → entry X 0 0 ≤ entry X 0 i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact le_rfl
    · have := hn0.2.2.2.2 i ⟨hipos, hi⟩
      have hlt := hn0.2.2.2.1
      omega
  have hhead : entry (Lift1 X.dropLast d) 0 0 = entry X 0 0 := by
    rw [entry0_Lift1, List.dropLast_eq_take,
      Wset.entry_take (show (0 : ℕ) < X.length - 1 by omega)]
  have hQr : ∀ p ∈ Lift1 X.dropLast d,
      entry (Lift1 X.dropLast d) 0 0 ≤ p.1 := by
    intro p hpm
    rw [hhead]
    unfold Lift1 at hpm
    rw [List.mem_map] at hpm
    obtain ⟨i, hi, rfl⟩ := hpm
    rw [List.mem_range, List.length_dropLast] at hi
    show entry X 0 0 ≤ entry X.dropLast 0 i
    rw [List.dropLast_eq_take, Wset.entry_take (show i < X.length - 1 by omega)]
    exact hdeep i (by omega)
  -- the lifted block expands to `n` copies of the lifted peel
  have hsrL : srow (Lift1 X d) ((Lift1 X d).length - 1) = 0 := by
    rw [Lift1_length, srow_Lift1 (by omega)]
    exact hsr
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [Lift1_length, srow_Lift1 (by omega), hasParent_Lift1]
    exact hp
  have hbpL : parent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) = 0 := by
    rw [Lift1_length, srow_Lift1 (by omega), parent_Lift1]
    exact hbp
  rw [oper_of_srow0_par0 (by rw [Lift1_length]; omega) hpL hbpL hsrL n,
    Lift1_dropLast]
  exact W_flatMap_copies hQ hQr n

/-! ### 枝 `i1 = 2`: リフトはコピー塊の周期マスクになる

`gexp` の成分は `gexp_getD_mir` で明示的に書けるので、`Lift1` を先にかけた
コピー塊は「コピー塊に周期マスク `glift` をかけたもの」に一致する。これは
`D0`、`D1` を固定した**純粋な計算**で、`i1` にも親の位置にも依らない。 -/

theorem getElem_eq_getD' {l : TrioSeq} {i : ℕ} (h : i < l.length) :
    l[i] = l.getD i ((0, 0, 0) : ℕ × ℕ × ℕ) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

open Classical in
/-- **The root lift of a copies block is the block's periodic mask lift.** -/
theorem gexp_lift_eq_glift (X : TrioSeq) (L D0 D1 n d : ℕ)
    (hlen : 0 + L + 1 = X.length) (hLpos : 0 < L) :
    gexp (Lift1 X d) 0 L D0 D1 n = glift X L 0 d (gexp X 0 L D0 D1 n) := by
  classical
  have hlenL : 0 + L + 1 = (Lift1 X d).length := by rw [Lift1_length]; exact hlen
  have hlenA : (gexp (Lift1 X d) 0 L D0 D1 n).length = 0 + n * L :=
    gexp_length hlenL
  have hlenB : (glift X L 0 d (gexp X 0 L D0 D1 n)).length = 0 + n * L := by
    rw [glift_length]; exact gexp_length hlen
  refine List.ext_getElem (by rw [hlenA, hlenB]) ?_
  intro i h1 h2
  rw [hlenA] at h1
  obtain ⟨k, q, hk, hq, rfl⟩ := index_decomp hLpos (show i < n * L by omega)
  have hqL : q < X.length := by omega
  have hidx : (k * L + q) % L = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hq
  have hA := gexp_getD_mir (M := Lift1 X d) (j0 := 0) (Lb := L) (d0 := D0)
    (d1 := D1) (n := n) hlenL hk hq
  have hB := gexp_getD_mir (M := X) (j0 := 0) (Lb := L) (d0 := D0)
    (d1 := D1) (n := n) hlen hk hq
  rw [Nat.zero_add, Nat.zero_add] at hA hB
  have hiff : (le1 (Lift1 X d) 0 q) = (le1 X 0 q) := propext le1_Lift1
  have hgetA : (gexp (Lift1 X d) 0 L D0 D1 n)[k * L + q]
      = (entry X 0 q + k * D0,
         entry X 1 q + (if le1 X 0 q then d else 0)
           + (if le1 X 0 q then k * D1 else 0),
         entry X 2 q) := by
    rw [getElem_eq_getD' (by omega), hA, entry0_Lift1, entry2_Lift1,
      entry1_Lift1 hqL, hiff]
  have e0 : entry (gexp X 0 L D0 D1 n) 0 (k * L + q) = entry X 0 q + k * D0 := by
    show ((gexp X 0 L D0 D1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = _
    rw [hB]
  have e1 : entry (gexp X 0 L D0 D1 n) 1 (k * L + q)
      = entry X 1 q + (if le1 X 0 q then k * D1 else 0) := by
    show ((gexp X 0 L D0 D1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 = _
    rw [hB]
  have e2 : entry (gexp X 0 L D0 D1 n) 2 (k * L + q) = entry X 2 q := by
    show ((gexp X 0 L D0 D1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 = _
    rw [hB]
  have hgetB : (glift X L 0 d (gexp X 0 L D0 D1 n))[k * L + q]
      = (entry X 0 q + k * D0 + 0,
         entry X 1 q + (if le1 X 0 q then k * D1 else 0)
           + (if le1 X 0 q then d else 0),
         entry X 2 q) := by
    unfold glift
    rw [List.getElem_map, List.getElem_range, hidx, e0, e1, e2]
  rw [hgetA, hgetB]
  refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) rfl)

open Classical in
/-- **Branch `badPar = 0`, collapse row `2`**: here the lift commutes with the
expansion.  `gexp_lift_eq_glift` turns the lifted expansion into the periodic
mask lift, and `glift_eq_Lift1` identifies that mask with the intrinsic cone
(this is where `0 < d0` and `0 < d1`, i.e. the row-2 collapse, are used). -/
theorem lspOn_srow2 :
    LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 2) := by
  classical
  rintro m d X h2 hp ⟨hbp, hsr⟩ hop n hn
  unfold badPar at hbp
  set L : ℕ := X.length - 1 with hLdef
  have hLpos : 0 < L := by omega
  have hlen : 0 + L + 1 = X.length := by omega
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn2 : nextrel2 X 0 L := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hcone : le1 X 0 L := hn2.2.2.2.2.1
  have hup : ∀ l, 0 < l → l ≤ L → entry X 0 0 < entry X 0 l :=
    window_of_rtg0 (rtg0_of_rtg1 hcone.2.2) (by omega)
  have hlt0 : entry X 0 0 < entry X 0 L := hup L hLpos le_rfl
  set D0 : ℕ := entry X 0 L - entry X 0 0 with hD0
  set D1 : ℕ := entry X 1 L - entry X 1 0 with hD1
  have hd0pos : 0 < D0 := by omega
  have hd0e : entry X 0 L = entry X 0 0 + D0 := by omega
  have hd1pos : 0 < D1 := by
    have := le1_entry1_lt hcone (by omega)
    omega
  have hz : ¬ (entry X 0 L = 0 ∧ entry X 1 L = 0 ∧ entry X 2 L = 0) := by
    rintro ⟨h0, -, -⟩; omega
  have hgexpX : X⟦n⟧ = gexp X 0 L D0 D1 n := by
    have h := oper_eq_gexp (M := X) n (by omega) hz hp hbp
    rw [hsr, if_pos (by omega : 0 < 2), if_pos (by omega : 1 < 2)] at h
    exact h
  -- the same data for the lifted block
  have hlenL : (Lift1 X d).length = X.length := Lift1_length X d
  have hsrL : srow (Lift1 X d) ((Lift1 X d).length - 1) = 2 := by
    rw [hlenL, srow_Lift1 (by omega)]; exact hsr
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlenL, srow_Lift1 (by omega), hasParent_Lift1]; exact hp
  have hbpL : parent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) = 0 := by
    rw [hlenL, srow_Lift1 (by omega), parent_Lift1]; exact hbp
  have hzL : ¬ (entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0) := by
    rw [hlenL, ← hLdef, entry0_Lift1]
    rintro ⟨h0, -, -⟩; omega
  have hE1L : entry (Lift1 X d) 1 L = entry X 1 L + d := by
    rw [entry1_Lift1 (by omega), if_pos hcone]
  have hE10 : entry (Lift1 X d) 1 0 = entry X 1 0 + d := by
    rw [entry1_Lift1 (by omega), if_pos (le1_refl (by omega))]
  have hD0eq : entry (Lift1 X d) 0 L - entry (Lift1 X d) 0 0 = D0 := by
    rw [entry0_Lift1, entry0_Lift1, hD0]
  have hD1eq : entry (Lift1 X d) 1 L - entry (Lift1 X d) 1 0 = D1 := by
    rw [hE1L, hE10, hD1]; omega
  have hgexpL : (Lift1 X d)⟦n⟧ = gexp (Lift1 X d) 0 L D0 D1 n := by
    have h := oper_eq_gexp (M := Lift1 X d) n (by rw [hlenL]; omega) hzL hpL hbpL
    rw [hsrL, if_pos (by omega : 0 < 2), if_pos (by omega : 1 < 2), hlenL,
      ← hLdef, hD0eq, hD1eq] at h
    exact h
  rw [hgexpL, gexp_lift_eq_glift X L D0 D1 n d hlen hLpos, ← hgexpX,
    glift_eq_Lift1 (by omega) hgexpX hup hd0pos hd0e hd1pos hcone]
  exact hop n hn

/-! ### 枝 `1 ≤ badPar` に向けて: 錐輸送の易しい半分

`1 ≤ badPar` の可換性に要るのは「`X⟦n⟧` の**添字 0 からの**錐」であり、
`gexp_guard_transport` が運ぶ「`j0` からの錐」とは `j0 ≥ 1` では一致しない
（§1.9.60）。頭 `M.take j0` の部分だけは前置局所性（`le1_take`）で片付く。 -/

theorem le1_gexp_low {M : TrioSeq} {j0 Lb d0 d1 n p : ℕ}
    (hj0 : j0 ≤ M.length) (hp : p < j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 p ↔ le1 M 0 p := by
  have hlent : (M.take j0).length = j0 := by rw [List.length_take]; omega
  have htake : (gexp M j0 Lb d0 d1 n).take j0 = M.take j0 := by
    unfold gexp
    exact List.take_left' hlent
  have hj0len : j0 ≤ (gexp M j0 Lb d0 d1 n).length := by
    unfold gexp
    rw [List.length_append, hlent]
    omega
  rw [← le1_take hj0len hp, htake, le1_take hj0 hp]

/-- **The row-2 tower falls to (WL) over the LIFT-FREE `Wstar`.**  The tower's
induction only ever needs the single lift `d1`, so the `∀ s` strengthening (and
with it `Wstar2`, `GraftAll`, `GX`) is unnecessary once the stage law is
available. -/
theorem towerGraft2_of_liftStage (hWL : LiftStage) : Wset.TowerGraft2 := by
  classical
  intro v z m a R hR hRne hz1 hva hd hi1 hgr hpM n _
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  have hroot2 : entry M 2 0 = z := by rw [hMdef]; simp [entry, hp0]
  have hnr := parent_nextR hpM'
  rw [hpar0, hsrM] at hnr
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 M 0 (M.length - 1) := hn2.2.2.2.2.1
  have hwv : v < entry R 1 (R.length - 1) := by
    have := le1_entry1_lt hle1lp (by omega)
    rw [hroot1, hMlen, hE 1] at this
    exact this
  have hz2 : z < entry R 2 (R.length - 1) := by
    have := hn2.2.2.2.1
    rw [hroot2, hMlen, hE 2] at this
    exact this
  set d1 : ℕ := entry R 1 (R.length - 1) - v with hd1
  have hlev := hd.1
  unfold lev at hlev
  have hbound : 2 * v + z + 2 * d1 ≤ m := by rw [hd1]; omega
  have hM0 : M⟦0⟧ = [] := by
    rw [oper_bad_unfold 0 hL hzz hpM', hpar0]
    simp
  have hstep : ∀ j, M⟦j + 1⟧ = p0 :: graft R (Lift1 (M⟦j⟧) d1) := by
    intro j
    rw [hd1]
    exact oper_cons_tower2 hR hRne hd hi1 hpM
  have hbased : ∀ j, based (M⟦j⟧) := by
    intro j
    cases j with
    | zero => rw [hM0]; exact based_nil
    | succ j => rw [hstep j]; exact based_cons v z _
  have key : ∀ j : ℕ, M⟦j⟧ ∈ W (2 * v + z) := by
    intro j
    induction j with
    | zero => rw [hM0]; exact W_nil _
    | succ j ih =>
        have hmem : Lift1 (M⟦j⟧) d1 ∈ W (2 * v + z + 2 * d1) := hWL _ _ _ ih
        have hmem' : Lift1 (M⟦j⟧) d1 ∈ W m := W_mono hbound hmem
        have hb : based (Lift1 (M⟦j⟧) d1) := based_Lift1 _ (hbased j)
        rw [hstep j]
        exact hgr _ hmem' hb (argOK_graft hRne hR _) v z (2 * v + z) hz1
          (le_refl _)
  exact W_mono hva (key n)

/-! ### 添字 0 からの錐輸送（`d0 > 0` の枝）

`1 ≤ badPar` の可換性 `(Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d` を列ごとに開くと、
頭の部分は `le1_gexp_low` で片付き、コピー領域には

```
(T0)   le1 (gexp M j0 Lb d0 d1 n) 0 (j0 + (k*Lb + q))  ↔  le1 M 0 (j0 + q)
```

だけが残る。`gexp_guard_transport` が運ぶのは `j0` からの錐なので、`j0 ≥ 1` では
これとは別物である（§1.9.60）。計測 `tools/probe_cone0.py`: 1812 ホスト・
85680 例で違反 0。

証明の骨格は次の切断である。窓 `(j0, j0+Lb]` の行 0 値はすべて `entry M 0 j0`
より真に大きい（`hup`）ので、**行 0 の鎖は窓に入る前に必ず `j0` を通る**。
切断の下側は接頭辞局所性（`le1_gexp_le`）でホストに戻り、上側は
`gexp_chain_inversion` で鏡映に分解する。ガードが立った位置では
`le1 M j0 ·` から行 1 値がすでに `entry M 1 j0` を超えているので、乗るリフト
`k*d1` は不等式を壊さない。 -/

/-- **A row-0 edge cannot jump over `j0`.**  If every column of `(j0, B]` sits
strictly above `j0` in row 0, then a `nextrel0` chain starting at or below `j0`
and ending inside the window factors through `j0` itself. -/
theorem rtg0_split_at {A : TrioSeq} {j0 B : ℕ}
    (hgt : ∀ l, j0 < l → l ≤ B → entry A 0 j0 < entry A 0 l)
    {a p : ℕ} (h : Relation.ReflTransGen (nextrel0 A) a p) (ha : a ≤ j0) :
    j0 ≤ p → p ≤ B →
      Relation.ReflTransGen (nextrel0 A) a j0 ∧
        Relation.ReflTransGen (nextrel0 A) j0 p := by
  induction h with
  | refl =>
      intro hp0 _
      have hj : a = j0 := by omega
      subst hj
      exact ⟨.refl, .refl⟩
  | @tail c p' hac hcp ih =>
      intro hp0 hp1
      have hclt : c < p' := hcp.2.2.1
      rcases Nat.lt_or_ge c j0 with hcj | hcj
      · rcases Nat.eq_or_lt_of_le hp0 with hj | hj
        · have hp'j : p' = j0 := by omega
          subst hp'j
          exact ⟨hac.tail hcp, .refl⟩
        · exfalso
          have hnodip := hcp.2.2.2.2 j0 ⟨hcj, hj⟩
          have := hgt p' hj hp1
          omega
      · obtain ⟨h1, h2⟩ := ih hcj (by omega)
        exact ⟨h1, h2.tail hcp⟩

/-- The copy-`0` root of the expansion is the host's bad root verbatim. -/
theorem gexp_getD_root {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) :
    (gexp M j0 Lb d0 d1 n).getD j0 (0, 0, 0) = M.getD j0 (0, 0, 0) := by
  have h := gexp_getD_mir (M := M) (j0 := j0) (Lb := Lb) (d0 := d0) (d1 := d1)
    (n := n) (k := 0) (q := 0) hlen hn hLb
  simp only [Nat.zero_mul, Nat.add_zero, ite_self] at h
  rw [h, getD_eq_entries]

/-- The expansion agrees with the host on the closed prefix `[0, j0]`. -/
theorem gexp_take_succ {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) :
    (gexp M j0 Lb d0 d1 n).take (j0 + 1) = M.take (j0 + 1) := by
  have hlenG : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  refine List.ext_getElem ?_ ?_
  · rw [List.length_take, List.length_take, hlenG]; omega
  · intro i hi1 hi2
    rw [List.length_take, hlenG] at hi1
    rw [List.getElem_take, List.getElem_take,
      getElem_eq_getD' (by omega), getElem_eq_getD' (by omega)]
    rcases Nat.lt_or_ge i j0 with h | h
    · exact gexp_getD_low hlen h
    · have hij : i = j0 := by omega
      subst hij
      exact gexp_getD_root hlen hLb hn

/-- **Closed-prefix locality of the `0`-cone** (the `p ≤ j0` strengthening of
`le1_gexp_low`; the bad root itself is included). -/
theorem le1_gexp_le {M : TrioSeq} {j0 Lb d0 d1 n p : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) (hp : p ≤ j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 p ↔ le1 M 0 p := by
  have hlenG : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  rw [← le1_take (X := gexp M j0 Lb d0 d1 n) (l := j0 + 1) (by omega) (by omega),
    gexp_take_succ hlen hLb hn,
    le1_take (X := M) (l := j0 + 1) (by omega) (by omega)]

/-- The row-0 profile of the copies region stays strictly above the bad root. -/
theorem gexp_entry0_gt_root {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) :
    ∀ l, j0 < l → l ≤ j0 + n * Lb - 1 →
      entry (gexp M j0 Lb d0 d1 n) 0 j0 < entry (gexp M j0 Lb d0 d1 n) 0 l := by
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  intro l hl0 hl1
  rw [gexp_entry_root hlen hn hLb]
  exact gexp_entry0_gt hlen hLb hup hd0pos l hl0 (by omega)

/-- **Cone-from-`0` transport** (probe `tools/probe_cone0.py`: 1812 hosts,
85680 instances, 0 violations).  For an ascending window (`d0 > 0`) the cone of
the sequence's own root is mirrored by the expansion — the companion of
`gexp_guard_transport`, which mirrors the cone of the bad root `j0`. -/
theorem gexp_cone0_transport {M : TrioSeq} {j0 Lb d0 d1 n k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hcone : le1 M j0 (j0 + Lb)) :
    le1 (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  have hlenG : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hgtG := gexp_entry0_gt_root (d1 := d1) hlen hLb hn hup hd0pos
  have hE10 : entry (gexp M j0 Lb d0 d1 n) 1 0 = entry M 1 0 := by
    show ((gexp M j0 Lb d0 d1 n).getD 0 (0, 0, 0)).2.1 = _
    rw [gexp_getD_low hlen hj0, getD_eq_entries]
  -- the row-0 chains that both sides ride on
  have hrtgM : ∀ r : ℕ, r < Lb → Relation.ReflTransGen (nextrel0 M) j0 (j0 + r) :=
    fun r hr => rtg0_of_window (by omega) (by omega)
      (fun l hl0 hl1 => hup l hl0 (by omega))
  have hrtgG : ∀ r : ℕ, r < n * Lb →
      Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0 (j0 + r) :=
    fun r hr => gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  constructor
  · -- `G`-side cone ⟹ `M`-side cone
    intro h
    obtain ⟨hsp1, hsp2⟩ :=
      rtg0_split_at hgtG (rtg0_of_rtg1 h.2.2) (Nat.zero_le _) (by omega) (by omega)
    have hG0j0 : le1 (gexp M j0 Lb d0 d1 n) 0 j0 :=
      (le1_iff_chain_window (by omega) hsp1).2
        (fun x hx1 hx2 hne => le1_chain_window h.2.2 x hx1 (hx2.trans hsp2) hne)
    have hM0j0 : le1 M 0 j0 := (le1_gexp_le hlen hLb hn le_rfl).1 hG0j0
    have hlt0 : entry M 1 0 < entry M 1 j0 := le1_entry1_lt hM0j0 (by omega)
    refine (le1_iff_chain_window (by omega)
      ((rtg0_of_rtg1 hM0j0.2.2).trans (hrtgM q hq))).2 ?_
    intro x hx1 hx2 hne
    rcases Nat.lt_or_ge x (j0 + 1) with hxl | hxg
    · obtain ⟨hs1, -⟩ := rtg0_split_at hup hx2 (by omega) (by omega) (by omega)
      exact le1_chain_window hM0j0.2.2 x hx1 hs1 hne
    · -- a window position: read it off the `k`-th mirror
      have hxle : x ≤ j0 + q := nextrel0_rtrancl_index_le hx2
      set q' : ℕ := x - j0 with hq'def
      have hxe : x = j0 + q' := by omega
      have hq'lt : q' < Lb := by omega
      have hx'2 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk (by rw [← hxe]; exact hx2) q rfl hq
      have hx'1 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) 0
          (j0 + (k * Lb + q')) :=
        (rtg0_of_rtg1 hG0j0.2.2).trans (hrtgG _ (by omega))
      have hwin := le1_chain_window h.2.2 (j0 + (k * Lb + q')) hx'1 hx'2
        (by omega)
      rw [hE10] at hwin
      have hval : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + q'))
          = entry M 1 (j0 + q')
            + (if le1 M j0 (j0 + q') then k * d1 else 0) := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + q')) (0, 0, 0)).2.1 = _
        rw [gexp_getD_mir hlen hk hq'lt]
      rw [hval] at hwin
      rw [hxe]
      by_cases hg : le1 M j0 (j0 + q')
      · have := le1_entry1_lt hg (by omega)
        omega
      · rw [if_neg hg] at hwin
        omega
  · -- `M`-side cone ⟹ `G`-side cone
    intro h
    obtain ⟨hsp1, hsp2⟩ :=
      rtg0_split_at hup (rtg0_of_rtg1 h.2.2) (Nat.zero_le _) (by omega) (by omega)
    have hM0j0 : le1 M 0 j0 :=
      (le1_iff_chain_window (by omega) hsp1).2
        (fun x hx1 hx2 hne => le1_chain_window h.2.2 x hx1 (hx2.trans hsp2) hne)
    have hlt0 : entry M 1 0 < entry M 1 j0 := le1_entry1_lt hM0j0 (by omega)
    have hG0j0 : le1 (gexp M j0 Lb d0 d1 n) 0 j0 :=
      (le1_gexp_le hlen hLb hn le_rfl).2 hM0j0
    refine (le1_iff_chain_window (by omega)
      ((rtg0_of_rtg1 hG0j0.2.2).trans (hrtgG _ hbnd))).2 ?_
    intro x hx1 hx2 hne
    rcases Nat.lt_or_ge x (j0 + 1) with hxl | hxg
    · obtain ⟨hs1, -⟩ := rtg0_split_at hgtG hx2 (by omega) (by omega) (by omega)
      exact le1_chain_window hG0j0.2.2 x hx1 hs1 hne
    · obtain ⟨k', q', hk', hq', rfl, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e x hx2 (by omega)
      rw [hE10]
      have hval : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k' * Lb + q'))
          = entry M 1 (j0 + q')
            + (if le1 M j0 (j0 + q') then k' * d1 else 0) := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k' * Lb + q')) (0, 0, 0)).2.1 = _
        rw [gexp_getD_mir hlen (by omega) hq']
      rw [hval]
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · -- a copy root: it carries the bad root's row 1, possibly lifted
        rw [Nat.add_zero]
        split_ifs <;> omega
      · have hM0q' : Relation.ReflTransGen (nextrel0 M) 0 (j0 + q') :=
          (rtg0_of_rtg1 hM0j0.2.2).trans (hrtgM _ hq')
        rcases hcase with ⟨-, hM⟩ | ⟨-, hM⟩
        · have := le1_chain_window h.2.2 (j0 + q') hM0q' hM (by omega)
          split_ifs <;> omega
        · have := le1_chain_window hcone.2.2 (j0 + q') (hrtgM _ hq') hM (by omega)
          split_ifs <;> omega

/-- **The root lift commutes with an ascending expansion whose bad root is not
the sequence's own root.**  The two masks are cones of *different* roots — the
lift rides on `le1 X 0 ·`, the copies on `le1 X j0 ·` — so they simply add up on
each mirror, once `gexp_cone0_transport` says the `0`-cone is mirrored. -/
theorem gexp_Lift1_comm {X : TrioSeq} {j0 Lb D0 D1 n d : ℕ}
    (hlen : j0 + Lb + 1 = X.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hn : 0 < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry X 0 j0 < entry X 0 l)
    (hd0pos : 0 < D0) (hd0e : entry X 0 (j0 + Lb) = entry X 0 j0 + D0)
    (hcone : le1 X j0 (j0 + Lb)) :
    gexp (Lift1 X d) j0 Lb D0 D1 n = Lift1 (gexp X j0 Lb D0 D1 n) d := by
  classical
  have hlenLX : (Lift1 X d).length = X.length := Lift1_length X d
  have hlenL' : j0 + Lb + 1 = (Lift1 X d).length := by rw [hlenLX]; exact hlen
  have hlenG : (gexp X j0 Lb D0 D1 n).length = j0 + n * Lb := gexp_length hlen
  have hlenGL : (gexp (Lift1 X d) j0 Lb D0 D1 n).length = j0 + n * Lb :=
    gexp_length hlenL'
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  refine List.ext_getElem (by rw [hlenGL, Lift1_length, hlenG]) ?_
  intro i hia hib
  rw [hlenGL] at hia
  rw [getElem_eq_getD' (by omega), getElem_eq_getD' (by rw [Lift1_length]; omega),
    Lift1_getD (by omega)]
  rcases Nat.lt_or_ge i j0 with hlow | hhigh
  · -- head: both sides read the host verbatim
    have hlowX : (gexp X j0 Lb D0 D1 n).getD i (0, 0, 0) = X.getD i (0, 0, 0) :=
      gexp_getD_low hlen hlow
    have hE : ∀ y, entry (gexp X j0 Lb D0 D1 n) y i = entry X y i := by
      intro y; unfold entry; rw [hlowX]
    rw [gexp_getD_low hlenL' hlow, Lift1_getD (by omega), hE 0, hE 1, hE 2,
      le1_gexp_low (by omega) hlow]
  · -- copies: the two masks add up
    obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hhigh (by omega)
    have hmir : (gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)
        = (entry X 0 (j0 + q) + k * D0,
           entry X 1 (j0 + q) + (if le1 X j0 (j0 + q) then k * D1 else 0),
           entry X 2 (j0 + q)) := gexp_getD_mir hlen hk hq
    have hE0 : entry (gexp X j0 Lb D0 D1 n) 0 (j0 + (k * Lb + q))
        = entry X 0 (j0 + q) + k * D0 := by
      show ((gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).1 = _
      rw [hmir]
    have hE1 : entry (gexp X j0 Lb D0 D1 n) 1 (j0 + (k * Lb + q))
        = entry X 1 (j0 + q) + (if le1 X j0 (j0 + q) then k * D1 else 0) := by
      show ((gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).2.1 = _
      rw [hmir]
    have hE2 : entry (gexp X j0 Lb D0 D1 n) 2 (j0 + (k * Lb + q))
        = entry X 2 (j0 + q) := by
      show ((gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).2.2 = _
      rw [hmir]
    rw [gexp_getD_mir hlenL' hk hq, hE0, hE1, hE2, entry0_Lift1, entry2_Lift1,
      entry1_Lift1 (by omega)]
    simp only [le1_Lift1,
      gexp_cone0_transport (M := X) (d1 := D1) hlen hj0 hLb hk hq hup hd0pos
        hd0e hcone]
    rw [Nat.add_right_comm]

/-- A collapse row above `0` means the last column is nonzero in that row. -/
theorem entry_pos_of_srow {X : TrioSeq} {j : ℕ} (h : 1 ≤ srow X j) :
    0 < entry X 1 j ∨ 0 < entry X 2 j := by
  unfold srow at h
  split at h
  · exact Or.inr (by assumption)
  · split at h
    · exact Or.inl (by assumption)
    · omega

/-- The collapse row `i1 ≥ 1` puts the bad root in the row-1 cone of the last
column, which is what makes the two lift masks nest. -/
theorem le1_parent_of_srow_pos {X : TrioSeq} {i1 j0 j1 : ℕ} (hi1 : 1 ≤ i1)
    (hnr : nextR X i1 j0 j1) : le1 X j0 j1 := by
  unfold nextR at hnr
  rw [if_neg (by omega)] at hnr
  rcases Nat.lt_or_ge i1 2 with h | h
  · rw [if_pos (by omega)] at hnr
    exact ⟨hnr.1, hnr.2.1, Relation.ReflTransGen.single hnr⟩
  · rw [if_neg (by omega)] at hnr
    exact hnr.2.2.2.2.1

/-- **The branch `1 ≤ badPar`, ascending collapse (`i1 ≥ 1`)**: `oper` commutes
with the root lift.  All the expansion data (`j0`, `Lb`, `D0`, `D1`) is
transported verbatim by `Lift1`; the row-1 datum `D1` survives because the bad
root and the last column lie in the *same* `0`-cone (`le1_of_le1_le1`), so the
lift cancels in the difference. -/
theorem lift_oper_comm_of_parent {X : TrioSeq} {d n : ℕ} (h2 : 2 ≤ X.length)
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1))
    (hjpos : 0 < parent X (srow X (X.length - 1)) (X.length - 1))
    (hi1 : 1 ≤ srow X (X.length - 1)) (hn : 0 < n) :
    (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d := by
  classical
  have hlenL : (Lift1 X d).length = X.length := Lift1_length X d
  have hnr := parent_nextR hp
  have hlt : parent X (srow X (X.length - 1)) (X.length - 1) < X.length - 1 :=
    nextR_index_lt hnr
  have hch0 := nextR_chain0 hnr
  have hj1ne : X.length - 1 ≠ 0 := by omega
  set j1 : ℕ := X.length - 1 with hj1def
  set i1 : ℕ := srow X j1 with hi1def
  set j0 : ℕ := parent X i1 j1 with hj0def
  set Lb : ℕ := j1 - j0 with hLbdef
  have hlen : j0 + Lb + 1 = X.length := by omega
  have hLb : 0 < Lb := by omega
  have hj1e : j0 + Lb = j1 := by omega
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry X 0 j0 < entry X 0 l := by
    have hw := window_of_rtg0 hch0 (by omega)
    intro l hl0 hl1
    exact hw l hl0 (by omega)
  have hcone : le1 X j0 (j0 + Lb) := by rw [hj1e]; exact le1_parent_of_srow_pos hi1 hnr
  set D0 : ℕ := if 0 < i1 then entry X 0 j1 - entry X 0 j0 else 0 with hD0def
  set D1 : ℕ := if 1 < i1 then entry X 1 j1 - entry X 1 j0 else 0 with hD1def
  have hd0pos : 0 < D0 := by
    rw [hD0def, if_pos (by omega)]
    have := hup j1 (by omega) (by omega)
    omega
  have hd0e : entry X 0 (j0 + Lb) = entry X 0 j0 + D0 := by
    rw [hj1e, hD0def, if_pos (by omega)]
    have := hup j1 (by omega) (by omega)
    omega
  -- the two `oper` presentations, sharing the same data
  have hpos1 : 0 < entry X 1 j1 ∨ 0 < entry X 2 j1 := entry_pos_of_srow hi1
  have hz : ¬ (entry X 0 j1 = 0 ∧ entry X 1 j1 = 0 ∧ entry X 2 j1 = 0) := by
    rintro ⟨-, ha, hb⟩; omega
  have hgX : X⟦n⟧ = gexp X j0 Lb D0 D1 n := by
    have h := oper_gcopies (M := X) n hj1ne hz hp
    rw [← hj1def, ← hi1def, ← hj0def, ← hLbdef, ← hD0def, ← hD1def] at h
    unfold gexp
    exact h
  -- the lifted side: every datum transports
  have hlenL1 : (Lift1 X d).length - 1 = j1 := by rw [hlenL]
  have hsrL : srow (Lift1 X d) j1 = i1 := srow_Lift1 hj1ne
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlenL1, hsrL, hasParent_Lift1]; exact hp
  have hzL : ¬ (entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0) := by
    rw [hlenL1, entry0_Lift1, entry2_Lift1, entry1_Lift1 (by omega)]
    rintro ⟨-, ha, hb⟩
    omega
  -- the row-1 datum: the bad root and the last column share the `0`-cone
  have hg01 : le1 X 0 j0 ↔ le1 X 0 j1 := by
    constructor
    · intro h; rw [← hj1e]; exact le1_trans h hcone
    · intro h; exact le1_of_le1_le1 h (by rw [← hj1e]; exact hcone) (by omega)
  have hD1L : (if 1 < i1 then entry (Lift1 X d) 1 j1
        - entry (Lift1 X d) 1 j0 else 0) = D1 := by
    rw [entry1_Lift1 (by omega), entry1_Lift1 (by omega), hD1def]
    by_cases hc : le1 X 0 j0
    · rw [if_pos hc, if_pos (hg01.1 hc)]
      split_ifs <;> omega
    · rw [if_neg hc, if_neg (fun hcon => hc (hg01.2 hcon))]
      split_ifs <;> omega
  have hgL : (Lift1 X d)⟦n⟧ = gexp (Lift1 X d) j0 Lb D0 D1 n := by
    have h := oper_gcopies (M := Lift1 X d) n (by rw [hlenL1]; exact hj1ne) hzL hpL
    rw [hlenL1, hsrL, parent_Lift1, ← hj0def, entry0_Lift1, entry0_Lift1,
      hD1L] at h
    rw [show j1 - j0 = Lb from hLbdef.symm, ← hD0def] at h
    unfold gexp
    exact h
  rw [hgL, hgX, gexp_Lift1_comm hlen hjpos hLb hn hup hd0pos hd0e hcone]

/-- Splitting the `1 ≤ badPar` residue by the collapse row. -/
theorem lspOn_pos_of
    (h0 : LSPOn (fun X => 1 ≤ badPar X ∧ srow X (X.length - 1) = 0))
    (hhi : LSPOn (fun X => 1 ≤ badPar X ∧ 1 ≤ srow X (X.length - 1))) :
    LSPOn (fun X => 1 ≤ badPar X) := by
  intro m d X h2 hp hpos hop n hn
  rcases Nat.eq_zero_or_pos (srow X (X.length - 1)) with hs | hs
  · exact h0 m d X h2 hp ⟨hpos, hs⟩ hop n hn
  · exact hhi m d X h2 hp ⟨hpos, hs⟩ hop n hn

/-- **Branch `1 ≤ badPar`, `i1 ≥ 1`** — commutation, so the stage is inherited
straight from the hypothesis on `X⟦n⟧`. -/
theorem lspOn_pos_hi :
    LSPOn (fun X => 1 ≤ badPar X ∧ 1 ≤ srow X (X.length - 1)) := by
  rintro m d X h2 hp ⟨hjpos, hi1⟩ hop n hn
  rw [lift_oper_comm_of_parent h2 hp hjpos hi1 (by omega)]
  exact hop n hn

end TRIO
