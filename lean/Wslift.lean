/-
Wslift.lean: **階段リフトは `W` 所属を段の押し上げつきで運ぶ**。

`slift_oper` (G2) により階段リフトは `oper` と**可換**なので、`Aop` の節 2 は
そのまま移る。節 3 は長さ 2 以上では節 2 に吸収される（`Wchar`）。残るのは
長さ 1 の根だけで、そこでは

```
slift [(d,b,c)] φ = [(d, φ b, c)]     （レベル 2b+c → 2 (φ b) + c）
```

なので**段を上げれば通る**。これが `CoreStairOm`（段を固定したままでは通らない
唯一の箇所）の正体で、段を `2 * φ m + m` まで緩めれば核なしで証明できる。

計測（`tools/probe_lift.py`）: 根リフトについては
`minstage (Lift1 X d) = minstage X + 2d` が 18300 例で**等号**で成立。
本補題はその階段リフト版（上界は緩め）。
-/
import Wchar
import Aexp

namespace TRIO

open Wset

theorem slift_of_length_one {X : TrioSeq} (h1 : X.length = 1) {φ : ℕ → ℕ}
    (hφ : Stair φ) :
    slift X φ = [((entry X 0 0, φ (entry X 1 0), entry X 2 0) : ℕ × ℕ × ℕ)] := by
  unfold slift
  rw [h1, show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [amin_zero]
  have hge := hφ.ge (entry X 1 0)
  rw [show entry X 1 0 + (φ (entry X 1 0) - entry X 1 0) = φ (entry X 1 0) from
    by omega]

/-- **The staircase lift transports `W`-membership**, at the cost of a stage
bump.  No cores: clause 2 rides on `slift_oper` (G2), clause 3 collapses into
clause 2 above length 1 (`aop_clause3_to_clause2`), and the one-column roots —
the only place where the stage genuinely has to rise — are discharged by
`singleton_mem_W` because the bumped stage `2 * φ m + m` dominates
`2 * φ b + c` whenever `2 * b + c ≤ m`. -/
theorem slift_mem_W {m : ℕ} {φ : ℕ → ℕ} (hφ : Stair φ) :
    ∀ X ∈ W m, slift X φ ∈ W (2 * φ m + m) := by
  have hsub : W m ⊆ {X : TrioSeq | slift X φ ∈ W (2 * φ m + m)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · -- clause 1: short with a zero root
      rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show slift ([] : TrioSeq) φ ∈ W (2 * φ m + m)
        simpa [slift] using W_nil (2 * φ m + m)
      · have h1 : X.length = 1 := by omega
        show slift X φ ∈ W (2 * φ m + m)
        rw [slift_of_length_one h1 hφ]
        have hb : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hb.1, hb.2, hφ.zero]
        exact singleton_mem_W (by omega)
    · -- clause 2: `slift` commutes with `oper`
      rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show slift X φ ∈ W (2 * φ m + m)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact hop n hn
    · -- clause 3: absorbed above length 1; a stage bump at length 1
      rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlev := hd.1
        rw [show X.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        show slift X φ ∈ W (2 * φ m + m)
        rw [slift_of_length_one h1 hφ]
        refine singleton_mem_W ?_
        have hmono : φ (entry X 1 0) ≤ φ m :=
          hφ.mono (by omega)
        omega
      · show slift X φ ∈ W (2 * φ m + m)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact aop_clause3_to_clause2 hbig hd hgr n hn
  exact fun X hX => hsub hX

/-- **Tight form**: if the staircase never lifts by more than `d`, the stage
rises by exactly `2 * d` — the same law the root lift obeys with equality
(`tools/probe_lift.py`).  The bound is only used at the one-column roots, where
`2 * φ b + c ≤ (2 * b + c) + 2 * d ≤ m + 2 * d`. -/
theorem slift_mem_W_tight {m d : ℕ} {φ : ℕ → ℕ} (hφ : Stair φ)
    (hb : ∀ k, φ k ≤ k + d) : ∀ X ∈ W m, slift X φ ∈ W (m + 2 * d) := by
  have hsub : W m ⊆ {X : TrioSeq | slift X φ ∈ W (m + 2 * d)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show slift ([] : TrioSeq) φ ∈ W (m + 2 * d)
        simpa [slift] using W_nil (m + 2 * d)
      · have h1 : X.length = 1 := by omega
        show slift X φ ∈ W (m + 2 * d)
        rw [slift_of_length_one h1 hφ]
        have hbc : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hbc.1, hbc.2, hφ.zero]
        exact singleton_mem_W (by omega)
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show slift X φ ∈ W (m + 2 * d)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact hop n hn
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlev := hd.1
        rw [show X.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        show slift X φ ∈ W (m + 2 * d)
        rw [slift_of_length_one h1 hφ]
        refine singleton_mem_W ?_
        have hbk := hb (entry X 1 0)
        omega
      · show slift X φ ∈ W (m + 2 * d)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact aop_clause3_to_clause2 hbig hd hgr n hn
  exact fun X hX => hsub hX

/-- **The ambient mask lift costs exactly `2 * d` stages.**  `mlift` is the
staircase lift by the step function (`mlift_eq_slift`), which never lifts by
more than `d`. -/
theorem mlift_mem_W {m v d : ℕ} : ∀ X ∈ W m, mlift X v d ∈ W (m + 2 * d) := by
  intro X hX
  rw [mlift_eq_slift]
  exact slift_mem_W_tight (stair_step v d) (fun k => by split <;> omega) X hX

/-! ## (ULIFT): 行 1 の**一様**シフトも `W` を運ぶ — `Stair.zero` は不要

`Stair.zero`（`φ 0 = 0`）は `slift` が `oper` と**可換**であるために本当に必要で
ある（行 1 が 0 の列を動かすと `srow` が `0 → 1` に変わり、展開の枝データが
変わる）。しかし **`W` 所属の輸送には不要**であることが分かった:

一様シフト `shiftr01 0 d` が `srow` を上げるのは末尾列が `srow = 0` のときだけで、
そのとき持ち上げ後の末尾列の行 1 値はちょうど `d`、他の列は `≥ d` なので、
行 1 で真に小さい祖先が存在せず**必ず孤児**になる。よって展開は `dropLast` に
潰れ、節 2 の `n = 1` の帰納法仮定（`oper_one_eq_dropLast`）でそのまま閉じる。

計測（`tools/probe_ulift.py`）: 378075 例 0 違反。これで使えるリフトの言語は
「`φ m - m` が単調非減少」だけに緩む（`φ 0 = 0` は落ちる）。 -/

theorem entry0_shiftr1 (d : ℕ) (W : TrioSeq) (p : ℕ) :
    entry (shiftr01 0 d W) 0 p = entry W 0 p := by
  rcases Nat.lt_or_ge p W.length with hp | hp
  · rw [entry0_shiftr01 hp]; omega
  · show ((shiftr01 0 d W).getD p ((0, 0, 0) : ℕ × ℕ × ℕ)).1
      = ((W.getD p ((0, 0, 0) : ℕ × ℕ × ℕ)).1 : ℕ)
    rw [getD_out (by rw [shiftr01_length]; omega), getD_out hp]

theorem entry1_shiftr1 {d : ℕ} {W : TrioSeq} {p : ℕ} (hp : p < W.length) :
    entry (shiftr01 0 d W) 1 p = entry W 1 p + d := by
  show ((shiftr01 0 d W).getD p ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1
    = ((W.getD p ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 : ℕ) + d
  rw [shiftr01_getD hp]

theorem nextrel0_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel0 (shiftr01 0 d W) a b ↔ nextrel0 W a b := by
  unfold nextrel0
  rw [shiftr01_length]
  simp only [entry0_shiftr1]

theorem rtg0_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    Relation.ReflTransGen (nextrel0 (shiftr01 0 d W)) a b
      ↔ Relation.ReflTransGen (nextrel0 W) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel0_shiftr1.1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel0_shiftr1.2 hyz)

theorem le0_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    le0 (shiftr01 0 d W) a b ↔ le0 W a b := by
  unfold le0
  rw [shiftr01_length, rtg0_shiftr1]

theorem nextrel1_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel1 (shiftr01 0 d W) a b ↔ nextrel1 W a b := by
  unfold nextrel1
  rw [shiftr01_length]
  constructor
  · rintro ⟨ha, hb, hab, hlt, hc, hmin⟩
    rw [entry1_shiftr1 ha, entry1_shiftr1 hb] at hlt
    refine ⟨ha, hb, hab, by omega, le0_shiftr1.mp hc, ?_⟩
    intro j hj
    have hjlt : j < W.length := hj.2.1
    have hh := hmin j ⟨hj.1, le0_shiftr1.mpr hj.2⟩
    rw [entry1_shiftr1 hb, entry1_shiftr1 hjlt] at hh
    omega
  · rintro ⟨ha, hb, hab, hlt, hc, hmin⟩
    refine ⟨ha, hb, hab, ?_, le0_shiftr1.mpr hc, ?_⟩
    · rw [entry1_shiftr1 ha, entry1_shiftr1 hb]; omega
    · intro j hj
      have hjlt : j < W.length := (le0_shiftr1.mp hj.2).1
      have hh := hmin j ⟨hj.1, le0_shiftr1.mp hj.2⟩
      rw [entry1_shiftr1 hb, entry1_shiftr1 hjlt]
      omega

theorem le1_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    le1 (shiftr01 0 d W) a b ↔ le1 W a b := by
  unfold le1
  rw [shiftr01_length]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel1_shiftr1.1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel1_shiftr1.2 hyz)

theorem nextrel2_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel2 (shiftr01 0 d W) a b ↔ nextrel2 W a b := by
  unfold nextrel2
  rw [shiftr01_length]
  simp only [entry2_shiftr01, le1_shiftr1]

theorem nextR_shiftr1 {d : ℕ} {W : TrioSeq} {i a b : ℕ} :
    nextR (shiftr01 0 d W) i a b ↔ nextR W i a b := by
  unfold nextR
  split
  · exact nextrel0_shiftr1
  · split
    · exact nextrel1_shiftr1
    · exact nextrel2_shiftr1

theorem hasParent_shiftr1 {d : ℕ} {W : TrioSeq} {i b : ℕ} :
    hasParent (shiftr01 0 d W) i b ↔ hasParent W i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_shiftr1.mp hj0, fun y hy => hu y (nextR_shiftr1.mpr hy)⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_shiftr1.mpr hj0, fun y hy => hu y (nextR_shiftr1.mp hy)⟩

theorem parent_shiftr1 {d : ℕ} {W : TrioSeq} {i b : ℕ} :
    parent (shiftr01 0 d W) i b = parent W i b := by
  unfold parent
  congr 1
  funext j0
  exact propext nextR_shiftr1

theorem lev_shiftr1 {d : ℕ} {W : TrioSeq} {j : ℕ} (hj : j < W.length) :
    lev (shiftr01 0 d W) j = lev W j + 2 * d := by
  unfold lev
  rw [entry1_shiftr1 hj, entry2_shiftr01]
  omega

/-- 一様シフトが `srow` を変えるのは `srow = 0` の列だけ。 -/
theorem srow_shiftr1 {d : ℕ} {W : TrioSeq} {j : ℕ} (hj : j < W.length)
    (hsr : 1 ≤ srow W j) : srow (shiftr01 0 d W) j = srow W j := by
  unfold srow at hsr ⊢
  rw [entry2_shiftr01, entry1_shiftr1 hj]
  by_cases h2 : 0 < entry W 2 j
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2] at hsr ⊢
    rw [if_neg h2]
    have h1 : 0 < entry W 1 j := by
      by_contra hc
      rw [if_neg (by omega)] at hsr
      omega
    rw [if_pos (by omega : 0 < entry W 1 j + d), if_pos h1]

theorem gcopy_shiftr1 {d : ℕ} {W : TrioSeq} {r L : ℕ} (hb : r + L ≤ W.length)
    (d0 d1 k : ℕ) :
    gcopy (shiftr01 0 d W) r L d0 d1 k = shiftr01 0 d (gcopy W r L d0 d1 k) := by
  show _ = List.map
    (fun p : ℕ × ℕ × ℕ => ((p.1 + 0, p.2.1 + d, p.2.2) : ℕ × ℕ × ℕ)) _
  unfold gcopy
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro j hj
  have hjlt : j < W.length := by
    have := List.mem_range'_1.1 hj
    omega
  rw [entry0_shiftr1, entry1_shiftr1 hjlt, entry2_shiftr01]
  simp only [Function.comp_apply]
  refine Prod.ext (by dsimp only; omega) (Prod.ext ?_ (by dsimp only))
  dsimp only
  by_cases hg : le1 W r j
  · rw [if_pos hg, if_pos (le1_shiftr1.mpr hg)]
    omega
  · rw [if_neg hg, if_neg (fun hc => hg (le1_shiftr1.mp hc))]
    omega

theorem gcopies_shiftr1 {d : ℕ} {W : TrioSeq} {r L : ℕ} (hb : r + L ≤ W.length)
    (d0 d1 n : ℕ) :
    gcopies (shiftr01 0 d W) r L d0 d1 n
      = shiftr01 0 d (gcopies W r L d0 d1 n) := by
  show _ = List.map
    (fun p : ℕ × ℕ × ℕ => ((p.1 + 0, p.2.1 + d, p.2.2) : ℕ × ℕ × ℕ)) _
  unfold gcopies
  rw [List.map_flatMap]
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_shiftr1 hb d0 d1 k

theorem Pred_shiftr1 {d : ℕ} (W : TrioSeq) :
    Pred (shiftr01 0 d W) = shiftr01 0 d (Pred W) := by
  unfold Pred
  rw [shiftr01_length]
  split_ifs with h
  · rfl
  · exact shiftr01_dropLast 0 d W

set_option maxHeartbeats 1000000 in
/-- **一様行 1 シフトは `oper` と可換** — 末尾列の `srow` が `1` 以上なら。 -/
theorem oper_shiftr1 {d : ℕ} (W : TrioSeq) (n : ℕ)
    (hsr1 : 1 ≤ srow W (W.length - 1)) :
    (shiftr01 0 d W)⟦n⟧ = shiftr01 0 d (W⟦n⟧) := by
  by_cases hL : W.length - 1 = 0
  · rw [oper_eq_self_of_short n (by rw [shiftr01_length]; exact hL),
      oper_eq_self_of_short n hL]
  · have hlt : W.length - 1 < W.length := by omega
    have hlenmap : (shiftr01 0 d W).length - 1 = W.length - 1 := by
      rw [shiftr01_length]
    have hLm : (shiftr01 0 d W).length - 1 ≠ 0 := by rw [shiftr01_length]; exact hL
    have hsr : srow (shiftr01 0 d W) (W.length - 1) = srow W (W.length - 1) :=
      srow_shiftr1 hlt hsr1
    have hz : ¬ (entry W 0 (W.length - 1) = 0 ∧ entry W 1 (W.length - 1) = 0 ∧
        entry W 2 (W.length - 1) = 0) := by
      rintro ⟨-, h1, h2⟩
      unfold srow at hsr1
      rw [if_neg (by omega), if_neg (by omega)] at hsr1
      omega
    have hzM : ¬ (entry (shiftr01 0 d W) 0 ((shiftr01 0 d W).length - 1) = 0 ∧
        entry (shiftr01 0 d W) 1 ((shiftr01 0 d W).length - 1) = 0 ∧
        entry (shiftr01 0 d W) 2 ((shiftr01 0 d W).length - 1) = 0) := by
      rw [hlenmap]
      rintro ⟨h0, h1, h2⟩
      rw [entry0_shiftr1] at h0
      rw [entry1_shiftr1 hlt] at h1
      rw [entry2_shiftr01] at h2
      exact hz ⟨h0, by omega, h2⟩
    by_cases hp : hasParent W (srow W (W.length - 1)) (W.length - 1)
    · have hpM : hasParent (shiftr01 0 d W)
          (srow (shiftr01 0 d W) ((shiftr01 0 d W).length - 1))
          ((shiftr01 0 d W).length - 1) := by
        rw [hlenmap, hsr]
        exact hasParent_shiftr1.mpr hp
      rw [oper_gcopies n hLm hzM hpM, oper_gcopies n hL hz hp, hlenmap, hsr,
        parent_shiftr1, shiftr01_take]
      have hj0lt : parent W (srow W (W.length - 1)) (W.length - 1) < W.length - 1 :=
        nextR_index_lt (parent_nextR hp)
      have hd0 : entry (shiftr01 0 d W) 0 (W.length - 1)
          - entry (shiftr01 0 d W) 0
              (parent W (srow W (W.length - 1)) (W.length - 1))
          = entry W 0 (W.length - 1)
            - entry W 0 (parent W (srow W (W.length - 1)) (W.length - 1)) := by
        rw [entry0_shiftr1, entry0_shiftr1]
      have hd1 : entry (shiftr01 0 d W) 1 (W.length - 1)
          - entry (shiftr01 0 d W) 1
              (parent W (srow W (W.length - 1)) (W.length - 1))
          = entry W 1 (W.length - 1)
            - entry W 1 (parent W (srow W (W.length - 1)) (W.length - 1)) := by
        rw [entry1_shiftr1 hlt, entry1_shiftr1 (by omega : parent W
          (srow W (W.length - 1)) (W.length - 1) < W.length)]
        omega
      rw [hd0, hd1, gcopies_shiftr1 (by omega), shiftr01_append]
    · have hpM : ¬ hasParent (shiftr01 0 d W)
          (srow (shiftr01 0 d W) ((shiftr01 0 d W).length - 1))
          ((shiftr01 0 d W).length - 1) := by
        rw [hlenmap, hsr]
        intro hh
        exact hp (hasParent_shiftr1.mp hh)
      rw [oper_eq_pred_of_noParent n hL hz hp,
        oper_eq_pred_of_noParent n hLm hzM hpM, Pred_shiftr1]

/-- **節 2 の一段**: 末尾列の `srow` が `1` 以上なら可換性、`0` なら持ち上げ後の
末尾列が孤児になって展開が `dropLast = X⟦1⟧` に潰れる。 -/
theorem ulift_step {m d : ℕ} {X : TrioSeq} (hbig : 2 ≤ X.length)
    (hop : ∀ n, 1 ≤ n → shiftr01 0 d (X⟦n⟧) ∈ W (m + 2 * d)) :
    shiftr01 0 d X ∈ W (m + 2 * d) := by
  have hlt : X.length - 1 < X.length := by omega
  have hlen : (shiftr01 0 d X).length = X.length := shiftr01_length 0 d X
  rcases Nat.eq_zero_or_pos (srow X (X.length - 1)) with hsr0 | hsr1
  · rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · refine mem_of_oper_mem (fun n hn => ?_)
      have hh := hop n hn
      rw [shiftr01_zero] at hh ⊢
      exact hh
    · have h12 : entry X 1 (X.length - 1) = 0 ∧ entry X 2 (X.length - 1) = 0 := by
        unfold srow at hsr0
        by_cases h2 : 0 < entry X 2 (X.length - 1)
        · rw [if_pos h2] at hsr0; omega
        · rw [if_neg h2] at hsr0
          by_cases h1 : 0 < entry X 1 (X.length - 1)
          · rw [if_pos h1] at hsr0; omega
          · exact ⟨by omega, by omega⟩
      have hsrM : srow (shiftr01 0 d X) (X.length - 1) = 1 := by
        unfold srow
        rw [entry2_shiftr01, entry1_shiftr1 hlt, h12.1, h12.2,
          if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent (shiftr01 0 d X) 1 (X.length - 1) := by
        rintro ⟨j0, hj0, -⟩
        unfold nextR at hj0
        rw [if_neg one_ne_zero, if_pos rfl] at hj0
        obtain ⟨ha, hb, -, hlt1, -, -⟩ := hj0
        rw [hlen] at ha hb
        rw [entry1_shiftr1 ha, entry1_shiftr1 hb, h12.1] at hlt1
        omega
      have hnp' : ¬ hasParent (shiftr01 0 d X)
          (srow (shiftr01 0 d X) ((shiftr01 0 d X).length - 1))
          ((shiftr01 0 d X).length - 1) := by
        rw [hlen, hsrM]; exact hnp
      have hzM : ¬ (entry (shiftr01 0 d X) 0 ((shiftr01 0 d X).length - 1) = 0 ∧
          entry (shiftr01 0 d X) 1 ((shiftr01 0 d X).length - 1) = 0 ∧
          entry (shiftr01 0 d X) 2 ((shiftr01 0 d X).length - 1) = 0) := by
        rw [hlen]
        rintro ⟨-, h1, -⟩
        rw [entry1_shiftr1 hlt, h12.1] at h1
        omega
      refine mem_of_oper_mem (fun n hn => ?_)
      rw [oper_eq_pred_of_noParent n (by rw [hlen]; omega) hzM hnp']
      unfold Pred
      rw [if_neg (by rw [hlen]; omega), shiftr01_dropLast]
      have hh := hop 1 le_rfl
      rwa [oper_one_eq_dropLast (by omega)] at hh
  · refine mem_of_oper_mem (fun n hn => ?_)
    rw [oper_shiftr1 X n hsr1]
    exact hop n hn

theorem shiftr01_of_length_one {X : TrioSeq} (h1 : X.length = 1) (d : ℕ) :
    shiftr01 0 d X = [((entry X 0 0, entry X 1 0 + d, entry X 2 0) : ℕ × ℕ × ℕ)] := by
  rcases X with _ | ⟨p, t⟩
  · simp at h1
  · have ht : t = [] := List.eq_nil_of_length_eq_zero (by simpa using h1)
    subst ht
    simp [shiftr01, entry]

/-- **★ (ULIFT)**: 行 1 の一様シフトは `W` を `2 * d` の段の押し上げつきで運ぶ。
`Stair.zero` を使わないので `mlift` では届かない「閾値 `-1`」の場合を埋める。 -/
theorem ulift_mem_W {m d : ℕ} : ∀ X ∈ W m, shiftr01 0 d X ∈ W (m + 2 * d) := by
  have hsub : W m ⊆ {X : TrioSeq | shiftr01 0 d X ∈ W (m + 2 * d)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show shiftr01 0 d ([] : TrioSeq) ∈ W (m + 2 * d)
        simpa using W_nil (m + 2 * d)
      · have h1 : X.length = 1 := by omega
        show shiftr01 0 d X ∈ W (m + 2 * d)
        rw [shiftr01_of_length_one h1 d]
        have hbc : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hbc.1, hbc.2]
        exact singleton_mem_W (by omega)
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show shiftr01 0 d X ∈ W (m + 2 * d)
        exact ulift_step hbig (fun n hn => hop n hn)
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlev := hd.1
        rw [show X.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        show shiftr01 0 d X ∈ W (m + 2 * d)
        rw [shiftr01_of_length_one h1 d]
        exact singleton_mem_W (by omega)
      · show shiftr01 0 d X ∈ W (m + 2 * d)
        exact ulift_step hbig (aop_clause3_to_clause2 hbig hd hgr)
  exact fun X hX => hsub hX

end TRIO

