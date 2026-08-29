/-
課題 L53: 置換補題を `z ∈ W m` についての帰納（`A2'`）で証明する計画。

## 向きの訂正（team-lead の指摘）

`Aop` の節 3 は「全部の graft が `W u`」⟹「`A ++ [t]` が `W u`」で、**短いほうを
長いほうから**出す。欲しいのは逆（`A ++ z'` を出す）なので、**`z` についての帰納**が本筋。

    shiftBlk t z := z.map (fun p => (p.1 + t.1, p.2.1, p.2.2))
    P(z) := ∀ A t, …文脈… → A ++ shiftBlk t z ∈ W u

`A2'` で `z` の 3 節に場合分けする。この file はその**骨組みと、各節が何に落ちるか**を
書いたもの。
-/
import Wtower2

namespace TRIO
namespace L53

open Wset

/-- `z` を `t` の行 0 の深さにずらしたもの（`graft` が作る形。`graft_snoc` 参照）。 -/
def shiftBlk (t : ℕ × ℕ × ℕ) (z : TrioSeq) : TrioSeq :=
  z.map fun p => ((p.1 + t.1, p.2.1, p.2.2) : ℕ × ℕ × ℕ)

@[simp] theorem shiftBlk_nil (t : ℕ × ℕ × ℕ) : shiftBlk t [] = [] := rfl

@[simp] theorem shiftBlk_length (t : ℕ × ℕ × ℕ) (z : TrioSeq) :
    (shiftBlk t z).length = z.length := by simp [shiftBlk]

/-! ## 節 1 の底 —— **`snoc_flat_root` が届く**（課題 L53 (1)）

節 1 は `|z| ≤ 1 ∧ lev z 0 = 0`、つまり `z'` は**レベル 0 の 1 列** `(x,0,0)`。
要るのは `A ++ [(x,0,0)] ∈ W u`。

既存の証明書を当てると:

    `snoc_zeroRow2`（`Wtower2.lean:3127`）… **`A` の行 2 ≡ 0** を要求。一般には届かない
    `snoc_orphan`（`:3053`）              … 足す列が**孤児**であることを要求。届かない
    **`snoc_flat_root`（`:2208`）          … ★ 届く**

```lean
theorem snoc_flat_root {u C p} (hC : C ∈ W u) (hCne : C ≠ [])
    (hsr  : srow (C ++ [p]) C.length = 0)                       -- p はフラット
    (hbp  : parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length = 0)  -- 親は**根**
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) :
    C ++ [p] ∈ W u
```

⟹ **節 1 の底は「足す列の行 0 の親が `A` の根であること」だけに落ちる。**
`z` が `based`（根の行 0 が 0）なら `z'` の根は `t.1` にあり、`t` は `A ++ [t]` の
末尾の孤児だったので、`A` の中で `t.1` より浅いのは根の側だけ。**多くの場合これで足りる。**

⚠ 足りないのは「`A` の中に `t.1` より浅い柱が根以外にもある」場合。
そこは `nextrel0` の最小性（谷が無い）が破れる場合で、**新しい仮定に切り出す必要がある**。 -/
def SubstBase : Prop :=
  ∀ (u : ℕ) (A : TrioSeq) (x : ℕ), A ∈ W u → A ≠ [] →
    A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)] ∈ W u

/-- **★ 節 1 の底は `snoc_flat_root` で出る**（親が根のとき）。 -/
theorem substBase_of_flat_root {u : ℕ} {A : TrioSeq} {x : ℕ} (hA : A ∈ W u)
    (hAne : A ≠ [])
    (hsr : srow (A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) A.length = 0)
    (hbp : parent (A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) A.length) A.length = 0)
    (hpar : hasParent (A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) A.length) A.length) :
    A ++ [((x, 0, 0) : ℕ × ℕ × ℕ)] ∈ W u :=
  snoc_flat_root hA hAne hsr hbp hpar

/-! ## 節 2 —— 交換律（課題 L53 の本体） -/

/-- **(SCOMM)** 節 2 で要る交換律。`A` に置いても展開が `z` の中で閉じること。

⚠ **上昇行列 `A_xy` は行列全体の木で決まる**ので、`z'` 単体で計算した上昇と
`A ++ z'` の中で計算した上昇はずれうる。H11 の実測では
**ずれるのは行 1 だけ**（非一様な写し 556 件が 100% 「行 0 は一様・行 1 だけ列ごと・
行 2 は不動」）＝ (MLIFT)。 -/
def SComm : Prop :=
  ∀ (A : TrioSeq) (t : ℕ × ℕ × ℕ) (z : TrioSeq) (n : ℕ), 1 ≤ n → 1 < z.length →
    (A ++ shiftBlk t z)⟦n⟧ = A ++ shiftBlk t (z⟦n⟧)

/-! ## 節 3 —— 孤児が孤児のまま（「復活しない」） -/

/-- **(SDOM)** 節 3 で要るもの: `z` の末尾の孤児が `A ++ z'` でも孤児のまま。
`A` が親を供給すると破れる（＝ **復活**）。 -/
def SDom : Prop :=
  ∀ (A : TrioSeq) (t : ℕ × ℕ × ℕ) (z : TrioSeq) (m' : ℕ), 1 < z.length →
    domT z m' → domT (A ++ shiftBlk t z) m'

/-! ## ★ 課題 L53 (2): 「レベル 0 の孤児で `|z| > 1`」は**実在する**

`domT` はレベル `≥ 1` を要求するので、この場合は節 3 が使えない。そして
`A` が行 0 の親を供給すると交換律も破れる。**隙間はここ 1 つ。** -/

/-- 最小の証人。`|z| = 2 > 1`、末尾のレベルは 0、しかも `z` の中では孤児。 -/
def Zgap : TrioSeq := [(0, 0, 0), (0, 0, 0)]

theorem Zgap_len : 1 < Zgap.length := by decide

theorem Zgap_lev : lev Zgap (Zgap.length - 1) = 0 := rfl

theorem Zgap_based : based Zgap := rfl

/-- `Zgap` の末尾は `z` の中で**孤児**（行 0 で真に浅い柱が無い）。 -/
theorem Zgap_orphan :
    ¬ hasParent Zgap (srow Zgap (Zgap.length - 1)) (Zgap.length - 1) := by
  intro h
  obtain ⟨j0, hj0, -⟩ := h
  have hsr : srow Zgap (Zgap.length - 1) = 0 := rfl
  rw [hsr] at hj0
  rw [nextR] at hj0
  simp only [if_pos rfl] at hj0
  have hlt := hj0.2.2.2.1
  simp [entry, Zgap] at hlt

/-- `Zgap` は行 2 ≡ 0 なので `Wself`。⟹ **帰納の母集団に本当に現れる**。 -/
theorem Zgap_mem : Zgap ∈ Wself := by
  refine zeroRow2_mem_Wself ?_
  intro p hp
  simp only [Zgap] at hp
  rcases List.mem_cons.mp hp with h | h
  · rw [h]
  · rcases List.mem_cons.mp h with h2 | h2
    · rw [h2]
    · simp at h2

/-- **⟹ `domT Zgap m'` はどの `m'` でも成り立たない**（レベルが 0 だから）。
節 3 が使えないことの証明。 -/
theorem Zgap_not_domT (m' : ℕ) : ¬ domT Zgap m' := by
  intro h
  have h1 := h.1
  rw [Zgap_lev] at h1
  omega

/-! ## まとめ —— 3 節がどこに落ちるか

    節 1  `|z| ≤ 1`            → **`snoc_flat_root`**（親が根のとき）。`SubstBase`
    節 2  `∀ n, z⟦n⟧ ∈ X`      → **交換律 (SCOMM)**。ずれるのは**行 1 だけ**＝ (MLIFT)
    節 3  `domT z m'`          → **(SDOM)**「孤児が孤児のまま」＝ 復活しないこと
    隙間  レベル 0 の孤児 `|z| > 1` → **実在**（`Zgap`）。節 3 が使えず、
                                    `A` が行 0 の親を供給すると交換律も破れる

⟹ **`Subst1g` の本体は (SCOMM) と (SDOM) の 2 本＋隙間 1 つ**である。 -/

/-! ## 課題 L53-c: 「逃げるかは 1 段目で決まる」は **`oper` の定義から出る**

`oper M n` は `j1 = |M|-1`、`i1 = srow M j1`、`j0 = parent M i1 j1`、`d0`、`d1` を
**`M` だけから**決め、`n` は `(List.range n).flatMap` にしか現れない。
⟹ **バッドルートの位置も上昇量も `n` に依らない。**

H11 の「K 感度ゼロ（K=1,2,4,8 で逃げる行の集合が完全に同一）」は、
**同じ行列に対しては定義から自明**である（測定が確かめたのは、塔を伸ばしても
逃げ方が変わらない、という**別の行列どうし**の話）。

下の `oper_unfold` がその形。**3 つの `if` を潰した一般形**なので、
個別の行列（`M275` / `M284` / `M316`）で手作業していた部分がこれ 1 本で済む。 -/

open Classical in
/-- **★ `oper` の展開（3 つの `if` を潰した一般形）。**

`j0`（バッドルート）・`d0`・`d1` は **`M` だけで決まり `n` に依らない**。 -/
theorem oper_unfold {M : TrioSeq} {j1 i1 j0 d0 d1 : ℕ}
    (hj1 : j1 = M.length - 1) (hj1ne : j1 ≠ 0)
    (hz : ¬(entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0))
    (hi1 : i1 = srow M j1) (hpar : hasParent M i1 j1)
    (hj0 : j0 = parent M i1 j1)
    (hd0 : d0 = if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)
    (hd1 : d1 = if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) (n : ℕ) :
    M⟦n⟧ = M.take j0 ++ (List.range n).flatMap fun k =>
      (List.range' j0 (j1 - j0)).map fun j =>
        ((entry M 0 j + (if le0 M j0 j then k * d0 else 0),
          entry M 1 j + (if le1 M j0 j then k * d1 else 0),
          entry M 2 j) : ℕ × ℕ × ℕ) := by
  subst hj1
  subst hi1
  subst hj0
  rw [oper]
  dsimp only
  rw [if_neg hj1ne, if_neg hz, if_neg (not_not_intro hpar)]
  subst hd0
  subst hd1
  rfl

open Classical in
/-- **`n` に依らないことの系**: 2 つの展開は同じ接頭辞・同じ写しを共有する。 -/
theorem oper_prefix_indep {M : TrioSeq} {j1 i1 j0 d0 d1 : ℕ}
    (hj1 : j1 = M.length - 1) (hj1ne : j1 ≠ 0)
    (hz : ¬(entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0))
    (hi1 : i1 = srow M j1) (hpar : hasParent M i1 j1)
    (hj0 : j0 = parent M i1 j1)
    (hd0 : d0 = if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)
    (hd1 : d1 = if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) (n : ℕ) :
    M⟦n + 1⟧ = M⟦n⟧ ++ (List.range' j0 (j1 - j0)).map fun j =>
        ((entry M 0 j + (if le0 M j0 j then n * d0 else 0),
          entry M 1 j + (if le1 M j0 j then n * d1 else 0),
          entry M 2 j) : ℕ × ℕ × ℕ) := by
  rw [oper_unfold hj1 hj1ne hz hi1 hpar hj0 hd0 hd1 (n + 1),
    oper_unfold hj1 hj1ne hz hi1 hpar hj0 hd0 hd1 n]
  rw [List.range_succ, List.flatMap_append]
  simp [List.append_assoc]

/-! ## 課題 L53-b: 復活なしの (TOWER)

H11 の実測（構造だけ、所属判定を使わない、4482 行）:

    段の幅 b >= 2 に限ると逃げるのは 577 / 3743 = 15.4%
    **b >= 2 では逃げ先の 100% が `A` の中**（前の段に落ちるのは 0 件）
    ⟹ **復活は塔の内部では起きない。段どうしの相互作用は考えなくてよい。**
    (a) 一様な塔 逃げる 10.4% ／ (b) 行 1 に印つき 逃げる 43.9%
    ⟹ (MLIFT) と (REVIVE) は同じ難所の 2 つの顔 -/

/-- **復活しない**: `A ++ z'` のバッドルートが `z'` の側にある。 -/
def NoRevive (A z' : TrioSeq) : Prop :=
  A.length ≤ parent (A ++ z')
    (srow (A ++ z') ((A ++ z').length - 1)) ((A ++ z').length - 1)

/-- **(TOWER-NR)** 復活なしの版。実測では `b >= 2` の **84.6%**、
一様な塔に限れば **89.6%** がここに入る。 -/
def TowerNoRevive : Prop :=
  ∀ (u : ℕ) (A : TrioSeq) (t : ℕ × ℕ × ℕ) (z : TrioSeq),
    A ∈ W u → A ≠ [] → z ∈ Wself → based z → 1 < z.length →
    NoRevive A (shiftBlk t z) →
    A ++ shiftBlk t z ∈ W u


/-! ## 課題 L54-a: `Blk` —— 実際に現れる段だけに制限する

実測（SESSION §47、シート 4467 行の 1 段目 `Q`）:

    Q の中に親を持つ   3153  70.58%   節 2（SCOMM）
    |Q| <= 1            734  16.43%   節 1（snoc_flat_root）
    孤児で lev >= 1     578  12.94%   節 3（SDOM）
    **Zgap の形            0   0.00%**

⟹ **3 節がちょうど分割し、穴は 1 件も出ない。** 2 段目でも 0 件。 -/

/-- **段のクラス**: `Zgap`（レベル 0 の孤児で `|z| > 1`）だけを除いたもの。 -/
def Blk (z : TrioSeq) : Prop :=
  z.length ≤ 1 ∨
    hasParent z (srow z (z.length - 1)) (z.length - 1) ∨
    (¬ hasParent z (srow z (z.length - 1)) (z.length - 1) ∧
      1 ≤ lev z (z.length - 1))

/-- **`Blk` は「`Zgap` の形を除く」と同値**。 -/
theorem blk_iff (z : TrioSeq) :
    Blk z ↔ ¬(1 < z.length ∧
      ¬ hasParent z (srow z (z.length - 1)) (z.length - 1) ∧
      lev z (z.length - 1) = 0) := by
  classical
  unfold Blk
  constructor
  · rintro (h | h | ⟨-, h⟩) ⟨h1, h2, h3⟩
    · omega
    · exact h2 h
    · omega
  · intro h
    by_cases hp : hasParent z (srow z (z.length - 1)) (z.length - 1)
    · exact Or.inr (Or.inl hp)
    · by_cases hl : 1 ≤ lev z (z.length - 1)
      · exact Or.inr (Or.inr ⟨hp, hl⟩)
      · left
        by_contra hc
        exact h ⟨by omega, hp, by omega⟩

/-- **`Zgap` は `Blk` でない**（除かれる形の証人）。 -/
theorem Zgap_not_blk : ¬ Blk Zgap := by
  rw [blk_iff]
  intro h
  exact h ⟨Zgap_len, Zgap_orphan, Zgap_lev⟩

/-- **制限した置換補題**（課題 L54-a）。一般の `z ∈ W m` では `Zgap` があるので偽。
`Blk z` を足すと実測の 100% が入る。 -/
def SubstBlk : Prop :=
  ∀ (u m : ℕ) (A : TrioSeq) (t : ℕ × ℕ × ℕ) (z : TrioSeq),
    A ∈ W u → A ≠ [] → z ∈ W m → based z → Blk z →
    A ++ shiftBlk t z ∈ W u

/-- **`Blk` は展開と `graft` で閉じる**（実測では 2 段の深さまで確認）。
`SubstBlk` の帰納を回すのに要る。 -/
def BlkClosed : Prop :=
  (∀ (z : TrioSeq) (n : ℕ), Blk z → 1 ≤ n → Blk (z⟦n⟧)) ∧
  (∀ (z y : TrioSeq), Blk z → based y → Blk y → Blk (graft z y))

/-! ## 課題 L54-b: (SDOM) は「`A` の側に真に浅い列が無い」だけで出る -/

/-- **★ 真に浅い列が無ければ親は無い。** `nextrel0/1/2` はどれも
「`entry M i j0 < entry M i j1`」を含むので、行 `i` で真に浅い列が無ければ即座に出る。 -/
theorem not_hasParent_of_no_shallow {M : TrioSeq} {i j1 : ℕ}
    (h : ∀ j, j < j1 → entry M i j1 ≤ entry M i j) : ¬ hasParent M i j1 := by
  intro hp
  obtain ⟨j0, hj0, -⟩ := hp
  rw [nextR] at hj0
  split at hj0
  · rename_i hi
    subst hi
    have h1 := h j0 hj0.2.2.1
    have h2 := hj0.2.2.2.1
    omega
  · split at hj0
    · rename_i hi
      subst hi
      have h1 := h j0 hj0.2.2.1
      have h2 := hj0.2.2.2.1
      omega
    · rename_i hi0 hi1
      -- `entry` は `i ≥ 2` でどれも行 2 を返す
      have he : ∀ j, entry M i j = entry M 2 j := fun j => by
        simp [entry, hi0, hi1]
      have h1 := h j0 hj0.2.2.1
      rw [he, he] at h1
      have h2 := hj0.2.2.2.1
      omega

/-- **(SDOM) の具体形**（課題 L54-b）。`z'` の末尾が `z'` の中で孤児でも、
`A` が親を供給すると復活する。**供給しない条件は「`A` の側に真に浅い列が無い」だけ。** -/
theorem sdom_of_no_shallow {A z' : TrioSeq}
    (h : ∀ j, j < (A ++ z').length - 1 →
      entry (A ++ z') (srow (A ++ z') ((A ++ z').length - 1))
          ((A ++ z').length - 1)
        ≤ entry (A ++ z') (srow (A ++ z') ((A ++ z').length - 1)) j) :
    ¬ hasParent (A ++ z') (srow (A ++ z') ((A ++ z').length - 1))
      ((A ++ z').length - 1) :=
  not_hasParent_of_no_shallow h

/-! ### `snoc_orphan` との違い

    `snoc_orphan`（`Wtower2.lean:3053`）
      仮定 `¬ hasParent (A ++ [t]) …`   ← **全体で孤児**であることを直に要求
    `sdom_of_no_shallow`
      仮定 「行 `srow` で真に浅い列が無い」 ← **`A` と `z'` を分けて確かめられる**

⟹ (SDOM) は `snoc_orphan` の仮定を**確かめやすい形に分解したもの**。
`z'` の側は `z` が孤児であることから、`A` の側は上の不等式から出る。 -/

/-! ## 課題 L54-c: (SCOMM) のずれは行 1 だけ ＝ (MLIFT)

H11 の実測（非一様な写し 556 件）: **100% が「行 0 は一様・行 1 だけ列ごと・行 2 は不動」**。
⟹ `(A ++ z')⟦n⟧` と `A ++ (z⟦n⟧)'` の差は**行 1 のマスクつき持ち上げ**だけ。

`mlift_mem_W`（`Wslift.lean:146`、**証明ずみ**）は行 1 の階段状持ち上げを
`W (m + 2d)` へ運ぶ。⟹ **(SCOMM) と (MLIFT) は同じ 1 本。**
橋は `Lift1_eq_mlift_of_tieFree`（`Wtower2.lean:76`）で、条件は `TieFree`
（課題 L10 で標準形の族では空虚と判明）。 -/

/-- **(SCOMM-R1)** ずれが行 1 だけであること。行 0 と行 2 は一致する。 -/
def SCommRow1 : Prop :=
  ∀ (A : TrioSeq) (t : ℕ × ℕ × ℕ) (z : TrioSeq) (n : ℕ), 1 ≤ n → 1 < z.length →
    Blk z →
    ((A ++ shiftBlk t z)⟦n⟧).length = (A ++ shiftBlk t (z⟦n⟧)).length ∧
    (∀ j, entry ((A ++ shiftBlk t z)⟦n⟧) 0 j
        = entry (A ++ shiftBlk t (z⟦n⟧)) 0 j) ∧
    (∀ j, entry ((A ++ shiftBlk t z)⟦n⟧) 2 j
        = entry (A ++ shiftBlk t (z⟦n⟧)) 2 j) ∧
    (∀ j, entry (A ++ shiftBlk t (z⟦n⟧)) 1 j
        ≤ entry ((A ++ shiftBlk t z)⟦n⟧) 1 j)


/-! ## 課題 L55-b: (C13) —— `srow = 0`（持ち上げ無し）の節 2 -/

open Classical in
/-- **★ `srow M j1 = 0` なら上昇が無いので、写しは `k` に依らない。** -/
theorem oper_flat {M : TrioSeq} {j1 j0 : ℕ}
    (hj1 : j1 = M.length - 1) (hj1ne : j1 ≠ 0)
    (hz : ¬(entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0))
    (hsr : srow M j1 = 0) (hpar : hasParent M 0 j1) (hj0 : j0 = parent M 0 j1)
    (n : ℕ) :
    M⟦n⟧ = M.take j0 ++ (List.range n).flatMap fun _ =>
      (List.range' j0 (j1 - j0)).map fun j =>
        ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ) := by
  rw [oper_unfold (i1 := 0) (d0 := 0) (d1 := 0) hj1 hj1ne hz hsr.symm hpar hj0
    (by simp) (by simp) n]
  simp

/-- **★★ (C13)**: `srow = 0` の行は、節 2 が `W_flatMap_copies` ＋ `W_add` で
`∀ n` いっぺんに閉じる。`rsum` が `n` に依らないのが要点。 -/
theorem mem_W_of_flat {u : ℕ} {M Q : TrioSeq} {j1 j0 : ℕ}
    (hj1 : j1 = M.length - 1) (hj1ne : j1 ≠ 0)
    (hz : ¬(entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0))
    (hsr : srow M j1 = 0) (hpar : hasParent M 0 j1) (hj0 : j0 = parent M 0 j1)
    (hQdef : Q = (List.range' j0 (j1 - j0)).map fun j =>
      ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))
    (hA : M.take j0 ∈ W u) (hQ : Q ∈ W u) (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1)
    (hrs : ∀ n : ℕ, rsum (M.take j0) ((List.range n).flatMap fun _ => Q)) :
    M ∈ W u := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  rw [oper_flat hj1 hj1ne hz hsr hpar hj0 n, ← hQdef]
  exact W_add hA (W_flatMap_copies hQ hQr n) (hrs n)

/-! ## ★ 課題 L55-a: 行 278 は **`rsum` が破れるので (C13) では落ちません**

    行 278  (0,0,0)(1,1,1)(1,0,0)(2,1,0)
    M⟦n⟧ = (0,0,0)(1,1,1) ++ [(1,0,0),(2,0,0),…,(n,0,0)]       ← 平らな梯子

梯子 `Lad n` 自身に (C13) を当てると:

    末尾 `(n,0,0)` は `srow = 0`                      ✓ `oper_flat` が使える
    行 0 の親は **1 つ前の `(n-1,0,0)`**（増加列で谷が無いから）
      ⟹ `j0 = |Lad n| - 2 ≠ 0` なので `mem_W_of_flat_root` は使えない
    `Q = [(n-1,0,0)]`、`M.take j0` は `(0,0,0)` を含む
      ⟹ **`rsum (M.take j0) (Q^m)` は `entry Q 0 0 = n-1 > 0 = (0,0,0).1` で破れる**

⟹ **(C13) の側条件 `rsum` が、梯子では `k ≥ 2` から必ず破れる。**
`snoc_flat_root`（親が根）が `k ≥ 2` で届かないのと**同じ理由**である
（親が根から離れる ＝ 根が `Q` より浅くなる）。

下の `example` がその形（`A = (0,0,0)(1,1,1)`、`B = [(1,0,0)]`）。 -/
example : ¬ rsum [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1)] [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
  intro h
  have h9 := h (0, 0, 0) (by simp)
  simp [entry] at h9


/-! ## 課題 L55'-a: `parent = 0` はどこで効いているか

`snoc_flat_root` の docstring:「親が根なら**写しは `C` そのもの**なので、
`W_flatMap_copies` が核を使わずに閉じる」。`oper_flat` で書き下すと理由が見える:

    M⟦n⟧ = **M.take j0** ++ (range n).flatMap (fun _ => Q)

    j0 = 0 … `M.take 0 = []` なので **`W_flatMap_copies` だけで閉じる。`rsum` は不要**
    j0 > 0 … `W_add` が要り、その側条件 `rsum (M.take j0) (Q^n)` は
             **`M.take j0` に `Q` の根より浅い列があると破れる**

⟹ **`parent = 0` が効いているのは「`take` が空になる」ことだけ。**
これが (SNOC-flat) の核である。 -/

/-- **★ `j0 = 0`（親が根）なら `rsum` が要らない。** `M.take 0 = []` なので
`W_flatMap_copies` がそのまま閉じる。 -/
theorem mem_W_of_flat_root {u : ℕ} {M Q : TrioSeq} {j1 : ℕ}
    (hj1 : j1 = M.length - 1) (hj1ne : j1 ≠ 0)
    (hz : ¬(entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0))
    (hsr : srow M j1 = 0) (hpar : hasParent M 0 j1) (hj0 : parent M 0 j1 = 0)
    (hQdef : Q = (List.range' 0 (j1 - 0)).map fun j =>
      ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))
    (hQ : Q ∈ W u) (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) : M ∈ W u := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  rw [oper_flat (j0 := 0) hj1 hj1ne hz hsr hpar hj0.symm n, ← hQdef]
  simp only [List.take_zero, List.nil_append]
  exact W_flatMap_copies hQ hQr n

/-! ## 課題 L55'-b: 「行 2 ≡ 0 ＋ 途中に任意の 1 列」は作れない（理由）

行 278 の梯子は `(0,0,0)` `(1,1,1)` `(1,0,0)` `(2,0,0)` … で、
**行 2 = 1 は添字 1 だけ**。`snoc_zeroRow2` は「行 2 ≡ 0 ＋ **末尾**に任意の 1 列」なので届かない。

⚠ **「途中に 1 列」版は、いまの道具では作れない。** 理由は課題 L49 で確定している:

`zeroRow2_mem_Wself`（`Wtower2.lean:3011`）の中身は

    M を 2 行の `YAPSS.PairSeq` に落とす（行 2 ≡ 0 だから戻せる）
    `YAPSS.Wset.mem_W_maxr1`（**2 行の定理を丸ごと**）
    `PairBridge.emb_mem_W` で戻す

つまり**技巧ではなく輸入**であり、行 2 = 1 の列が 1 本でも混ざると
**2 行の断片から出てしまう**ので、この経路は使えない。

`snoc_zeroRow2`（末尾 1 列）が通るのは、末尾の列が**展開で剥がれる**からで、
途中の列は**悪い部分に入ると複製される**（`PROOF-STATUS §5` の「末尾 2 列は通らない」と同じ）。

⟹ 行 278 の梯子で `(1,1,1)` が複製されないのは**この行列に固有の事情**（悪い部分が
末尾側にある）であって、`Blk` のような**構文的な条件では捕まえられない**。

**⟹ (SNOC-flat) は「`take` が空でない場合の `rsum`」＝ 節 3（graft）＝ 残核**
（課題 L52-a で Lean 同一視ずみ）。 -/


/-! ## 課題 L56: 残余は `WCat` ただ 1 本

R1 の測定（SESSION §50）:

    神託なし        ラダー 10 行 / 覆い 10
    (TOW) だけ      ラダー 10 行（**1 行も伸びない**）/ 覆い 50
    **rsum を外す（＝ WCat）  ラダー 16 行** / 覆い 29
    両方            ラダー 24 行 / 覆い 98

⟹ **ラダーを伸ばすのは `WCat`。** そして `(TOW)` は `WCat` から出る
（`shiftTowerClosed_of_cat`）ので **実質 `WCat` 1 本**。

下の `mem_W_of_flat_cat` が、(C13) の `rsum` を `WCat` に置き換えたもの。
**`rsum` は `W_add` の側条件でしかなく、`WCat` があれば要らない。** -/

/-- **★★ (C13) の `WCat` 版**: `rsum` を仮定に持たない。 -/
theorem mem_W_of_flat_cat {u : ℕ} {M Q : TrioSeq} {j1 j0 : ℕ} (hcat : WCat)
    (hj1 : j1 = M.length - 1) (hj1ne : j1 ≠ 0)
    (hz : ¬(entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0))
    (hsr : srow M j1 = 0) (hpar : hasParent M 0 j1) (hj0 : j0 = parent M 0 j1)
    (hQdef : Q = (List.range' j0 (j1 - j0)).map fun j =>
      ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))
    (hA : M.take j0 ∈ W u) (hQ : Q ∈ W u) (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) :
    M ∈ W u := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  rw [oper_flat hj1 hj1ne hz hsr hpar hj0 n, ← hQdef]
  exact hcat u _ _ hA (W_flatMap_copies hQ hQr n)

/-- **(SNOC-flat)** —— `snoc_flat_root`（`Wtower2.lean:2208`）から
**「親が根」`parent = 0` を外した**もの（課題 L56-a で切り出す命題）。 -/
def SnocFlat : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ∈ W u → C ≠ [] →
    srow (C ++ [p]) C.length = 0 →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length →
    C ++ [p] ∈ W u

/-- **`snoc_flat_root` は (SNOC-flat) の `parent = 0` の場合**。 -/
theorem snocFlat_root_case {u : ℕ} {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hC : C ∈ W u)
    (hCne : C ≠ []) (hsr : srow (C ++ [p]) C.length = 0)
    (hbp : parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length = 0)
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) :
    C ++ [p] ∈ W u :=
  snoc_flat_root hC hCne hsr hbp hpar

/-! ### 課題 L56-b: (SNOC-flat) と残核の関係

`mem_W_of_flat_cat` のとおり、`j0 > 0` のときに要るのは **`M.take j0` と写しの連結**
だけである。⟹ **`WCat` があれば (SNOC-flat) は出る**（`rsum` は要らない）。

    `WCat`      `A ∈ W u → B ∈ W u → A ++ B ∈ W u`
    `WSnoc`     1 列版。`wcat_of_snoc : WSnoc → WCat`
    `SubstClosedG` / `Subst1gReviveSelf`   残核

R1 の §R42 のとおり **`WCat` は残核より広い**ので、
**残核に落ちるならそちらが標的**である。課題 L52-a で

    「深い側に足す」＝ `Aop` の節 3（`graft`）　（`graft_snoc` / `wAddDeep_of_clause3`）

を Lean 上で同一視したので、**(SNOC-flat) → `WCat` → 節 3 → 残核**という向きは付いている。
逆（残核 → `WCat`）は `substClosed_of_substClosedG` 経由で既にある。

⟹ **標的は `WCat`。(SNOC-flat) はその 1 列版であり、`mem_W_of_flat_cat` で
`WCat` から機械的に出る。** -/


/-! ## 課題 L57: 「印」で 2 本立てにする

H11 の判別子（SESSION §51、`b>=2` かつ `t=2` の 1586 行）:

    段の最後の列の**印 = 1**（行 1 が上がる） ⟹ 復活する **0 / 1329**（例外なし）
    段の最後の列の**印 = 0**                  ⟹ 復活する 244 / 257（94.9%）
    一致率 **99.2%**

⟹ **(MLIFT) と (REVIVE) は同じ 1 つの量で決まる。** -/

open Classical in
/-- **印**（課題 L57-a）: 段の最後の列 `j1 - 1` で**行 1 が上がる**か。

`oper_unfold` の `d1 = if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0` が
正で、かつその列が上昇の対象（`le1 M j0 (j1-1)`）であること。 -/
def MarkOne (M : TrioSeq) : Prop :=
  1 < srow M (M.length - 1) ∧
  entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
    < entry M 1 (M.length - 1) ∧
  le1 M (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1 - 1)

open Classical in
/-- 印が立っていれば `oper_unfold` の `d1` は正。 -/
theorem d1_pos_of_markOne {M : TrioSeq} (h : MarkOne M) :
    0 < (if 1 < srow M (M.length - 1) then
          entry M 1 (M.length - 1)
            - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
         else 0) := by
  rw [if_pos h.1]
  have h9 := h.2.1
  omega

/-! ### 課題 L57-b: (TOWER-易) —— 印 = 1 の塔

「印 = 1 ⟹ バッドルートが段の中に留まる」を `oper` の定義から出したい。
写しの行 1 は段ごとに `d1` ずつ**真に増える**ので、`k` 段目の最後の列にとって
`k-1` 段目の同じ列が**行 1 で真に浅い候補**になる。⟹ 親は段の中で見つかり、
前置きまで戻らない。

⚠ **成り立つのは `srow = 1` のとき。** `srow = 2` だと親は**行 2** で探すが、
行 2 は写しで**不変**（上昇行列 `A_xy` は行 2 に乗らない）なので、
候補は写しの外（前置き）にもありうる。

    srow = 1 … 行 1 が段ごとに増える ⟹ **段の中に親がいる**（復活しない）
    srow = 2 … 行 2 が不変          ⟹ **段の外に逃げうる**（復活）

⟹ H11 の「印 = 1 なら復活 0/1329」は、**`srow = 1` の場合の構造**である。
`t = 2` の母集団で測ったので、印 = 0 は `srow = 2`（行 2 で親を探す）に対応する。 -/

/-- **(TOWER-易)**: 印 = 1 の段だけからなる塔は復活しない。 -/
def TowerEasy : Prop :=
  ∀ (u : ℕ) (M : TrioSeq), M ∈ W u → MarkOne M →
    ∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ W u

/-! ### 課題 L57-c: 帰納は 2 つだけ見ればよい

H11 の実測（「復活は 1 段目で決まる」＋「復活は 1 回で済む、直後は 98.1% が逃げない」）と、
私が課題 L53-c で示した **`oper_unfold` による `n` 非依存性**を合わせると:

    バッドルート `j0`・上昇量 `d0`,`d1` は `M` だけで決まり `n` に依らない（`oper_unfold`）
    ⟹ 同じ行列については「何段目か」を見る必要が無い
    ⟹ 見るのは **最初の 1 段** と **復活直後の 1 段** の 2 つだけ

**復活の正体**（H11、577 件で例外なし）:

    塔のまま 100% ／ 新しい `Q` に古い `Q` が部分列として入る 100% ／ 新しい `b` > 古い `b` 100%
    ⟹ **復活 ＝ 段が古い段を丸ごと飲み込んで太る ＝ 1 つ上のレベルへ繰り上がる**

`ebp2bms/algorithm/2` の `M(Ω_v) = B ++ L(B) ++ L²(B) ++ …`
（「基数の後続 1 段 ＝ 持ち上げ 1 回」）と同じ構造。 -/

/-- **(TOWER-2)**: 帰納で見るのは「最初の 1 段」と「復活直後の 1 段」の 2 つだけ。 -/
def TowerTwoStage : Prop :=
  ∀ (u : ℕ) (M : TrioSeq), M ∈ W u →
    (∀ n : ℕ, 1 ≤ n → MarkOne (M⟦n⟧) → M⟦n⟧ ∈ W u) →
    (∀ n : ℕ, 1 ≤ n → ¬ MarkOne (M⟦n⟧) → M⟦n⟧ ∈ W u) →
    ∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ W u


/-! ## 課題 L58: 交換律 (COMM) を `oper` の定義から計算する -/

/-- **L58-a**: バッドルートが `B` の側なら `take` は `A` を丸ごと含む。 -/
theorem take_append_of_le {A B : TrioSeq} {j0 : ℕ} (h : A.length ≤ j0) :
    (A ++ B).take j0 = A ++ B.take (j0 - A.length) := by
  rw [List.take_append, List.take_of_length_le h]

/-- 右側の列の成分は `A` を付けても変わらない。 -/
theorem entry_append_right {A B : TrioSeq} {i j : ℕ} :
    entry (A ++ B) i (A.length + j) = entry B i j := by
  unfold entry
  simp only []
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

/-- `srow` も右側の列では変わらない。 -/
theorem srow_append_right {A B : TrioSeq} {j : ℕ} :
    srow (A ++ B) (A.length + j) = srow B j := by
  unfold srow
  rw [entry_append_right, entry_append_right]

open Classical in
/-- **★★ (COMM)**（課題 L58-c）。`oper` を 2 回開くだけの計算。

仮定は **3 つだけ**:

* `j0` が `|A|` ずれる（＝ バッドルートが `N` の中）… H43 の「印 = 1 なら 0/1329」
* `le0` のマスクが一致する … H41 の「行 0 が非一様なものは 0 件」
* `le1` のマスクが一致する … **ここだけがずれる ＝ (MLIFT)**

**`d0` と `d1` の一致は仮定に要らない。** `j0` のずれと `entry_append_right` から
自動的に出る（`d0`/`d1` は `entry` の差でしかないから）。 -/
theorem comm_of_parts {A N : TrioSeq} {jN j0N iN : ℕ} (n : ℕ) (hNne : N ≠ [])
    (hjN : jN = N.length - 1) (hjNne : jN ≠ 0)
    (hzN : ¬(entry N 0 jN = 0 ∧ entry N 1 jN = 0 ∧ entry N 2 jN = 0))
    (hiN : iN = srow N jN) (hparN : hasParent N iN jN) (hj0N : j0N = parent N iN jN)
    (hparM : hasParent (A ++ N) iN (A.length + jN))
    (hj0M : parent (A ++ N) iN (A.length + jN) = A.length + j0N)
    (hle0 : ∀ j, le0 (A ++ N) (A.length + j0N) (A.length + j) ↔ le0 N j0N j)
    (hle1 : ∀ j, le1 (A ++ N) (A.length + j0N) (A.length + j) ↔ le1 N j0N j) :
    (A ++ N)⟦n⟧ = A ++ N⟦n⟧ := by
  have hNpos : 0 < N.length := List.length_pos_iff.mpr hNne
  have hlenM : (A ++ N).length - 1 = A.length + jN := by
    rw [List.length_append, hjN]; omega
  have hsrM : srow (A ++ N) (A.length + jN) = iN := by
    rw [srow_append_right, hiN]
  have hzM : ¬(entry (A ++ N) 0 (A.length + jN) = 0 ∧
      entry (A ++ N) 1 (A.length + jN) = 0 ∧
      entry (A ++ N) 2 (A.length + jN) = 0) := by
    rw [entry_append_right, entry_append_right, entry_append_right]
    exact hzN
  rw [oper_unfold (M := A ++ N) (j1 := A.length + jN) (i1 := iN)
      (j0 := A.length + j0N) hlenM.symm (by omega) hzM hsrM.symm hparM hj0M.symm
      rfl rfl n,
    oper_unfold (M := N) hjN hjNne hzN hiN hparN hj0N rfl rfl n,
    take_append_of_le (by omega)]
  have hsub : A.length + jN - (A.length + j0N) = jN - j0N := by omega
  rw [hsub, Nat.add_sub_cancel_left, List.append_assoc]
  refine congrArg (fun L => A ++ L) ?_
  refine congrArg (fun L => N.take j0N ++ L) ?_
  refine congrArg (fun f => (List.range n).flatMap f) ?_
  funext k
  rw [show List.range' (A.length + j0N) (jN - j0N)
      = (List.range' j0N (jN - j0N)).map (A.length + ·) from
    (List.map_add_range' _ _ _).symm, List.map_map]
  refine List.map_congr_left ?_
  intro j _
  simp only [Function.comp_apply]
  simp only [entry_append_right]
  simp only [if_congr (hle0 j) rfl rfl, if_congr (hle1 j) rfl rfl]


/-! ## 課題 L58 の 4 / L59: 祖先関係の移送

`nextrel0/1/2` の鎖は添字が増えるので `[j0, j1]` に留まる。⟹ `A` を前に足しても
右側だけで決まる。**これが (COMM) の `le0` / `le1` の仮定を落とす鍵。** -/

/-- **`nextrel0` の移送**。 -/
theorem nextrel0_append_right {A N : TrioSeq} {a b : ℕ} :
    nextrel0 (A ++ N) (A.length + a) (A.length + b) ↔ nextrel0 N a b := by
  unfold nextrel0
  simp only [List.length_append, entry_append_right]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, h4, ?_⟩
    intro j hj
    have h9 := h5 (A.length + j) ⟨by omega, by omega⟩
    rwa [entry_append_right] at h9
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, h4, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    have h9 := h5 j' ⟨by omega, by omega⟩
    rwa [entry_append_right]

/-- 右側から出た `nextrel0` の鎖は右側に留まる。 -/
theorem rtg0_of_append {A N : TrioSeq} {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (A ++ N)) (A.length + a) c) :
    ∃ c', c = A.length + c' ∧ Relation.ReflTransGen (nextrel0 N) a c' := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | tail _ h2 ih =>
      obtain ⟨c', hc, hchain⟩ := ih
      subst hc
      rename_i d _
      obtain ⟨d', rfl⟩ : ∃ d', d = A.length + d' :=
        ⟨d - A.length, by have := h2.2.2.1; omega⟩
      exact ⟨d', rfl, hchain.tail (nextrel0_append_right.mp h2)⟩

/-- 右側の `nextrel0` の鎖は `A` を足しても鎖のまま。 -/
theorem rtg0_to_append {A N : TrioSeq} {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 N) a c) :
    Relation.ReflTransGen (nextrel0 (A ++ N)) (A.length + a) (A.length + c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact ih.tail (nextrel0_append_right.mpr h2)

/-- **★ `le0` の移送**（課題 L58 の 4 の前半）。 -/
theorem le0_append_right {A N : TrioSeq} {a b : ℕ} :
    le0 (A ++ N) (A.length + a) (A.length + b) ↔ le0 N a b := by
  unfold le0
  simp only [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨c', hc, hchain⟩ := rtg0_of_append h3
    have hb : c' = b := by omega
    subst hb
    exact ⟨by omega, by omega, hchain⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, rtg0_to_append h3⟩


/-- **`nextrel1` の移送**。最小性の `∀ j` は `le0 M j j1` から `j ≤ j1` に限られる。 -/
theorem nextrel1_append_right {A N : TrioSeq} {a b : ℕ} :
    nextrel1 (A ++ N) (A.length + a) (A.length + b) ↔ nextrel1 N a b := by
  unfold nextrel1
  simp only [List.length_append, entry_append_right, le0_append_right]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    have h9 := h6 (A.length + j) ⟨by omega, le0_append_right.mpr hj.2⟩
    rwa [entry_append_right] at h9
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    have h9 := h6 j' ⟨by omega, le0_append_right.mp hj.2⟩
    rwa [entry_append_right]

theorem rtg1_of_append {A N : TrioSeq} {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel1 (A ++ N)) (A.length + a) c) :
    ∃ c', c = A.length + c' ∧ Relation.ReflTransGen (nextrel1 N) a c' := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | tail _ h2 ih =>
      obtain ⟨c', hc, hchain⟩ := ih
      subst hc
      rename_i d _
      obtain ⟨d', rfl⟩ : ∃ d', d = A.length + d' :=
        ⟨d - A.length, by have := h2.2.2.1; omega⟩
      exact ⟨d', rfl, hchain.tail (nextrel1_append_right.mp h2)⟩

theorem rtg1_to_append {A N : TrioSeq} {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel1 N) a c) :
    Relation.ReflTransGen (nextrel1 (A ++ N)) (A.length + a) (A.length + c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact ih.tail (nextrel1_append_right.mpr h2)

/-- **★ `le1` の移送**（課題 L58 の 4 の後半）。 -/
theorem le1_append_right {A N : TrioSeq} {a b : ℕ} :
    le1 (A ++ N) (A.length + a) (A.length + b) ↔ le1 N a b := by
  unfold le1
  simp only [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨c', hc, hchain⟩ := rtg1_of_append h3
    have hb : c' = b := by omega
    subst hb
    exact ⟨by omega, by omega, hchain⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, rtg1_to_append h3⟩

/-- **`nextrel2` の移送**。 -/
theorem nextrel2_append_right {A N : TrioSeq} {a b : ℕ} :
    nextrel2 (A ++ N) (A.length + a) (A.length + b) ↔ nextrel2 N a b := by
  unfold nextrel2
  simp only [List.length_append, entry_append_right, le1_append_right]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    have h9 := h6 (A.length + j) ⟨by omega, le1_append_right.mpr hj.2⟩
    rwa [entry_append_right] at h9
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    have h9 := h6 j' ⟨by omega, le1_append_right.mp hj.2⟩
    rwa [entry_append_right]

/-- **★★ `nextR` の移送**（3 行ぶんまとめて）。 -/
theorem nextR_append_right {A N : TrioSeq} {i a b : ℕ} :
    nextR (A ++ N) i (A.length + a) (A.length + b) ↔ nextR N i a b := by
  unfold nextR
  split
  · exact nextrel0_append_right
  · split
    · exact nextrel1_append_right
    · exact nextrel2_append_right


/-! ## ★★★ (COMM) の仮定は「復活しない」1 本だけ（課題 L58 完了） -/

open Classical in
/-- **`hasParent` と `parent` の移送**。仮定は「親の候補が `N` の中にしかない」だけ。 -/
theorem hasParent_parent_append_right {A N : TrioSeq} {i b : ℕ}
    (h : hasParent N i b)
    (hall : ∀ j0, nextR (A ++ N) i j0 (A.length + b) → A.length ≤ j0) :
    hasParent (A ++ N) i (A.length + b) ∧
      parent (A ++ N) i (A.length + b) = A.length + parent N i b := by
  obtain ⟨p0, hp0, huniq⟩ := h
  have hexN : ∃ j0, nextR N i j0 b := ⟨p0, hp0⟩
  have hspecN : nextR N i (parent N i b) b := Classical.epsilon_spec hexN
  have hpN : parent N i b = p0 := huniq _ hspecN
  have hM : nextR (A ++ N) i (A.length + p0) (A.length + b) :=
    nextR_append_right.mpr hp0
  have hMu : ∀ y, nextR (A ++ N) i y (A.length + b) → y = A.length + p0 := by
    intro y hy
    obtain ⟨y', rfl⟩ : ∃ y', y = A.length + y' := ⟨y - A.length, by
      have := hall y hy; omega⟩
    rw [huniq y' (nextR_append_right.mp hy)]
  refine ⟨⟨A.length + p0, hM, hMu⟩, ?_⟩
  have hexM : ∃ j0, nextR (A ++ N) i j0 (A.length + b) := ⟨A.length + p0, hM⟩
  have hspec : nextR (A ++ N) i (parent (A ++ N) i (A.length + b)) (A.length + b) :=
    Classical.epsilon_spec hexM
  rw [hMu _ hspec, hpN]

open Classical in
/-- **★★★ (COMM)**: 仮定は **「バッドルートが `N` の中」1 本だけ**。

team-lead の実測（SESSION §52）: 陽性 65841/65841（100%）、陰性対照 0/72617（0%）。
⟹ **`j0 ≥ |A|` は必要十分条件**であり、`d0`・`d1`・マスクの一致は**全部自動**。 -/
theorem comm_of_noRevive {A N : TrioSeq} (n : ℕ) (hNne : N ≠ [])
    (hjNne : N.length - 1 ≠ 0)
    (hzN : ¬(entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0 ∧
      entry N 2 (N.length - 1) = 0))
    (hparN : hasParent N (srow N (N.length - 1)) (N.length - 1))
    (hall : ∀ j0, nextR (A ++ N) (srow N (N.length - 1)) j0
      (A.length + (N.length - 1)) → A.length ≤ j0) :
    (A ++ N)⟦n⟧ = A ++ N⟦n⟧ := by
  obtain ⟨hparM, hj0M⟩ := hasParent_parent_append_right hparN hall
  exact comm_of_parts n hNne rfl hjNne hzN rfl hparN rfl hparM hj0M
    (fun j => le0_append_right) (fun j => le1_append_right)


/-! ## ★★★ 課題 L61-a: 「段の中に親がある」だけで (COMM) が出る

H11 の判別子（H44、`b>=2` の 3743 行、`t = 0/1/2` すべてで食い違い 0）:

    段の最後の列が**段の中で親を持つ** ⟹ 復活 **0 / 3166**
    段の最後の列が**段の中では孤児**   ⟹ 復活 **577 / 577**

これは Lean で**証明できる**。理由は `nextrel` の**最小性**:

> `N` 単体で親 `p0` があるなら、`A ++ N` の中で `|A| + p0` は
> どの `j0 < |A|` より右にあり、しかも `entry` が真に小さい。
> ⟹ `j0` の最小性の条件（間に自分より小さい列があってはいけない）を**破る**。
> ⟹ `j0 < |A|` は親になれない。

⟹ **`comm_of_noRevive` の `hall` は `hparN` から出る。仮定は「段内に親がある」1 本。** -/

/-- **★★ 段内に親があれば、`A` を前に足しても親は `A` に逃げない。** -/
theorem noRevive_of_hasParent {A N : TrioSeq} {i b : ℕ} (h : hasParent N i b)
    {j0 : ℕ} (hj0 : nextR (A ++ N) i j0 (A.length + b)) : A.length ≤ j0 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p0, hp0, -⟩ := h
  have hM : nextR (A ++ N) i (A.length + p0) (A.length + b) := nextR_append_right.mpr hp0
  rw [nextR] at hj0 hM
  by_cases hi0 : i = 0
  · rw [if_pos hi0] at hj0 hM
    have h1 := hj0.2.2.2.2 (A.length + p0) ⟨by omega, hM.2.2.1⟩
    have h2 := hM.2.2.2.1
    omega
  · rw [if_neg hi0] at hj0 hM
    by_cases hi1 : i = 1
    · rw [if_pos hi1] at hj0 hM
      have h1 := hj0.2.2.2.2.2 (A.length + p0) ⟨by omega, hM.2.2.2.2.1⟩
      have h2 := hM.2.2.2.1
      omega
    · rw [if_neg hi1] at hj0 hM
      have h1 := hj0.2.2.2.2.2 (A.length + p0) ⟨by omega, hM.2.2.2.2.1⟩
      have h2 := hM.2.2.2.1
      omega

/-- **段内に親がある**（H11 の判別子。`MarkOne` の置き換え）。 -/
def HasParentInBlock (N : TrioSeq) : Prop :=
  hasParent N (srow N (N.length - 1)) (N.length - 1)

open Classical in
/-- **★★★ (COMM) は「段内に親がある」1 本だけで出る**（課題 L61-a）。

`MarkOne`（`srow = 1`）は**十分条件**でしかなかった（`t = 1` で 274/2060 の例外）。
`HasParentInBlock` が**必要十分**（実測は食い違い 0）で、しかも Lean で証明できる。 -/
theorem comm_of_hasParentInBlock {A N : TrioSeq} (n : ℕ) (hNne : N ≠ [])
    (hjNne : N.length - 1 ≠ 0)
    (hzN : ¬(entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0 ∧
      entry N 2 (N.length - 1) = 0))
    (hblk : HasParentInBlock N) :
    (A ++ N)⟦n⟧ = A ++ N⟦n⟧ :=
  comm_of_noRevive n hNne hjNne hzN hblk
    (fun _ hj0 => noRevive_of_hasParent hblk hj0)

/-! ## 課題 L61-d: 復活は高々 3 回

H11 の実測: 0 回 70.67% / 1 回 22.99% / 2 回 5.31% / **3 回 1.03% / 4 回以上 0 件**。
⟹ 帰納法は**有限段**で閉じる（無限降下を作らなくてよい）。 -/

/-- **(REV-k)**: 復活の回数に上限 `k` があること。実測では `k = 3`。 -/
def ReviveBounded (k : ℕ) : Prop :=
  ∀ (N : TrioSeq), ∃ m : ℕ, m ≤ k ∧
    ∀ n : ℕ, m ≤ n → HasParentInBlock (N⟦n⟧)


/-! ## ★★★ 課題 L62-a: `split_lastMin` の `TrioSeq` 版

2 行の完成証明（`lean/Pair/Wset.lean:512`）は **「深い側に足す」を一度も証明していない。
避けている。** その要が `split_lastMin`:

> **いつも「最後の最上位の木」を剥がす**ので、その根は行列全体の最小深さにあり、
> **`rsum` が構成から出る。** ⟹ `W_add` に深い `B` が渡ることは一度もない。

`Pair` 版の証明は **`entry _ 0 _`（行 0）だけ**を見ており、行数に依存しない。
⟹ **ほぼそのまま写せる。** -/

/-- **★★ `split_lastMin`（3 行版）**: 空でない行列は、
**根が全体で最浅**な接尾辞 `P` を持つように `A ++ P` に分けられる。
`rsum A P` が**構成から**出るのが要点。 -/
theorem split_lastMin : ∀ {M : TrioSeq}, M ≠ [] →
    ∃ A P, M = A ++ P ∧ P ≠ [] ∧ rsum A P ∧ (∀ p ∈ P.tail, entry P 0 0 < p.1) := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton M' q ih =>
      intro _
      by_cases hM' : M' = []
      · subst hM'
        refine ⟨[], [q], by simp, by simp, ?_, by simp⟩
        intro p hp
        simp only [List.nil_append, List.mem_singleton] at hp
        subst hp
        simp [entry]
      · obtain ⟨A', P', hEq, hPne, hrs, htail⟩ := ih hM'
        by_cases hq : q.1 ≤ entry P' 0 0
        · refine ⟨M', [q], by simp, by simp, ?_, by simp⟩
          intro p hp
          have hq0 : entry ([q] : TrioSeq) 0 0 = q.1 := by simp [entry]
          rw [hq0]
          rcases List.mem_append.mp hp with hp | hp
          · exact le_trans hq (hrs p (by rw [hEq] at hp; exact hp))
          · simp only [List.mem_singleton] at hp
            subst hp
            exact le_rfl
        · push Not at hq
          refine ⟨A', P' ++ [q], by rw [hEq, List.append_assoc], by simp, ?_, ?_⟩
          · have hhd : entry (P' ++ [q]) 0 0 = entry P' 0 0 := by
              rcases P' with _ | ⟨p0, P''⟩
              · exact absurd rfl hPne
              · simp [entry]
            intro p hp
            rw [hhd]
            rcases List.mem_append.mp hp with hp | hp
            · exact hrs p (List.mem_append_left _ hp)
            · rcases List.mem_append.mp hp with hp | hp
              · exact hrs p (List.mem_append_right _ hp)
              · simp only [List.mem_singleton] at hp
                subst hp
                omega
          · have hhd : entry (P' ++ [q]) 0 0 = entry P' 0 0 := by
              rcases P' with _ | ⟨p0, P''⟩
              · exact absurd rfl hPne
              · simp [entry]
            intro p hp
            rw [hhd]
            rcases P' with _ | ⟨p0, P''⟩
            · exact absurd rfl hPne
            · simp only [List.cons_append, List.tail_cons] at hp
              rcases List.mem_append.mp hp with hp | hp
              · exact htail p (by simpa using hp)
              · simp only [List.mem_singleton] at hp
                subst hp
                exact hq


/-! ## 課題 L62-b: `mem_W_of_bound_aux`（`Pair/Wset.lean:1489`）の 3 行版

2 行の道筋:

    1. `split_lastMin` で `M = A ++ (p0 :: R)`（`rsum` つき、`R` の全列が `p0` より深い）  ✓ **移植ずみ**
    2. 正規化 `R.map (q => (q.1 - p0.1, q.2))` が `argOK`                                ✓ 下で 3 行版
    3. **`mem_Wstar`**: `(0, p0.2) :: 正規化 R ∈ W p0.2`                                 ← **ここが本体**
    4. `tree_shift` ＋ `W_shift` で押し戻す                                              ✓ 下で 3 行版
    5. `W_mono` で `W u` へ、最後に `W_add`（`rsum` は 1 で無料）                        ✓ 既存

⟹ **3 行で足りないのは 3 の `Wstar` だけ。** 1・2・4・5 は道具が揃っている。 -/

/-- **`tree_shift` の 3 行版**: 根を `(0, v, z)` に正規化して行 0 をずらすと元に戻る。 -/
theorem tree_shift3 {p0 : ℕ × ℕ × ℕ} {R : TrioSeq} (h : ∀ q ∈ R, p0.1 ≤ q.1) :
    shiftr01 p0.1 0
        (((0, p0.2.1, p0.2.2) : ℕ × ℕ × ℕ) ::
          R.map fun q => ((q.1 - p0.1, q.2.1, q.2.2) : ℕ × ℕ × ℕ))
      = p0 :: R := by
  unfold shiftr01
  simp only [List.map_cons, List.map_map]
  congr 1
  · simp
  · conv_rhs => rw [← List.map_id R]
    refine List.map_congr_left ?_
    intro q hq
    have h9 := h q hq
    simp only [Function.comp_apply, id_eq]
    have hq1 : q.1 - p0.1 + p0.1 = q.1 := by omega
    rw [hq1]
    simp

/-- **正規化した引数ブロックは `argOK`**（3 行版）。 -/
theorem argOK_normalize {p0 : ℕ × ℕ × ℕ} {R : TrioSeq} (h : ∀ q ∈ R, p0.1 < q.1) :
    argOK (R.map fun q => ((q.1 - p0.1, q.2.1, q.2.2) : ℕ × ℕ × ℕ)) := by
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨r, hr, hrq⟩ := hq
  have h9 := h r hr
  rw [← hrq]
  simp only []
  omega

/-- **`Wstar` の 3 行版**（課題 L62-c）。根は `(0, v, z)` の 2 パラメータ。

⚠ `L10Tie.lean:35` の警告: `Wstar` は `∀ v z` で `v` を**全部**走るので、
`v` が `R` の行 1 の値とぶつかった瞬間にタイができる
（反例 `M = [(0,2,1),(4,1,0)]` は `TieFree` だが `(0,2,0) :: (行 0 を +1 した M)` で破れる）。
⟹ **`TieFree` の言語では `Wstar` を扱えない**。ただしこれは `TieFree` の限界であって、
`Wstar` 自体が偽という意味ではない。 -/
def Wstar3 : Set TrioSeq :=
  {R | argOK R → ∀ v z : ℕ, (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z)}


/-! ## ★★★ 課題 L63: **2 行の道筋は既に 3 行に移植ずみだった**

`lean/Wset.lean` を数えたところ、`Wstar` の一式は**全部ある**:

    Wstar              `Wset.lean:2684`
    graft_cons         `:2545`     rsum_self_cons  `:2539`
    based_cons         `:2536`     entry_cons      `:1708`
    argOK_oper / argOK_graft / argOK_dropLast      `:2523 / :2526 / :2530`
    oper_mem_ge / graft_mem_ge / graft_append      `:1536 / :1575 / :1434`
    tow                `:2780`
    oper_cons_nat      `:2041`     oper_cons_succ  `:2392`
    oper_cons_tower1   `:2789`     oper_cons_tower2 `:3231`
    **Wstar_closed (htow : TowerOK)  `:4372`**
    mem_Wstar          `:4646`     mem_W_of_bound_aux / mem_W_of_bound `:4653 / :4732`

⟹ **課題 L62-b で「足りないのは `mem_Wstar` だけ」と書いたが、それも既にある。
残っているのは仮定 `TowerOK` ただ 1 本。**

## ★ `TowerOK` は私の課題 L57 の分析そのもの

```lean
def TowerOK : Prop :=
  ∀ v z u0 a R, argOK R → R ≠ [] → z ≤ 1 → 2*v+z ≤ a →
    Aop W u0 Wstar R → (∃ m, domT R m) →
    **hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|** →      ← 根が R の末尾の孤児を**復活**させる
    ∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ ∈ W a
```

その docstring:

> **The one remaining core.** When the principal root **revives** `R`'s trailing orphan …
> **For `srow = 1` the row-1 lift is `0`** and the plain `graft` recursion applies;
> **for `srow = 2` the copies raise row 1 by `w - v` on the `le1`-cone of the root**,
> so the substituted block is the *lifted* tower.

⟹ **課題 L57 で書いた「`srow = 1` は段の中で閉じる／`srow = 2` は行 2 が不変なので逃げる」
と逐語で一致する。** そして `TowerOK` の仮定の `hasParent ((0,v,z) :: R) …` は、
`R` 単体では孤児（`¬ HasParentInBlock R`）なのに根を付けると親ができる、という
**まさに復活の条件**である。

## ⟹ 現在地（正確な形）

    **非復活**（`HasParentInBlock R`）… `comm_of_hasParentInBlock` で閉じる  ← 課題 L61-a、**証明ずみ**
    **復活**（`TowerOK` の仮定）      … `srow = 1` は graft の再帰で閉じるはず（docstring）
                                        `srow = 2` が**唯一の核**

⟹ **`TowerOK` を `srow` で 2 つに割り、`srow = 1` の側を落とすのが次の緑。** -/

/-- **`TowerOK` の `srow = 1` の側**（docstring の「plain `graft` recursion」）。 -/
def TowerOK1 : Prop :=
  ∀ (v z u0 a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    Aop W u0 Wstar R → (∃ m, domT R m) →
    srow R (R.length - 1) = 1 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- **`TowerOK` の `srow = 2` の側**（唯一の核。行 2 が写しで不変なので逃げる）。 -/
def TowerOK2 : Prop :=
  ∀ (v z u0 a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    Aop W u0 Wstar R → (∃ m, domT R m) →
    srow R (R.length - 1) = 2 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

theorem srow_le_two (M : TrioSeq) (j : ℕ) : srow M j ≤ 2 := by
  unfold srow
  split
  · omega
  · split <;> omega

/-- **`TowerOK` は 2 つに割れる**（`srow = 0` は `domT` と両立しない）。 -/
theorem towerOK_of_split (h1 : TowerOK1) (h2 : TowerOK2)
    (h0 : ∀ (R : TrioSeq), R ≠ [] → (∃ m, domT R m) → srow R (R.length - 1) ≠ 0) :
    TowerOK := by
  intro v z u0 a R hR hRne hz hva hAop hdom hpar n hn
  rcases Nat.lt_or_ge (srow R (R.length - 1)) 2 with hs | hs
  · have hs1 : srow R (R.length - 1) = 1 := by
      have := h0 R hRne hdom
      omega
    exact h1 v z u0 a R hR hRne hz hva hAop hdom hs1 hpar n hn
  · have hs2 : srow R (R.length - 1) = 2 := by
      have h9 := srow_le_two R (R.length - 1)
      omega
    exact h2 v z u0 a R hR hRne hz hva hAop hdom hs2 hpar n hn


end L53
end TRIO
