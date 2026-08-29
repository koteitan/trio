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


end L53
end TRIO
