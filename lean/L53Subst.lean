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


/-! ## ★★ 課題 L64: `TowerOK1` は既存定理に落ちる

`Wset.lean` に**証明ずみ**で揃っている:

    `oper_cons_tower1` `:2789`  `srow = 1` の塔の恒等式
                                `((0,v,z) :: R)⟦n⟧ = tow v z R n`
    `tower1_mem2`      `:4093`  その塔が `W a` に留まる（graft 閉包 `hgr` を仮定）
    `Lift1_zero`                `Lift1 X 0 = X`

⟹ **`TowerOK1` は `Aop` の節 3（graft の与件）だけで出る。** -/

/-- **★★ `TowerOK1` は節 3 の与件から出る**（課題 L64-c）。 -/
theorem towerOK1_of_clause3 {v z a m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hd : domT R m) (hgr3 : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hi1 : srow R (R.length - 1) = 1)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  intro n _
  rw [oper_cons_tower1 hR hRne hd hi1 hpM]
  refine tower1_mem2 hR hRne hz1 hva hd hi1 ?_ hpM n
  intro y hy hb hargOK a' ha'
  rw [Lift1_zero]
  exact hgr3 y hy hb hargOK v z a' hz1 ha'


/-! ## ★★★ 課題 L64-d: `TowerOK2` の正体 —— 段が `+2t` 上がってしまう

`oper_cons_tower2`（`Wset.lean:3231`、**証明ずみ**）:

    ((0,v,z) :: R)⟦n+1⟧
      = (0,v,z) :: graft R (**Lift1** (((0,v,z) :: R)⟦n⟧) **(entry R 1 (|R|-1) - v)**)

`srow = 1` との差は **`Lift1` の持ち上げ量 `t = entry R 1 (|R|-1) - v`** ただ 1 つ:

    srow = 1 … `t = 0`。`Lift1 X 0 = X` なので `tower1_mem2` がそのまま効く   ✓ 落ちた
    srow = 2 … `t > 0`。`tower1_mem`（`:4088`）の形は
               **`∀ a t, 2*(v+t)+z ≤ a → Lift1 ((0,v,z) :: graft S y) t ∈ W a`**
               ＝ **段が `2t` 上がる**

ところが `TowerOK2` の結論は `2v+z ≤ a` の `a` で `∈ W a` を要求する。
⟹ **`+2t` を払わずに持ち上げを通す**必要がある。

これが `ulift_mem_W`（`Wslift.lean:461`、`shiftr01 0 t X ∈ W (m + 2t)`）の `+2t` と
同じもので、避ける道具が `mlift_mem_W`（`:146`、**階段マスク**なら段はそのまま）。
橋は `Lift1_eq_mlift_of_tieFree`（`Wtower2.lean:76`）で、条件は **`TieFree`**。

⟹ **`TowerOK2` ＝ 「`le1`-錐の持ち上げを段を上げずに通す」＝ (MLIFT) ＝ `TieFree` の壁。**
課題 L52-b / L54-c / L57 で別々に着いた場所が、ここで 1 点に合流する。

    **3 行が 2 行より難しい理由（最終形）**:
    行 2 は写しで不変（`oper` の第 3 成分は `entry M 2 j` そのまま）なので、
    `srow = 2` の塔では親が段の外に逃げ、その代償に**行 1 を `le1`-錐で持ち上げる**
    必要が生じる。2 行にはそもそも行 2 が無いので `t = 0` しか起きない。 -/

/-- **`TowerOK2` の残差**: 持ち上げを段を上げずに通せること。 -/
def LiftNoCost : Prop :=
  ∀ (v z a t : ℕ) (S y : TrioSeq), 2 * v + z ≤ a → argOK (graft S y) →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft S y) t ∈ W a


/-! ## ★★★ 課題 L65: 3 つの道の判定

`Lift1_eq_mlift_of_tieFree`（`Wtower2.lean:76`）の中身を読んだ:

```lean
def TieFree (X) := ∀ j, coneV X (entry X 1 0 - 1) j → **le1 X 0 j**   -- coneV ⊆ le1
theorem coneV_of_le1 (hv : 1 ≤ entry X 1 0) : le1 X 0 j → coneV X (...) j  -- **無条件**
```

    `Lift1 X d` … 根の **`le1` 錐**（行 1 の木の子孫）で行 1 を `d` 上げる
    `mlift X v0 d` … **`coneV` 錐**（行 0 祖先が全部行 1 で `v0` 超）で上げる
    `TieFree` … その 2 つが**一致**すること（片側 `le1 ⊆ coneV` は無条件で成立）

## ★ L65-c の答え: 錐が階段でなくなるのは**タイ**のせい

`coneV` は**値**の条件、`le1` は**木**の条件。**行 1 の値が等しい**と
`nextrel1` の `entry X 1 j0 < entry X 1 j1` が破れて木の辺が消えるが、
値の条件は満たしたままになる。⟹ `coneV ⊄ le1`。

`L10Tie.lean:25` の最小例がまさにそれ:

    M = [(0,1,1), (2,3,0)]   TieFree
    M⟦2⟧ = [(0,1,1), (2,1,1)]  ← 列 1 の行 1 が根と**同じ 1**
      `nextrel1 (M⟦2⟧) 0 1` は `1 < 1` を要求して**偽** ⟹ `le1` に入らない
      しかし `coneV`（行 0 祖先の行 1 が全部 `≥ 1`）は**満たす**

## ⚠ L65-a の判定: **死んでいる可能性が高い**

`L10Tie.lean:35` の 2 つ目の反例は **`Wstar` の `cons` 操作そのもの**:

    M = [(0,2,1), (4,1,0)]  TieFree
    (0,2,0) :: (行 0 を +1 した M)  **破れる**

`TowerOK2` で `TieFree` が要るのは `X = ((0,v,z) :: R)⟦n⟧`、つまり
**根を cons した形**である。⟹ **反例と同じ形。**

さらに `L10Tie` は「`TieFree` が中身を持つのは根の行 1 が 1 以上のとき、つまり
`Wstar` の `(0,v,z) :: R`（`v ≥ 1`）」と書いている。⟹ **狙う場所でちょうど非空虚、
かつちょうど破れる。** 局所化の見込みは薄い。

**測るなら 1 本**: 実際の `TowerOK2` の事例で `TieFree (((0,v,z) :: R)⟦n⟧)` が
立つ割合。陽性対照に `coneV ⊆ le1` の破れの個数。

## ⚠ L65-b の判定: **`TieFree` は `Row1Mono` に置き換わるだけ**

`TieFree` は**等式**のためにしか使っていない。ところが要るのは所属だけで、
`le1 ⊆ coneV` は**無条件**だから

    `Lift1 X d` は `mlift X v0 d` より**行 1 が小さい**（持ち上げる列が少ない）

⟹ **`W` が行 1 の引き下げで閉じている**なら `mlift_mem_W` から出る。それは
`Row1Mono` / `WConvex`（`Wtower2.lean:151 / :450`）である。

⚠ ただし `Row1Mono` の計測（369068 / 773483 / 258507、違反 0）は
**課題 L45 で ⛔ 空虚と判定した**（`inW` の退化）。⟹ **支えが無い。**

## ⟹ 判定

    L65-a 局所化    … 反例と同じ形。**薄い**（測定 1 本で決着可能）
    L65-b 別の橋    … `TieFree` → `Row1Mono` / `WConvex` に**置き換わるだけ**。
                      しかも `Row1Mono` の支えは空虚だった
    L65-c なぜ階段でないか … **タイ**（行 1 の値が等しいと木の辺が消える）。**答えた**

**⟹ 核は「行 1 のタイをどう扱うか」に落ちた。** `TieFree` も `Row1Mono` も
`WConvex` も、**同じタイを別の言葉で避けようとしている**。 -/

/-- **`Lift1` は `mlift` より行 1 が小さい**（`le1 ⊆ coneV` は無条件だから）。
⟹ `W` が行 1 の引き下げで閉じていれば `LiftNoCost` は `mlift_mem_W` から出る。 -/
def Row1Down : Prop :=
  ∀ (u : ℕ) (X Y : TrioSeq), X ∈ W u → X.length = Y.length →
    (∀ j, entry Y 0 j = entry X 0 j) → (∀ j, entry Y 2 j = entry X 2 j) →
    (∀ j, entry Y 1 j ≤ entry X 1 j) → Y ∈ W u


/-! ## ★★★ 課題 L66: `coneV`（値）が入る場所の特定

### L66-a の答え: 値依存は **`amin`** から入る

```lean
noncomputable def slift (A : TrioSeq) (φ : ℕ → ℕ) : TrioSeq :=      -- `Cgraft.lean:919`
  (List.range A.length).map fun j =>
    (entry A 0 j, entry A 1 j + **(φ (amin A j) - amin A j)**, entry A 2 j)

structure Stair (φ : ℕ → ℕ) : Prop where                            -- `Cgraft.lean:883`
  ge   : ∀ m, m ≤ φ m
  step : ∀ m n, m ≤ n → **φ m - m ≤ φ n - n**
  zero : φ 0 = 0
```

**持ち上げ量が `amin A j`（行 0 祖先鎖の行 1 の最小値）の関数**である。
これが `mlift`（`Cgraft.lean:312`）を `slift` に落とす `mlift_eq_slift`（`:1033`）の中身で、
使い所は **`slift_oper`（`Aexp.lean:394`）: `slift (A⟦n⟧) φ = (slift A φ)⟦n⟧`**。

    ⟹ **`Stair.step` は「展開で写しが作られたとき持ち上げ量が整合する」ために要る。**
       値の関数だからこそ、写しの `amin` が計算でき、`oper` と可換になる。

### L66-b の答え: **`le1` 錐は階段マスクにならない。既に証明されている**

`Lift1` を `slift` として書くには `φ (amin X j) - amin X j = d ⟺ j ∈ le1 錐` が要る。
`amin` は値なので、これは**錐が値の閾値集合であること** ＝ `TieFree` そのもの。

そして **`Lift1` は `oper` と可換ではない**。可換なのは `slift` だけで、`Lift1` については
**サンドイッチ 2 本しか無く、しかもそれは既に証明ずみ**である:

    `Le1_Lift1_oper`（`Wtower2.lean:4408`）        `Lift1 (X⟦n⟧) d ≤₁ (Lift1 X d)⟦n⟧`
    `Le1_oper_Lift1_shiftr01`（`:4457`）           `(Lift1 X d)⟦n⟧ ≤₁ shiftr01 0 d (X⟦n⟧)`

⟹ **`le1` 版の `slift_oper` は作れない（等式が成り立たない）。作れるのは挟み込みだけ。**
そしてその**隙間を潰すのが `WConvex`**（`liftStage_of_wconvex'`、`Wtower2.lean:4473`）。

## ⟹ 3 つの道が同じである理由（構造として）

    `TieFree`   … 錐を**値の閾値**に寄せて `slift` の等式を使う
    `mlift`     … 同上（`mlift_eq_slift`）
    `Row1Mono` / `WConvex` … 挟み込みの**隙間を潰す**

**どれも「行 1 のタイで `le1` の木の辺が消える」ことを別の言葉で避けている。**
`oper` と可換なのは**値の持ち上げ**だけで、**木の持ち上げ（`le1`）は可換でない** ——
これが `TowerOK2` の核であり、3 行が 2 行より難しい理由の最終形である。

（2 行には行 2 が無いので `srow = 2` の枝が起きず、`t = 0` しか現れない。
⟹ `Lift1` を使う必要が無く、タイの問題に触れずに済む。） -/


/-! ## ★★★ 課題 L67: `TowerOK2` は `z` で割れる

### L67-a/b の判定: **入れ子の深さは有界でない。`k ≤ Y` とは対応しない**

    `oper_cons_tower2`:  ((0,v,z) :: R)⟦n+1⟧ = (0,v,z) :: graft R (Lift1 (…⟦n⟧) t)

`⟦n⟧` を展開すると **`Lift1` が `n` 重**に入れ子になる。`n` は写しの本数なので**無限**。
H11 の `k ≤ Y` は「**復活の連続回数**」＝ `Wstar` の帰納で `TowerOK` が入れ子に
呼ばれる回数であり、**1 つの塔の中の写しの本数とは別の量**である。
⟹ **L67-a は使えない。**

### ★★ しかし段の勘定をすると、`z` で 2 つに割れる

`graft R (Lift1 X t)` を節 3 で使うには、**持ち上げた塊が `W m` に入る**必要がある
（`m` は `domT R m` の段）。持ち上げた塊の根は `(0, v+t, z)` で、
`t = entry R 1 (|R|-1) - v` だから根のレベルは `2w + z`（`w = entry R 1 (|R|-1)`）。

一方 `domT R m` より `m + 1 = lev R (|R|-1) = 2w + z'`（`z' = entry R 2 (|R|-1)`）。
`srow = 2` なので **`z' ≥ 1`**。要るのは

    2w + z ≤ m = 2w + z' - 1   ⟺   **z < z'**

`z ≤ 1` かつ `z' ≤ 1`（z<2 の断片）なので

    **z = 0 … `z' ≥ 1` が自動で成り立つ ⟹ 段がぴったり収まる**
    **z = 1 … `z' ≥ 2` が要るが断片では不可能 ⟹ 収まらない**

⟹ **`TowerOK2` の核は `z = 1`（根の行 2 が 1）だけ。** -/

/-- `srow = 2` なら行 2 は正。 -/
theorem srow_two_row2_pos {M : TrioSeq} {j : ℕ} (h : srow M j = 2) :
    0 < entry M 2 j := by
  by_contra hc
  unfold srow at h
  rw [if_neg hc] at h
  split at h <;> omega

/-- **★★ `z = 0` なら持ち上げた塊の段がちょうど `m` に収まる**（課題 L67）。 -/
theorem tower2_stage_fits {v z m : ℕ} {R : TrioSeq} (hz0 : z = 0) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hvw : v ≤ entry R 1 (R.length - 1)) :
    2 * (v + (entry R 1 (R.length - 1) - v)) + z ≤ m := by
  have h1 := hd.1
  have h2 := srow_two_row2_pos hi2
  unfold lev at h1
  omega

/-- **⚠ `z = 1` では収まらない**（`z' ≥ 2` が要るが z<2 の断片では不可能）。 -/
theorem tower2_stage_fails {v m : ℕ} {R : TrioSeq} (hd : domT R m)
    (hz' : entry R 2 (R.length - 1) ≤ 1)
    (hvw : v ≤ entry R 1 (R.length - 1)) :
    ¬ (2 * (v + (entry R 1 (R.length - 1) - v)) + 1 ≤ m) := by
  have h1 := hd.1
  unfold lev at h1
  omega


/-! ## ★★★ 課題 L68: `z = 1` の核 —— **ちょうど 1 段足りない**

`z<2` の断片では `entry R 2 (|R|-1) ≤ 1`、`srow = 2` なら `= 1`。よって

    `domT R m` … `m + 1 = 2w + 1`  ⟹ **`m = 2w`**
    要求        … 持ち上げた塊の根のレベル `2*(v+t) + z = 2w + z`

    **z = 0 … `2w ≤ m = 2w`   ぴったり収まる（余裕ゼロ）**
    **z = 1 … `2w + 1 ≤ 2w`   ちょうど 1 段足りない**

⟹ **不足はちょうど 1 段。** しかも持ち上げた塊の根のレベルは `m + 1` で、
これは `domT R m` が言う**孤児のレベルそのもの**である
（＝「穴とちょうど同じ大きさの塊」を差し込もうとしている）。
節 3 は `∀ y ∈ W m` を要求するので、**真に小さいことを要求している**のに等しい。 -/

/-- **★★ `z = 1` では不足がちょうど 1 段**（課題 L68-a）。 -/
theorem tower2_deficit_one {v m : ℕ} {R : TrioSeq} (hd : domT R m)
    (hz' : entry R 2 (R.length - 1) = 1)
    (hvw : v ≤ entry R 1 (R.length - 1)) :
    2 * (v + (entry R 1 (R.length - 1) - v)) + 1 = m + 1 := by
  have h1 := hd.1
  unfold lev at h1
  omega

/-- **`z = 0` はぴったり収まる（余裕ゼロ）**。 -/
theorem tower2_exact_z0 {v m : ℕ} {R : TrioSeq} (hd : domT R m)
    (hz' : entry R 2 (R.length - 1) = 1)
    (hvw : v ≤ entry R 1 (R.length - 1)) :
    2 * (v + (entry R 1 (R.length - 1) - v)) + 0 = m := by
  have h1 := hd.1
  unfold lev at h1
  omega

/-! ### 課題 L68-b の判定: `m` は `domT` で釘付け。余裕は無い

節 3 は `∃ m < u, domT M m ∧ ∀ y ∈ W m, based y → graft M y ∈ X`。
`m` は `domT` の第 1 連言 `lev M (|M|-1) = m + 1` で**一意に決まる**ので、
`W (m+1)` に緩める余地は無い（`u` には `m < u` の余裕があるが、
要求されるのは `y ∈ W m` であって `y ∈ W u` ではない）。

⟹ **段を別の場所から取ることはできない。** 残る道は
「外側に節 3 でなく**節 2** を使う（さらに展開する）」だけ。

### ★ 課題 L68-c: `z = 1` では**根が親になれない**

`srow = 2` の親は行 2 で真に浅い列。`z<2` の断片で孤児の行 2 は `1` なので、
親の行 2 は `0` でなければならない。根 `(0,v,1)` の行 2 は `1` ⟹ **根は候補外**。

⟹ **`z = 1` の復活は、根そのものではなく `R` の中の行 2 が `0` の列が
「根を付けたことで行 1 の祖先になった」ために起きる。**
（`nextrel2` は `le1 M j0 j1` を要求するので、行 1 の祖先関係が根の追加で変わる。）

これは `z = 0` の場合（根の行 2 が `0` なので根自身が親になれる）と**構造が違う**。
⟹ **`z = 1` の核は「根が行 1 の祖先関係を変えて、`R` の中の列を親にする」現象**である。 -/

/-- **★★ `z = 1` では復活の親は根ではない**（課題 L68-c）。 -/
theorem tower2_parent_ne_root {v : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz' : entry R 2 (R.length - 1) = 1) {j0 : ℕ}
    (h : nextR (((0, v, 1) : ℕ × ℕ × ℕ) :: R) 2 j0 R.length) : j0 ≠ 0 := by
  intro hj0
  subst hj0
  rw [nextR] at h
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)] at h
  have hlt := h.2.2.2.1
  rw [entry_cons_last hRne 2, hz'] at hlt
  simp [entry] at hlt


/-! ## ★★★ 課題 L69-a: 根の `z` は `0` に強制される ⟹ `z = 1` の場合は起きない

`srow = 2` なら孤児の行 2 は（`z<2` の断片で）`1`。行 2 の親は `entry2` が
**真に小さい**列を要求するので、親の行 2 は `0`。親が根なら根の行 2 ＝ `z` = `0`。

⟹ **課題 L68 の `tower2_stage_fails`（`z = 1` では段が収まらない）は真だが、
その場合が起きない。** `TowerOK2` は `tower2_stage_fits`（`z = 0`）だけで済む。

実測（H11、H47/H48）: `TowerOK` の `srow=2` の場面 **624 件すべてが `(v,z) = (0,0)`**。 -/

/-- **★★ 根が行 2 の親なら `z = 0`**（課題 L69-a）。 -/
theorem tower2_root_z_zero {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz' : entry R 2 (R.length - 1) = 1)
    (h : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 R.length) : z = 0 := by
  rw [nextR] at h
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)] at h
  have hlt := h.2.2.2.1
  rw [entry_cons_last hRne 2, hz'] at hlt
  have hz : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 = z := by simp [entry]
  rw [hz] at hlt
  omega

open Classical in
/-- **同じことを `parent = 0` の形で。** -/
theorem tower2_z_zero_of_parent {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz' : entry R 2 (R.length - 1) = 1)
    (hpar : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 R.length)
    (hp0 : parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 R.length = 0) : z = 0 := by
  obtain ⟨p0, hp0', -⟩ := hpar
  have hex : ∃ j0, nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 j0 R.length := ⟨p0, hp0'⟩
  have hspec : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2
      (parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 R.length) R.length :=
    Classical.epsilon_spec hex
  rw [hp0] at hspec
  exact tower2_root_z_zero hRne hz' hspec

/-! ## 課題 L69-b/c: `TieFree` の構文的な同値形

H11 の測定（食い違い **0 / 3120**、立つ割合 96.2%、`n` 感度ゼロ）:

    **`TieFree ((0,v,z) :: R)` ⟺ `∀ p ∈ R, p.2.1 ≠ v`**

理由の骨: `coneV X (v-1) j` は「`j` の行 0 祖先の行 1 が全部 `≥ v`」。
`R` に行 1 `= v` の列が無ければ、それらは全部 **`> v`（真に大きい）**になるので、
`nextrel1` の狭義不等式が通り、行 1 の鎖が根から届く ⟹ `le1 X 0 j`。

⟹ **タイ（行 1 が根と同値）が無ければ 2 つの錐は一致する。**
破れる最小は 行 331 `ψ(Ω_ω·ω+Ω_ω)`、`R = (1,1,1)(2,0,0)(1,1,1)`、破れる列は `(2,0,0)`。

**⟹ 残る核は「`R` に行 1 = `v` の列がある」場合（3.8%）だけ。**

### 使える数字（H11）

    `R` に「`z=0` かつ行 1 で末尾の祖先」の列は 1 本も無い … **624/624**（`domT` より強い）
    持ち上げ量 `w - v` は **99.5% が 1**（3 件だけ 2）
      ⟹ **`d1 = 1` を先に落とすと 99.5% 片づく** -/

/-- **(TIE-SYN)** `TieFree` の構文的な十分条件（課題 L69-b。片側だけでよい）。 -/
def TieSyn : Prop :=
  ∀ (v z : ℕ) (R : TrioSeq), argOK R → (∀ p ∈ R, p.2.1 ≠ v) →
    TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)

/-- **★★★ (TIE-SYN) の証明**（課題 L69-b）。

`le1_zero_iff`（`Lcone.lean:36`）: 根が狭義最浅なら
`le1 A 0 j ⟺ ∀ y ⟶₀ j, y ≠ 0 → entry A 1 0 < entry A 1 y`。

`coneV A (v-1) j` は `∀ y ⟶₀ j, v - 1 < entry A 1 y`、すなわち `≥ v`。
`R` に行 1 `= v` の列が無ければ `y ≠ 0` で `≠ v` なので **`> v`** になる。
⟹ 2 つの錐が一致し `TieFree`。 -/
theorem tieSyn_holds : TieSyn := by
  intro v z R hargOK hne j hcone
  have hA1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
  rw [hA1] at hcone
  have hA0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0 = 0 := by simp [entry]
  have hlen : (((0, v, z) : ℕ × ℕ × ℕ) :: R).length = R.length + 1 := by simp
  have hrow1 : ∀ y, y ≠ 0 → y < R.length + 1 →
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 y = entry R 1 (y - 1) := by
    intro y hy0 _
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    simpa using entry_cons ((0, v, z) : ℕ × ℕ × ℕ) R 1 y'
  have hr : ∀ l, 0 < l → l < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length →
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0
        < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 l := by
    intro l hl0 hl
    rw [hlen] at hl
    rw [hA0]
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [entry_cons]
    exact hargOK _ (entry_pair_mem (B := R) (by omega))
  have hjlt : j < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by
    by_contra hc
    push_neg at hc
    have h9 := hcone j Relation.ReflTransGen.refl
    have h0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 j = 0 := by
      simp [entry, List.getElem?_eq_none hc]
    rw [h0] at h9
    omega
  rw [le1_zero_iff hr hjlt, hA1]
  intro y hyj hy0
  have h1 := hcone y hyj
  have hylt : y < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by
    by_contra hc
    push_neg at hc
    have h0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 y = 0 := by
      simp [entry, List.getElem?_eq_none hc]
    rw [h0] at h1
    omega
  rw [hlen] at hylt
  rw [hrow1 y hy0 hylt] at h1 ⊢
  have hmem : entry R 1 (y - 1) ≠ v := by
    have h8 := hne _ (entry_pair_mem (B := R) (show y - 1 < R.length by omega))
    simpa [entry] using h8
  omega


/-! ## ★★★ 課題 L72-a: `v = 0` では `TieFree` は要らない —— 無タイ ＝ **窓条件**

⚠ `Lift1_eq_mlift_of_tieFree` は `hv : 1 ≤ entry X 1 0` を要求する。
`Wtower2.lean:100` の doc いわく「`TieFree` は `mlift` の閾値が `v0 - 1` なので
**`v0 = 0` では原理的に届かない**」。

ところが H11 の実測では `TowerOK` の `srow=2` の場面は **624 件すべてが `(v,z) = (0,0)`**、
つまり **`v = 0`**。⟹ `TieFree` の道は実例に当たらない。

★ しかし `v = 0` には**別の道が既にある**:

```lean
theorem liftStage_of_window (hX : X ∈ W m)
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)   -- 行 0 で狭義最浅
    (hw : ∀ l, 0 < l → l < X.length → entry X 1 0 < entry X 1 l) : -- **行 1 で狭義最小**
    Lift1 X d ∈ W (m + 2 * d)                                       -- `Wtower2.lean:128`
```

`X = (0,0,z) :: R` なら `entry X 1 0 = 0` なので `hw` は
**「`R` の全列の行 1 が `≥ 1`」** ＝ **`∀ p ∈ R, p.2.1 ≠ 0` ＝ 無タイ条件そのもの**。
`hr` は `argOK R` から出る。

⟹ **`v = 0` では無タイ条件がそのまま窓条件になり、`liftStage_of_window` が
核なしで使える。** `TieFree` も `mlift` も経由しない。 -/

/-- 根 `(0,v,z)` は行 0 で狭義最浅（`argOK R` から）。 -/
theorem root_row0_min {v z : ℕ} {R : TrioSeq} (hargOK : argOK R) :
    ∀ l, 0 < l → l < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length →
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0
        < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 l := by
  intro l hl0 hl
  simp only [List.length_cons] at hl
  have hA0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0 = 0 := by simp [entry]
  rw [hA0]
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [entry_cons]
  exact hargOK _ (entry_pair_mem (B := R) (by omega))

/-- **★★★ `v = 0` では無タイだけで根リフトが通る**（課題 L72-a）。
`TieFree` も `mlift` も経由しない。 -/
theorem liftStage_of_noTie_zero {m d z : ℕ} {R : TrioSeq} (hargOK : argOK R)
    (hne : ∀ p ∈ R, p.2.1 ≠ 0)
    (hX : (((0, 0, z) : ℕ × ℕ × ℕ) :: R) ∈ W m) :
    Lift1 (((0, 0, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d) := by
  refine liftStage_of_window hX (root_row0_min hargOK) ?_
  intro l hl0 hl
  simp only [List.length_cons] at hl
  have hA1 : entry (((0, 0, z) : ℕ × ℕ × ℕ) :: R) 1 0 = 0 := by simp [entry]
  rw [hA1]
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [entry_cons]
  have h8 := hne _ (entry_pair_mem (B := R) (show l' < R.length by omega))
  simpa [entry] using Nat.pos_of_ne_zero (by simpa [entry] using h8)


/-! ## ★★★ 課題 L73: `v` は強制されない。だが **`v` で割れば全 `v` で閉じる**

### L73-a の判定: **`v = 0` は強制されない**

`TowerOK2` の仮定は `srow R (|R|-1) = 2` ＋ 根が行 2 の親。`nextrel2` は
`le1 M j0 j1` を要求するので、根が親なら `le1 M 0 |R|`、つまり行 1 の鎖が根から届く。
`nextrel1` の狭義不等号から **`v < w`**（`w = entry R 1 (|R|-1)`）は出るが、
**`v = 0` は出ない。**

⟹ H11 の「シートに `v ≥ 1` の事例は 0 件」は**母集団の性質**であって、
`TowerOK2` の仮定からの帰結ではない。

### ★★ L73-c: `v` で割ると**両側とも閉じる**

    `v = 0`  … 無タイ ＝ **窓条件** ⟹ `liftStage_of_window`（核なし）
    `v ≥ 1`  … `tieSyn_holds` ⟹ `TieFree` ⟹ `Lift1_eq_mlift_of_tieFree`
               （`hv : 1 ≤ entry X 1 0 = v` がちょうど満たされる）⟹ `mlift_mem_W`

**⟹ `TieFree` の仕事は無駄にならない。`v ≥ 1` 側でちょうど使える。** -/

/-- **`v ≥ 1` では `TieFree` の道が使える**（課題 L73-c）。 -/
theorem liftStage_of_noTie_pos {m d v z : ℕ} {R : TrioSeq} (hv : 1 ≤ v)
    (hargOK : argOK R) (hne : ∀ p ∈ R, p.2.1 ≠ v)
    (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W m) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d) := by
  have hv1 : 1 ≤ entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 := by
    simpa [entry] using hv
  rw [Lift1_eq_mlift_of_tieFree hv1 (tieSyn_holds v z R hargOK hne) d]
  exact mlift_mem_W _ hX

/-- **★★★ 無タイなら根リフトは全 `v` で通る**（課題 L73-c）。
`v = 0` は窓、`v ≥ 1` は `TieFree`。**どちらも核なし。** -/
theorem liftStage_of_noTie {m d v z : ℕ} {R : TrioSeq} (hargOK : argOK R)
    (hne : ∀ p ∈ R, p.2.1 ≠ v)
    (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W m) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d) := by
  rcases Nat.eq_zero_or_pos v with hv0 | hv
  · subst hv0
    exact liftStage_of_noTie_zero hargOK hne hX
  · exact liftStage_of_noTie_pos hv hargOK hne hX


/-! ## ★★★ 課題 L74-a: タイで割る（行 1 版の `split_lastMin`）

H11 の実測（タイ 120 件、例外ゼロ）:

    **タイは常に 1 本**（2 本以上は 0 件）⟹ 帰納は **1 段**で済む
    分解 `R = R₁ ++ [tie] ++ R₂` が **120/120** で通る
      `R₁ ≠ []` / `R₂ ≠ []` / 両方 `argOK` / **`R₂` にタイが無い**
      `R₂` の末尾が `R₂` 内で孤児 / `srow R₂ (末尾) = 2` / 根を付けると親ができる
      **`(0,v,0) :: R₂` は無タイ** / **`(0,v,0) :: R₁` も無タイ**

⟹ **`R₂` は `TowerOK2`（無タイ）の場面そのもの。**

⚠ 「タイが持ち上げの壁になる」（課題 L71-b の予想）は**外れ**。`le1` の鎖はタイを
**迂回**する（120/120）。壁ではないが、**分解はできる**。 -/

/-- **★★ 最後のタイで割る**（課題 L74-a）。`R` に行 1 `= v` の列があれば、
**いちばん右のもの**で `R = R₁ ++ [tie] ++ R₂` と割れ、**`R₂` にはタイが無い**。 -/
theorem split_lastTie {v : ℕ} : ∀ {R : TrioSeq}, (∃ p ∈ R, p.2.1 = v) →
    ∃ R₁ tie R₂, R = R₁ ++ [tie] ++ R₂ ∧ tie.2.1 = v ∧
      (∀ p ∈ R₂, p.2.1 ≠ v) := by
  intro R
  induction R using List.reverseRecOn with
  | nil => intro h; obtain ⟨p, hp, -⟩ := h; simp at hp
  | append_singleton R' q ih =>
      intro h
      by_cases hq : q.2.1 = v
      · exact ⟨R', q, [], by simp, hq, by simp⟩
      · have h' : ∃ p ∈ R', p.2.1 = v := by
          obtain ⟨p, hp, hpv⟩ := h
          rcases List.mem_append.mp hp with hp | hp
          · exact ⟨p, hp, hpv⟩
          · simp only [List.mem_singleton] at hp
            subst hp
            exact absurd hpv hq
        obtain ⟨R₁, tie, R₂, hEq, htie, hR₂⟩ := ih h'
        refine ⟨R₁, tie, R₂ ++ [q], ?_, htie, ?_⟩
        · rw [hEq, List.append_assoc, List.append_assoc]
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hR₂ p hp
          · simp only [List.mem_singleton] at hp
            subst hp
            exact hq

/-- **タイが無ければ分解は要らない**（対になる形）。 -/
theorem noTie_or_split {v : ℕ} (R : TrioSeq) :
    (∀ p ∈ R, p.2.1 ≠ v) ∨
      ∃ R₁ tie R₂, R = R₁ ++ [tie] ++ R₂ ∧ tie.2.1 = v ∧
        (∀ p ∈ R₂, p.2.1 ≠ v) := by
  classical
  by_cases h : ∃ p ∈ R, p.2.1 = v
  · exact Or.inr (split_lastTie h)
  · left
    intro p hp hpv
    exact h ⟨p, hp, hpv⟩


/-! ## 課題 L75: 無タイの `TowerOK2` —— 組み立ての骨と、残る 3 つの債務

`oper_cons_tower2` を使った `n` の帰納は次の形になる:

    n = 0     `⟦0⟧ = M.take j0`（写しが 0 個）。**`j0 = 0` なら `[]`**
    n → n+1   `⟦n+1⟧ = (0,v,0) :: graft R (Lift1 (⟦n⟧) t)`
              ⟹ `liftStage_of_noTie` で `Lift1 (⟦n⟧) t ∈ W (2v + 2t)`
              ⟹ `tower2_stage_fits` で `2v + 2t ≤ m` ⟹ `W_mono` で `W m`
              ⟹ `hgr`（節 3 の与件）で `graft R (…) ∈ Wstar`
              ⟹ `Wstar` の定義で `(0,v,0) :: graft R (…) ∈ W (2v)`

### 残る債務 3 つ（名前つき）

1. **`j0 = 0`（親は根）**。`oper_cons_tower2` は結論に `⟦0⟧` を残さないので、
   底のために別途要る。**証明できる**: `j0 ≥ 1` なら `nextR_append_right`
   （`A = [(0,v,0)]`）で `nextR R i (j0-1) (|R|-1)` に移り、
   `domT R m` の第 2 連言 `¬ hasParent R …` と矛盾する。
   ⚠ `hasParent` は `∃!` なので、**一意性も移す**必要がある（存在だけでは足りない）。

2. **`based (Lift1 (⟦n⟧) t)`**。`Lift1` は行 0 を動かさず、`⟦n⟧` の根は `(0,v,0)`
   なので `entry _ 0 0 = 0`。`entry0_Lift1` があれば短い。

3. **伝播**: 各段の尾 `graft R (Lift1 (⟦n⟧) t)` が `argOK` かつ**無タイ**。
   `argOK` は `argOK_graft`（`Wset.lean:2526`）＋ `argOK` の `Lift1` 保存で出るはず。
   **無タイは H11 に測ってもらう最後の 1 本**（`v = 0` なら「行 1 が全部 `≥ 1`」）。

⟹ **1 と 2 は Lean だけで閉じる。3 の無タイだけが外からの入力。** -/


open Classical in
/-- **★★ 債務 1: 親は根**（課題 L75）。`domT R m` は「`R` の末尾は `R` の中では孤児」
なので、`(0,v,z) :: R` で親ができるならそれは**根しかありえない**。

`j0 ≥ 1` なら `nextR_append_right`（`A = [(0,v,z)]`）で `R` の中の親に移り、
`domT` の第 2 連言と矛盾する。**一意性も同じ移送で移る**（`∃!` なので必要）。 -/
theorem parent_is_root_of_domT {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : domT R m)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length = 0 := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  have hcons : ([((0, v, z) : ℕ × ℕ × ℕ)] ++ R) = ((0, v, z) : ℕ × ℕ × ℕ) :: R := rfl
  have hAlen : ([((0, v, z) : ℕ × ℕ × ℕ)] : TrioSeq).length = 1 := rfl
  have hidx : ([((0, v, z) : ℕ × ℕ × ℕ)] : TrioSeq).length + (R.length - 1)
      = R.length := by rw [hAlen]; omega
  obtain ⟨j0, hj0, huniq⟩ := hpM
  have hex : ∃ y, nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) y
      R.length := ⟨j0, hj0⟩
  have hspec : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      (parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length)
      R.length := Classical.epsilon_spec hex
  rw [huniq _ hspec]
  by_contra hne0
  refine absurd ?_ hd.2
  obtain ⟨j0', hj0'⟩ : ∃ j0',
      j0 = ([((0, v, z) : ℕ × ℕ × ℕ)] : TrioSeq).length + j0' :=
    ⟨j0 - 1, by rw [hAlen]; omega⟩
  refine ⟨j0', ?_, ?_⟩
  · show nextR R (srow R (R.length - 1)) j0' (R.length - 1)
    rw [← nextR_append_right (A := [((0, v, z) : ℕ × ℕ × ℕ)]) (N := R)]
    rw [hcons, ← hj0', hidx]
    exact hj0
  · intro y hy
    have h1 := nextR_append_right (A := [((0, v, z) : ℕ × ℕ × ℕ)]) (N := R)
      (i := srow R (R.length - 1)) (a := y) (b := R.length - 1) |>.mpr hy
    rw [hcons, hidx] at h1
    have h2 := huniq _ h1
    rw [hj0'] at h2
    omega


/-- **★ 債務 2: `Lift1` は `based` を保つ**（行 0 を動かさないから）。 -/
theorem based_Lift1 {X : TrioSeq} {d : ℕ} (h : based X) : based (Lift1 X d) := by
  unfold based at h ⊢
  rw [entry0_Lift1]
  exact h

/-- 根が `(0,v,z)` の列は `based`。 -/
theorem based_cons_root (v z : ℕ) (R : TrioSeq) :
    based (((0, v, z) : ℕ × ℕ × ℕ) :: R) := by simp [based, entry]


/-- **★ 債務 3 の `argOK` 側**: `Lift1` は行 0 を動かさないので `argOK` を保つ。 -/
theorem argOK_Lift1 {X : TrioSeq} {d : ℕ} (h : argOK X) : argOK (Lift1 X d) := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  rw [List.mem_range] at hj
  rw [← hjp]
  show 0 < entry X 0 j
  exact h _ (entry_pair_mem (B := X) hj)

/-- **タイでの分解は長さを真に減らす** ⟹ **長さの帰納**が回る（課題 L76）。

⚠ team-lead の §75.3 の訂正: 正しい母集団ではタイは**複数本あり得る**
（1 本 1982 / 2 本 478 / 3 本 14）。⟹ 帰納は 1 段では止まらない。
だが `split_lastTie` の `R₁` は `R` より**真に短い**ので、
**長さについての帰納**なら本数を数えずに回る。 -/
theorem split_lastTie_len {R R₁ R₂ : TrioSeq} {tie : ℕ × ℕ × ℕ}
    (h : R = R₁ ++ [tie] ++ R₂) : R₁.length < R.length := by
  rw [h]
  simp only [List.length_append, List.length_singleton]
  omega


/-! ## ★★★ 課題 L77: 伝播の急所 2 つ

### 急所 1 の答え: **`Lift1` は根（添字 0）を持ち上げる**

`le1 X 0 0` は `ReflTransGen` の**反射**なので `X ≠ []` なら成り立つ。
⟹ `Lift1` のマスク `if le1 X 0 j then d else 0` は `j = 0` で `d` を返す。
⟹ **`Lift1 (X⟦n⟧) t` の根の行 1 は `v + t`**（`t > 0` ならタイにならない）。

### ★★ 急所 2 の答え: **狭義に取り直すと全 `v` で `liftStage_of_window` が直に効く**

無タイ `∀ p ∈ R, p.2.1 ≠ v` を **狭義 `∀ p ∈ R, v < p.2.1`** に強めると:

    `liftStage_of_window`（`Wtower2.lean:128`）の `hw`（行 1 で狭義最小）が
    **そのまま**その条件である ⟹ **`v = 0` に限らず全 `v` で核なしに通る**

⟹ **`TieFree` も `mlift` も経由しなくてよくなる。** `v = 0` では
`p.2.1 ≠ 0 ⟺ 0 < p.2.1` なので `liftStage_of_noTie_zero` は影響を受けない。
`v ≥ 1` では狭義のほうが強いが、**伝播（急所 2 の「元が `< v` の列」）を塞ぐには
狭義が要る**ので、最初から狭義に取るのが正しい。 -/

/-- **急所 1**: `le1 X 0 0` は反射で成り立つ。 -/
theorem le1_zero_self {X : TrioSeq} (h : X ≠ []) : le1 X 0 0 := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr h
  exact ⟨hpos, hpos, Relation.ReflTransGen.refl⟩

/-- **急所 1 の帰結**: `Lift1` は根の行 1 を `+d` する。 -/
theorem entry1_Lift1_zero {X : TrioSeq} (h : X ≠ []) (d : ℕ) :
    entry (Lift1 X d) 1 0 = entry X 1 0 + d := by
  have hpos : 0 < X.length := List.length_pos_iff.mpr h
  rw [entry1_Lift1 hpos, if_pos (le1_zero_self h)]

/-- **★★★ 急所 2: 狭義最小なら全 `v` で核なしに根リフトが通る**（課題 L77）。
`TieFree` も `mlift` も経由しない。 -/
theorem liftStage_of_strict {m d v z : ℕ} {R : TrioSeq} (hargOK : argOK R)
    (hstrict : ∀ p ∈ R, v < p.2.1)
    (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W m) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d) := by
  refine liftStage_of_window hX (root_row0_min hargOK) ?_
  intro l hl0 hl
  simp only [List.length_cons] at hl
  have hA1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
  rw [hA1]
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [entry_cons]
  have h8 := hstrict _ (entry_pair_mem (B := R) (show l' < R.length by omega))
  simpa [entry] using h8

/-- 狭義は無タイを含む。 -/
theorem noTie_of_strict {v : ℕ} {R : TrioSeq} (h : ∀ p ∈ R, v < p.2.1) :
    ∀ p ∈ R, p.2.1 ≠ v := fun p hp => by have := h p hp; omega


/-! ## ★★★ 課題 L77: `towerOK2_of_noTie` の組み立て -/

/-- `srow` は根を cons しても末尾の列で変わらない。 -/
theorem srow_cons_last {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) :
    srow (p :: R) R.length = srow R (R.length - 1) := by
  unfold srow
  rw [entry_cons_last hRne 2, entry_cons_last hRne 1]

open Classical in
/-- **底**: `⟦0⟧ = []`（親が根なので `take 0`）。 -/
theorem oper_cons_zero {v z m : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hd : domT R m)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦0⟧ = [] := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  rw [oper_unfold (M := ((0, v, z) : ℕ × ℕ × ℕ) :: R) (j1 := R.length)
      (i1 := srow R (R.length - 1)) (j0 := 0)
      (d0 := if 0 < srow R (R.length - 1) then
        entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 R.length
          - entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0 else 0)
      (d1 := if 1 < srow R (R.length - 1) then
        entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 R.length
          - entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 else 0)
      (by simp) (by omega) ?hz (srow_cons_last hRne).symm hpM
      (parent_is_root_of_domT hRne hd hpM).symm rfl rfl 0]
  · simp
  · intro hc
    have h1 := hc.1
    rw [entry_cons_last hRne 0] at h1
    omega


open Classical in
/-- **★★★★ 無タイの `TowerOK2`**（課題 L77）。伝播 `hprop` だけを仮定に残した形。

H11 の実測（H50、標本 20000、`n = 1..12`）: **伝播は 100%**、対照も鳴っている
（タイのある場面では無タイが 0/6000、持ち上げ量を `t±1` にすると `hstep` が 0/4000）。 -/
theorem towerOK2_of_noTie {v m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hz' : entry R 2 (R.length - 1) = 1)
    (hvw : v ≤ entry R 1 (R.length - 1))
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hprop : ∀ n : ℕ,
      argOK (graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v))) ∧
      (∀ p ∈ graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v)), p.2.1 ≠ v)) :
    ∀ n : ℕ, (((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v) := by
  have hfits : 2 * v + 2 * (entry R 1 (R.length - 1) - v) ≤ m := by
    have h9 := tower2_stage_fits (v := v) (z := 0) rfl hd hi2 hvw
    omega
  have hzero := oper_cons_zero (v := v) (z := 0) hR hRne hd hpM
  intro n
  induction n with
  | zero =>
      rw [hzero]
      exact W_nil _
  | succ n ih =>
      rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
      have hin : Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
          (entry R 1 (R.length - 1) - v) ∈ W m := by
        cases n with
        | zero =>
            rw [hzero]
            simpa using W_nil m
        | succ k =>
            rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM] at ih ⊢
            exact W_mono hfits (liftStage_of_noTie (hprop k).1 (hprop k).2 ih)
      have hb : based (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
          (entry R 1 (R.length - 1) - v)) := by
        refine based_Lift1 ?_
        cases n with
        | zero =>
            rw [hzero]
            exact based_nil
        | succ k =>
            rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
            exact based_cons_root v 0 _
      exact hgr _ hin hb (hprop n).1 v 0 (2 * v) (by omega) (by omega)


/-! ## ★★★ 課題 L78: 狭義版

条件の整理:

    `TieFree`（錐の包含）           … 狭義に取り直すと**要らなくなった**
    無タイ `∀ p ∈ R, p.2.1 ≠ v`     … `tieSyn_holds` / `liftStage_of_noTie` が使う
    **狭義 `∀ p ∈ R, v < p.2.1`**   … `liftStage_of_strict` が使う。**本線**

⚠ team-lead の指摘どおり、**分解も直す必要がある**。狭義の否定は
`∃ p ∈ R, p.2.1 ≤ v` なので、`= v` で割る `split_lastTie` では届かない。
⟹ **述語版に一般化**して `≤ v` でも割れるようにする。 -/

/-- **★★ 最後の `P` で割る**（`split_lastTie` の述語版）。 -/
theorem split_last_pred {P : ℕ × ℕ × ℕ → Prop} [DecidablePred P] :
    ∀ {R : TrioSeq}, (∃ p ∈ R, P p) →
    ∃ R₁ q R₂, R = R₁ ++ [q] ++ R₂ ∧ P q ∧ (∀ p ∈ R₂, ¬ P p) := by
  intro R
  induction R using List.reverseRecOn with
  | nil => intro h; obtain ⟨p, hp, -⟩ := h; simp at hp
  | append_singleton R' q ih =>
      intro h
      by_cases hq : P q
      · exact ⟨R', q, [], by simp, hq, by simp⟩
      · have h' : ∃ p ∈ R', P p := by
          obtain ⟨p, hp, hpv⟩ := h
          rcases List.mem_append.mp hp with hp | hp
          · exact ⟨p, hp, hpv⟩
          · simp only [List.mem_singleton] at hp
            subst hp
            exact absurd hpv hq
        obtain ⟨R₁, q', R₂, hEq, hq', hR₂⟩ := ih h'
        refine ⟨R₁, q', R₂ ++ [q], ?_, hq', ?_⟩
        · rw [hEq, List.append_assoc, List.append_assoc]
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hR₂ p hp
          · simp only [List.mem_singleton] at hp
            subst hp
            exact hq

/-- **狭義版の分解**: `v` 以下の列で割ると、右側は**狭義**になる。 -/
theorem split_lastLe {v : ℕ} {R : TrioSeq} (h : ∃ p ∈ R, p.2.1 ≤ v) :
    ∃ R₁ q R₂, R = R₁ ++ [q] ++ R₂ ∧ q.2.1 ≤ v ∧ (∀ p ∈ R₂, v < p.2.1) := by
  obtain ⟨R₁, q, R₂, hEq, hq, hR₂⟩ :=
    split_last_pred (P := fun p => p.2.1 ≤ v) h
  exact ⟨R₁, q, R₂, hEq, hq, fun p hp => by have := hR₂ p hp; omega⟩

/-- 狭義か、`≤ v` の列で割れるか。 -/
theorem strict_or_split {v : ℕ} (R : TrioSeq) :
    (∀ p ∈ R, v < p.2.1) ∨
      ∃ R₁ q R₂, R = R₁ ++ [q] ++ R₂ ∧ q.2.1 ≤ v ∧ (∀ p ∈ R₂, v < p.2.1) := by
  classical
  by_cases h : ∃ p ∈ R, p.2.1 ≤ v
  · exact Or.inr (split_lastLe h)
  · left
    intro p hp
    by_contra hc
    exact h ⟨p, hp, by omega⟩

open Classical in
/-- **★★★★ 狭義版の `TowerOK2`**（課題 L78-1）。`TieFree` も `mlift` も経由しない。 -/
theorem towerOK2_of_strict {v m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hz' : entry R 2 (R.length - 1) = 1)
    (hvw : v ≤ entry R 1 (R.length - 1))
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hprop : ∀ n : ℕ,
      argOK (graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v))) ∧
      (∀ p ∈ graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v)), v < p.2.1)) :
    ∀ n : ℕ, (((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v) := by
  have hfits : 2 * v + 2 * (entry R 1 (R.length - 1) - v) ≤ m := by
    have h9 := tower2_stage_fits (v := v) (z := 0) rfl hd hi2 hvw
    omega
  have hzero := oper_cons_zero (v := v) (z := 0) hR hRne hd hpM
  intro n
  induction n with
  | zero =>
      rw [hzero]
      exact W_nil _
  | succ n ih =>
      rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
      have hin : Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
          (entry R 1 (R.length - 1) - v) ∈ W m := by
        cases n with
        | zero =>
            rw [hzero]
            simpa using W_nil m
        | succ k =>
            rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM] at ih ⊢
            exact W_mono hfits (liftStage_of_strict (hprop k).1 (hprop k).2 ih)
      have hb : based (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
          (entry R 1 (R.length - 1) - v)) := by
        refine based_Lift1 ?_
        cases n with
        | zero =>
            rw [hzero]
            exact based_nil
        | succ k =>
            rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
            exact based_cons_root v 0 _
      exact hgr _ hin hb (hprop n).1 v 0 (2 * v) (by omega) (by omega)


/-! ## ★★★ 課題 L79: 狭義の伝播は自明に閉じる

team-lead の骨（紙）をそのまま Lean に:

    `R.dropLast`            … `R` の部分列 ⟹ `Strict R` から直に
    `Lift1 (X⟦n⟧) t` の根   … `entry1_Lift1_zero` で `v + t`、`t > 0` ⟹ `v < v+t`
    `Lift1` の残り          … 帰納法の仮定 ＋ `Lift1` は行 1 を**足すだけ**
    `graft`                 … **行 0 しかずらさない**ので行 1 は不変

**減る操作が 1 つも無い**ので `n` の帰納でそのまま出る。

「無タイ（`≠ v`）」で閉じない理由も同じ骨で見える: `p.2.1 < v` の列が `+t` で
**ちょうど `v`** になり得る。狭義なら「`v` より大きい」が上向きの操作で保たれる。 -/

/-- **狭義条件**。 -/
def Strict (v : ℕ) (R : TrioSeq) : Prop := ∀ p ∈ R, v < p.2.1

theorem strict_dropLast {v : ℕ} {R : TrioSeq} (h : Strict v R) :
    Strict v R.dropLast := fun p hp => h p (List.dropLast_subset _ hp)

/-- `graft` は**行 0 しかずらさない**ので行 1 の狭義性は不変。 -/
theorem strict_graft {v : ℕ} {R y : TrioSeq} (hR : Strict v R.dropLast)
    (hy : Strict v y) : Strict v (graft R y) := by
  intro p hp
  simp only [graft, List.mem_append] at hp
  rcases hp with h | h
  · exact hR p h
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact hy q hq

open Classical in
/-- `Lift1` は行 1 を**足すだけ**。根は `v + d`、残りは帰納法の仮定。 -/
theorem strict_Lift1_cons {v z d : ℕ} {R : TrioSeq} (hd : 0 < d)
    (hR : Strict v R) :
    Strict v (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) := by
  intro p hp
  simp only [Lift1, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  show v < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 i
      + (if le1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 i then d else 0)
  cases i with
  | zero =>
      have h0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := rfl
      rw [h0, if_pos (le1_zero_self (by simp))]
      omega
  | succ k =>
      have hk : k < R.length := by
        simp only [List.length_cons] at hi; omega
      have h1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 (k + 1) = entry R 1 k :=
        entry_cons _ _ _ _
      have hm : v < entry R 1 k := hR _ (entry_pair_mem (B := R) hk)
      rw [h1]
      split <;> omega

/-- 1 段ぶんの伝播。 -/
theorem strict_step {v z d : ℕ} {R Rn : TrioSeq} (hd : 0 < d)
    (hR : Strict v R) (hRn : Strict v Rn) :
    Strict v (graft R (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: Rn) d)) :=
  strict_graft (strict_dropLast hR) (strict_Lift1_cons hd hRn)

open Classical in
/-- **★★★ 伝播（課題 L79-2）**: 狭義なら `hprop` が `n` の帰納で出る。 -/
theorem strict_prop {v m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2) (hst : Strict v R)
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n : ℕ,
      argOK (graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v))) ∧
      (∀ p ∈ graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v)), v < p.2.1) := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  have ht : 0 < entry R 1 (R.length - 1) - v := by
    have := hst _ (entry_pair_mem (B := R) (show R.length - 1 < R.length by omega))
    simp only at this
    omega
  have hzero := oper_cons_zero (v := v) (z := 0) hR hRne hd hpM
  intro n
  refine ⟨argOK_graft hRne hR _, ?_⟩
  induction n with
  | zero =>
      rw [hzero, Lift1_nil, graft_nil]
      exact strict_dropLast hst
  | succ k ih =>
      rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
      exact strict_step ht hst ih

open Classical in
/-- **★★★★★ 仮定ゼロの狭義 `TowerOK2`**（課題 L79-4）。`hprop` が消えた。 -/
theorem towerOK2_of_strict' {v m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hz' : entry R 2 (R.length - 1) = 1)
    (hst : Strict v R)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n : ℕ, (((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v) := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  have hvw : v ≤ entry R 1 (R.length - 1) := by
    have := hst _ (entry_pair_mem (B := R) (show R.length - 1 < R.length by omega))
    simp only at this
    omega
  exact towerOK2_of_strict hR hRne hd hi2 hz' hvw hgr hpM
    (strict_prop hR hRne hd hi2 hst hpM)


/-! ## ★★★ 課題 L80: `le1` 錐は行 1 の狭義増加

H11 の全数（70557 件）が出した構造的理由:

    **`Lift1` のマスクは `le1` 錐。`nextrel1` は行 1 の狭義増加を要求する。**
    **⟹ 行 1 が根以下の列は錐に入らない ⟹ `Lift1` が一度も触れない。**

⚠ 1 点だけ team-lead の文言を直す: `le1` は**反射的**なので `j = 0` は
（行 1 が根と等しくても）錐に入る。よって `j ≠ 0` が要る。 -/

/-- `le1` の鎖に沿って行 1 は単調。 -/
theorem rtg1_entry1_mono {X : TrioSeq} {i j : ℕ}
    (h : Relation.ReflTransGen (nextrel1 X) i j) :
    entry X 1 i ≤ entry X 1 j := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (le_of_lt hbc.2.2.2.1)

/-- 1 段でも進めば行 1 は**狭義**に増える。 -/
theorem le1_entry1_lt {X : TrioSeq} {i j : ℕ} (h : le1 X i j) (hne : i ≠ j) :
    entry X 1 i < entry X 1 j := by
  obtain ⟨-, -, hr⟩ := h
  cases hr with
  | refl => exact absurd rfl hne
  | tail hab hbc => exact lt_of_le_of_lt (rtg1_entry1_mono hab) hbc.2.2.2.1

/-- **★★ 課題 L80 の鍵**: 行 1 が根以下の列は `le1` 錐に入らない。 -/
theorem lift1_untouched_of_le {X : TrioSeq} {j : ℕ} (hj : j ≠ 0)
    (h : entry X 1 j ≤ entry X 1 0) : ¬ le1 X 0 j := by
  intro hle
  have := le1_entry1_lt hle (Ne.symm hj)
  omega

open Classical in
/-- ⟹ `Lift1` はその列の行 1 を**変えない**。 -/
theorem entry1_Lift1_untouched {X : TrioSeq} {d j : ℕ} (hj : j ≠ 0)
    (hlt : j < X.length) (h : entry X 1 j ≤ entry X 1 0) :
    entry (Lift1 X d) 1 j = entry X 1 j := by
  rw [entry1_Lift1 hlt, if_neg (lift1_untouched_of_le hj h), Nat.add_zero]

/-! ### ⟹ 伝播は**無タイでも**閉じる（狭義は `liftStage_of_window` の都合だけ） -/

/-- **無タイ条件**。 -/
def NoTie (v : ℕ) (R : TrioSeq) : Prop := ∀ p ∈ R, p.2.1 ≠ v

theorem noTie_dropLast {v : ℕ} {R : TrioSeq} (h : NoTie v R) :
    NoTie v R.dropLast := fun p hp => h p (List.dropLast_subset _ hp)

theorem noTie_graft {v : ℕ} {R y : TrioSeq} (hR : NoTie v R.dropLast)
    (hy : NoTie v y) : NoTie v (graft R y) := by
  intro p hp
  simp only [graft, List.mem_append] at hp
  rcases hp with h | h
  · exact hR p h
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact hy q hq

open Classical in
/-- **★★★ 無タイの `Lift1` 保存**。`< v` の列は錐に入らないので触れられない。 -/
theorem noTie_Lift1_cons {v z d : ℕ} {R : TrioSeq} (hd : 0 < d)
    (hR : NoTie v R) :
    NoTie v (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) := by
  intro p hp
  simp only [Lift1, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  show entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 i
      + (if le1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 i then d else 0) ≠ v
  have hroot : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := rfl
  cases i with
  | zero =>
      rw [hroot, if_pos (le1_zero_self (by simp))]
      omega
  | succ k =>
      have hk : k < R.length := by
        simp only [List.length_cons] at hi; omega
      have h1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 (k + 1) = entry R 1 k :=
        entry_cons _ _ _ _
      have hm : entry R 1 k ≠ v := hR _ (entry_pair_mem (B := R) hk)
      rcases Nat.lt_or_ge (entry R 1 k) v with hlt | hge
      · -- `< v` ⟹ 錐に入らない ⟹ `Lift1` は触れない
        rw [if_neg (lift1_untouched_of_le (X := ((0, v, z) : ℕ × ℕ × ℕ) :: R)
          (j := k + 1) (by omega) (by rw [h1, hroot]; omega))]
        rw [h1]; omega
      · -- `> v` ⟹ 足しても `v` を超えたまま
        rw [h1]
        split <;> omega

/-- 1 段ぶんの伝播（無タイ版）。 -/
theorem noTie_step {v z d : ℕ} {R Rn : TrioSeq} (hd : 0 < d)
    (hR : NoTie v R) (hRn : NoTie v Rn) :
    NoTie v (graft R (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: Rn) d)) :=
  noTie_graft (noTie_dropLast hR) (noTie_Lift1_cons hd hRn)

open Classical in
/-- **★★★ 伝播（無タイ版）**。狭義は `liftStage_of_window` の都合だけだった。 -/
theorem noTie_prop {v m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2) (hnt : NoTie v R)
    (hvw : v ≤ entry R 1 (R.length - 1))
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n : ℕ,
      argOK (graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v))) ∧
      (∀ p ∈ graft R (Lift1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
        (entry R 1 (R.length - 1) - v)), p.2.1 ≠ v) := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  have ht : 0 < entry R 1 (R.length - 1) - v := by
    have := hnt _ (entry_pair_mem (B := R) (show R.length - 1 < R.length by omega))
    simp only at this
    omega
  have hzero := oper_cons_zero (v := v) (z := 0) hR hRne hd hpM
  intro n
  refine ⟨argOK_graft hRne hR _, ?_⟩
  induction n with
  | zero =>
      rw [hzero, Lift1_nil, graft_nil]
      exact noTie_dropLast hnt
  | succ k ih =>
      rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
      exact noTie_step ht hnt ih

open Classical in
/-- **★★★★★ 仮定ゼロの無タイ `TowerOK2`**（課題 L80-2）。 -/
theorem towerOK2_of_noTie' {v m : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hz' : entry R 2 (R.length - 1) = 1)
    (hvw : v ≤ entry R 1 (R.length - 1))
    (hnt : NoTie v R)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n : ℕ, (((0, v, 0) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v) :=
  towerOK2_of_noTie hR hRne hd hi2 hz' hvw hgr hpM
    (noTie_prop hR hRne hd hi2 hnt hvw hpM)


/-! ## ★★★ 課題 L81: 核を「タイのある根」だけに絞る

`liftStage_of_noTie`（緑・仮定ゼロ）が無タイの全 `v` を覆うので、
(WL) の残りは**タイのある根**だけ。 -/

/-- **残る唯一の持ち上げ核**: 行 1 のタイがある根での (WL)。 -/
def LiftTie : Prop :=
  ∀ (m d v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W m →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d)

open Classical in
/-- タイ／無タイで場合分け ⟹ 根つきの (WL) が全部出る。 -/
theorem liftStage_cons (h : LiftTie) {m d v z : ℕ} {R : TrioSeq} (hargOK : argOK R)
    (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W m) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d) := by
  by_cases ht : ∃ p ∈ R, p.2.1 = v
  · exact h m d v z R hargOK ht hX
  · exact liftStage_of_noTie hargOK (fun p hp hpv => ht ⟨p, hp, hpv⟩) hX

/-- `LiftStage`（全体版）はもちろん `LiftTie` を含む。 -/
theorem liftTie_of_liftStage (h : LiftStage) : LiftTie :=
  fun m d _ _ _ _ _ hX => h m d _ hX

/-- ⟹ `Row1Mono` からも出る（`liftStage_of_row1mono` 経由）。 -/
theorem liftTie_of_row1mono (h : Row1Mono) : LiftTie :=
  liftTie_of_liftStage (liftStage_of_row1mono h)

/-! ### 親の関係から `z < r2` と `v < w` が出る ⟹ `hz'` / `hvw` は仮定に要らない -/

open Classical in
/-- 根が親なら `nextrel2` の中身がそのまま取れる。 -/
theorem tower2_root_spec {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    nextrel2 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 R.length := by
  have hp0 := parent_is_root_of_domT hRne hd hpM
  obtain ⟨q0, hq0, -⟩ := hpM
  have hex : ∃ j0, nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow R (R.length - 1)) j0 R.length := ⟨q0, hq0⟩
  have hspec : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      (parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length)
      R.length := Classical.epsilon_spec hex
  rw [hp0, hi2, nextR] at hspec
  simpa only [if_neg (by omega : (2 : ℕ) ≠ 0),
    if_neg (by omega : (2 : ℕ) ≠ 1)] using hspec

/-- **`z < entry R 2 (末尾)`**（親の行 2 の狭義増加）。 -/
theorem tower2_zr {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    z < entry R 2 (R.length - 1) := by
  have h := (tower2_root_spec hRne hd hi2 hpM).2.2.2.1
  rw [entry_cons_last hRne 2] at h
  have hz : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 = z := by simp [entry]
  rw [hz] at h
  exact h

/-- **`v < entry R 1 (末尾)`**（`le1` 錐は行 1 の狭義増加 — 課題 L80）。 -/
theorem tower2_vw {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    v < entry R 1 (R.length - 1) := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  have hle := (tower2_root_spec hRne hd hi2 hpM).2.2.2.2.1
  have h := le1_entry1_lt hle (by omega : (0 : ℕ) ≠ R.length)
  rw [entry_cons_last hRne 1] at h
  have hv : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
  rw [hv] at h
  exact h

/-- **★★ 段はいつでもちょうど収まる**（`z = 0` も `hz' = 1` も要らない）。 -/
theorem tower2_stage_fits' {v z m : ℕ} {R : TrioSeq} (hd : domT R m)
    (hzr : z < entry R 2 (R.length - 1)) (hvw : v ≤ entry R 1 (R.length - 1)) :
    2 * v + z + 2 * (entry R 1 (R.length - 1) - v) ≤ m := by
  have h1 := hd.1
  unfold lev at h1
  omega

/-- **`domT` なら末尾の `srow` は `0` でない**（`towerOK_of_split` の `h0`）。 -/
theorem srow_ne_zero_of_domT (R : TrioSeq) (hRne : R ≠ [])
    (hdom : ∃ m, domT R m) : srow R (R.length - 1) ≠ 0 := by
  obtain ⟨m, hd⟩ := hdom
  have h1 := hd.1
  unfold lev at h1
  intro h0
  unfold srow at h0
  split at h0
  · omega
  · split at h0
    · omega
    · omega

open Classical in
/-- **★★★★★ `TowerOK2` の節 3 側が `LiftTie` だけに落ちた**（課題 L81）。

`towerOK2_of_noTie'` / `towerOK2_of_strict'` を両方含む一般形:
`z` は一般、`hz'` と `hvw` は親の関係から自動、無タイ／狭義の場合分けも内蔵。 -/
theorem towerOK2_of_clause3 {v z a m : ℕ} {R : TrioSeq} (hlt : LiftTie)
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n : ℕ, (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  have hvw : v < entry R 1 (R.length - 1) := tower2_vw hRne hd hi2 hpM
  have hzr : z < entry R 2 (R.length - 1) := tower2_zr hRne hd hi2 hpM
  have hfits : 2 * v + z + 2 * (entry R 1 (R.length - 1) - v) ≤ m :=
    tower2_stage_fits' hd hzr (by omega)
  have hzero := oper_cons_zero (v := v) (z := z) hR hRne hd hpM
  have key : ∀ n : ℕ, (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v + z) := by
    intro n
    induction n with
    | zero => rw [hzero]; exact W_nil _
    | succ n ih =>
        rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
        have hin : Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
            (entry R 1 (R.length - 1) - v) ∈ W m := by
          cases n with
          | zero => rw [hzero]; simpa using W_nil m
          | succ k =>
              rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM] at ih ⊢
              exact W_mono hfits (liftStage_cons hlt (argOK_graft hRne hR _) ih)
        have hb : based (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
            (entry R 1 (R.length - 1) - v)) := by
          refine based_Lift1 ?_
          cases n with
          | zero => rw [hzero]; exact based_nil
          | succ k =>
              rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
              exact based_cons_root v z _
        exact hgr _ hin hb (argOK_graft hRne hR _) v z (2 * v + z) hz1 (by omega)
  exact fun n => W_mono hva (key n)


/-! ## ★★★★★ 課題 L81-b: `TowerGraft2`（開核 A）が `LiftTie` に落ちる

`Wset.towerOK_of (h2 : TowerGraft2) (he : TowerExp) : TowerOK` の構造:

    節 1            矛盾（`domT` と両立しない）        既済
    **節 2**        **`TowerExp`（開核 B）**            ← 別の核。手つかず
    節 3 / srow=1   `tower1_mem`                        既済
    **節 3 / srow=2** **`TowerGraft2`（開核 A）**        ← **これを閉じる**

`TowerGraft2` は `towerOK2_of_clause3` と**同じ文**なので、そのまま繋がる。 -/

/-- **★★★★★ 開核 A が `LiftTie` だけに落ちた。** -/
theorem towerGraft2_of_liftTie (hlt : LiftTie) : TowerGraft2 :=
  fun v z m a R hR hRne hz1 hva hd hi2 hgr hpM n _ =>
    towerOK2_of_clause3 hlt hR hRne hd hi2 hz1 hva hgr hpM n

/-- **⟹ `TowerOK` は `LiftTie` ＋ `TowerExp` から出る。**
（既存の `towerOK_of (towerGraft2_of_liftStage hWL) he` より核が真に小さい:
`LiftStage`（全部の根）→ **`LiftTie`（タイのある根だけ）**。） -/
theorem towerOK_of_liftTie (hlt : LiftTie) (he : TowerExp) : TowerOK :=
  towerOK_of (towerGraft2_of_liftTie hlt) he


/-! ### ⚠ `Final.lean` への登録は build が要る（team-lead へ）

`towerOK_of_liftTie` を `Final.TRIO_terminates_of_towerOK` に繋げば

    **`LiftTie` ＋ `TowerExp` ⟹ `WellFounded stepRel`**

が出る（`Final.TRIO_terminates_of_liftStage` より核が真に小さい）。ただし
`Final.lean` から `L53Subst` を `import` するには `L53Subst.olean` が要り、それには
`lakefile.toml` の `roots` に `"L53Subst"` を足して **1 回 build** する必要がある。
私は `leanman check` しか許可されていないので、ここまでで止める。

登録するときに足すのは次の 3 行だけ（`import L53Subst` の追加とセット）:

```lean
theorem TRIO_terminates_of_liftTie (hlt : L53.LiftTie) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates (L53.towerGraft2_of_liftTie hlt) he
```

（`Final.lean` に一時的に書いて `leanman check` した結果は
`unknown module prefix 'L53Subst'` のみ ＝ 中身の型は未検証。上の 1 行は
`towerGraft2_of_liftTie : LiftTie → TowerGraft2`（**この file で緑**）と
`Final.TRIO_terminates : TowerGraft2 → TowerExp → WellFounded stepRel`
の合成なので、型は合う。） -/


/-! ## ★★★★ 課題 L83: `Lift1` は `mlift` の行 1 を `coneV \ le1` で下げたもの

H11 の実測（H53）:

    `Lift1` と `mlift` の差は **0 本 364 (6.1%) / 1 本 3749 / 2 本 1824 / 3 本 63**
    差は**行 1 だけ**。量は `d`。**行 0 と行 2 は一切動かない**
    `coneV \ le1` の列は行 1 がちょうど `v` が 89.6%、`> v` が 10.4%

⟹ `Lift1_eq_mlift_of_tieFree` から `TieFree` を落とした**一般形**が書ける。 -/

theorem coneV_out {X : TrioSeq} {w j : ℕ} (hj : X.length ≤ j) :
    ¬ coneV X w j := by
  intro h
  have h2 := h j Relation.ReflTransGen.refl
  rw [entry1_out hj] at h2
  omega

theorem le1_out {X : TrioSeq} {j : ℕ} (hj : X.length ≤ j) : ¬ le1 X 0 j := by
  intro h; have := h.2.1; omega

open Classical in
/-- **★★ (L83-a) `TieFree` を落とした一般形**: `mlift` は `Lift1` の行 1 を
`coneV \ le1` の列でちょうど `d` **上げた**もの。 -/
theorem entry1_mlift_eq_Lift1 {X : TrioSeq} (hv : 1 ≤ entry X 1 0) (d j : ℕ) :
    entry (mlift X (entry X 1 0 - 1) d) 1 j
      = entry (Lift1 X d) 1 j
        + (if coneV X (entry X 1 0 - 1) j ∧ ¬ le1 X 0 j then d else 0) := by
  rcases Nat.lt_or_ge j X.length with hj | hj
  · rw [entry1_mlift hj, entry1_Lift1 hj]
    by_cases hc : coneV X (entry X 1 0 - 1) j
    · by_cases hl : le1 X 0 j
      · rw [if_pos hc, if_pos hl, if_neg (by tauto)]; omega
      · rw [if_pos hc, if_neg hl, if_pos ⟨hc, hl⟩]; omega
    · rw [if_neg hc, if_neg (fun h => hc (coneV_of_le1 hv h)), if_neg (by tauto)]
  · rw [entry1_out (by rw [mlift_length]; omega),
      entry1_out (by rw [Lift1_length]; omega), if_neg (by
        rintro ⟨hc, -⟩; exact coneV_out hj hc)]

/-- ⟹ 行 0・行 2・長さは完全に一致し、**行 1 だけ** `Lift1 ≤ mlift`。
これがそのまま `Row1Mono` の入力の形。 -/
theorem Lift1_le_mlift {X : TrioSeq} (hv : 1 ≤ entry X 1 0) (d : ℕ) :
    (Lift1 X d).length = (mlift X (entry X 1 0 - 1) d).length ∧
    (∀ j, entry (Lift1 X d) 0 j = entry (mlift X (entry X 1 0 - 1) d) 0 j) ∧
    (∀ j, entry (Lift1 X d) 2 j = entry (mlift X (entry X 1 0 - 1) d) 2 j) ∧
    (∀ j, entry (Lift1 X d) 1 j ≤ entry (mlift X (entry X 1 0 - 1) d) 1 j) := by
  refine ⟨by rw [Lift1_length, mlift_length], fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [entry0_Lift1, entry0_mlift]
  · rw [entry2_Lift1, entry2_mlift]
  · rw [entry1_mlift_eq_Lift1 hv]; omega

/-! ### L83-b: 核を `Row1DownLocal` に移す -/

/-- **(ROW1DOWNLOCAL)**: `mlift` から `Lift1` へ ——
行 1 を `coneV \ le1` の列（実測 1〜3 本）で `d` 下げても段は上がらない。
**`Row1Mono` より真に弱い**: 対象はその 1〜3 本だけ、下げ幅は `d` で一定、
行 0 と行 2 は一切動かない。 -/
def Row1DownLocal : Prop :=
  ∀ (a d : ℕ) (X : TrioSeq), 1 ≤ entry X 1 0 →
    mlift X (entry X 1 0 - 1) d ∈ W a → Lift1 X d ∈ W a

/-- 根の行 1 が `0` のときは `mlift` の閾値が届かないので一様シフトを台にする。 -/
def Row1DownRoot0 : Prop :=
  ∀ (a d : ℕ) (X : TrioSeq), entry X 1 0 = 0 →
    shiftr01 0 d X ∈ W a → Lift1 X d ∈ W a

/-- **★★★ (L83-b) 局所版から `(WL)` が出る。** -/
theorem liftStage_of_row1down (h1 : Row1DownLocal) (h0 : Row1DownRoot0) :
    LiftStage := by
  intro m d X hX
  rcases Nat.eq_zero_or_pos (entry X 1 0) with hv | hv
  · exact h0 _ _ _ hv (ulift_mem_W X hX)
  · exact h1 _ _ _ hv (mlift_mem_W X hX)

/-- ⟹ **核が `Row1DownLocal` ＋ `Row1DownRoot0` に移る。** -/
theorem liftTie_of_row1down (h1 : Row1DownLocal) (h0 : Row1DownRoot0) : LiftTie :=
  liftTie_of_liftStage (liftStage_of_row1down h1 h0)

/-- **`Row1Mono` より弱いことの証明**: `Row1Mono` から両方出る。 -/
theorem row1DownLocal_of_row1mono (h : Row1Mono) : Row1DownLocal := by
  intro a d X hv hm
  obtain ⟨hl, h0, h2, h1⟩ := Lift1_le_mlift (X := X) hv d
  exact h a _ _ hm hl h0 h2 h1

theorem row1DownRoot0_of_row1mono (h : Row1Mono) : Row1DownRoot0 := by
  intro a d X hv hs
  refine h a _ _ hs (by rw [Lift1_length, shiftr01_length]) (fun j => ?_)
    (fun j => ?_) (fun j => ?_)
  · rw [entry0_Lift1, entry0_shiftr1]
  · rw [entry2_Lift1, entry2_shiftr01]
  · rcases Nat.lt_or_ge j X.length with hj | hj
    · rw [entry1_Lift1 hj, entry1_shiftr1 hj]; split <;> omega
    · rw [entry1_out (by rw [Lift1_length]; omega),
        entry1_out (by rw [shiftr01_length]; omega)]

/-! ### L83-c: `TieFree` が成り立つタイ場面（実測 6.1%）は無料 -/

/-- タイがあっても `TieFree` が成り立てば `(WL)` は既存定理で通る。 -/
theorem liftTie_case_tieFree {m d : ℕ} {X : TrioSeq} (hX : X ∈ W m)
    (hv : 1 ≤ entry X 1 0) (h : TieFree X) : Lift1 X d ∈ W (m + 2 * d) :=
  liftStage_of_tieFree hX hv h


/-! ## ★★★★ 課題 L84-b: `TowerExp`（開核 B）は何を要求しているか

`Wset.TowerExp` は `TowerGraft2` と**同じ結論**で、仮定だけが違う:

    節 3（`TowerGraft2`）  `∀ y ∈ W m, based y → graft R y ∈ Wstar`   … **族ぜんぶ**
    節 2（`TowerExp`）     `∀ n ≥ 1, R⟦n⟧ ∈ Wstar`                    … **1 個だけ**

`domT R m` のとき末尾は孤児なので `R⟦n⟧ = graft R []`（`oper_eq_graft_nil_of_domT`）。
⟹ **節 2 がくれるのは `y = []` の 1 個、すなわち `R.dropLast ∈ Wstar` だけ。**
塔の段は空でないので、足りないのはちょうど

    `R.dropLast ∈ Wstar` ＋ `y ∈ W m`（`based`） ⟹ `graft R y ∈ Wstar`

で、`graft R y = R.dropLast ++ shiftBlk (末尾列) y` だから、これは
**連結（`WCat` / `WSnoc`）そのもの**。⟹ `Wstar` 路線でも相方は軽くならない。 -/

/-- 節 2 が実際にくれるもの（`|R| ≥ 2` のとき）。 -/
theorem exp_gives_dropLast {m : ℕ} {R : TrioSeq} (hL : 1 < R.length) (hd : domT R m)
    (hop : ∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) : R.dropLast ∈ Wstar := by
  have h := hop 1 le_rfl
  rw [oper_eq_graft_nil_of_domT hL hd, graft_nil] at h
  exact h

/-- **開核 B の正体**: `Aop` の節 2 から節 3 を作ること。 -/
def GraftFromExp : Prop :=
  ∀ (m : ℕ) (R : TrioSeq), R ≠ [] → argOK R → domT R m →
    (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) →
    ∀ y ∈ W m, based y → graft R y ∈ Wstar

/-- **★★★ `TowerExp` は `GraftFromExp` ＋ `TowerGraft2` に落ちる。**
節 2 を節 3 に直せば、あとは `TowerOK` の節 3 側（`tower1_mem` は証明ずみ、
`TowerGraft2` は課題 L81 で `LiftTie` に落ちた）と同じ。 -/
theorem towerExp_of_graftFromExp (h2 : TowerGraft2) (hg : GraftFromExp) :
    TowerExp := by
  intro v z m a R hR hRne hz1 hva hd hop hpM n hn
  have hgr := hg m R hRne hR hd hop
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
  have hsr : srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
    unfold srow
    unfold lev at hlevpos
    by_cases h2' : 0 < entry R 2 (R.length - 1)
    · rw [if_pos h2']; exact Or.inr rfl
    · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
  rcases hsr with h1 | h1
  · rw [oper_cons_tower1 hR hRne hd h1 hpM]
    exact tower1_mem hR hRne hz1 hva hd h1 hgr hpM n
  · exact h2 v z m a R hR hRne hz1 hva hd h1 hgr hpM n hn

/-- **★★★★★ 残る核は `LiftTie` と `GraftFromExp` のちょうど 2 本。** -/
theorem towerOK_of_liftTie_graft (hlt : LiftTie) (hg : GraftFromExp) : TowerOK :=
  towerOK_of (towerGraft2_of_liftTie hlt)
    (towerExp_of_graftFromExp (towerGraft2_of_liftTie hlt) hg)

/-! ### ⚠ 既存との重複の報告

`Wset.row2_revival_gap`（`Wset.lean:3793`）が私の `tower2_vw` / `tower2_zr` と
**同じ内容**（`v < entry R 1 (末尾) ∧ z < entry R 2 (末尾)`）だった。
`Wtower2.TowerExp2Root`（`Wtower2.lean:2257`）はそれを仮定に取り込んだ形で、
`towerExp2_of_root` / `towerExp2Low_of_root` も既にある。
⟹ `TowerExp2` の側は `TowerExp2Root` まで削れている。残るのは節 2 の中身
（`GraftFromExp`）で、そこは `TowerExp2Root` でも消えていない。 -/


/-! ## ★★★★★ 課題 L85-c: 核は「閾値の 1 段ぶん」だった

`le1_zero_iff`（`Lcone.lean:36`、緑）は、根が行 0 で狭義最浅なら

    `le1 X 0 j`  ⟺  **根以外の**行 0 祖先がすべて `entry X 1 0` より上

と言う。一方 `coneV X w j` は**根を含む**祖先すべてが `w` より上。
⟹ 根を判定から外した錐 `coneVR` を入れると、両方が**同じ 1 つの族**になる:

    `mlift X w d`  = `mliftR X w d`（`w < v0` のとき）  … **`mlift_mem_W` で証明ずみ**
    `Lift1 X d`    = `mliftR X v0 d`                     … **これが欲しい**

**⟹ 核は「閾値を `v0 - 1` から `v0` へ 1 段上げてよいか」だけ。**
`Row1Mono` も `Row1DownLocal` も経由しない、いちばん鋭い形。 -/

/-- 根を閾値の判定から**外した**行 1 錐。 -/
def coneVR (X : TrioSeq) (w j : ℕ) : Prop :=
  ∀ y, Relation.ReflTransGen (nextrel0 X) y j → y ≠ 0 → w < entry X 1 y

theorem coneVR_zero (X : TrioSeq) (w : ℕ) : coneVR X w 0 := by
  intro y hy hy0
  have := nextrel0_rtrancl_index_le hy
  omega

/-- `w < 根の行 1` なら 2 つの錐は一致する。 -/
theorem coneV_iff_coneVR {X : TrioSeq} {w j : ℕ} (hw : w < entry X 1 0) :
    coneV X w j ↔ coneVR X w j := by
  constructor
  · intro h y hy _; exact h y hy
  · intro h y hy
    by_cases hy0 : y = 0
    · subst hy0; exact hw
    · exact h y hy hy0

open Classical in
/-- 根を外した閾値のマスクリフト。 -/
noncomputable def mliftR (X : TrioSeq) (w d : ℕ) : TrioSeq :=
  (List.range X.length).map fun j =>
    ((entry X 0 j, entry X 1 j + (if coneVR X w j then d else 0),
      entry X 2 j) : ℕ × ℕ × ℕ)

open Classical in
/-- **★★ `Lift1` は閾値 `v0` の `mliftR` そのもの。** -/
theorem Lift1_eq_mliftR {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l) (d : ℕ) :
    Lift1 X d = mliftR X (entry X 1 0) d := by
  unfold Lift1 mliftR
  refine List.map_congr_left ?_
  intro j hj
  rw [List.mem_range] at hj
  have hif : (if le1 X 0 j then d else 0)
      = (if coneVR X (entry X 1 0) j then d else 0) := by
    by_cases hc : le1 X 0 j
    · have hcv : coneVR X (entry X 1 0) j := (le1_zero_iff hr hj).mp hc
      rw [if_pos hc, if_pos hcv]
    · have hcv : ¬ coneVR X (entry X 1 0) j :=
        fun h => hc ((le1_zero_iff hr hj).mpr h)
      rw [if_neg hc, if_neg hcv]
  rw [hif]

open Classical in
/-- **`mlift` は閾値 `w < v0` の `mliftR`。** -/
theorem mlift_eq_mliftR {X : TrioSeq} {w : ℕ} (hw : w < entry X 1 0) (d : ℕ) :
    mlift X w d = mliftR X w d := by
  unfold mlift mliftR
  refine List.map_congr_left ?_
  intro j _
  have hif : (if coneV X w j then d else 0)
      = (if coneVR X w j then d else 0) := by
    by_cases hc : coneV X w j
    · rw [if_pos hc, if_pos ((coneV_iff_coneVR hw).mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((coneV_iff_coneVR hw).mpr h))]
  rw [hif]

/-- **証明ずみの範囲**: 閾値が根の行 1 より**真に下**なら `mliftR` は `W` を運ぶ。 -/
theorem mliftR_mem_W_of_lt {m w d : ℕ} {X : TrioSeq} (hw : w < entry X 1 0)
    (hX : X ∈ W m) : mliftR X w d ∈ W (m + 2 * d) := by
  rw [← mlift_eq_mliftR hw]
  exact mlift_mem_W X hX

/-- **★★★★★ 核の正確な形**: 上の `mliftR_mem_W_of_lt` を閾値 `w = entry X 1 0`
（＝ 1 段上）まで伸ばすこと。**それだけ。** -/
def MliftR : Prop :=
  ∀ (m w d : ℕ) (X : TrioSeq), X ∈ W m → mliftR X w d ∈ W (m + 2 * d)

/-- **⟹ `LiftTie` は `MliftR` から出る。** -/
theorem liftTie_of_mliftR (h : MliftR) : LiftTie := by
  intro m d v z R hargOK _ hX
  rw [Lift1_eq_mliftR (root_row0_min hargOK)]
  exact h m _ d _ hX

/-- **⟹ `(WL)` 全体も。**（`argOK` の根つき列に限る形で十分。） -/
theorem liftStage_cons_of_mliftR (h : MliftR) {m d v z : ℕ} {R : TrioSeq}
    (hargOK : argOK R) (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W m) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (m + 2 * d) := by
  rw [Lift1_eq_mliftR (root_row0_min hargOK)]
  exact h m _ d _ hX

/-- **⟹ `TowerOK` は `MliftR` ＋ `GraftFromExp` から出る。** -/
theorem towerOK_of_mliftR_graft (h : MliftR) (hg : GraftFromExp) : TowerOK :=
  towerOK_of_liftTie_graft (liftTie_of_mliftR h) hg


/-! ## ★★★★ 課題 L86-b: `w = v0` で壊れるのは**証明の 1 行ではなく、マスクの表現力**

`mlift_mem_W` の鎖はこうなっている:

    `mlift A v d = slift A (fun m => m + if v < m then d else 0)`   `Cgraft.lean:1033`
      └ 途中で **`coneV_iff_amin : coneV A v j ↔ v < amin A j`**    `Cgraft.lean:863`
    `slift_mem_W_tight (Stair φ) …`                                 `Wslift.lean:97`
      └ 支えは **`amin_oper_mir`（(A2)：コピー列は同じ `amin`）**   `Aexp.lean:224`

`amin A j = sInf {entry A 1 y | y は j の行 0 祖先}`（`Cgraft.lean:848`）で、
**根は（`rtg0_zero` により）すべての列の行 0 祖先**。⟹ `amin A j ≤ entry A 1 0` が
**常に成り立つ**。

**⟹ 閾値を `w = v0` にすると `coneV` は空になり、`mlift X v0 d = X` に潰れる。**
つまり「1 段伸ばす」は証明のどこかが壊れるのではなく、**`amin` マスクが
根を含むせいで `v0` より上の閾値を表現できない**。要るのは根を除いた `aminR`。 -/

/-- 根を除いた行 0 祖先の行 1 最小値。 -/
noncomputable def aminR (X : TrioSeq) (j : ℕ) : ℕ :=
  sInf {m | ∃ y, y ≠ 0 ∧ Relation.ReflTransGen (nextrel0 X) y j ∧ entry X 1 y = m}

theorem aminR_le {X : TrioSeq} {j y : ℕ} (hy0 : y ≠ 0)
    (h : Relation.ReflTransGen (nextrel0 X) y j) : aminR X j ≤ entry X 1 y :=
  Nat.sInf_le ⟨y, hy0, h, rfl⟩

theorem aminR_mem {X : TrioSeq} {j : ℕ} (hj : j ≠ 0) :
    ∃ y, y ≠ 0 ∧ Relation.ReflTransGen (nextrel0 X) y j ∧ entry X 1 y = aminR X j := by
  have hne : {m | ∃ y, y ≠ 0 ∧ Relation.ReflTransGen (nextrel0 X) y j
      ∧ entry X 1 y = m}.Nonempty :=
    ⟨entry X 1 j, j, hj, Relation.ReflTransGen.refl, rfl⟩
  exact Nat.sInf_mem hne

/-- **`coneVR` は `aminR` の閾値条件**（`coneV_iff_amin` の根を外した版）。 -/
theorem coneVR_iff_aminR {X : TrioSeq} {w j : ℕ} (hj : j ≠ 0) :
    coneVR X w j ↔ w < aminR X j := by
  constructor
  · intro h
    obtain ⟨y, hy0, hy, hval⟩ := aminR_mem (X := X) hj
    rw [← hval]; exact h y hy hy0
  · intro h y hy hy0
    exact lt_of_lt_of_le h (aminR_le hy0 hy)

theorem amin_le_aminR {X : TrioSeq} {j : ℕ} (hj : j ≠ 0) : amin X j ≤ aminR X j := by
  obtain ⟨y, -, hy, hval⟩ := aminR_mem (X := X) hj
  rw [← hval]; exact amin_le hy

/-- **★ `amin` は根で頭打ち**（根はすべての列の行 0 祖先）。 -/
theorem amin_le_root {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {j : ℕ} (hj : j < X.length) : amin X j ≤ entry X 1 0 :=
  amin_le (rtg0_zero hr hj)

/-- **★★ 壊れる箇所そのもの**: 閾値を `v0` にすると `coneV` は空になる。 -/
theorem coneV_root_vacuous {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {j : ℕ} (hj : j < X.length) : ¬ coneV X (entry X 1 0) j := by
  intro h
  have h1 := coneV_iff_amin.mp h
  have h2 := amin_le_root hr hj
  omega

/-- ⟹ **素朴な「1 段上げ」は潰れる**: `mlift X v0 d` は `X` そのもの。 -/
theorem mlift_root_eq_self {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l) (d : ℕ) :
    mlift X (entry X 1 0) d = X := by
  classical
  refine List.ext_getElem (by rw [mlift_length]) ?_
  intro i hi1 hi2
  rw [mlift_length] at hi1
  rw [← entry_triple (X := mlift X (entry X 1 0) d) (by rw [mlift_length]; omega),
    ← entry_triple (X := X) hi1]
  rw [entry0_mlift, entry2_mlift, entry1_mlift hi1,
    if_neg (coneV_root_vacuous hr hi1), Nat.add_zero]

/-- **`amin` は根の値と `aminR` の小さいほう。**「根で頭打ち」の正確な形。 -/
theorem amin_eq_min_root {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {j : ℕ} (hj0 : j ≠ 0) (hj : j < X.length) :
    amin X j = min (entry X 1 0) (aminR X j) := by
  refine le_antisymm (le_min (amin_le_root hr hj) (amin_le_aminR hj0)) ?_
  obtain ⟨y, hy, hval⟩ := amin_mem X j
  rw [← hval]
  by_cases hy0 : y = 0
  · subst hy0; exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (aminR_le hy0 hy)

/-- **★★★ 伸ばすために要る 1 本**: `amin_oper_mir`（(A2)）の `aminR` 版。
これが出れば `slift` の機械がそのまま `aminR` で回り、`MliftR` が出る。 -/
def AminROper : Prop :=
  ∀ (M : TrioSeq) (n j0 Lb k q : ℕ),
    j0 + Lb + 1 = M.length → 0 < Lb → 0 < n →
    ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) →
    hasParent M (srow M (M.length - 1)) (M.length - 1) →
    parent M (srow M (M.length - 1)) (M.length - 1) = j0 →
    k < n → q < Lb →
    aminR (M⟦n⟧) (j0 + (k * Lb + q)) = aminR M (j0 + q)


/-! ## ★★★★ 課題 L87-a/b: `W_add` は**根と両立しない**（否定的、Lean で確認）

`rsum A P := ∀ p ∈ A ++ P, entry P 0 0 ≤ p.1`（`Wset.lean:1317`）は
「`P` は `A ++ P` の**本当の最上位接尾辞**」という意味。ところが `Wstar` は
根 `(0,v,z)` を **深さ 0** に cons する。⟹ 根の `p.1 = 0` が `entry P 0 0 ≤ 0` を強制し、
`argOK P`（全列の深さ `> 0`）と**両立しない**。

**⟹ `A ++ B ∈ Wstar` を `W_add` で作る道は、`B ≠ []` では閉じている。**
（R1 の実測「`split_lastMin` は `A = []` が 6131/6131」はこれの計測版。）

さらに `WstarCat` を仮定しても `GraftFromExp` は出ない: `graft R y` の連結の
`rsum` は **`d ≤ R.dropLast の全深さ`** を要求し、これは R1 の実測で
**19455/20345 (95.6%) で破れる**（`rsum_graft_iff` が要求そのもの）。 -/

/-- **★★ 根は `rsum` を壊す。** -/
theorem not_rsum_cons_root {v z : ℕ} {A B : TrioSeq} (hB : argOK B) (hBne : B ≠ []) :
    ¬ rsum (((0, v, z) : ℕ × ℕ × ℕ) :: A) B := by
  intro h
  have hroot : ((0, v, z) : ℕ × ℕ × ℕ)
      ∈ (((0, v, z) : ℕ × ℕ × ℕ) :: A) ++ B := by simp
  have h1 := h _ hroot
  cases B with
  | nil => exact hBne rfl
  | cons q t =>
      have hq : 0 < q.1 := hB q (by simp)
      have hE : entry (q :: t) 0 0 = q.1 := by simp [entry]
      rw [hE] at h1
      simp only at h1
      omega

/-- **★★ `graft` の連結が `rsum` になる条件**（R1 が測ったもの、そのもの）。 -/
theorem rsum_graft_iff {R y : TrioSeq} (hb : based y) (hyne : y ≠ []) :
    rsum R.dropLast (y.map fun p =>
        ((p.1 + entry R 0 (R.length - 1), p.2.1, p.2.2) : ℕ × ℕ × ℕ))
      ↔ ∀ p ∈ R.dropLast, entry R 0 (R.length - 1) ≤ p.1 := by
  set d := entry R 0 (R.length - 1) with hd
  set B := y.map fun p => ((p.1 + d, p.2.1, p.2.2) : ℕ × ℕ × ℕ) with hBdef
  have hB0 : entry B 0 0 = d := by
    cases y with
    | nil => exact absurd rfl hyne
    | cons q t =>
        have hq : entry (q :: t) 0 0 = q.1 := by simp [entry]
        rw [hb] at hq
        simp only [hBdef, List.map_cons]
        show q.1 + d = d
        omega
  constructor
  · intro h p hp
    have := h p (List.mem_append_left _ hp)
    rw [hB0] at this
    exact this
  · intro h p hp
    rw [hB0]
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      simp only
      omega

/-- **`Wstar` の連結**（team-lead の L87-a の形）。上の 2 本より、
`W_add` からは出ず、`GraftFromExp` にも直に効かない。 -/
def WstarCat : Prop :=
  ∀ (A B : TrioSeq), A ∈ Wstar → B ∈ Wstar → rsum A B → A ++ B ∈ Wstar

/-- 空の側は自明（`WstarCat` が空虚でないことの確認）。 -/
theorem wstarCat_nil (A : TrioSeq) (hA : A ∈ Wstar) :
    A ++ ([] : TrioSeq) ∈ Wstar := by
  rw [List.append_nil]; exact hA


/-! ## ⛔ 課題 L88 の判定: **`AminROper` は偽**。破れる場所は `j0 = 0` ＝ 塔そのもの

計測 `tools/probe_aminr_oper.py`（母数 64800 列、`n = 1,2,3`、`j0` で分割）:

    **陽性対照 `amin`（＝ `amin_oper_mir`、証明ずみ）… 破れ 0 件**   ← 計器は健全
    **`j0 > 0`  … `aminR` 不変 159348 / 159348 (100%)**
    **`j0 = 0`  … `aminR` 破れ  58587 / 232890 (25.2%)**            ⛔

（`j = 0` の列は `aminR` が空集合の `sInf` になるので母数から除いた。
`coneVR_iff_aminR` が `j ≠ 0` を要求するのと同じ理由。）

**最小の反例**（3 列、`n = 2`）:

    `M = [(0,0,0), (1,1,0), (1,0,0)]`,  `j0 = 0`, `Lb = 2`, `k = 1`, `q = 1`
    `aminR M 1 = 1`     （添字 1 の根以外の行 0 祖先は自分だけ、行 1 = 1）
    `aminR (M⟦2⟧) 3 = 0` （**コピー 1 の根の写し（添字 2）は添字 0 ではない**ので数に入る）

**⟹ 理由は構造的**: `j0 = 0` だと `take j0 = []` なので**すべてのコピーが根の写しを持つ**。
`aminR` は「添字 0 だけ」を除くので、コピー `k ≥ 1` の根の写しは除かれない。
`Wtower2.lean:41-56` の「**添字で決まる錐はコピーで壊れる（コピー `k` は自分自身の
錐を持つ）**」（計測 192996 例中 47718 例で不可換）を、`aminR` の側から見た同じ事実。

**⟹ `slift` の機械を `aminR` に移す道は閉じている。**しかも破れるのは `j0 = 0`
＝ **塔の場面そのもの**（`parent_is_root_of_domT` により塔では常に `j0 = 0`）。

⚠ ただし `MliftR` 自体が偽とは言っていない。`MliftR` は `W` **所属の輸送**であって
可換性ではない（`ulift_mem_W` が `Stair.zero` 無しで通ったのと同じ構図）。
閉じたのは「`slift`/`amin` の証明をそのまま移植する」道だけ。 -/


/-! ## ★★★★ 課題 L90-b: `WstarSnoc` は `Wself` の `snoc` そのもの

`Wself M := M ∈ W (lev M 0)`（`Wtower2.lean:2988`）で、根つき列なら
`lev ((0,v,z) :: R) 0 = 2v + z` なので

    **`Wstar R`  ⟺  `argOK R → ∀ v z, z ≤ 1 → ((0,v,z) :: R) ∈ Wself`**

（前向きは `a := 2v+z`、後ろ向きは `W_mono`。）
⟹ `Wstar R.dropLast → Wstar R` は `((0,v,z) :: R.dropLast) ++ [末尾列]` の形になり、
**既存の `snoc_orphan` / `snoc_step` がそのまま当たる**。 -/

theorem lev_cons_root (v z : ℕ) (R : TrioSeq) :
    lev (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 = 2 * v + z := by
  simp [lev, entry]

/-- **★★ `Wstar` は根つき `Wself` の言い換え。** -/
theorem Wstar_iff_Wself {R : TrioSeq} :
    R ∈ Wstar ↔ (argOK R → ∀ v z : ℕ, z ≤ 1 →
      (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself) := by
  constructor
  · intro h harg v z hz
    show (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (lev (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0)
    rw [lev_cons_root]
    exact h harg v z (2 * v + z) hz le_rfl
  · intro h harg v z a hz hva
    have h1 := h harg v z hz
    show (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W a
    have h2 : (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        ∈ W (lev (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0) := h1
    rw [lev_cons_root] at h2
    exact W_mono hva h2

/-- **末尾列を 1 本足し戻す**（課題 L90-b）。 -/
def WstarSnoc : Prop :=
  ∀ (R : TrioSeq), R ≠ [] → argOK R → R.dropLast ∈ Wstar → R ∈ Wstar

/-- 根つき列を末尾で分ける。 -/
theorem cons_dropLast_getLast {v z : ℕ} {R : TrioSeq} (hRne : R ≠ []) :
    ((((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ++ [R.getLast hRne])
      = ((0, v, z) : ℕ × ℕ × ℕ) :: R := by
  rw [List.cons_append, List.dropLast_append_getLast hRne]

/-- **★★★ 孤児の側は無料**（`snoc_orphan`）。 -/
theorem wstarSnoc_orphan {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : R.dropLast ∈ Wstar) (harg : argOK R) (hz : z ≤ 1)
    (hnp : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1)) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself := by
  have hargd : argOK R.dropLast := argOK_dropLast harg
  have hA : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ Wself :=
    Wstar_iff_Wself.mp hd hargd v z hz
  have hEq := cons_dropLast_getLast (v := v) (z := z) hRne
  have h := snoc_orphan hA (by simp) (R.getLast hRne) (by rw [hEq]; exact hnp)
  rwa [hEq] at h

/-- **★★★★ `WstarSnoc` は `WSnoc` から出る。**（親ありの側だけが開いている。） -/
theorem wstarSnoc_of_wsnoc (hsn : WSnoc) : WstarSnoc := by
  intro R hRne harg hd
  refine Wstar_iff_Wself.mpr (fun _ v z hz => ?_)
  have hargd : argOK R.dropLast := argOK_dropLast harg
  have hA : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ Wself :=
    Wstar_iff_Wself.mp hd hargd v z hz
  have hlev : lev (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 = 2 * v + z :=
    lev_cons_root v z _
  have hA' : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ W (2 * v + z) := by
    rw [← hlev]; exact hA
  have h := snoc_step hsn (u := 2 * v + z) (R.getLast hRne) hA' (by simp)
  rw [cons_dropLast_getLast hRne] at h
  show (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (lev (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0)
  rw [lev_cons_root]
  exact h

/-- 行 2 が全部 `0` の側も無料（`snoc_zeroRow2`）。 -/
theorem wstarSnoc_zeroRow2 {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz2 : ∀ p ∈ (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast), p.2.2 = 0) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself := by
  have hEq := cons_dropLast_getLast (v := v) (z := z) hRne
  have h := snoc_zeroRow2 hz2 (R.getLast hRne)
  rwa [hEq] at h


/-! ## ★★★★ 課題 L90-a: `graft` は残核 `Subst1gRevive` の場面そのもの

R1 の実測（R76、母数 20344、全部 100%）どおり、側条件は**構成から出る**:

    `S := (0,v,z) :: R`、`p := |R|`、`C := shiftr01 d 0 y`（`d := entry R 0 (|R|-1)`）
    ⟹ `S.take p ++ C ++ S.drop (p+1) = (0,v,z) :: graft R y`

    `entry C 0 0 = entry S 0 p`     ← `based y` と `d` ずらしから直に
    `∀ q ∈ C, entry S 0 p ≤ q.1`    ← 同上
    `C ∈ W (lev S p)`               ← `y ∈ W m` ＋ `W_shift` ＋ `domT` で `lev S p = m+1`

**⟹ `rsum` は 95.6% で破れるのに残核は当たる**（課題 L87 の裏返し）。
残核は「`C` の根が `A` の全列以下」ではなく「**宿主の列の深さと一致**」を要求する。 -/

open Classical in
/-- **★★★★ 残核 `Subst1gRevive` を `graft` に当てる**（課題 L90-a）。 -/
theorem graft_cons_mem_of_revive (hrev : Subst1gRevive) {v z m : ℕ} {R y : TrioSeq}
    (hRne : R ≠ []) (hd : domT R m) (hWR : R ∈ Wstar) (hR : argOK R)
    (hz : z ≤ 1) (hy : y ∈ W m) (hb : based y) (hyne : y ≠ [])
    (hpar : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft R y)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: graft R y)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: graft R y).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: graft R y).length - 1))
    (horph : ¬ hasParent (shiftr01 (entry R 0 (R.length - 1)) 0 y)
      (srow (shiftr01 (entry R 0 (R.length - 1)) 0 y)
        ((shiftr01 (entry R 0 (R.length - 1)) 0 y).length - 1))
      ((shiftr01 (entry R 0 (R.length - 1)) 0 y).length - 1)) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: graft R y) ∈ W (2 * v + z) := by
  have hRpos : 0 < R.length := List.length_pos_iff.mpr hRne
  set d : ℕ := entry R 0 (R.length - 1) with hddef
  set S : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: R with hSdef
  set C : TrioSeq := shiftr01 d 0 y with hCdef
  have hSlen : S.length = R.length + 1 := by rw [hSdef]; simp
  have hp : R.length < S.length := by omega
  have hSW : S ∈ W (2 * v + z) := hWR hR v z (2 * v + z) hz le_rfl
  have htake : S.take R.length = ((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast := by
    obtain ⟨k, hk⟩ : ∃ k, R.length = k + 1 := ⟨R.length - 1, by omega⟩
    rw [hSdef, hk, List.take_succ_cons, List.dropLast_eq_take, hk]
    simp
  have hdrop : S.drop (R.length + 1) = [] := by
    rw [hSdef, List.drop_succ_cons]
    exact List.drop_eq_nil_of_le le_rfl
  have hres : S.take R.length ++ C ++ S.drop (R.length + 1)
      = ((0, v, z) : ℕ × ℕ × ℕ) :: graft R y := by
    rw [htake, hdrop, List.append_nil, List.cons_append]
    congr 1
  have hCne : C ≠ [] := by
    rw [hCdef, shiftr01]
    exact fun h => hyne (List.map_eq_nil_iff.mp h)
  have hlevSp : lev S R.length = m + 1 := by
    have h1 : entry S 1 R.length = entry R 1 (R.length - 1) := entry_cons_last hRne 1
    have h2 : entry S 2 R.length = entry R 2 (R.length - 1) := entry_cons_last hRne 2
    unfold lev
    rw [h1, h2]
    exact hd.1
  have hCW : C ∈ W (lev S R.length) := by
    rw [hlevSp]
    exact W_mono (by omega) (W_shift hy d)
  have hSp0 : entry S 0 R.length = d := entry_cons_last hRne 0
  have hC0 : entry C 0 0 = entry S 0 R.length := by
    rw [hSp0, hCdef]
    cases y with
    | nil => exact absurd rfl hyne
    | cons q t =>
        have hq : entry (q :: t) 0 0 = q.1 := by simp [entry]
        rw [hb] at hq
        simp only [shiftr01, List.map_cons]
        show q.1 + d = d
        omega
  have hCge : ∀ q ∈ C, entry S 0 R.length ≤ q.1 := by
    intro q hq
    rw [hSp0]
    rw [hCdef, shiftr01, List.mem_map] at hq
    obtain ⟨q', -, rfl⟩ := hq
    simp only
    omega
  have hmain := hrev (2 * v + z) R.length S C hSW hp hCne hCW hC0 hCge
    (by rw [hres]; exact hpar) (Or.inl ⟨hdrop, horph⟩)
  rwa [hres] at hmain


/-! ## ★★★★★ 課題 L91: 持ち上げ核は **`d = 1`** に落ちる

### L91-a の答え: `ulift_mem_W` の型の帰納は**節 2 で同じ壁**に当たる

`ulift_mem_W`（`Wslift.lean:461`）は `A2'` で 3 節を追うが、節 2 と節 3 はどちらも
`ulift_step`（`Wslift.lean` 内）に落ち、そこは
`(shiftr01 0 d X)⟦n⟧` を `shiftr01 0 d (X⟦n⟧)` に直す —— **一様シフトの可換性**を使う。
`mliftR` 版はそこで課題 L88 の非可換性（`j0 = 0` で 25.2% 破れ）に当たる。

    節 1（底、`|X| ≤ 1`）  … `Lift1` でも同じに通る（列が 1 本なら錐は自明）
    **節 2（展開）        … ⛔ 可換性が要る。ここが壁**
    節 3（graft）          … `aop_clause3_to_clause2` で節 2 に落ちるので同じ壁

### ★★ L91-b の副産物: **`d` は 1 に落とせる**

`Wset.Lift1_Lift1 : Lift1 (Lift1 X t) s = Lift1 X (t + s)`（**既存・無条件**）は
「錐は持ち上げで不変」を言っている。⟹ **`d` の帰納で単位持ち上げに還元できる。**
サンドイッチ（`Le1_Lift1_oper` / `Le1_oper_Lift1_shiftr01`）の**窓の幅も 1 になる**ので、
`WConvex` に要るのは「行 1 が高々 1 しか違わない上下の witness」の場合だけ。 -/

/-- **単位持ち上げ**だけの (WL)。 -/
def LiftStage1 : Prop :=
  ∀ (m : ℕ) (X : TrioSeq), X ∈ W m → Lift1 X 1 ∈ W (m + 2)

/-- **★★★★★ (WL) は単位持ち上げに還元される。** -/
theorem liftStage_of_unit (h : LiftStage1) : LiftStage := by
  intro m d X hX
  induction d with
  | zero => simpa using hX
  | succ k ih =>
      have h1 := h (m + 2 * k) (Lift1 X k) ih
      rw [Lift1_Lift1] at h1
      have he : m + 2 * k + 2 = m + 2 * (k + 1) := by omega
      rw [he] at h1
      exact h1

/-- 逆も自明なので**同値**。 -/
theorem liftStage1_of_liftStage (h : LiftStage) : LiftStage1 :=
  fun m X hX => by simpa using h m 1 X hX

theorem liftStage_iff_unit : LiftStage ↔ LiftStage1 :=
  ⟨liftStage1_of_liftStage, liftStage_of_unit⟩

/-- ⟹ **核も `d = 1` だけになる。** -/
theorem liftTie_of_unit (h : LiftStage1) : LiftTie :=
  liftTie_of_liftStage (liftStage_of_unit h)

theorem towerOK_of_unit_graft (h : LiftStage1) (hg : GraftFromExp) : TowerOK :=
  towerOK_of_liftTie_graft (liftTie_of_unit h) hg

/-- **サンドイッチの窓は `d = 1` では幅 1**: 上端と下端は行 1 で高々 `1` しか違わない。 -/
theorem sandwich_window_one (Y : TrioSeq) (j : ℕ) :
    entry (shiftr01 0 1 Y) 1 j ≤ entry (Lift1 Y 1) 1 j + 1 := by
  classical
  rcases Nat.lt_or_ge j Y.length with hj | hj
  · rw [entry1_shiftr1 hj, entry1_Lift1 hj]
    split <;> omega
  · rw [entry1_out (by rw [shiftr01_length]; omega),
      entry1_out (by rw [Lift1_length]; omega)]
    omega

/-- 幅 1 の窓しか要らない凸性。`WConvex` より真に短い文。 -/
def WConvex1 : Prop :=
  ∀ (a : ℕ) (A B C : TrioSeq), A ∈ W a → C ∈ W a → Le1 A B → Le1 B C →
    (∀ j, entry C 1 j ≤ entry A 1 j + 1) → B ∈ W a

theorem wconvex1_of_wconvex (h : WConvex) : WConvex1 :=
  fun a A B C hA hC hAB hBC _ => h a A B C hA hC hAB hBC


/-! ## ★★★★★ 課題 L92-b: **`WConvex1`（幅 1 の窓）だけで `(WL)` が出る**

`liftStage_of_wconvex`（`Wtower2.lean`）を読むと、`WConvex` を使うのは
`lift1_mem_of_wconvex` の**ただ 1 か所**:

    `hconv (m+2d) (Lift1 (Y⟦n⟧) d) ((Lift1 Y d)⟦n⟧) (shiftr01 0 d (Y⟦n⟧))`
      下端 = 帰納法の仮定 ／ 上端 = `(ULIFT)` ／ 真ん中 = 欲しいもの

課題 L91 で `d = 1` に落ちたので、その 1 か所の**窓の幅は 1**（`sandwich_window_one`）。
⟹ **`WConvex1` で足りる。** -/

theorem lift1_mem_of_wconvex1 (hconv : WConvex1) {m : ℕ} {Y : TrioSeq}
    (hop : ∀ n, 1 ≤ n → Y⟦n⟧ ∈ W m ∧ Lift1 (Y⟦n⟧) 1 ∈ W (m + 2 * 1)) :
    Lift1 Y 1 ∈ W (m + 2 * 1) :=
  mem_of_oper_mem (fun n hn =>
    hconv (m + 2 * 1) (Lift1 (Y⟦n⟧) 1) ((Lift1 Y 1)⟦n⟧) (shiftr01 0 1 (Y⟦n⟧))
      (hop n hn).2 (ulift_mem_W (Y⟦n⟧) (hop n hn).1)
      (Le1_Lift1_oper Y 1 n) (Le1_oper_Lift1_shiftr01 Y 1 n)
      (fun j => sandwich_window_one (Y⟦n⟧) j))

/-- **★★★★★ 幅 1 の凸性だけで単位持ち上げが通る。** -/
theorem liftStage1_of_wconvex1 (hconv : WConvex1) : LiftStage1 := by
  intro m X hX
  have hsub : W m ⊆ {Y : TrioSeq | Y ∈ W m ∧ Lift1 Y 1 ∈ W (m + 2 * 1)} := by
    refine A2' ?_
    rintro Y (⟨hl, hlev⟩ | hop | ⟨m', hm', hd', hgr⟩)
    · refine ⟨A1_intro (Or.inl ⟨hl, hlev⟩), ?_⟩
      rcases Nat.eq_zero_or_pos Y.length with h0 | hpos
      · have hnil : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show Lift1 ([] : TrioSeq) 1 ∈ W (m + 2 * 1)
        simpa using W_nil (m + 2 * 1)
      · have h1 : Y.length = 1 := by omega
        have hbc : 2 * entry Y 1 0 + entry Y 2 0 = 0 := by
          unfold lev at hlev; omega
        exact lift1_singleton_mem h1 (by omega)
    · exact ⟨mem_of_oper_mem (fun n hn => (hop n hn).1),
        lift1_mem_of_wconvex1 hconv (fun n hn => hop n hn)⟩
    · have hY : Y ∈ W m :=
        A1_intro (Or.inr (Or.inr ⟨m', hm', hd', fun z hz hb => (hgr z hz hb).1⟩))
      refine ⟨hY, ?_⟩
      rcases Nat.lt_or_ge Y.length 2 with hsm | hbig
      · have hYne : Y ≠ [] := by
          intro hc
          rw [hc] at hd'
          exact not_domT_nil m' hd'
        have h1 : Y.length = 1 := by
          have : 0 < Y.length := List.length_pos_iff.mpr hYne
          omega
        have hlev := hd'.1
        rw [show Y.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        exact lift1_singleton_mem h1 (by omega)
      · exact lift1_mem_of_wconvex1 hconv (aop_clause3_to_clause2 hbig hd' hgr)
  have h := (hsub hX).2
  have he : m + 2 * 1 = m + 2 := by omega
  rwa [he] at h

/-- **★★★★★ ⟹ `(WL)` は幅 1 の凸性 1 本から出る**（既存の
`liftStage_of_wconvex'` は幅の制限が無い `WConvex` を要求していた）。 -/
theorem liftStage_of_wconvex1 (hconv : WConvex1) : LiftStage :=
  liftStage_of_unit (liftStage1_of_wconvex1 hconv)

theorem liftTie_of_wconvex1 (hconv : WConvex1) : LiftTie :=
  liftTie_of_liftStage (liftStage_of_wconvex1 hconv)

/-- **★★★★★ 核ちょうど 2 本の最終形**: 幅 1 の凸性 ＋ 節 2 の代入。 -/
theorem towerOK_of_wconvex1_graft (hconv : WConvex1) (hg : GraftFromExp) :
    TowerOK :=
  towerOK_of_liftTie_graft (liftTie_of_wconvex1 hconv) hg


/-! ## ★★★★ 課題 L93-b: **1 列 1 段の引き下げは `Subst1gRevive` から出る**

`Subst1gRevive` の差し替えブロック `C` を**1 列**にすると、「その列の行 1 を
1 だけ下げる」になる。側条件は次のとおり:

    `C = [c] ≠ []`                    自動
    `C ∈ W (lev S p)`                 自動（`singleton_mem_W`、下げるので `lev` は減る）
    `entry C 0 0 = entry S 0 p`       自動（深さは変えない）
    `∀ q ∈ C, entry S 0 p ≤ q.1`      自動
    **`hasParent (結果) …`**           ← 残る（「復活」の場合であること）
    **選言（尾が孤児終わり）**          ← `p = |S|-1` なら**自動**（1 列に親は無い）

**⟹ 末尾列なら側条件は「下げたあとも親が居る」1 本だけ。**
しかも**下端の witness は要らない**ので、`WConvexUnit` より強い形が出る。

⚠ `WSnoc` は列を**足す**だけで既存の列を変えないので、こちらには効かない。 -/

theorem not_hasParent_zero (M : TrioSeq) (i : ℕ) : ¬ hasParent M i 0 := by
  rintro ⟨j0, hj0, -⟩
  have := nextR_index_lt hj0
  omega

/-- 1 列だけ行 1 を 1 下げた列（`Subst1gRevive` の差し替えの形）。 -/
def lowerOne (S : TrioSeq) (p : ℕ) : TrioSeq :=
  S.take p ++ [((entry S 0 p, entry S 1 p - 1, entry S 2 p) : ℕ × ℕ × ℕ)]
    ++ S.drop (p + 1)

/-- **★★★ 1 列 1 段の引き下げ**（一般の位置、側条件 2 本）。 -/
theorem lowerOne_of_revive (hrev : Subst1gRevive) {u p : ℕ} {S : TrioSeq}
    (hS : S ∈ W u) (hp : p < S.length)
    (hpar : hasParent (lowerOne S p)
      (srow (lowerOne S p) ((lowerOne S p).length - 1))
      ((lowerOne S p).length - 1))
    (hdisj : S.drop (p + 1) = [] ∨
      (S.drop (p + 1) ≠ [] ∧
        ¬ hasParent (S.drop (p + 1))
          (srow (S.drop (p + 1)) ((S.drop (p + 1)).length - 1))
          ((S.drop (p + 1)).length - 1))) :
    lowerOne S p ∈ W u := by
  classical
  set c : ℕ × ℕ × ℕ := (entry S 0 p, entry S 1 p - 1, entry S 2 p) with hc
  have hCne : ([c] : TrioSeq) ≠ [] := by simp
  have hCW : ([c] : TrioSeq) ∈ W (lev S p) := by
    have : lev S p = 2 * entry S 1 p + entry S 2 p := rfl
    exact singleton_mem_W (by rw [this]; omega)
  have hC0 : entry ([c] : TrioSeq) 0 0 = entry S 0 p := by simp [entry, hc]
  have hCge : ∀ q ∈ ([c] : TrioSeq), entry S 0 p ≤ q.1 := by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    simp [hc]
  have hdisj' : ((S.drop (p + 1) = [] ∧
      ¬ hasParent ([c] : TrioSeq) (srow ([c] : TrioSeq) (([c] : TrioSeq).length - 1))
        (([c] : TrioSeq).length - 1)) ∨
      (S.drop (p + 1) ≠ [] ∧
        ¬ hasParent (S.drop (p + 1))
          (srow (S.drop (p + 1)) ((S.drop (p + 1)).length - 1))
          ((S.drop (p + 1)).length - 1))) := by
    rcases hdisj with h | h
    · exact Or.inl ⟨h, by simpa using not_hasParent_zero ([c] : TrioSeq) _⟩
    · exact Or.inr h
  exact hrev u p S [c] hS hp hCne hCW hC0 hCge hpar hdisj'

/-- **★★★★ 末尾列なら側条件は 1 本だけ**（選言が自動で消える）。
しかも**下端の witness を使わない** ⟹ `WConvexUnit` より強い。 -/
theorem lowerLast_of_revive (hrev : Subst1gRevive) {u : ℕ} {S : TrioSeq}
    (hSne : S ≠ []) (hS : S ∈ W u)
    (hpar : hasParent (lowerOne S (S.length - 1))
      (srow (lowerOne S (S.length - 1)) ((lowerOne S (S.length - 1)).length - 1))
      ((lowerOne S (S.length - 1)).length - 1)) :
    lowerOne S (S.length - 1) ∈ W u := by
  have hSpos : 0 < S.length := List.length_pos_iff.mpr hSne
  refine lowerOne_of_revive hrev hS (by omega) hpar (Or.inl ?_)
  exact List.drop_eq_nil_of_le (by omega)

/-- 末尾で下げた形は `dropLast ++ [下げた列]`。 -/
theorem lowerOne_last_eq {S : TrioSeq} (hSne : S ≠ []) :
    lowerOne S (S.length - 1)
      = S.dropLast ++ [((entry S 0 (S.length - 1), entry S 1 (S.length - 1) - 1,
          entry S 2 (S.length - 1)) : ℕ × ℕ × ℕ)] := by
  have hSpos : 0 < S.length := List.length_pos_iff.mpr hSne
  unfold lowerOne
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil,
    List.dropLast_eq_take]


/-! ## ★★★★★ 課題 L94 の判定: **`WConvex1` は 3 本目ではない。`WSnoc` から出る**

team-lead の読みが当たっていた。`Wtower2.lean` に鎖が**すべて緑で**ある:

    `WSnoc`             `Wtower2.lean:2049`
      ─ `wcat_of_snoc`               `Wtower2.lean:2078`
    `WCat`
      ─ `shiftTowerClosed_of_cat`    `Wtower2.lean:1983`
    `ShiftTowerClosed`
      ─ `shiftTowerClosedS_of_closed` `Wtower2.lean:1776`
    `ShiftTowerClosedS`
      ─ `liftStageParented_of_tower`  `Wtower2.lean:1835`
    `LiftStageParented`
      ─ `liftStage_of_parented`       `Wtower2.lean:560`
    **`LiftStage`**

⟹ **`WSnoc` だけで `(WL)` が出る。** `WConvex1` は「`LiftStage` に至る別経路」であって、
独立した 3 本目ではない（`LiftStage` が目的なら要らない）。

**⟹ 今日の核は `Subst1gRevive` ＋ `WSnoc` の 2 本に収束する。** -/

/-- **★★★★★ `WSnoc` だけで `(WL)`。** -/
theorem liftStage_of_wsnoc (hsn : WSnoc) : LiftStage :=
  liftStage_of_parented
    (liftStageParented_of_tower
      (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat (wcat_of_snoc hsn))))

theorem liftTie_of_wsnoc (hsn : WSnoc) : LiftTie :=
  liftTie_of_liftStage (liftStage_of_wsnoc hsn)

/-- **★★★★★ 今日の最終形**: `TowerOK` は `WSnoc` ＋ `GraftFromExp` から出る。 -/
theorem towerOK_of_wsnoc_graft (hsn : WSnoc) (hg : GraftFromExp) : TowerOK :=
  towerOK_of_liftTie_graft (liftTie_of_wsnoc hsn) hg

/-! ## ★ 今日の到達点: 未証明は 2 本（`STATUS.md` 用の正確な文）

### 1. `Wset.WSnoc`（`Wtower2.lean:2049`）

```lean
def WSnoc : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ∈ W u → C ≠ [] →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length → C ++ [p] ∈ W u
```

**効く先 2 つ**: 持ち上げ側（上の鎖で `LiftStage`）と、
`WstarSnoc`（`wstarSnoc_of_wsnoc`、この file）＝ `GraftFromExp` の 1 段。

### 2. `Wtower2.Subst1gRevive`（`Wtower2.lean:3251
3274`）

1 列（`p` 番目）を `Wself` のブロック `C` に差し替えても段は上がらない、という形。
`graft` の場面では側条件が構成から出る（`graft_cons_mem_of_revive`、この file）。

### 参考: 今日作って**要らなくなった**もの

    `Row1DownLocal` / `Row1DownRoot0`  … `MliftR` に畳まれた（課題 L85）
    `MliftR`                            … `slift` 移植が閉じた（課題 L88）
    `WConvex1`                          … `WSnoc` から `LiftStage` が出る（課題 L94）
    `WstarCat`                          … `rsum` が根と両立しない（課題 L87）

⚠ どれも「偽」ではなく「**要らない**」。`WConvex1` は `Row1Mono` より 2 段弱い
命題として正しく、独立に証明できれば別経路になる。 -/


/-! ## ★★★★ 課題 L95-a: **複数列は反復で回る**（`W` の側では）

⚠ まず: 課題 L94 で `WSnoc ⟹ LiftStage` が出たので、**本線では `WConvex1` は要らない**。
以下は「`WSnoc` が難しかったときの保険経路」を閉じるための判定。

差が `k` 本でも、**1 本ずつ下げる中間列**を作って `k` 回まわせる。下端の witness `A`
は使い回せる（`Le1_trans`）。⟹ **`WConvexUnit ⟹ WConvex1`。**

⚠ ただし `lowerOne_of_revive`（課題 L93-b）の側条件「下げたあとも親が居る」は
**各段で立つ必要がある**。そこは反復では自動にならない。 -/

/-- 1 列だけ行 1 を 1 下げた列（`W` 側の中間列）。 -/
def lowerAt (C : TrioSeq) (j0 : ℕ) : TrioSeq :=
  (List.range C.length).map fun j =>
    ((entry C 0 j, entry C 1 j - (if j = j0 then 1 else 0),
      entry C 2 j) : ℕ × ℕ × ℕ)

@[simp] theorem lowerAt_length (C : TrioSeq) (j0 : ℕ) :
    (lowerAt C j0).length = C.length := by simp [lowerAt]

theorem lowerAt_getD {C : TrioSeq} {j0 i : ℕ} (hi : i < C.length) :
    (lowerAt C j0).getD i (0, 0, 0)
      = ((entry C 0 i, entry C 1 i - (if i = j0 then 1 else 0),
          entry C 2 i) : ℕ × ℕ × ℕ) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [lowerAt_length]; exact hi)]
  unfold lowerAt
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem entry0_lowerAt (C : TrioSeq) (j0 i : ℕ) :
    entry (lowerAt C j0) 0 i = entry C 0 i := by
  rcases Nat.lt_or_ge i C.length with hi | hi
  · show ((lowerAt C j0).getD i (0, 0, 0)).1 = _
    rw [lowerAt_getD hi]
  · rw [entry_out (by rw [lowerAt_length]; omega), entry_out hi]

theorem entry2_lowerAt (C : TrioSeq) (j0 i : ℕ) :
    entry (lowerAt C j0) 2 i = entry C 2 i := by
  rcases Nat.lt_or_ge i C.length with hi | hi
  · show ((lowerAt C j0).getD i (0, 0, 0)).2.2 = _
    rw [lowerAt_getD hi]
  · rw [entry_out (by rw [lowerAt_length]; omega), entry_out hi]

theorem entry1_lowerAt {C : TrioSeq} {j0 i : ℕ} (hi : i < C.length) :
    entry (lowerAt C j0) 1 i = entry C 1 i - (if i = j0 then 1 else 0) := by
  show ((lowerAt C j0).getD i (0, 0, 0)).2.1 = _
  rw [lowerAt_getD hi]

theorem entry1_lowerAt_le (C : TrioSeq) (j0 i : ℕ) :
    entry (lowerAt C j0) 1 i ≤ entry C 1 i := by
  rcases Nat.lt_or_ge i C.length with hi | hi
  · rw [entry1_lowerAt hi]; omega
  · rw [entry1_out (by rw [lowerAt_length]; omega)]; omega

/-- 3 行とも一致すれば列は等しい。 -/
theorem eq_of_entries {A B : TrioSeq} (hl : A.length = B.length)
    (h0 : ∀ j, entry A 0 j = entry B 0 j) (h1 : ∀ j, entry A 1 j = entry B 1 j)
    (h2 : ∀ j, entry A 2 j = entry B 2 j) : A = B := by
  refine List.ext_getElem hl ?_
  intro i hi1 hi2
  rw [← entry_triple hi1, ← entry_triple (show i < B.length from hi2), h0, h1, h2]

/-- **1 列 1 段の凸性**（下端の witness つき）。 -/
def WConvexUnit : Prop :=
  ∀ (a : ℕ) (A B C : TrioSeq) (j0 : ℕ), A ∈ W a → C ∈ W a → Le1 A B → Le1 B C →
    (∀ j, j ≠ j0 → entry B 1 j = entry C 1 j) →
    entry C 1 j0 = entry B 1 j0 + 1 →
    B ∈ W a

/-- **★★★★ 反復は回る**: 1 列 1 段の凸性から幅 1 の凸性が出る（課題 L95-a）。
和や個数の計量は要らない —— **窓が幅 1 なので、各列はたかだか 1 回下げれば済む**。
添字 `i` の帰納で「`i` 以上では一致」を下ろしていけばよい。 -/
theorem wconvex1_of_unit (h : WConvexUnit) : WConvex1 := by
  classical
  intro a A B C hA hC hAB hBC hwin
  suffices H : ∀ i : ℕ, ∀ C' : TrioSeq, C' ∈ W a → Le1 B C' → Le1 A C' →
      (∀ j, entry C' 1 j ≤ entry A 1 j + 1) →
      (∀ j, i ≤ j → entry C' 1 j = entry B 1 j) → B ∈ W a by
    refine H C.length C hC hBC (Le1_trans hAB hBC) hwin (fun j hj => ?_)
    rw [entry1_out (by omega), entry1_out (by rw [hBC.1]; omega)]
  intro i
  induction i with
  | zero =>
      intro C' hC' hBC' _ _ hagree
      have : B = C' :=
        eq_of_entries hBC'.1 hBC'.2.1 (fun j => (hagree j (Nat.zero_le j)).symm)
          hBC'.2.2.1
      rw [this]; exact hC'
  | succ k ih =>
      intro C' hC' hBC' hAC' hwin' hagree
      by_cases hk : entry C' 1 k = entry B 1 k
      · refine ih C' hC' hBC' hAC' hwin' (fun j hj => ?_)
        rcases Nat.eq_or_lt_of_le hj with hje | hjl
        · rw [← hje]; exact hk
        · exact hagree j (by omega)
      · -- 列 `k` はちょうど 1 だけ高い（窓が幅 1、かつ `A ≤ B`）
        have hlt : entry B 1 k < entry C' 1 k := by
          have := hBC'.2.2.2 k; omega
        have hone : entry C' 1 k = entry B 1 k + 1 := by
          have h1 := hwin' k
          have h2 := hAB.2.2.2 k
          omega
        have hklen : k < C'.length := by
          by_contra hc
          have h1 : entry C' 1 k = 0 := entry1_out (by omega)
          have h2 : entry B 1 k = 0 := entry1_out (by rw [hBC'.1]; omega)
          omega
        set D : TrioSeq := lowerAt C' k with hD
        have hDlen : D.length = C'.length := lowerAt_length C' k
        have hD1k : entry D 1 k = entry B 1 k := by
          rw [hD, entry1_lowerAt hklen, if_pos rfl]; omega
        have hD1ne : ∀ j, j ≠ k → entry D 1 j = entry C' 1 j := by
          intro j hne
          rcases Nat.lt_or_ge j C'.length with hj | hj
          · rw [hD, entry1_lowerAt hj, if_neg hne]; omega
          · rw [hD, entry1_out (by rw [lowerAt_length]; omega),
              entry1_out (by omega)]
        have hBD : Le1 B D := by
          refine ⟨by rw [hDlen]; exact hBC'.1, fun j => ?_, fun j => ?_, fun j => ?_⟩
          · rw [hD, entry0_lowerAt]; exact hBC'.2.1 j
          · rw [hD, entry2_lowerAt]; exact hBC'.2.2.1 j
          · by_cases hj : j = k
            · subst hj; omega
            · rw [hD1ne j hj]; exact hBC'.2.2.2 j
        have hDC : Le1 D C' := by
          refine ⟨hDlen, fun j => ?_, fun j => ?_, fun j => ?_⟩
          · rw [hD, entry0_lowerAt]
          · rw [hD, entry2_lowerAt]
          · exact entry1_lowerAt_le C' k j
        have hAD : Le1 A D := Le1_trans hAB hBD
        have hDW : D ∈ W a :=
          h a A D C' k hA hC' hAD hDC (fun j hj => hD1ne j hj) (by omega)
        refine ih D hDW hBD hAD (fun j => le_trans (hDC.2.2.2 j) (hwin' j))
          (fun j hj => ?_)
        rcases Nat.eq_or_lt_of_le hj with hje | hjl
        · rw [← hje]; exact hD1k
        · rw [hD1ne j (by omega)]; exact hagree j (by omega)

/-! ## ★★★★★ 課題 L97-c: 3 回着いた同じ形 —— **接頭辞つきコピー**

今日、同じ形に 3 回着いた:

    §49  `snoc_flat_root` の「親が根」＝ **`take j0` が空**
    §96  `split_lastMin` の切れ目が `R.dropLast` の**中**に落ちる
    §109 `srow = 0` 枝で増えるのは **`C.take j0`** だけ

全部「**接頭辞との連結**」。ここを 1 本の `Prop` にする。

⚠ 素朴に「`A ∈ W u` ＋ `P ∈ W u` ⟹ `A ++ P ∈ W u`」（`rsum` 無しの `WCat`）と
書くのは**強すぎる**（`P` が `A` の浅い列の下に潜る）。実際に要るのはもっと狭い:

    **`A ++ Q ∈ W u`（1 個ぶんは既に `W` にいる）⟹ `A ++ (Q の n 個のコピー)` も `W u`**

これは `W_flatMap_copies`（`Wset.lean:2552`、**証明ずみ**）の **`A = []` を接頭辞つきに
一般化しただけ**。⟹ 「証明ずみ定理の 1 段の一般化」という、今日ずっと出てきた形。 -/

/-- **(PREFIXCOPIES)**: 接頭辞つきのコピー閉包。`A = []` は `W_flatMap_copies`。 -/
def PrefixCopies : Prop :=
  ∀ (u n : ℕ) (A Q : TrioSeq), A ++ Q ∈ W u →
    (∀ q ∈ Q, entry Q 0 0 ≤ q.1) →
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u

/-- `A = []` の場合は**証明ずみ**（`W_flatMap_copies`）。 -/
theorem prefixCopies_nil {u n : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u)
    (hQr : ∀ q ∈ Q, entry Q 0 0 ≤ q.1) :
    ([] : TrioSeq) ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  rw [List.nil_append]
  exact W_flatMap_copies hQ hQr n

/-! ### `srow = 0` 枝は `PrefixCopies` で閉じる

`srow = 0` では `d0 = d1 = 0`（`Trio.oper` の定義）なので、
`oper_unfold` の写しは**逐語**になり

    `(C ++ [t])⟦n⟧ = C.take j0 ++ （`C.drop j0` の n 個のコピー）`

で、しかも `C.take j0 ++ C.drop j0 = C ∈ W u` が**手元にある**。
⟹ `PrefixCopies` がそのまま当たる。 -/

theorem entry_snoc_left {C : TrioSeq} {p : ℕ × ℕ × ℕ} {i j : ℕ} (hj : j < C.length) :
    entry (C ++ [p]) i j = entry C i j := by
  unfold entry
  rw [getD_append_left hj]

open Classical in
/-- **★★★ `srow = 0` の展開は「接頭辞 ＋ 逐語コピー」**。 -/
theorem oper_snoc_srow0 {C : TrioSeq} {p : ℕ × ℕ × ℕ} {j0 : ℕ} (hCne : C ≠ [])
    (hz : ¬(entry (C ++ [p]) 0 C.length = 0 ∧ entry (C ++ [p]) 1 C.length = 0 ∧
      entry (C ++ [p]) 2 C.length = 0))
    (hsr : srow (C ++ [p]) C.length = 0)
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length)
    (hj0 : j0 = parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length)
    (hj0le : j0 ≤ C.length) (n : ℕ) :
    (C ++ [p])⟦n⟧
      = C.take j0 ++ (List.range n).flatMap fun _ => (C.drop j0).take (C.length - j0) := by
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  have hlen : (C ++ [p]).length - 1 = C.length := by simp
  have hu := oper_unfold (M := C ++ [p]) (j1 := C.length) (i1 := 0) (j0 := j0)
    (d0 := 0) (d1 := 0) hlen.symm (by omega) hz (by rw [hsr])
    (by rw [hsr] at hpar; exact hpar) (by rw [hj0, hsr]) (by simp) (by simp) n
  rw [hu]
  congr 1
  · rw [List.take_append_of_le_length hj0le]
  · refine List.flatMap_congr ?_
    intro k _
    have hdrop : (C.drop j0).take (C.length - j0)
        = (List.range' j0 (C.length - j0)).map fun j =>
            ((entry C 0 j, entry C 1 j, entry C 2 j) : ℕ × ℕ × ℕ) := by
      refine List.ext_getElem (by simp) ?_
      intro i hi1 hi2
      simp only [List.length_take, List.length_drop] at hi1
      have hij : j0 + i < C.length := by omega
      rw [List.getElem_take, List.getElem_drop]
      rw [List.getElem_map, List.getElem_range']
      simp only [Nat.one_mul]
      exact (entry_triple hij).symm
    rw [hdrop]
    refine List.map_congr_left ?_
    intro j hj
    have hjlt : j < C.length := by
      have := List.mem_range'.mp hj
      omega
    rw [entry_snoc_left hjlt, entry_snoc_left hjlt, entry_snoc_left hjlt]
    simp


open Classical in
/-- **★★★★ `PrefixCopies` は `WSnoc` の `srow = 0` 枝を閉じる。** -/
theorem wsnoc_srow0_of_prefixCopies (h : PrefixCopies) {u : ℕ} {C : TrioSeq}
    {p : ℕ × ℕ × ℕ} (hC : C ∈ W u) (hCne : C ≠ [])
    (hsr : srow (C ++ [p]) C.length = 0)
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) :
    C ++ [p] ∈ W u := by
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  set j0 : ℕ := parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length with hj0
  -- 親の関係を `nextrel0` として取り出す
  have hnr : nextrel0 (C ++ [p]) j0 C.length := by
    have h1 := parent_nextR hpar
    rw [← hj0, hsr, nextR, if_pos rfl] at h1
    exact h1
  have hj0lt : j0 < C.length := hnr.2.2.1
  have hdeep : entry (C ++ [p]) 0 j0 < entry (C ++ [p]) 0 C.length := hnr.2.2.2.1
  have hz : ¬(entry (C ++ [p]) 0 C.length = 0 ∧ entry (C ++ [p]) 1 C.length = 0 ∧
      entry (C ++ [p]) 2 C.length = 0) := by
    rintro ⟨h0, -, -⟩
    omega
  -- 落とすブロックは `C.drop j0`
  have htk : (C.drop j0).take (C.length - j0) = C.drop j0 := by
    apply List.take_of_length_le
    simp
  have hcat : C.take j0 ++ C.drop j0 = C := List.take_append_drop j0 C
  have hdrop0 : entry (C.drop j0) 0 0 = entry C 0 j0 := by
    have h1 : (C.drop j0).getD 0 (0, 0, 0) = C.getD j0 (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp; omega),
        List.getElem?_eq_getElem hj0lt]
      simp
    show ((C.drop j0).getD 0 (0, 0, 0)).1 = (C.getD j0 (0, 0, 0)).1
    rw [h1]
  have hQr : ∀ q ∈ C.drop j0, entry (C.drop j0) 0 0 ≤ q.1 := by
    intro q hq
    rw [hdrop0]
    obtain ⟨i, hi, hqe⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_drop] at hi
    have hidx : j0 + i < C.length := by omega
    have hqv : q = C[j0 + i] := by rw [← hqe]; simp
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hqv]
      have : entry C 0 (j0 + 0) = (C[j0 + 0]).1 := by
        rw [← entry_triple (show j0 + 0 < C.length by omega)]
      simp only [Nat.add_zero] at this ⊢
      omega
    · have hgap := hnr.2.2.2.2 (j0 + i) ⟨by omega, hidx⟩
      rw [entry_snoc_left hidx] at hgap
      rw [entry_snoc_left hj0lt] at hdeep
      have hEq : entry C 0 (j0 + i) = (C[j0 + i]).1 := by
        rw [← entry_triple hidx]
      rw [hqv]
      omega
  refine mem_of_oper_mem (fun n hn => ?_)
  rw [oper_snoc_srow0 hCne hz hsr hpar hj0 (by omega) n, htk]
  exact h u n (C.take j0) (C.drop j0) (by rw [hcat]; exact hC) hQr


/-- **★★★★★ `PrefixCopies` を認めると `WSnoc` は `srow ≥ 1` の枝だけ**（課題 L97）。 -/
def WSnocOpen1 : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ∈ W u → C ≠ [] →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length →
    (∃ q ∈ C, 0 < q.2.2) →
    srow (C ++ [p]) C.length ≠ 0 →
    C ++ [p] ∈ W u

theorem wsnoc_of_prefixCopies (hpc : PrefixCopies) (h : WSnocOpen1) : WSnoc := by
  classical
  intro u C p hC hCne hpar
  by_cases hs : srow (C ++ [p]) C.length = 0
  · exact wsnoc_srow0_of_prefixCopies hpc hC hCne hs hpar
  · by_cases hz2 : ∃ q ∈ C, 0 < q.2.2
    · exact h u C p hC hCne hpar hz2 hs
    · push_neg at hz2
      have hself : (C ++ [p]) ∈ Wself :=
        snoc_zeroRow2 (M' := C) (fun q hq => by have := hz2 q hq; omega) p
      have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
      have hlev : lev (C ++ [p]) 0 ≤ u := by
        have hE : ∀ i, entry (C ++ [p]) i 0 = entry C i 0 := by
          intro i; unfold entry; rw [getD_append_left hClen]
        have h1 : lev (C ++ [p]) 0 = lev C 0 := by
          unfold lev; rw [hE 1, hE 2]
        rw [h1]
        exact lev_root_le_of_mem_W hC hCne
      exact W_mono hlev hself

theorem towerOK_of_prefixCopies (hpc : PrefixCopies) (h : WSnocOpen1)
    (hg : GraftFromExp) : TowerOK :=
  towerOK_of_wsnoc_graft (wsnoc_of_prefixCopies hpc h) hg


/-! ### 課題 L98-a: `W_flatMap_copies` が `A = []` を使うのは **`W_add` の `rsum` 1 か所**

`Wset.W_flatMap_copies`（`Wset.lean:2552`）の証明:

```
| succ n ih =>
    rw [List.range_succ, List.flatMap_append]     -- Q^(n+1) = Q^n ++ Q
    refine W_add ih hQ ?_                         -- ← ここ
    intro p hp; rcases … ; exact hQr p …          -- 全部の列が Q の列なので `hQr` で足りる
```

接頭辞 `A` を付けると `W_add` の `rsum` は `(A ++ Q^n) ++ Q` の**全列**に
`entry Q 0 0 ≤ p.1` を要求する。`Q^n` と `Q` の列は `hQr` で足りるが、
**`A` の列は足りない**。⟹ 増えるのはちょうど

    **`∀ q ∈ A, entry Q 0 0 ≤ q.1`**（＝ `rsum A Q`）

**それさえあれば証明は逐語で伸びる**（下の `prefixCopies_of_rsum`、緑）。 -/

/-- **★★★ `rsum` があれば `PrefixCopies` は定理**（証明は `W_flatMap_copies` の逐語の伸長）。 -/
theorem prefixCopies_of_rsum {u : ℕ} {A Q : TrioSeq} (hA : A ∈ W u) (hQ : Q ∈ W u)
    (hQr : ∀ q ∈ Q, entry Q 0 0 ≤ q.1) (hAr : ∀ q ∈ A, entry Q 0 0 ≤ q.1) :
    ∀ n : ℕ, A ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  intro n
  induction n with
  | zero => simpa using hA
  | succ k ih =>
      have hsplit : A ++ ((List.range (k + 1)).flatMap fun _ => Q)
          = (A ++ ((List.range k).flatMap fun _ => Q)) ++ Q := by
        rw [List.range_succ, List.flatMap_append]
        simp [List.append_assoc]
      rw [hsplit]
      refine W_add ih hQ ?_
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact hAr p hp
        · rw [List.mem_flatMap] at hp
          obtain ⟨-, -, hp⟩ := hp
          exact hQr p hp
      · exact hQr p hp

/-- **⟹ `PrefixCopies` の**開いている**のは「接頭辞に `Q` の根より浅い列がある」場合だけ。**
（`A ++ Q ∈ W u` から `A ∈ W u` は `W_take` で無料、`Q ∈ W u` は仮定に要る。） -/
def PrefixCopiesOpen : Prop :=
  ∀ (u n : ℕ) (A Q : TrioSeq), A ∈ W u → Q ∈ W u →
    (∀ q ∈ Q, entry Q 0 0 ≤ q.1) →
    (∃ q ∈ A, q.1 < entry Q 0 0) →
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u

theorem prefixCopies_of_open (h : PrefixCopiesOpen) {u : ℕ} {A Q : TrioSeq}
    (hA : A ∈ W u) (hQ : Q ∈ W u) (hQr : ∀ q ∈ Q, entry Q 0 0 ≤ q.1) (n : ℕ) :
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  classical
  by_cases hc : ∃ q ∈ A, q.1 < entry Q 0 0
  · exact h u n A Q hA hQ hQr hc
  · push_neg at hc
    exact prefixCopies_of_rsum hA hQ hQr (fun q hq => hc q hq) n

/-! ### L98-b の見立て

我々の場面では `A = C.take j0`、`Q = C.drop j0`、`entry Q 0 0 = entry C 0 j0` なので

    `rsum A Q`  ⟺  **`j0` は `C` の最上位（深さ最小）の位置以降にある**

`split_lastMin`（この file、緑）は `C` を**最後の最上位の木**で切るので、
「`j0` がその切れ目以降か」がそのまま判定条件になる。R1 の R79 が測っている量。 -/


/-! ## ★★★ 課題 L99-b: `j0 = 0` の必要条件（全 `srow` で一様）

R1 の実測「**`j0 = 0` ⟹ `∀ 0<j<j1, M[0] の行 0 < M[j] の行 0`**、例外 0」を証明する。
どの `srow` でも親の関係は行 0 の祖先鎖 `rtg0 M 0 j1` を含む
（`nextrel0` は自分、`nextrel1` は `le0`、`nextrel2` は `le1 → rtg1 → rtg0`）ので、
**行 0 の鎖の「窓」性**に落ちる。 -/

/-- 行 0 の祖先鎖に沿って深さは単調。 -/
theorem rtg0_entry0_mono {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : entry M 0 a ≤ entry M 0 b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (le_of_lt hbc.2.2.2.1)

/-- **★★ 行 0 の鎖は窓を作る**: `0` から `j1` へ鎖があれば、間の列はすべて根より深い。 -/
theorem rtg0_zero_window {M : TrioSeq} {j1 : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) 0 j1) :
    ∀ j, 0 < j → j < j1 → entry M 0 0 < entry M 0 j := by
  induction h with
  | refl => intro j h0 hj; omega
  | @tail b c hab hbc ih =>
      intro j h0 hj
      rcases Nat.lt_or_ge j b with hjb | hjb
      · exact ih j h0 hjb
      · rcases Nat.eq_or_lt_of_le hjb with heq | hbj
        · subst heq
          exact rtg0_entry0_lt hab (by omega)
        · have hdip := hbc.2.2.2.2 j ⟨hbj, hj⟩
          have hstep := hbc.2.2.2.1
          have hmono := rtg0_entry0_mono hab
          omega

/-- どの行の親関係も行 0 の祖先鎖を含む。 -/
theorem rtg0_of_nextR {M : TrioSeq} {i a b : ℕ} (h : nextR M i a b) :
    Relation.ReflTransGen (nextrel0 M) a b := by
  unfold nextR at h
  split at h
  · exact Relation.ReflTransGen.single h
  · split at h
    · exact h.2.2.2.2.1.2.2
    · exact rtg1_to_rtg0 h.2.2.2.2.1.2.2

open Classical in
/-- **★★★ (L99-b) `j0 = 0` の必要条件**: バッドルートが根なら、
根と末尾の間の列はすべて**根より深い**。 -/
theorem badroot_zero_window {M : TrioSeq} {i j1 : ℕ} (hpar : hasParent M i j1)
    (hj0 : parent M i j1 = 0) :
    ∀ j, 0 < j → j < j1 → entry M 0 0 < entry M 0 j := by
  have hnr := parent_nextR hpar
  rw [hj0] at hnr
  exact rtg0_zero_window (rtg0_of_nextR hnr)

/-- ⚠ 逆は成り立たない（R1 の実測: 条件が真でも `j0 > 0` が 44.3%）。
`M = [(0,0,0),(1,0,0),(2,0,0),(3,0,0)]` のように**深さが単調に増える**列では
窓の条件は真だが、末尾の行 0 の親は**直前の列**であって根ではない。 -/
example : True := trivial


/-! ### ⚠ 課題 L99-a の判定（見立て、**Lean 未検証**）:
**`PrefixCopies` と `WSnoc` の `srow = 0` 枝は同じ内容**

片方向は緑（`wsnoc_srow0_of_prefixCopies`）。逆向きの構成は次のとおり:

    `A ++ Q ∈ W u`、`Q` の根が `Q` 内で**狭義**最小（深さ `q0`）とする
    `t := (q0 + 1, 0, 0)` を足すと
      `srow (A ++ Q ++ [t]) |A ++ Q| = 0`（行 1・行 2 が 0）
      行 0 の親は `|A|`（= `Q` の根）—— `q0 < q0+1` かつ `Q` の他の列は `≥ q0+1`
    ⟹ `WSnoc` で `A ++ Q ++ [t] ∈ W u`
    ⟹ `Wset.oper_closed`（`Wset.lean:2103`）で `(A ++ Q ++ [t])⟦n⟧ ∈ W u`
    ⟹ `oper_snoc_srow0`（この file、緑）でそれは `A ++ Q^n`

**⟹ `srow = 0` 枝を `PrefixCopies` に落としても、内容は減らない。**
「逐語コピーだから扱いやすい」は形の話で、**難しさは同じ**。

⚠ この逆向きは**まだ Lean で書いていない**（行 0 の親の一意性 `∃!` の構成が要る）。
「見立て」として記録する。**R1 の測定でも、この構成が実際に作れるかを確かめると良い。** -/


/-! ### 課題 L96-b: `srow = 0` の枝で **`snoc_flat_root` から増えるのは接頭辞だけ**

`Trio.oper` の定義（`Trio.lean:98`）を読むと、`i1 = srow M j1` に対し

    `d0 := if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0`
    `d1 := if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0`

なので **`srow = 0` なら `d0 = d1 = 0`** ——**上昇が一切乗らない**。よって

    `(C ++ [t])⟦n⟧ = C.take j0 ++ （`C.drop j0` の n 個の**逐語**コピー）`

`j0 = 0` なら `take 0 = []` で `W_flatMap_copies` がそのまま効く（＝ `snoc_flat_root`）。
**`j0 > 0` で増えるのは接頭辞 `C.take j0` ただ 1 つ**（team-lead が §49 で特定した点）。

⟹ その枝を `W_add` で閉じるのに要るのは

    **`rsum (C.take j0) (C.drop j0)`** ＝ **`C.take j0` の全列の深さが `entry C 0 j0` 以上**

だけ。コピー側は自動:バッドルートの `nextrel0` の「谷なし」節から、
`j0 < j < |C|` の列はどれも `t.1 > entry C 0 j0` 以上（`entry C 0 j0 < t.1 ≤ entry C 0 j`）。

⚠ 接頭辞側は自動でない: `j0` より手前に**より浅い**列があり得る。
**そこが `srow = 0` 枝の核**で、形は `split_lastMin` の切れ目の問題そのもの
（課題 L87 で見た「切れ目が中に落ちる」と同じ構造）。 -/


/-! # ★★★★★ 課題 L100: 2 行と 3 行の `Wstar_closed` を分岐ごとに突き合わせた

## 結論（3 点）

### (1) `TowerOK` が要るのは **2 か所**（`Wset.lean:4447` と `:4461`）

    `:4461` … **節 3 / srow = 2**（`oper_cons_tower2`）—— **本質**（塔の持ち上げ）
    `:4447` … **節 2**（`Aop` の第 2 節から来た `R`）—— **本質ではない**（下記 (2)）

R1 の読み「`srow = 2` の枝だけ」は `:4461` については正しいが、**`:4447` を見落としている**。

### (2) ★★ `:4447` が生じる理由: **3 行の `Aop` の節 2 に `natDom` のガードが無い**

```lean
-- 2 行（`Pair/Wset.lean:179`）
(M.length ≤ 1 ∧ entry M 1 0 = 0) ∨
  (**natDom M** ∧ ∀ n, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m, m < u ∧ domT M m ∧ …)

-- 3 行（`Wset.lean:171`）
(M.length ≤ 1 ∧ lev M 0 = 0) ∨
  (∀ n, 1 ≤ n → M⟦n⟧ ∈ X) ∨                 -- ← **ガードが無い**
  (∃ m, m < u ∧ domT M m ∧ …)
```

`natDom M ↔ lev M (末尾) = 0 ∨ hasParent M (srow …) (末尾)`（`Wset.lean:121`）なので、
ガードがあれば `Wstar_closed` の節 2 の分岐で

    `¬ hasParent R …`（`R` 内で孤児）**かつ** `lev R (末尾) ≠ 0`

という場合が**起きえない**。ところがそこが `:4447`（塔）に落ちる唯一の枝である。
⟹ **ガードを足せば `:4447` は消え、`TowerExp` / `GraftFromExp` が要らなくなる。**

`natDom` は 3 行にも**定義がある**（`Wset.lean:83`）—— 節 2 で使っていないだけ。

### (3) ⚠ ただし `Aop` を強めると `W` は**小さくなる**

`W = lfpS (Aset W u)` なので、節 2 を狭めると `W` の要素が減る。
⟹ **`mem_W_of_bound` / `W_membership`（ラダー側）が通るかを確かめる必要がある。**
2 行では同じ設計で通っているが、3 行で確認していないので**未判定**。

**⟹ team-lead の ⚠「`GraftFromExp` が本当に不要か慎重に」への答え:
いまの `Aop` の定義のままなら `GraftFromExp` は要る。
`Aop` の節 2 に `natDom` を足せば要らなくなるが、それは `W` の定義変更で、
ラダー側の再検査が要る。** -/

/-- **★★★ ガードがあれば節 2 の塔の枝は起きない。** -/
theorem natDom_no_tower_branch {R : TrioSeq} (hnat : natDom R)
    (hp : ¬ hasParent R (srow R (R.length - 1)) (R.length - 1))
    (hw : lev R (R.length - 1) ≠ 0) : False := by
  rcases natDom_iff.mp hnat with h | h
  · exact hw h
  · exact hp h

/-- ⟹ ガード付きなら `domT R m` は起きない（節 2 と節 3 が排他になる）。 -/
theorem natDom_not_domT {R : TrioSeq} {m : ℕ} (hnat : natDom R) : ¬ domT R m :=
  hnat m


/-! # ⛔ 課題 L101 の判定: **`natDom` のガードは足せない。理由は行 2 の非対称性**

⚠ 新しいファイル `L101Guard.lean` は**作りませんでした**（道が閉じているため）。

## 決め手: `Wset.lean:4470` は **`domT (p0 :: R) m` の下で節 2 を使う**

```lean
· have hdM : domT (p0 :: R) m := domT_cons_of_dead hRnil hd hpM
  by_cases hma : m < a
  · refine A1_intro (Or.inr (Or.inr ⟨m, hma, hdM, …⟩))        -- 節 3（m < a のとき）
  · -- the stage is below the orphan: fall back on the successor route
    refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))          -- ★ **節 2**（a ≤ m）
```

`domT (p0 :: R) m` は `natDom (p0 :: R)` の**否定そのもの**（`natDom M := ∀ m, ¬ domT M m`）。
⟹ **ガードを付けるとこの枝が塞がる。**

しかも節 2 のこの使い方は `mem_of_oper_mem` として **`Wtower2` 17 / `Wslift` 7 /
この file 3 か所**で使われている。

## ★ なぜ 2 行では要らないか: **行 1 の孤児は必ず根の段より下にいる**

`Wset.entry1_le_of_dead_one`（`Wset.lean:2694`）の docstring:

> 行 1 の孤児が根に復活してもらえないなら、その列の行 1 は高々 `v`。
> ⟹ レベルは高々 `2v ≤ 2v+z` —— **孤児は自動的に根の段より下**。
> **行 2 にはそのような上界が無い**（`no_hasParent_two_of_row1_zero` が
> レベル 0 の根の下にレベル 1 の永久孤児を与える）。
> **この非対称性こそが trio が yapss より難しい理由。**

⟹ **2 行では `a ≤ m` の場合が起きない**ので、`m < a` の節 3 だけで足り、
節 2 に `natDom` のガードを置ける。**3 行では行 2 の孤児が `a ≤ m` を作る**ので、
節 2 の「後退路」が要る。

**⟹ `natDom` は移植のときに落ちたのではなく、3 行では置けない。**

## ⟹ `GraftFromExp`（＝ `TowerExp`）は本当に要る

課題 L100 (3) の懸念のとおり。**`TowerOK` を `TowerOK2` に弱めることはできない。** -/

/-- ガードが塞ぐ枝（`Wset.lean:4470`）。 -/
theorem guard_blocks_fallback {v z m : ℕ} {R : TrioSeq}
    (hdM : domT (((0, v, z) : ℕ × ℕ × ℕ) :: R) m) :
    ¬ natDom (((0, v, z) : ℕ × ℕ × ℕ) :: R) := fun h => h m hdM

/-- **★★ 行 1 の死んだ孤児は必ず根の段より下**（⟹ 節 3 で足りる）。 -/
theorem dead_row1_stage_lt {v z a m : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hva : 2 * v + z ≤ a) (h2 : entry R 2 (R.length - 1) = 0)
    (hnp : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 R.length)
    (hlev : lev R (R.length - 1) = m + 1) : m < a := by
  have h1 := entry1_le_of_dead_one hR hRne hnp
  unfold lev at hlev
  omega

/-- ⚠ **行 2 では上界が無い**ので `a ≤ m` が起こりうる。
そこだけが節 2 の「後退路」を必要とし、そこだけがガードを不可能にする。 -/
example : True := trivial


/-! # ⚠ 課題 L101' の判定: **中間案も `GraftFromExp` に戻る**

（team-lead の `git log -S` による訂正を受けて。ガードは
`2643c7a v0.79.0` で **意図的に外された** —— `z=1` の dead root を節 2 で認めるため。）

## 1. `dead root ⟹ M⟦n⟧ = M.dropLast` は**既存**（`live` でも同じ）

`Wset.oper_eq_graft_nil_of_domT`（`Wset.lean:137`）は `1 < |M|` と **`domT M m`
だけ**を要求する。`dead` か `live` かは効かない。⟹ 下の `domT_oper_dropLast`。

## 2. ⛔ 「`:4447` に来る `R` は `live` だから節 3 が届く」は**使えない**

**理由は `Aop` が選言だから。** `Wstar_closed` は

```lean
rcases AR with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
```

で**渡された選言子だけ**を手に持つ。`R` が意味論的に節 3 も満たしていても、
`hgr`（graft 閉包）は**手元に来ない**。節 2 の `hop` から `hgr` を作るのが
まさに `GraftFromExp`（課題 L84-b）である。

    `hop` が実際にくれるもの … `R.dropLast ∈ Wstar` の**1 個だけ**（`exp_gives_dropLast`）
    塔が要るもの           … `∀ y ∈ W m, based y → graft R y ∈ Wstar` の**族**

## 3. ⟹ `Aop` を触らずに `:4447` を消すには `GraftFromExp` が要る

**中間案（`natDom M ∨ dead root` のガード）も同じ壁**に当たる:
`:4447` の `R` は根に復活してもらう `live` な孤児を持つので、
ガードの `dead root` の側では拾えず、`natDom` の側でも拾えない
（`domT R m'` があるので `natDom R` は偽）。
⟹ **ガードを緩めても `:4447` は残る。**

## ⟹ 結論は課題 L94 の形のまま

    `TowerOK` ┬ 節 3 / srow=2 = `TowerGraft2` ⟸ `LiftTie` ⟸ `WSnoc`
              └ 節 2         = `TowerExp`     ⟸ `GraftFromExp`
                                              ⟸ `Subst1gRevive` ＋ `WstarSnoc` ⟸ `WSnoc`

**`WSnoc` が二重に効く形が最良。** -/

/-- `domT` なら展開は `dropLast` に潰れる（`dead` / `live` を問わない）。 -/
theorem domT_oper_dropLast {M : TrioSeq} {m n : ℕ} (hL : 1 < M.length)
    (hd : domT M m) : M⟦n⟧ = M.dropLast := by
  rw [oper_eq_graft_nil_of_domT hL hd, graft_nil]

/-- `:4447` の `R` は `natDom` でも `dead root` でもない: `domT R m'` を持ち、
かつ根に復活してもらう。⟹ **ガードをどう緩めても拾えない**。 -/
theorem tower_branch_not_natDom {R : TrioSeq} {m : ℕ} (hd : domT R m) :
    ¬ natDom R := fun h => h m hd


/-! # ★★★★★ 今日の到達点（課題 L95-c、明日の再開点）

## 1. 上から下への連鎖（全部 Lean で緑）

```
Final.TRIO_terminates_of_towerOK  (Wset.TowerOK → WellFounded stepRel)   Final.lean:90
  └ Wset.towerOK_of  (TowerGraft2 → TowerExp → TowerOK)                  Wset.lean:4514
      ├ 節 1                    矛盾（domT と両立しない）                  既済
      ├ 節 3 / srow = 1         Wset.tower1_mem                           既済
      ├ 節 3 / srow = 2 = TowerGraft2
      │    └ L53.towerGraft2_of_liftTie   (LiftTie → TowerGraft2)         この file
      │         └ L53.liftTie_of_wsnoc    (WSnoc → LiftTie)               この file
      │              └ Wtower2 の鎖: wcat_of_snoc → shiftTowerClosed_of_cat
      │                → shiftTowerClosedS_of_closed → liftStageParented_of_tower
      │                → liftStage_of_parented                            全部既存・緑
      └ 節 2 = TowerExp
           └ L53.towerExp_of_graftFromExp (GraftFromExp → TowerGraft2 → TowerExp)
                └ GraftFromExp ⟸ Subst1gRevive ＋ WstarSnoc
                     L53.graft_cons_mem_of_revive（側条件は構成から、場合条件 2 本のみ残る）
                     L53.wstarSnoc_of_wsnoc  (WSnoc → WstarSnoc)
```

**⟹ 未証明はちょうど 2 本。**

## 2. 未証明 2 本の正確な文

### (1) `Wset.WSnoc`（`Wtower2.lean:2049`）— **二重に効く**

```lean
def WSnoc : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ∈ W u → C ≠ [] →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length → C ++ [p] ∈ W u
```

* 持ち上げ側: `WSnoc → … → LiftStage → LiftTie → TowerGraft2`
* 節 2 側: `WSnoc → WstarSnoc`（`R.dropLast ∈ Wstar` を `R ∈ Wstar` へ 1 段上げる）

### (2) `Wtower2.Subst1gRevive`（`Wtower2.lean:3251`）

1 列（`p` 番目）を `W (lev S p)` のブロック `C` に差し替えても段は上がらない。
`graft` の場面では側条件（`entry C 0 0 = entry S 0 p` / 深さ / `lev`）が**構成から出る**。

## 3. 今日証明した主な補題（この file）

```
towerOK2_of_clause3 / towerGraft2_of_liftTie   TowerGraft2 は LiftTie 1 本
liftStage_of_wsnoc                              WSnoc だけで (WL)          ★
strict_prop / noTie_prop                        伝播は仮定ゼロ
liftStage_of_strict / liftStage_of_noTie        狭義 88.5% ＋ 無タイ 2.8%
lift1_untouched_of_le / le1_entry1_lt           le1 錐は行 1 の狭義増加
Lift1_eq_mliftR / coneV_root_vacuous            核は「閾値の off-by-one」
liftStage_of_unit / liftStage_iff_unit          d は 1 に落ちる            ★
liftStage_of_wconvex1                           幅 1 の凸性で足りる
wconvex1_of_unit                                1 列 1 段 ⟹ 幅 1          ★
lowerOne_of_revive / lowerLast_of_revive        1 列 1 段は Subst1gRevive から
Wstar_iff_Wself / wstarSnoc_of_wsnoc            Wstar は根つき Wself
graft_cons_mem_of_revive                        graft は残核の場面そのもの
not_rsum_cons_root / rsum_graft_iff             W_add は根と両立しない（否定）
tower2_stage_fits' / tower2_zr / tower2_vw      段はいつでも収まる
```

## 4. 作ったが**要らなくなった**もの（どれも偽ではない）

```
Row1DownLocal / Row1DownRoot0   MliftR に畳まれた（L85）
MliftR / AminROper              slift 移植が閉じた。AminROper は**偽**（L88、反例つき）
WConvex1 / WConvexUnit          WSnoc から LiftStage が出る（L94）。保険経路として有効
WstarCat                        rsum が根と両立しない（L87）
```

## 5. 明日の最初の一手（候補）

1. **`WSnoc`** —— 1 本で 2 か所に効くので、費用対効果が最大
2. `graft_cons_mem_of_revive` に残る**場合条件 2 本**を潰して `GraftFromExp` を完成
3. 保険: `WConvexUnit`（1 列 1 段の凸性）—— `Subst1gRevive` の「復活」条件つきなら出る
-/


/-! ## ★★★★ 課題 L96: `WSnoc` の**開いている場合**を切り出す

`WSnoc`（`Wtower2.lean:2049`）で既に証明ずみなのは 3 本:

    `snoc_orphan`（`:3053`）    足す列が**孤児**なら無料 —— `WSnoc` は `hasParent` を
                                仮定するので、この枝は**そもそも現れない**
    `snoc_zeroRow2`（`:3127`）  **`C` の行 2 ≡ 0** なら、足す列は任意で無料
    `snoc_flat_root`（`:2208`） 足す列が**平ら（`srow = 0`）で親が根**なら無料

⟹ 開いているのは次の 2 条件を**両方**満たす場合だけ:

    (a) `C` に行 2 > 0 の列がある
    (b) 「`srow = 0` かつ親が根」ではない

場合の表（`t := 足す列`）:

    `srow t = 0`（`t.2.1 = t.2.2 = 0`）… 親が根なら**無料**、親が根でなければ**開いている**
    `srow t = 1`（`t.2.1 > 0`, `t.2.2 = 0`）… `C` の行 2 ≡ 0 なら無料、でなければ**開いている**
    `srow t = 2`（`t.2.2 > 0`）           … 同上

⚠ `srow` は `C ++ [t]` 上で測る（`entry (C ++ [t]) i |C| = t の成分`）ので、
`t` の成分だけで決まる。 -/

/-- **`WSnoc` の真の核**（課題 L96-a）。 -/
def WSnocOpen : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ∈ W u → C ≠ [] →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length →
    (∃ q ∈ C, 0 < q.2.2) →
    ¬ (srow (C ++ [p]) C.length = 0 ∧
        parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length = 0) →
    C ++ [p] ∈ W u

theorem entry_snoc_root {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hCne : C ≠ []) (i : ℕ) :
    entry (C ++ [p]) i 0 = entry C i 0 := by
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  unfold entry
  rw [getD_append_left hClen]

/-- **★★★★ `WSnoc` は開いている場合だけ**（既存 3 本で他は埋まる）。 -/
theorem wsnoc_of_open (h : WSnocOpen) : WSnoc := by
  classical
  intro u C p hC hCne hpar
  by_cases hz2 : ∃ q ∈ C, 0 < q.2.2
  · by_cases hflat : srow (C ++ [p]) C.length = 0 ∧
        parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length = 0
    · exact snoc_flat_root hC hCne hflat.1 hflat.2 hpar
    · exact h u C p hC hCne hpar hz2 hflat
  · push_neg at hz2
    have hself : (C ++ [p]) ∈ Wself :=
      snoc_zeroRow2 (M' := C) (fun q hq => by have := hz2 q hq; omega) p
    have hlev : lev (C ++ [p]) 0 ≤ u := by
      have h1 : lev (C ++ [p]) 0 = lev C 0 := by
        unfold lev
        rw [entry_snoc_root hCne 1, entry_snoc_root hCne 2]
      rw [h1]
      exact lev_root_le_of_mem_W hC hCne
    exact W_mono hlev hself

/-- ⟹ **核 2 本のうち片方が `WSnocOpen` に細くなる。** -/
theorem liftStage_of_wsnocOpen (h : WSnocOpen) : LiftStage :=
  liftStage_of_wsnoc (wsnoc_of_open h)

theorem towerOK_of_wsnocOpen_graft (h : WSnocOpen) (hg : GraftFromExp) : TowerOK :=
  towerOK_of_wsnoc_graft (wsnoc_of_open h) hg


end L53
end TRIO
