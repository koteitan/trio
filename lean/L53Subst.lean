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


end L53
end TRIO
