/-
課題 L7: `SubstFree`（課題 L5 の 1 行の命題）を **`W` の最小不動点の帰納法**で
証明しに行った記録。

    SubstFree := ∀ S, S ∈ Wself → ∀ p C, p < |S| → C ≠ [] → C ∈ Wself →
                   S.take p ++ C ++ S.drop (p+1) ∈ Wself

`Wself := {M | M ∈ W (lev M 0)}` で `W u` は `Aop` の最小不動点なので、
`Wset.A2'`（「`Aop`-閉な集合は `W u` を含む」）が使える。目標を

    Ysub := {S | SubstProp S}

に取ると、`Aop` の 3 節がそのまま 3 つの場合になる。

* **節 1（`|M| ≤ 1`）は証明できた**（下の `substProp_of_short`）。
  `p < |M|` から `|M| = 1, p = 0` なので差し替えの結果は `C` そのもの。
* **節 2（`∀ n ≥ 1, M⟦n⟧ ∈ X`）が山**。下の `Clause2`。
* **節 3（孤児 ＋ graft）** は下の `Clause3`。

## 節 2 のどこで詰まるか

**`Wtower2.subst1g_of_revive`（`Wtower2.lean:3424`）が既に同じ帰納をやっている。**
向こうは側条件つきの `SubstProp u`、こちらは側条件なし。閉じ方は同じ 3 つ:

| 場合 | 条件 | 閉じ方 |
|---|---|---|
| **clause 1** | `|S| ≤ 1` | 差し替えの結果が `C` そのもの（下で証明ずみ） |
| **mirror** | `|D| ≥ 2` かつ `D` の末尾列が `D` の中で親を持つ | `Xbar.oper_append_inner` で `S⟦n⟧ = S.take (p+1) ++ D⟦n⟧`、`R⟦n⟧ = (S.take p ++ C) ++ D⟦n⟧`。帰納法の仮定が直に効く |
| **orphan** | `D ≠ []` かつ `R` の末尾列が `R` の中でも孤児 | `R⟦n⟧ = Pred R = S.take p ++ C ++ D.dropLast` ＝ **接頭辞 `S.dropLast` への差し替え**。接頭辞パッケージ（`∀ k, SubstProp (S.take k)`）が払う |
| **revival（残り）** | `D ≠ []` かつ `R` の末尾列が `R` では親を持つのに `D` の中では孤児／または `D = []` | **開いたまま** |

つまり **`SubstFree` を `W` の帰納で回しても、止まる場所は
`Subst1gReviveSelf` とまったく同じ「復活の場合」である。**
側条件 6 本を落として得たのは「帰納のたびに側条件を建て直す手間が消える」
ことだけで、**壁は動かない**。

⚠ `RESIDUE-PROBLEM.md §4.5` は「接頭辞パッケージ `hpre` が呼び出し地点に実在し
**捨てられている**」と書くが、上の表のとおり `hpre` は **orphan の場合で実際に
使われている**。捨てられているのは revival の場合だけである。

### 実測（`lean/L1-NOTES.md` 課題 L7）

`S, C ∈ Wself` の 103579 例（`R` を展開したときのバッドルート `j0` の位置で分類）:

| | 割合 | `R⟦n⟧ = subst (S⟦n⟧) p C` か |
|---|---|---|
| `R` が展開しない（`Pred`）＝ orphan の場合 | **54%** | — (`Pred` で閉じる) |
| `j0` が `D` の中 ＝ mirror の場合 | 7% | **つねに成り立つ**（6944/6944） |
| `j0` が `S.take p` の中 ＝ revival | 14% | 98.4% 成り立たない |
| `j0` が `C` の中 ＝ revival | 25% | 98.5% 成り立たない |

revival の場合、`R` の展開は「`C` を含む区間の `n` 個のコピー」になるので
`S⟦n⟧` への **1 ブロックの差し替え**にならない（多ブロックになる）。
しかも `d1 > 0`（コピーに行 1 のリフトが乗る）のが `S.take p` 側で 21%、
`C` 側で 24% ある。そこを塔として処理しようとすると

    C ∈ Wself → （ガード付き行 1 リフトした C）∈ Wself

が要り、これが既知の核 `(WL)` `Wtower2.LiftStage`。
`RESIDUE-PROBLEM.md §4.8` の「どの顔も同じところに落ちる」と一致する。
-/
import Wtower2
import Final

namespace TRIO
namespace L7

open Wset

/-- 1 ブロックの差し替えの性質（**側条件なし**）。 -/
def SubstProp (S : TrioSeq) : Prop :=
  ∀ (p : ℕ) (C : TrioSeq), p < S.length → C ≠ [] → C ∈ Wself →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

/-- 課題 L5 の 1 行の命題（`lean/L5Subst.lean` の `SubstFree` と同じ）。 -/
def SubstFree : Prop := ∀ S : TrioSeq, S ∈ Wself → SubstProp S

/-- `A2'` を回す集合。 -/
def Ysub : Set TrioSeq := {S | SubstProp S}

/-- **`Aop` の節 1 は証明できる。** `|S| ≤ 1` かつ `p < |S|` なら `|S| = 1`,
`p = 0` なので、差し替えの結果は `C` そのもの。 -/
theorem substProp_of_short {S : TrioSeq} (h : S.length ≤ 1) : SubstProp S := by
  intro p C hp hCne hC
  have hp0 : p = 0 := by omega
  have h1 : S.length = 1 := by omega
  subst hp0
  have ht : S.take 0 = [] := by simp
  have hd : S.drop 1 = [] := by
    rw [List.drop_eq_nil_iff]; omega
  rw [ht, hd]
  simpa using hC

/-- **`Aop` の節 2**（未証明）。

上の doc の表のとおり、**clause 1 / mirror / orphan の 3 つは
`Wtower2.subst1g_of_revive` と同じやり方で閉じ、残るのは revival の場合だけ**。
`Wtower2.Subst1gRevive` から側条件 6 本を落とした形にあたる。 -/
def Clause2 : Prop :=
  ∀ (S : TrioSeq), (∀ n : ℕ, 1 ≤ n → SubstProp (S⟦n⟧)) → SubstProp S

/-- **`Aop` の節 3**（未証明）。

`D = S.drop (p+1) ≠ []` なら `graft R z = subst (graft S z) p C`（末尾列が
`S` と `R` で同じなので、`graft` の再基底の量も同じ）で帰納法の仮定が効く。
`D = []` のときは `graft R z` が `C` の末尾を差し替えるので `graft S z` と
直接の関係が無い。 -/
def Clause3 : Prop :=
  ∀ (u m : ℕ) (S : TrioSeq), m < u → domT S m →
    (∀ z ∈ W m, based z → SubstProp (graft S z)) → SubstProp S

/-- **`SubstFree` は節 2 と節 3 に割れる**（節 1 は証明ずみ）。

`Wset.A2'`（最小不動点の帰納原理）を `Ysub` に当てるだけ。 -/
theorem substFree_of_clauses (h2 : Clause2) (h3 : Clause3) : SubstFree := by
  intro S hS
  have key : W (lev S 0) ⊆ Ysub := by
    refine A2' (u := lev S 0) (Y := Ysub) ?_
    intro M hM
    rcases hM with ⟨hlen, -⟩ | hop | ⟨m, hm, hd, hgr⟩
    · exact substProp_of_short hlen
    · exact h2 M hop
    · exact h3 _ m M hm hd hgr
  exact key hS

/-- **したがって 3 行バシクの停止性は節 2 ＋ 節 3 に帰着する。**

`lean/L5Subst.lean` の `TRIO.L5.TRIO_terminates_of_substFree` と同じ形。 -/
theorem TRIO_terminates_of_clauses (h2 : Clause2) (h3 : Clause3) :
    WellFounded stepRel := by
  refine TRIO_terminates_of_revive_self ?_
  intro p S C hS hp hCne hC _ _ _ _ _ _
  exact substFree_of_clauses h2 h3 S hS p C hp hCne hC

end L7
end TRIO

#print axioms TRIO.L7.substProp_of_short
#print axioms TRIO.L7.substFree_of_clauses
#print axioms TRIO.L7.TRIO_terminates_of_clauses
