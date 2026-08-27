/-
課題 L8: **多ブロックの差し替え**に一般化した形と、その帰着。

課題 L7 で分かったこと: `SubstFree` を `W` の最小不動点の帰納で回すと、
`revival` の場合で `R⟦n⟧` が `S⟦n⟧` への **1 ブロックの差し替えにならない**
（`C` を含む区間の `n` 個のコピーになるので**多ブロック**になる）。
そこで帰納の不変量を多ブロックに取る、というのが次の手である。

    SubstMulti := 位置が真に減少する列 `ps = [(p₁,C₁), …, (pₖ,Cₖ)]`
                  （`p₁ > p₂ > … > pₖ`、どの `Cᵢ` も `Wself`）について
                  `S` の各 `pᵢ` を `Cᵢ` に同時に差し替えたものも `Wself`

位置が真に減少するので右から順に 1 つずつ当てれば同時差し替えと同じ
（後ろを差し替えても前の位置は動かない）。

## ⚠ ただしこの道は **循環する**（課題 L8 の判定）

多ブロックの帰納で残るのは `i1 = 2`（行 2 の崩壊）の場合だけで、そこで要るのは

    C ∈ Wself → Lift1 C d ∈ Wself          （= `Wtower2.LiftStage` の `Wself` 版）

ところが `LiftStage` は**残核から導出されている**:

    Wtower2.substClosedG_of_subst1g      : Subst1g → SubstClosedG
    Wtower2.shiftTowerClosedS_of_substG  : SubstClosedG → ShiftTowerClosedS   (:3615)
    Wtower2.liftStageParented_of_tower   : ShiftTowerClosedS → LiftStageParented (:1800)
    Wtower2.liftStage_of_parented        : LiftStageParented → LiftStage      (:560)

つまり **残核 → LiftStage** が既にある。ここで **LiftStage → 残核** を足すと
`残核 ⟺ LiftStage` の輪が閉じるだけである。`RESIDUE-PROBLEM.md §5` が
「**多ブロック版に一般化して帰納する**」を「`TowerExp` 経由で自分に戻る」
として却下しているのは、まさにこれ。

しかも `LiftStage` はさらに先まで削られていて（`liftStage_of_wconvex'`:
`WConvex → LiftStage`）、その `WConvex` の素直な `oper` 帰納は**反証済み**、
そして `Wtower2.lean:477` 付近の doc によれば

> `le1` 錐 ⊆ `amin` 錐 は**無条件**。逆包含（`TieFree`）が成り立てば (WL) は
> その場で無料

で、`TieFree`（**行 1 のタイが無い**）は `PROOF-STATUS.md §5.7` によれば
**ST_TS 到達可能性そのもの**である。

⟹ **この file は「多ブロックに一般化しても輪が閉じるだけ」を記録するためのもの。**
下の鎖は機械検査ずみだが、`SubstMulti` を証明する道は開いていない。

## 測定（`lean/L1-NOTES.md` 課題 L8）

* `SubstMulti`（2〜3 ブロック同時、深さもレベルも自由）… 下のノートを見よ
* `C ∈ Wself → Lift1 C d ∈ Wself` … **138708 例 判定 / 違反 0**
  （陽性対照: 段を 1 つ下げると **138719/138719 で違反**）
-/
import Wtower2
import Final

namespace TRIO
namespace L8

open Wset

/-- 1 か所の差し替え。 -/
def substAt (S : TrioSeq) (p : ℕ) (C : TrioSeq) : TrioSeq :=
  S.take p ++ C ++ S.drop (p + 1)

/-- 位置が真に減少する列にそって、右から順に差し替える（＝同時差し替え）。 -/
def substMany : TrioSeq → List (ℕ × TrioSeq) → TrioSeq
  | S, [] => S
  | S, (p, C) :: r => substMany (substAt S p C) r

/-- 1 ブロックの差し替え（課題 L5 / L7 の `SubstFree`）。 -/
def SubstFree : Prop :=
  ∀ (p : ℕ) (S C : TrioSeq), S ∈ Wself → p < S.length → C ≠ [] → C ∈ Wself →
    substAt S p C ∈ Wself

/-- **多ブロックの差し替え**。位置は真に減少する（＝相異なる位置の同時差し替え）。 -/
def SubstMulti : Prop :=
  ∀ (S : TrioSeq) (ps : List (ℕ × TrioSeq)), S ∈ Wself →
    ps.IsChain (fun a b => b.1 < a.1) →
    (∀ q ∈ ps, q.1 < S.length ∧ q.2 ≠ [] ∧ q.2 ∈ Wself) →
    substMany S ps ∈ Wself

/-- **多ブロックは 1 ブロックを含む**（`k = 1` の場合）。 -/
theorem substFree_of_multi (h : SubstMulti) : SubstFree := by
  intro p S C hS hp hCne hC
  have := h S [(p, C)] hS (by simp) ?_
  · simpa [substMany] using this
  · intro q hq
    rcases List.mem_singleton.mp hq with rfl
    exact ⟨hp, hCne, hC⟩

/-- **したがって 3 行バシク（`z<2`）の停止性は `SubstMulti` からも出る。**

`lean/L5Subst.lean` の `TRIO.L5.TRIO_terminates_of_substFree` と同じ配線。 -/
theorem TRIO_terminates_of_multi (h : SubstMulti) : WellFounded stepRel := by
  refine TRIO_terminates_of_revive_self ?_
  intro p S C hS hp hCne hC _ _ _ _ _ _
  exact substFree_of_multi h p S C hS hp hCne hC

/-! ### 逆向き（`SubstFree → SubstMulti`）について

右から順に 1 つずつ当てるだけなので成り立つ（位置が真に減少するので、後ろを
差し替えても前の位置は動かず、`|C| ≥ 1` なので長さも減らない）。
プロジェクト側の同じ議論は `Wtower2.substClosedG_of_subst1g`
（`Subst1g → SubstClosedG`）。

⟹ **`SubstMulti` と `SubstFree` は命題としては同値**である。強くなるのは
「帰納法の不変量として使うとき」だけで、そこは上の doc のとおり `LiftStage` に
落ちて輪が閉じる。だから `SubstMulti` を目標に取り替えても命題は 1 ミリも
弱くならない。 -/

end L8
end TRIO

#print axioms TRIO.L8.substFree_of_multi
#print axioms TRIO.L8.TRIO_terminates_of_multi
