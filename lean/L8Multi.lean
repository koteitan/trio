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

## ⚠ この道は 2 つの理由で通らない

### 理由 1（課題 L9 で測って判明）: そもそも帰納法の仮定が届かない

課題 L7/L8 では「`i1 <= 1` なら `R⟦n⟧` の中の `C` のコピーは行 0 ずらしちょうど
（57066/57066）だから、多ブロック化すれば帰納法の仮定で閉じる」と書いた。
**これは早とちりだった。** 「ブロックが行 0 ずらしである」ことと
「`R⟦n⟧` が `S⟦n⟧` への差し替えになっている」ことは別である。

実測（`i1 <= 1` の revival、`n = 1,2,3` の各回を 1 件、69981 件）:

| | 件数 | |
|---|---|---|
| `R⟦n⟧` が `S⟦n⟧` への多ブロック差し替えになる | 43254 | **61%** |
| `S` が展開しない（`R` はする） | 12132 | 17% |
| バッドルートが `C` の中に移った | 7447 | 10% |
| バッドルートの位置が違う（その他） | 766 | 1% |
| その他 | 6382 | 9% |

⟹ **`i1 <= 1` の revival でも 39% は多ブロックの帰納法の仮定が届かない。**

原因は 1 行で言える: **差し替えはバッドルートを動かす。**
挿入した `C` の柱が末尾列の新しい行 0 の親になってしまうと、`R` のコピー区間は
`C` の内側から始まり、`S⟦n⟧` にはそれに対応するものが無い。例:

    S = [(0,4,0), (3,0,0)]   p = 0   C = [(0,2,1), (1,1,1), (2,0,0)]
    R = [(0,2,1), (1,1,1), (2,0,0), (3,0,0)]
    S のバッドルート = 0（= p 自身）   R のバッドルート = 2（= C の中）

### 理由 2: 仮に届いても循環する

多ブロックの帰納で残るのは `i1 = 2` の場合で、そこで要るのはちょうど

    C ∈ Wself → Lift1 C d ∈ Wself          （= `Wtower2.LiftStage` の `Wself` 版）

ところが `LiftStage` は**残核から導出されている**:

    Wtower2.substClosedG_of_subst1g      : Subst1g → SubstClosedG
    Wtower2.shiftTowerClosedS_of_substG  : SubstClosedG → ShiftTowerClosedS   (:3615)
    Wtower2.liftStageParented_of_tower   : ShiftTowerClosedS → LiftStageParented (:1800)
    Wtower2.liftStage_of_parented        : LiftStageParented → LiftStage      (:560)

`LiftStage → 残核` を足すと `残核 ⟺ LiftStage` の輪が閉じるだけである。
`RESIDUE-PROBLEM.md §5` が「**多ブロック版に一般化して帰納する**」を
「`TowerExp` 経由で自分に戻る」として却下しているのはこれ。

⟹ **この file は「多ブロックに一般化しても駄目」を記録するためのもの。**
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
