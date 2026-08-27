/-
課題 L5 の副産物: 残核 `Subst1gReviveSelf` を**仮定を全部落とした一般形**
から導く。

`tools/probe_residue_cover.py` の測定（`lean/L1-NOTES.md` 課題 L5）で、残核の
6 つの側条件

    lev (C 0) <= lev S p          （ブロックのレベル）
    entry C 0 0 = entry S 0 p     （頭の深さ）
    ∀ q ∈ C, entry S 0 p <= q.1   （深さ）
    (i) R の末尾列が R の中で親を持つ
    (ii) その列が自分のブロックでは孤児
    (iii) R[:-1] に行 2 > 0 の列がある

が **1 本も真理値に効いていない**ことが分かった（1 本ずつ落として 10148 /
28383 / 8720 / 3160 / 2632 / 739 例、全部まとめて落として 156247 例、
さらに深さもレベルも自由にした反証型ハントで 164760 例、**いずれも違反 0**）。

そこで残るのは次の 1 行の命題だけになる。

    Wself は、任意の位置で任意の Wself ブロックに差し替えても閉じている

これは残核より**真に強い**（仮定を 6 本落としたのだから）。だから
`Subst1gReviveSelf` はここから**仮定を忘れるだけ**で出る（下の 3 行）。
`TRIO_terminates_of_revive_self` と合わせて、3 行バシクの停止性は
この 1 行に帰着する。

⚠ 強い命題が易しいとは限らない。狙いは「帰納のたびに側条件を建て直す手間が
消えること」で、`GRAFTALL-PLAN.md:3332` が深さ条件を厳格から非厳格に弱めた
（`oper` が厳格性を保たないから）のと同じ向きの、その極限である。
-/
import Wtower2
import Final

namespace TRIO
namespace L5

open Wset

/-- **(SUBST-FREE)** — `Wself` は任意の位置での任意の `Wself` ブロックの
差し替えで閉じている。残核 `Subst1gReviveSelf` の仮定を 6 本とも落とした形。

測定: `tools/probe_residue_cover.py`（seed 20260828, 200000 サンプル）で
**164760 例 判定 / 違反 0**。内訳は 頭の深さが違う 137954 / `C` に浅い列あり
75187 / `lev (C 0) > lev S p` 74261 / `R` に行 2 の列あり 155319 /
行 2 の崩壊 11047 / 永久孤児 `(x,0,1)` あり 68552。 -/
def SubstFree : Prop :=
  ∀ (p : ℕ) (S C : TrioSeq), S ∈ Wself → p < S.length → C ≠ [] →
    C ∈ Wself →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

/-- **一般形は残核を導く**（仮定を 6 本忘れるだけ）。 -/
theorem subst1gReviveSelf_of_free (h : SubstFree) : Subst1gReviveSelf := by
  intro p S C hS hp hCne hC _ _ _ _ _ _
  exact h p S C hS hp hCne hC

/-- **したがって 3 行バシク（`z<2` 断片）の停止性は (SUBST-FREE) 1 本に帰着する。** -/
theorem TRIO_terminates_of_substFree (h : SubstFree) : WellFounded stepRel :=
  TRIO_terminates_of_revive_self (subst1gReviveSelf_of_free h)

/-- 無限展開列が無いこと。 -/
theorem no_infinite_expansion_of_substFree (h : SubstFree) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_revive_self (subst1gReviveSelf_of_free h)

end L5
end TRIO

#print axioms TRIO.L5.subst1gReviveSelf_of_free
#print axioms TRIO.L5.TRIO_terminates_of_substFree
#print axioms TRIO.L5.no_infinite_expansion_of_substFree
