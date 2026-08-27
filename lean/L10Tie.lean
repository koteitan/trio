/-
課題 L10: **`TieFree` は構文的不変量にならない**（`oper` も `cons` も破る）。
あわせて「標準形ではタイが起きない」という観察が**`TieFree` については空虚**で
あることの構造的な理由（根の 3 行が全部 0）を証明する。

## `TieFree` とは（`Wtower2.lean:59`）

    coneV A v j  := ∀ y, y は j の行 0 祖先 → v < entry A 1 y
    TieFree X    := ∀ j, coneV X (entry X 1 0 - 1) j → le1 X 0 j

`Wtower2.liftStage_of_tieFree` は**証明ずみ**で、`1 ≤ entry X 1 0` と `TieFree X`
があれば `(WL)` はその場で無料になる。だから `TieFree` を構文的な不変量として
立てられれば大きい。**が、立たない。**

## 測定（`lean/L1-NOTES.md` 課題 L10）

    陽性対照   乱択列 60000 個のうち TieFree が偽 18904 個（31%）
    対角       v = 0..11 の 12 個すべて TieFree
    **oper**   TieFree な列から 393438 回展開して **34330 回破れる（8.7%）**
    take       69585 / 69585 保つ
    dropLast   69585 / 69585 保つ
    **cons**   `(0,v,z) :: (行 0 を +1 した M)` は **34813 / 69585 で破れる（50%）**
    drop       10312 / 69585 で破れる

`oper` の最小の反例:

    M = [(0,1,1), (2,3,0)]        TieFree
    M⟦2⟧ = [(0,1,1), (2,1,1)]     **破れる**

`M` の末尾列 `(2,3,0)` は `srow = 1`、その行 1 の親は根（行 1 が `1 < 3`）。
だから `j0 = 0`, `d0 = 2`, `d1 = 0` でコピーされる区間は根そのもの。
コピー 1 は根の行 1 をそのまま持つので、**根とのタイが生まれる**
（`nextrel1 (M⟦2⟧) 0 1` が `1 < 1` を要求して偽）。

`cons` の反例（`Wstar` の操作そのもの）:

    M = [(0,2,1), (4,1,0)]                    TieFree
    (0,2,0) :: 行 0 を +1 した M = [(0,2,0), (1,2,1), (5,1,0)]   **破れる**

`Wstar` は `∀ v z a` で `v` を**全部**走るので、`v` が `R` の行 1 の値と
ぶつかった瞬間にタイができる。⟹ **`W` の機構を `TieFree` に制限できない。**

## 「標準形ではタイが起きない」は `TieFree` については空虚

下で証明するとおり、**BMS 3 行標準形の根は 3 行とも 0** である。
すると `entry M 1 0 - 1 = 0` なので `coneV M 0 j` は「`j` の行 0 祖先が全部
行 1 で正」を要求するが、根はそれを満たさない。実測でも BM4 の展開閉包
2473 個は**全部 `entry M 1 0 = 0`** だった。

⟹ `TieFree` が中身を持つのは**根の行 1 が 1 以上のとき**、つまり
`Wstar` の `(0,v,z) :: R`（`v ≥ 1`）や悪い部分の**部分ブロック**に対してだけ。
全体の標準形を測っても `TieFree` については何も言えない。
（`Wtower2.lean:98` 付近の doc が「実 ST_TS では行 2 崩壊の**悪い部分**の
53634/53642 が窓を満たす」と**悪い部分**について書いているのはこのため。）
-/
import Wtower2

namespace TRIO
namespace L10

open Wset

/-- **標準形の根は 3 行とも 0。** `oper_take_prefix`（コピー 0 はずれない）から。 -/
theorem entry_root_ST_TS {M : TrioSeq} (h : ST_TS M) (i : ℕ) : entry M i 0 = 0 := by
  induction h with
  | diag v =>
      rw [diagSeqT_cons (Nat.zero_le v)]
      unfold entry
      simp
  | @oper N n hN hn ih =>
      rcases Nat.lt_or_ge 1 N.length with hL | hL
      · have htk : (N⟦n⟧).take 1 = N.take 1 := oper_take_prefix hL hn (by omega)
        have e1 : entry (N⟦n⟧) i 0 = entry ((N⟦n⟧).take 1) i 0 :=
          (Wset.entry_take (X := N⟦n⟧) (l := 1) (i := i) (by omega)).symm
        have e2 : entry (N.take 1) i 0 = entry N i 0 :=
          Wset.entry_take (X := N) (l := 1) (i := i) (by omega)
        rw [e1, htk, e2]
        exact ih
      · rw [oper_eq_self_of_short n (by omega)]
        exact ih

theorem entry1_root_ST_TS {M : TrioSeq} (h : ST_TS M) : entry M 1 0 = 0 :=
  entry_root_ST_TS h 1

/-- **系: 標準形では `TieFree` の前提 `coneV` が根で落ちる。**

`coneV M (entry M 1 0 - 1) j = coneV M 0 j` は「`j` の行 0 祖先が全部行 1 で
正」を要求する。根は行 1 が 0 なので、根が `j` の行 0 祖先であるかぎり前提は偽。
とくに `j = 0` では（`ReflTransGen` は反射的なので）つねに偽。

⟹ **全体の標準形について `TieFree` を測っても中身は無い。**
`Wtower2.liftStage_of_tieFree` が `1 ≤ entry X 1 0` を要求しているのは
まさにこのため。 -/
theorem coneV_root_false_ST_TS {M : TrioSeq} (h : ST_TS M) :
    ¬ coneV M (entry M 1 0 - 1) 0 := by
  intro hc
  have := hc 0 Relation.ReflTransGen.refl
  rw [entry1_root_ST_TS h] at this
  omega

end L10
end TRIO

#print axioms TRIO.L10.entry_root_ST_TS
#print axioms TRIO.L10.coneV_root_false_ST_TS
