# 壁

## 目標（シート行376）

    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)

## 行376 までの緑の還元（2026-09-12 に大幅に短くなった）

    R376_of_BdAll : BdAll → R373 (5,3,0) ∈ W 0
      BdAll := ∀ j m, GOK (bdA (List.replicate m j))        ★これ 1 本
      bdA [] = nil ;  bdA (j::js) = one nil (stkP j (bdA js))

    R376_of_StkL  : StkL → 行376
      StkL := ∀ n, GOK (one nil (stk n))
      StkL_of_BdAll : BdAll → StkL   （`GOK_runNil_gen` の階段）

`j = 0` と `j = 1`（`GOK_bdA1`）は緑。**`j ≥ 2` だけが壁**。
語で見ると `bdA (2::js)` は `(l+1,1,0)(l+2,2,0)(l+3,2,0)...`、つまり走り 2 連。

**文脈の量化は要らない。** `tw_R344_42R` が `RunAll` から使っていたのは
`GOK (one nil (stk n))` だけで、`RunAll`（`∀ q ks, APd (true::ks) (stk q)`）は
必要より強い条件だった（`StkL_of_RunAll` で片方向だけ）。

## 2026-09-12 に閉じた壁

- **`TowOk`（#14 の壁）は既に緑だった。** `TowOkM m : ∀ n, GOK (one nil (two nil (TWm m n)))`
  は `WPd` 層で無条件に緑で、`TWm_one : TWm 1 n = TW n`。
  `TowOk_green` / `R14_mem_green : R375m (5,2,0) ∈ W 0` は**無条件**。
- **`GOK T6`（走り 2 連の直上に荷）**。
  `T6 = one nil (two nil (two nil (pay nil [(0,0,0)])))`、
  `U375a6 = (1,1,0) :: wordJ 1 1 [T6]`、`R600 = R338 ++ U375a6`。
  `SegA_U375a6`（`seg` の段、緑）と同じ `flat_mem''` の議論
  （塔 `(l+4,2,0)^n` を平らにして `(l+5,0,0)`）が `pk` と `pu` でも回る。
  `T6` は `JkOk` でない（走り 2 連）ので `GOK_all` では出ない。

## 「字」と「文脈」は難しさが違う

`GOK T`（T を語の右に字として継ぐ）は `flat_mem''` / `snocY_mem` の塔で直接押せる。
`APd ks X` / `SG ks X`（T を文脈の中に差す）は族の側条件が要り、階段が形のリストを
伸ばすところで割れる。**同じ「走り 2 連」でも、字なら通り（`GOK T6`）、
文脈なら通らない（`BdAll` の `j ≥ 2`）。**
新しい壁を立てるときは、まず「字の主張に落ちないか」を見る。

## もう 1 つの壁の最小形：`ZApp2`（いま開いている最小の行列）

    Pay2 := ∀ B, Bok B → GOK (Wall2 B)
      Wall2 B = one nil (two nil (two nil (pay nil B)))   （幅 2 の走りの上に荷）
    Pay2_of_ZApp2 : ZApp2 → Pay2                          （`PZ_cons`。荷の W 帰納は済み）
      ZApp2 := ZAppend [fone nil, ftwo nil] nil
             = ∀ M, JkA M → GOK (one nil (two nil M)) → GOK (one nil (two nil (two M nil)))
    R375m61_of_ZApp2 : ZApp2 → R375m (6,1,0) ∈ W 0

底は緑: `Wall2 []`（語が `one nil (stk 2)` と同じ）、`Wall2 [(0,0,0)] = T6`（`GOK_T6`）。
残るのは「2 の記録の左の兄弟を `nil` から一般の良い木 `M` に広げる」1 手。
`PZ_cons` の中で `M` は水平鎖 `twoIt nil (pay nil B') n` の元として現れる。

`Pay2` が出れば `Wall2 B` が**いまで一番強い字**になり（`T6 = Wall2 [(0,0,0)]` が
既に一番強い）、証明済みも一気に大きくなる。

## 台座と junk の差し替え（証明済みを増やす安い道）

    Rz1 ws  = R338 (1,1,0) ++ wordJ 1 1 ws ++ (2,2,1)      RunA 0 1（緑、ws は任意の良い語）
    T6w k   = T6 を k 個            → 台座が k 方向に無限
    Rz1j k ws = Rz1 (T6w k) (2,2,0) ++ wordJ 2 2 ws        PkGA 2
    LadB Y n  = Y (3,3,0)(4,4,1)(4,4,0)(5,5,1)...          PU の梯子

junk に入れられる `GoodFb` 族は `Zw ⊂ wordC ⊂ wordJ`（木の語、`GOK_all` + `GOK T6`）。
大小は `bms -c` で必ず測る。実測では `k`（台座の `T6` の本数）が一番強い。

## 既存の族の一覧（新しい族を作る前に必ずここを見る）

| 族 | 文脈 | 2 の枠 | 荷 | 空木 | 走り |
|---|---|---|---|---|---|
| `APd` / `GCtx` | Bool 列 | `[fone U, ftwo N]` 対で 1 枚 | 緑 | 緑 | 表現できない |
| `SCtx` / `SG` | Bool 列 | `ftwo nil` 何枚でも | `SPayF` | `SNilT` | `SG_stkS`（長さ帰納、緑） |
| `RCtx` / `RG` | Bool 列 | `ftwo N`（∀j 条件） | 緑 | 緑 | `RSp (false::ks)` が偽 |
| `ZT` / `ZG` | 生 | `ftwo nil` | — | — | `ZStep` |
| `ECtx` / `FCtx` / `GCx` / `HGx` / `RCx` | 生・ℕ 列 | いろいろ | — | — | 追記315 の表 |
| `WPd` / `WFd` | ℕ 列（予算） | — | — | — | 予算が鎖に追いつかない（死） |

## 走りの道具（`GOK` 側、全部緑）

    GOK_twoNilW_gen    : two N nil                    ← 塔 (fone N)^m N
    GOK_twoTwoNilW_gen : two N (two Wl nil)           ← 階段 nstN2
    GOK_stkW_gen       : two N (stkP p (two nil nil)) ← 階段 nstQ
    GOK_runNil_gen     : one V (stkP j (two A nil))   ← 階段 Trm A ([(V,j)] ++ (A,j)^i)
    GOK_runGNil_gen    : 一般兄弟の走り（runJ / unR / nstR）

`GOK_runNil_gen` の階段が `bdA (replicate m j)` なので、`BdAll` が最後の 1 本。
