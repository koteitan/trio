# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)`。
証明中の行（#14）も同じ壁から出る。

## 目標行までの緑の還元（全部 Lean で緑）

    R376_of_RunAll : RunAll → R373 (5,3,0) ∈ W 0
      RunAll := ∀ q ks, APd (true :: ks) (stk q)
      （全部 nil の走り stk q = (l+1,2,0)(l+2,2,0)...(l+q,2,0) が 1 の枠の直上で良い）

    RunAll_of_SNilT : SNilT → RunAll        （走りの長さ q の帰納法 SG_stkS）
      SNilT := ∀ ks, SG (true :: ks) nil
    SNilT_of_SPayF  : SPayF → SNilT
      SPayF := ∀ ks V, JkA V → SG (false::ks) V → SPy (false::ks) V   （2 の枠の直上の荷）
    SPayF_of_SHtow  : SHtow → SPayF
      SHtow := ∀ ks V, JkA V → SG (false::ks) V → ∀ D0, SCtx ks D0 →
                 ∀ N, VCh V N → GOK (plug D0 (two N V))              ★ 最前線

    RunAll_of_ZStep : ZStep → RunAll        （別の言い方、同じくらい細かい）
      ZT   := nil | pay X C | one U X（2 の記録を含まない木）
      ZStep := ∀ ctx, ZOk ctx → ZG ctx → ZG (ctx ++ [ftwo nil])

    R14_of_SHtow : SHtow → R375m (5,2,0) ∈ W 0   （証明中の行も同じ）

## `SHtow` の中身

`VCh V N` は水平鎖 `N = nil | two N' (pay V Y)`。`N = nil` は緑（`SHtow_nil`）。
残るのは「2 の記録の左の兄弟を `nil` から鎖 `two N' (pay V Y)` に広げる」1 手。
語で見ると、同じ高さ `l+1` に 2 の記録が並び、各記録の右に `jk1 (l+1) V` と荷が付く形。
A2' の複製鎖がこの形を出すので、鎖の右端に `V` を載せた木が要る。

## 何度も同じところで割れている理由（形のリストが伸びる）

走りの階段は文脈を `[ftwo N] ++ ... ++ [fone ...]` と伸ばす。族の側条件は
「`ks` に `true` を前置した形」でしか木の良さをくれないのに、階段は
`false` を前置した形（2 の枠を 1 枚増やした形）を要求する。
`APd` / `SCtx` / `RCtx` / `ECtx` / `WPd` のどれでもここで割れる。

## 既存の族の一覧（新しい族を作る前に必ずここを見る）

| 族 | 文脈 | 2 の枠 | 荷 | 空木 | 走り |
|---|---|---|---|---|---|
| `APd` / `GCtx` | Bool 列 | `[fone U, ftwo N]` 対で 1 枚 | 緑 | 緑 | 表現できない |
| `SCtx` / `SG` | Bool 列 | `ftwo nil` 何枚でも | `SPayF` | `SNilT` | `SG_stkS` で長さ帰納（緑） |
| `RCtx` / `RG` | Bool 列 | `ftwo N` 何枚でも（∀j 条件） | 緑（`RP_of_RG`） | `RG_nil_true` 緑 | `RSp (false::ks)` が偽 |
| `ZT` / `ZG` | 生 `List Frm` | `ftwo nil` | — | — | `ZStep` |
| `ECtx` / `EOk` | ℕ×ℕ列 | 1 形 | 緑 | 1 の枠なら緑 | `ERun` |
| `FCtx` / `FOk` | ℕ | 帰納的閉包 | 緑 | 未 | 緑 |
| `GCx` / `QOk` | ℕ | 吊るしも側条件 | `QPayAll` | 緑 | 緑 |
| `HGx` / `GAll` | 生 | `ftwo A`（点ごと `GOK`） | — | `GNilO`/`GNilT` 相互再帰 | — |
| `RCx` / `RNil` | 生 | `ftwo nil` 何枚でも | `RHang` | `RNil` | `GOK_stk_step`（緑、長さ帰納） |
| `WPd` / `WFd` | ℕ列（予算） | — | — | — | 予算が鎖の長さに追いつかない（死） |

`RCx` は `SCtx` の再発見（2026-09-12）。`GOK_stk_RCx` は `SG_stkS` と同じ内容。

## 走りの道具（`GOK` 側、全部緑）

    GOK_twoNilW_gen    : two N nil          ← 塔 (fone N)^m N
    GOK_twoTwoNilW_gen : two N (two Wl nil) ← 階段 nstN2 N Wl k
    GOK_stkW_gen       : two N (stkP p (two nil nil)) ← 階段 nstQ N p k
    GOK_runGNil_gen    : 一般兄弟の走り（runJ / unR / nstR / snocR_of_tower）

どれも文脈が `ctx0 ++ [fone V]`（1 の枠止まり）であることを要求する。
2 の枠止まりの文脈のための道具は無い。
