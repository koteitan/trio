# T0AbsW から t=0 の V3 入口まで

調査対象は現在の `V3TranslationAbsUV3.desc3_of_step_enginesV3U` までの経路。行番号は 2026-11-02 時点。

## 主な経路

| 場所 | 定理・定義 | `Lhd z` の位置 | `T0AbsW` を直接使うか |
|---|---|---|---|
| `Ytosk/V3T0D.lean:579-580` | `T0AbsW` | 展開ごとの `AbsWN` を返す。`Lhd z` は含まない。 | 定義そのもの |
| `Ytosk/V3T0D.lean:773-782` | `t0_dep_lhd` | 結論が `DepX ... b i` なら `Lhd z (valB σ b i) (valB ρ b i)`。 | 直接の引数は `hAbs : AbsWN ...`。上位の `t0_coreG2` が `T0AbsW` を適用して渡す。 |
| `Ytosk/WfDrL4.lean:4042-4071` | `t0_coreG2` | 定理の結論には `Lhd z` の欄はない。内部の `t0_dep_lhd` から `hdl : σ.o d ≤ ρ.o d` を作り、`Good3`、`FrameClosed`、`BumpKidsDec`、`BumpTermDec` の構成に使う（4188-4210 行付近）。 | はい。引数 `hAbsS : T0AbsW` を 4189 行で適用し、`t0_dep_lhd` に渡す。 |
| `Ytosk/V3T0DepS.lean:96-127` | `t0_dep_otS` | 結論の第 2 欄が、`DepX` のとき `Lhd z (valB σ b i) (valB ρ b i)`。加えて `RClaimU` と `REr` の欄を返す。 | 直接の引数は `hAbs : AbsWN ...`。呼び出し側が `T0AbsW` を適用して渡す。 |
| `Ytosk/V3T0DepS.lean:737-767` | `t0_otdS` | 結論の `DepX true` 欄に `Lhd z (σ.o i) (ρ.o i)`、`DepX false` 欄に `Lhd z (σ.v i) (ρ.v i)`。 | はい。1060 行で `hAbsS n ...` を適用して `t0_dep_otS` に渡す。 |
| `Ytosk/WfDrL4.lean:4264-4291` | `t0_otdG2` | `t0_otdS` と同じ T0DF 型の `o` / `v` の `Lhd z` 欄。 | はい。4379 行で `hAbsS n ...` を適用して `t0_dep_otS` に渡す。 |
| `Ytosk/V3T0CarrierV3.lean:134-163` | `t0DF_of_seed_inputs` | 出力 `T0DF` に、各 DepX `o` / `v` の `Lhd z` 欄がある。型の定義は `V3T0TopR.lean:49-55`。 | はい。155 行で `hAbs M ...` を `t0_otdG2` に渡す。 |
| `Ytosk/V3T0CarrierV3.lean:12-124` | `t0_carrierV3` | 自身の結論に `Lhd z` はない。`T0DF` の `Lhd z` から `hdl`（107-108 行）を作り、`t0VSD_atC2` 経由でも使う。 | はい。引数 `hAbW : T0AbsW` を37-39行で `t0_coreG2` に渡す。 |
| `Ytosk/V3T0CarrierV3.lean:168-181` | `expCore0_of_seeds` | 出力 `ExpCoreV3 0` の型に `Lhd z` はない。内部で `t0DF_of_seed_inputs` と `t0_carrierV3` を使う。 | はい。`hAbs` を両方へ渡す（177-179行）。 |
| `Ytosk/V3TranslationAbsUV3.lean:50-52` | `desc3_of_step_enginesV3U` | `Desc3` を返す。`Lhd z` は出力型にない。 | `hAbs` を `expCore0_of_seeds` に渡す。 |

## `t0_dep_otS` の直接の読者

検索した直接呼び出しは次の 3 箇所。

1. `V3T0DepS.t0_otdS`（`V3T0DepS.lean:1059-1070`）。`hdep true` の `Lhd z` を `o` の結論に、`hdep false` の `Lhd z` を `v` の結論に入れる。ほかに `RClaimU` と `REr` も読み取る。
2. `WfDrL4.t0_otdG2`（`WfDrL4.lean:4378-4388`）。同じく `hdep` の `o` / `v` の `Lhd z` を T0DF 型の欄に入れる。これは現在の `t0DF_of_seed_inputs` の経路。
3. 旧経路 `V3T0Bad.t0_otdG`（`V3T0Bad.lean:380-390`）。こちらも `t0_otdG2` と同じ出力形を組み立てる。

また `t0_otdS` を直接呼ぶ旧経路として `V3T0Inv2S.t0DF_ofS`（`V3T0Inv2S.lean:31-44`）がある。現在の V3 入口はこの旧 wrapper ではなく `t0_otdG2` を使う。

## PX 形へ弱めた場合の見込み

`Lhd z` を `Lhd z ∨ (Bd i ∧ Lhd (v(P1 i)))` に替えるだけでは、現在の読者にそのまま渡せない。

- `t0_coreG2` の内部では `t0_dep_lhd` の `Lhd z` から `hdl` を作り、`σ.o d ≤ ρ.o d` として `good3_N_t0`、`frameClosed_N_t0`、`bumpKidsDec_N_t0`、`bumpTermDec_N_t0` へ渡している。PX の右枝から同じ比較を作る橋が別に必要。
- `t0_otdG2` と `t0_otdS` は `t0_dep_otS` の結果を、無条件の `Lhd z` を要求する `T0DF` に格納する。まず出力型を PX 版にし、その先の T0DF 読者を適応する必要がある。
- 具体的な T0DF 読者では、`t0_carrierV3` の `hdl`（107-108 行）が `Lhd z` から値の比較を作る。さらに `t0VSD_atC2`（`V3T0ConsumersV3.lean:119-143`）は、変更した `v c` に対する `Lhd z` を142行で使う。PX 右枝を扱う場合はこの補題も拡張が要る。
- `expCore0_of_seeds` と `desc3_of_step_enginesV3U` の型にある `Lhd z` はないので、直接の問題箇所ではない。変更が必要になるのは、その手前のエンジンと T0DF の読者。

したがって、最初の適応点は `t0_dep_lhd` と `t0_dep_otS` の PX 版だけでなく、`t0_coreG2` と T0DF の下流読者である。`t0_otdS` / `t0DF_ofS` は旧経路にも残っているため、共通の型を変える場合は合わせて確認が必要。
