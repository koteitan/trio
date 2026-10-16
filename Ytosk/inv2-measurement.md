# Inv3V2 の再測定

再開時に未測定だった AbsUS・TPLoS・TrigS・VSmallRAll を調べる。
スクリプトは [tools/probe_inv2.py](../tools/probe_inv2.py)。古い一時ディレクトリへの依存はない。

```bash
nice -n 15 python3 tools/probe_inv2.py \
  d3s deep2 deep3 Cprime t0ext ext1 ext1x t2ext ext2 expP \
  --output tmp/ytosk-handoff/results/inv2
```

TrigS が偽と判明したため、反例が出た集合を修正版で全数測定し直す。
元の TrigS が全数で成立した集合では、それより弱い TrigS0 も成立する。
この含意は `trigS0_of_trigS` で Lean でも確認。したがって反例ゼロの集合の再走査は不要。
この 2 本は同時に実行しない。

```bash
nice -n 15 python3 tools/probe_trigs0.py t2ext expP \
  --output tmp/ytosk-handoff/results/trigs0
```

全数測定。SRO = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0) より下に絞る。
必須の 9 集合に ext1x も加えた 10 集合。Python のワーカーは 4 個。
結果の JSON は集合ごとに保存する。入力数・測定数・除外数・評価失敗・条件の件数・反例を記録する。
評価が失敗した行列は、条件が成立したものとして数えない。

## Lean との対応

| Python | Lean | 対応の確認 |
|---|---|---|
| `dependencies` | V3Dep の `DepX` | leaf・ochild・ov・vpar・vupg・vbump の最小閉包 |
| `C.vOpt1(i)` | `vOpt ρ (par M 1 i)` | 親がなければ 0 |
| `seed = T.o(r)` | `(drop1 M x rk).o r` | 接頭辞を評価。評価の一意性による同じ値 |
| AbsUS | V3SeedFields の `AbsUS` | q != r、v の DepX、upg、穴の段 = mu、種で吸収 |
| TPLoS | V3SeedFields の `TPLoS` | q != r、o の DepX、低い部分 = 0、最後の添字に穴、穴の段 = mu |
| TrigS | V3Inv2 の `TrigS` | q = r、種 < psi_mu(1)、数える DepX の子、書き換えの両条件 |
| TrigS0 | V3TrigSeed の `TrigS0` | TrigS と同じ前件に、子 c の dOf = 0 を追加 |
| `lift_counts` | V3QRIdx の `DepL`・`dOf` | 6 構成子に loQ・lbQ の重みを付け、最小回数を固定点で求める。v が到達可能なら v の回数を優先 |
| `paths` | V3VSRAll の `PathLvAll` | 全ての数える子で top と step。親 < 子なので左から完全に計算 |
| VSmallRAll | V3VSRAll の `VSmallRAll` | 高い部分 != 0、u <= v(k)、全ての `comps u s` を検査 |

前件も Lean の定義に合わせる。AbsUS・TPLoS では q = r の枠や別の段の穴を数えない。
TrigS では種の上限を満たさない枠を数えない。
VSmallRAll の道は、途中の枠の高い部分が 0 でも運ぶ。
`Lhd` の標本近似は、この測定では使用しない。

表の条件件数の単位は、AbsUS は加数、VSmallRAll は成分、TPLoS・TrigS は枠。
前件が立たない場合、または加数・成分が空の場合、条件は空で成立する。

TrigS0 が必要な範囲であることは `V3TrigSeed.hYB_of_trigS0` で証明済み。
実際の消費者は `m + dOf c` 番目の鎖の項を使う。正の回数なら TP1C で足りる。
測定後に TrigS0 の定義を V3Inv2 から V3TrigSeed、AbsDS・AbsUS・TPLoS を V3SeedFields に移した。条件そのものは変えていない。JSON の定義ファイル名は測定時点の記録。

## 結果

全 10 集合の全数確認が完了。AbsUS・TPLoS・VSmallRAll・修正版 TrigS0 は反例ゼロ。
評価失敗・種の評価失敗もゼロ。T0Ext だけ、SRO 以上の 3 行列を除外した。
入力は合計 5,375,155、SRO より下の測定行列は合計 5,375,152。集合間の重複を含む。
機械で読める全結果は [inv2-measurement.json](inv2-measurement.json)。

| 集合 | 測定行列 | AbsUS の加数 | TPLoS の枠 | VSmallRAll の成分 | 旧 TrigS の枠 | 旧 TrigS の反例 |
|---|---:|---:|---:|---:|---:|---:|
| Cprime | 404,051 | 398 | 110,567 | 2,244,252 | 33,749 | 0 |
| t0ext | 181,287 | 0 | 0 | 1,196,689 | 0 | 0 |
| d3s | 15,000 | 233 | 18,669 | 134,137 | 2,017 | 0 |
| deep2 | 128,150 | 1,790 | 156,467 | 1,207,899 | 17,110 | 0 |
| deep3 | 123,493 | 1,726 | 154,154 | 1,111,864 | 15,623 | 0 |
| ext1 | 1,082,667 | 2 | 46,690 | 4,605,591 | 15,904 | 0 |
| ext1x | 119,974 | 57 | 11,569 | 936,699 | 12,714 | 0 |
| t2ext | 1,207,960 | 5,862 | 390,133 | 11,130,033 | 231,592 | 1 |
| ext2 | 1,497,986 | 29,063 | 779,462 | 15,542,051 | 80,174 | 0 |
| expP | 614,584 | 4,734 | 152,140 | 10,219,525 | 118,808 | 1 |

TrigS0 は、旧 TrigS に反例のある T2Ext・expP を全数再走査した。
それ以外の 8 集合は、旧 TrigS の全数結果と `trigS0_of_trigS` の含意による確認。

| 再走査した集合 | 入力行列 | TrigS0 の枠 | TrigS0 の反例 |
|---|---:|---:|---:|
| t2ext | 1,207,960 | 132,229 | 0 |
| expP | 614,584 | 68,892 | 0 |

旧 TrigS の反例は 2 集合に含まれる同じ行列・同じ枠。子 c = 22 の dOf は 2。
修正版の全数走査でも旧 TrigS の件数と反例数は最初の測定と一致した。
行列の全体と反例の値は [desc.md](desc.md) の「TrigS の反例と TrigS0 への修正」を参照。

測定は有限の集合での確認であり、全ての標準形での証明ではない。
