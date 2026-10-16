# PassRootRes の全数確認

2026-10-15。Lean の `V3ExpT1V.lean` の PassRootRes を、既存の全 10 集合で調べた。抽出や Lhd の近似は使っていない。**有限の測定であり、標準形全体の証明ではない。**

最後の列を x、その行 1 の親を r とする t = 1 の行列だけが対象。r の数える子 c について、c < x、DepX M x false c、cof(last(v(c))) = big(v(r)) を満たすなら、c より前に数える子がないことを確認した。

| 集合 | 入力 | SRO より下 | t = 1 の評価数 | 前件を満たす枠 | 反例 |
|---|---:|---:|---:|---:|---:|
| Cprime | 404051 | 404051 | 195711 | 6971 | 0 |
| t0ext | 181290 | 181287 | 0 | 0 | 0 |
| d3s | 15000 | 15000 | 9103 | 341 | 0 |
| deep2 | 128150 | 128150 | 79172 | 2938 | 0 |
| deep3 | 123493 | 123493 | 74939 | 2868 | 0 |
| ext1 | 1082667 | 1082667 | 479397 | 315 | 0 |
| ext1x | 119974 | 119974 | 64453 | 188 | 0 |
| t2ext | 1207960 | 1207960 | 631354 | 21572 | 0 |
| ext2 | 1497986 | 1497986 | 854899 | 4085 | 0 |
| expP | 614584 | 614584 | 292846 | 8376 | 0 |
| 合計 | 5375155 | 5375152 | 2681874 | 47654 | 0 |

集合間の重複は除いていない。SRO 以上の 3 行列は対象外。評価の失敗は 0。t = 1 以外の行列にはこの条件を課していない。

数える子は Lean の CL の順序に対応させた。DepX は `tools/probe_inv2.py` の 6 構成子の最小閉包を共用する。定義の前件に共終数の条件を含む枠を数え、その子の CL 内の添字が 0 であることを調べた。

検出の確認: 非標準の対照行列を 1 個用意し、このプログラムが PassRootRes 違反を 1 件検出することと、yaBMS の bms -s が 0 を返すことも確認した。対照行列は JSON に全列を記録し、上の標準形の集計には含めていない。

再現コマンド:

```sh
nice -n 15 python3 tools/probe_passroot.py --workers 4 --output tmp/ytosk-handoff/results/passroot
```

元のデータは task.md の集合一覧を参照。機械可読の結果は [passroot-measurement.json](passroot-measurement.json)。生の各集合の結果は `tmp/ytosk-handoff/results/passroot/` に出力する。

Lean では `expStep_vsmallF_pass_inv3V2` が PassRootRes を仮定して VSmallF の保存を出す。`qr_vsmallF_final_inv3V2`・`qn_vsmallF_final_inv3V2` は、その経路を展開の両入口へ接続する。PassRootRes 自体は未証明のまま。
