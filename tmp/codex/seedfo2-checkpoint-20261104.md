# G6 の区切り

## Lean

新規 `Ytosk/lean/Ytosk/V3SeedFO2.lean`。
既存Leanは変更せず、lakefile.tomlにrootを1個追加。

- `cl_C_q`: C配置でCL_N(q)=[r+L]。unもC2の残りも不要。
- `seedFO_C_q`: qの前の状態は空。Good3 Nのot_vだけでQFOを閉じる。
- `hFO_of_C2`: QR/SV/QNとC1は既存の補題で閉じる。
  残す入力はC2のrにおけるSeedFr QFOだけ。qは残りに含めない。

単体exit 0、全体1353 jobs・exit 0、公理確認exit 0。
3定理とも `[propext, Classical.choice, Quot.sound]`。
ログ: `seedfo2-check-20261104.log`、`seedfo2-build-20261104.log`、
`seedfo2-axioms-20261104.log`（すべてtmp/codex内）。
コミットメッセージ案: `Reduce QFO seed input to upgraded C root frames`。

## G6(b) 起動用

`bash tmp/codex/run_seedfo_C2_shapes_20261104.sh` をClaude氏が起動する。
nice15、親1+worker3。測定器は `seedfo_C2_shapes_20261104.py`。
G5のチェックポイントを使い、un偽の全ソースを取り出す。
n=2/3を別々に測る。新しい残りを仮定したりLeanに入れたりしない。

出力は `tmp/codex/seedfo_C2_shapes_20261104/`。
元の各区画に対応するJSONに全行列と全結果、最後にsummary.json。
ログは `tmp/codex/seedfo_C2_shapes_20261104.log`。再実行で再開できる。

分類:

- CL_T(r)、CL_N(r)、各子の位置、ブロック番号、写し元番号。
- 各子のoがprefix/sourceのどの列のoと等しいか（全一致列番号）。
- oの変化はequal / Lhd_z / lt_only / not_lt。
  Lhdはlhd_exact.lhdを使用し、問題のあったeta付き判定器は使わない。
- kとのP0/P1祖先関係、M/T/Nでのupg。
- rの各途中状態が、Mまたはprefixのどの列のどの枠と完全に一致するか。
- 候補: CLの末尾q追加、添字不変、旧い子の非増加/Lhd下降、
  変わった子がkの子孫/上げ元、途中状態がsource/prefixの枠の写し。
  各候補を真偽に分けて集計し、QFOそのものも記録。

16列例のself-testとbash構文確認はexit 0。
この例ではQFOは真だが、旧い子の非増加と途中状態の完全一致は偽。
この2候補は一般の補題としては採用できない。

## G5の件数の注記

構造のC配置は151844、un偽2666。正常に値を比較できたのは151842、un偽2665。
区画set040-shard000000000に評価不能がある:

- index259: un真、n=2/3でtargetの評価不能。
- index828: un偽、sourceまたはprefixの評価不能。

新測定でもindex828を除外せずUNRESOLVEDとして残す。
正常な2665枠と評価不能1枠を区別する。
