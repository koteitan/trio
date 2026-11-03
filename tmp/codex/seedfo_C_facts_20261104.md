# G5: C 配置の前提の直接測定

起動: `bash tmp/codex/run_seedfo_C_facts_20261104.sh`。
Claude氏が起動する。nice 15。親1本とworker3本で最大4プロセス。
Leanの変更なし。

- 入力: `inv3v3_inputs_sets_20261101.json` の86集合。その順序を固定する。
- 配置の選別: `tmp/claude/measure_un.py` と同じ。SRO未満のフィルタは置かない。
  比較する期待値は151844枠、un偽2666枠。複数集合の重複は元の測定と同様に数える。
- n は2と3を**別に**測定する。無限個のnを検証したとは主張しない。
- 全C配置でhun、hqP、hv0、hvq0、vqP、vq_eq_gexpを測定。
  hqPは単なるCLへの非所属でなく、V3Rank.Countedの否定。
  vqPはV3T2SeedQNL.qnSの式を直接評価する。
- source/prefix/targetのConsの全方程式、Rkの存在（依存グラフの非巡回性）、
  Good3の3欄も測定。prefixのrでFrameOTと全子を入れた状態のOTも測定。
  データセットのStd/SInv/Inv3V3は再証明しない。
- data_Cの結論4欄（CL_N_r、prefix_o_agree、v_N_r、CL_N_q）と、
  目的のQFO_r/QFO_qも別に測定。前提の偽とQFOの偽を混同しない。
- source/prefix/targetは決定的評価器の値づけ。ConsとRkを確認し、
  Consの一意性により他の値づけを標本抽出する必要を避ける。
- 例外や評価不能はUNRESOLVED。偽として数えない。

ログ: `tmp/codex/seedfo_C_facts_20261104.log`。
チェックポイント: `tmp/codex/seedfo_C_facts_20261104/setNNN-shardNNNNNNNNN.json`。
各ファイルのfailuresに、偽の欄の一覧、全行列、n、r、q、L、主要な値を保存。
unが偽なら必ず記録する。途中停止後も同じコマンドで未完の区画だけ再開。
全件終了時の集計は同ディレクトリのsummary.json（complete=true）。
集計キーはallとun_true/un_falseに分け、nごと・各欄ごとにtrue/falseを数える。
空集合もチェックポイントを作る。

事前確認: `--self-test` の16列の標準例でn=2,3とも評価成功。
hun/vqP/hvq0/prefix_o_agreeが偽、hqPとQFO_r/QFO_qは真。
これはQFOの反例ではない。
