# G8: C2のQFOをMの状態との比較に帰着

新規: `Ytosk/lean/Ytosk/V3SeedFOC2.lean`。
変更: `Ytosk/lean/lakefile.toml`（root1個追加）。既存Leanとトップは変更なし。

- `qFO_of_state_lhd`: 標準形の添字aと新引数ANについて、AN=AMまたは
  Lhd z AN AMと、旧psiのOTから新psiのOTを証明。
  `psi_ot_of_lhd`の許容はzなので、その成分の条件は空。
- `T2C2RootRel`: sourceのCLとprefixのCLの一致、targetのCLがsourceのCL+[q]、
  targetとsourceのv(r)の一致、全j≤length(CL M r)での引数の等号またはLhd z。
  n≥2のすべて、ConsとGood3を満たすすべてのtarget値づけを量化。
- `seedFO_C2_of`: jが子の数より小さければsourceのFrameOT、等しければ
  sourceのConsとGood3による全体のo(r)のOTを使う。
  新引数のOTはtargetのGood3.ot_oとisOT_sumN/isOT_spArgから出す。
- `hFO_of_C2rel`: C2に限ったT2C2RootRelを、既存hFO_of_C2へ渡す橋。

子ごとの関係からspArg後のLhdへの輸送は未証明。
既存のLhd/spArg関連の補題を調べたが、そのまま使える補題は見つからず、
今回は指示にある代案の「状態の関係」を明示的な残りにした。
子ごとのLhdだけから状態のLhdが出ると暗黙には仮定していない。
source_children欄は測定された構造を残すためのもので、橋自体はtarget欄だけを読む。

単体チェックexit0、全体1354 jobs・exit0。
ログ: tmp/codex/seedfoc2-check-20261105.log、seedfoc2-build-20261105.log。
公理確認: tmp/codex/seedfoc2-axioms-20261105.lean/.log。
コミット案: `Derive C2 QFO from source argument equality or Lhd`。
