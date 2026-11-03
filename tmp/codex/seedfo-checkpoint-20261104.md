# G4 checkpoint

新規本体: `Ytosk/lean/Ytosk/V3SeedFO.lean`。変更: `Ytosk/lean/lakefile.toml` に重複確認後root追加。

namespace: `Ytosk.V3Main.SeedFO`。

- `seedFO_qr` (706行): StepCtx3と実際のqr枠からSeedFr QFO。QRRes、Res3Wなし。
- `seedFO_qn` (719行): StepCtx3と実際のqn枠からr/qのSeedFr QFO。QNRes/QNDom/旧PVなし。
- `seedFO_sv` (744行): StepCtx3とsv枠からSeedFr QFO。SVRes/SVFixなし。prefixのCons/Good3/FOはC.pre。
- `seedFO_C` (768行): 実際のC枠と `T2SeedCUnVq` の2欄だけからr/qのSeedFr QFO。
- `cUnVq_of_un` (763行): 既存 `c_vqP_of_un` で、CのvqPはunから導ける。
- `hFO_of` (809行): 実際のC枠での2欄の残りから、入口のhFO全体を出す。
- `hFO_of_un` (825行): 実際のC枠でupg M (r+L-1)=noneだけを仮定して、hFO全体を出す。

4つのdata補題は旧frame-dataの証明を写し、新しい子のoの正確なshift式を計算する前に止めた。このため、共通copyの旧R引数をダミーで供給する必要もない。data_Cも旧C_frameの構造・一致の部分だけを抽出。

残る点: CのunをStd/StepCtx3だけから出す証明は未取得。旧 `qP_C` もunを前提にする。旧StepCtxT2のC.goodに戻って供給してはいない。新しい条件付きの橋は、unが全標準C枠で真だという主張を含まない。その強い構造条件の全称測定は未確認で、入口の仮定の置換はしていない。

検証:
- 単体 leanman check: exit 0 (`seedfo-check-20261104.log`)。
- 全体 nice -n 5 leanman build: exit 0、1352 jobs (`seedfo-build-20261104.log`)。
- 公理確認 leanman check: exit 0 (`seedfo-axioms-20261104.log`)。上の7定理はすべて [propext, Classical.choice, Quot.sound]。
- sorry/admit/new axiom なし。

コミットメッセージ案: Prove QFO seed frames without legacy drop assumptions

作業用: `tmp/codex/make_seedfo_20261104.py`（最初のdata部分を作った生成器。以後の手修正を含まないため、再実行用ではない）、`tmp/codex/seedfo-axioms-20261104.lean`、上のログ。このcheckpoint以外の追加の証明・測定は開始していない。
