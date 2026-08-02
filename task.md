# trio: トリオ数列（z<2）停止性の構文的証明

- [x] BM4 実行可能モデル tools/trio.py ✅
- [x] 検証 tools/verify_trio.py（ペア一致・対角・psi(I) 塔・z<2 閉性・A≡1 探索）✅
- [x] Trio.lean 定義（TrioSeq / 親子 / oper / ST_TS / step）✅ build 緑
- [x] Term.lean 記法（添字対 p_{a1,a2}(b)+c）・順序 olt（推移律まで）・翻訳 tr ✅
- [x] Decrease.lean 測度の減少 m_step_decreases ✅ build 緑
- [x] Reduction.lean 停止性への還元（条件付き停止性）✅
- [x] Seqlex.lean 列辞書式順序との同型 olt_ST_iff_seqlex ✅
- [ ] Cnf.lean（cnf・閉包・ctx_cong・一様コピーで cnf_oper）← 次
- [ ] Column.lean 不変量（z0ok / y0ok / r1ok / r2ok / 窓の下界 → A≡1）
- [ ] 共終性（2 次元上昇の核）
- [ ] W 階層（反射の壁: (2,0,0) 型の一手）
