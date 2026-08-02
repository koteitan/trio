# trio: トリオ数列（z<2）停止性の構文的証明

- [x] BM4 実行可能モデル tools/trio.py ✅
- [x] 検証 tools/verify_trio.py（ペア一致・対角・psi(I) 塔・z<2 閉性・A≡1 探索）✅
- [x] Trio.lean 定義（TrioSeq / 親子 / oper / ST_TS / step）✅ build 緑
- [x] Term.lean 記法（添字対 p_{a1,a2}(b)+c）・順序 olt（推移律まで）・翻訳 tr ✅
- [x] Decrease.lean 測度の減少 m_step_decreases ✅ build 緑
- [x] Reduction.lean 停止性への還元（条件付き停止性）✅
- [x] Seqlex.lean 列辞書式順序との同型 olt_ST_iff_seqlex ✅
- [x] Cnf.lean cnf・閉包・ctx_cong・コピー塔・cnf_oper_of_window ✅（cnf_ST_TS は Column 後）
- [x] ピボット: A_x1≡1・W2ok は ST_TS 上で反証（HOST 系列）→ ガード付きコピーが実挙動 ✅probe
- [x] Lift.lean 心材リフト lsub（単調性・cnf 保存）✅
- [x] 経路補題 le1 ⟺ chain 窓（無条件）✅（スパイン⊆D は不要と判明）
- [x] Gcopy/Goper: translate_gseg・cnf_gcopiesFrom・cnf_oper・**cnf_ST_TS** ✅（不変量も窓仮説も不要）
- [ ] Column.lean 不変量保存（r1ok / z0ok / noninc、ガード対応；後続章向け）
- [ ] 共終性（2 次元上昇の核）: Part 0-2 ✅（seqlex 配管・還元・self 枝）; 核は z=0 制限で probe 済（53757 例 0 違反）
- [ ] W 階層（反射の壁: (2,0,0) 型の一手）
