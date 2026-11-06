# 接ぎ木の悪い形 Bad2 への対応（2026-10-24）

接ぎ木の標準形（tmp/ytosk-handoff/sets/graftA.pkl・graftB.pkl、作り方 tmp/claude/gen_graft.py）で、最上位の残り HFrameV2・HDropV2W と不変条件 Inv3V2 の欄 TPLoW・AbsDW が偽だった。

## 残りの地図（2026-10-31、最上位 trio_terminates_main_V2_cur の 15 個）

**16 回目（2026-11-06、claude）**: 入力 hN の写しと VSmallRAll の残りを 86 集合で測り、偽だった 3 つを弱い形に替え、2 つを狭い残りに帰着させた（すべて緑、1257 jobs、公理は標準 3 つ）。
- KAG（V3T2VRAK）は偽: graft の 5 集合で 2643 件。KG に第 3 の選択肢（a − V の動く位置の成分以下）を足した KAG2 は失敗 0。σ 移送 qVRAshK_KVRA2（V3T2VRAK2）。
- T2VRACopyEsc は偽: 同じ 5 集合で 6467 件。どれも g が comps u v_N(i+L) のどれか以下（QVRAt の第 3 の選択肢）。それを先に場合分けする CopyEsc2 は失敗 0（V3T2SmallV3U2、hN_of3）。
- T2CopyK CopyVDomK は graftE で 9 件偽（段が枠の段 LevAt にないか V より上）。qVRAshK は VDomF を枠の段 u ≤ V でしか使わない。段 u だけの VDomU（σ B の選択肢つき）は失敗 0、VDomF ⇒ VDomU。KVRA3 = VDomU ∧ KAG2 と qVRAshK_KVRA3（V3T2VRAK3）、入口 hN_of4（V3T2SmallV3U3）。
- T2VRAPre ⟸ hBXU ∧ SeedPFResV3 ∧ T2C2Kids（V3VRAPreU・V3VRAPreC、hPre_of）。T2C2Kids は C2 の r の子: CL_N(r) = CL_M(r) ++ [q]、v(r) と最後より前の子の o は M と同じ、最後の子は添字が同じで引数が大きくならない（C2 の全 7386 枠で失敗 0）。sv の残り T2SVc0 は落とす補題の PO から証明した（t2SVc0_ofV3）。
- T2VRASeed ⟸ SeedPFResV3 ∧ T2VRAPre ∧ T2VRAQNDom ∧ T2VRASeedC ∧ T2C2QKids（V3VRASeedU）。sv の枠は証明済み。T2C2QKids は C2 の q の枠: CL_N(q) = [x]、v_N(x) = v_N(q)。
- 残り（hN）: hBXU、SeedVFResV3、T2CopyK FDshAt、T2VRAPre・T2VRASeed の上の残り、CopyEsc2、T2VRAK VDomU、T2VRAK KAG2。

**15 回目（2026-11-04〜05、claude と codex）**: 入口の入力 hFO・hSF・hSP を、狭い残りに帰着させた（すべて緑、1356 jobs、公理は標準 3 つ）。
- hFO（t = 2 の種の枠の途中の状態の標準形）: 「Good3 だけから途中の状態の標準形」は項の反例で偽（a = 0、子の o = [ψ_1(ψ_0(Ω_2)), ψ_0(Ω_2)]）。種の配置ごとに既存の補題から QFO だけを抜き出し、古い束 Res3W と旧 PV を使わない形にした（V3SeedFO）。qr・qn・sv は残りなし。
- C の配置（q ≠ r で q が r の最後の数える子でない）の条件 un（upg M (x−1) = none）は偽（151844 枠中 2666、上げ先は祖先）。C を un の真偽で分け、真（C1）は閉じた（V3SeedFO2）。
- un が偽の C2 では、x − 1 は T = M.take x の最後の列なので上げを持てず、v(x−1) が M と T で違う。N = M[n] を T でなく M と比べると、r の数える子は CL_N(r) = CL_M(r) ++ [q]、v(r) は不変、最後の子の o は ◁ で下がり、前の子は等しい。各途中の状態の引数は M と等しいか ◁ で下で、M の状態の標準形が ◁ で移る（V3SeedFOC2、残り T2C2RootRel）。
- hSF・hSP: PH3c・FC3 の種の補題を配置ごとに今の文脈へ移し（V3SeedPF）、読む欄だけの束 SeedPFResV3 と、C2 の種の枠から入力を出した（V3SeedPFAll）。SeedPFResV3 は SRO 未満の全データで失敗 0。
- hN: N の VSmallF・FrameClosed・VSmallRAll の橋を U の鎖へ写し（V3T2SmallV3U・V3T2LocalV3U）、種の枠の QVSF・QFCo の補題を今の文脈へ移した（V3SeedVF、V3SeedVFAll）。hN ⟸ hBXU、SeedVFResV3（SeedPFResV3・T2SeedQNDom・T2SeedCDom と C2 の種の枠）、写しと VSmallRAll の 6 つの残り（T2CopyK FDshAt・T2VRASeed・T2VRAPre・T2VRACopyEsc・T2CopyK CopyVDomK・T2VRAK KAG）。T2SeedQNDom・T2SeedCDom は SRO 未満の全データで失敗 0。
- hD: 既存の hDropV3_of_inputs の 5 つの入力 DropInputsV3（HardArg・VSmallNew・BumpWeakSrcB2・BumpAbsCB2・ua）を 86 集合で測り、すべて失敗 0（HardArg 1736 万件、BumpAbsCB2 の吸収の破れ 5465 件はすべて WCSP2 の側、ua の弱い場合 14.5 万件もすべて WCSP2 の側）。
- hF: 不変条件 Inv3V3 の全欄の監査を 86 集合で走らせ、hF の枠の 8 欄（adsx・aus・tplosx・tploq・auw0・trigs・tplon・adn0）は失敗 0。葉の 2 欄（TP1LeafG・TP1WLeafG）は未測定。
- hN の残り T2VRAK KAG は今の形（段 u を LevAt に限る）でも偽だった（86 集合、graft の 5 集合で 2643 件、tmp/claude/measure_t2vrak86.py）。例は V = v_P(r) = 0、s = a = v_P(i) で、s − V の動く位置の成分 g = ψ_{ψ_{p(1)+1}(0)}(0) は Ω_s より大きく、B = 0。QVRAt はこの枠で第 3 の選択肢（g ≤ comps u a の成分）で成り立つ。KG に第 3 の選択肢「g ≤ d、d は a − V の動く位置の成分」を足した KAG2 は失敗 0（tmp/claude/measure_kag2.py）。σ g ≤ σ d で、σ d は f(a) の成分（compsAN_sh_fwdK）。σ 移送 qVRAshK_KVRA2 と入口 hN_of2（KAG の代わりに KAG2）を示した（V3T2VRAK2・V3SeedVFAll2、緑）。
- 残り: hFO・hSF・hSP は T2C2RootRel と SeedPFResV3（どちらも測定で失敗 0）に帰着。hN は上の残りに帰着（写しと VSmallRAll の 6 つは未測定）。hD は DropInputsV3（測定で失敗 0）に帰着。ほかの 6 入力は測定だけ。

**14 回目（2026-11-01〜03、claude と codex）**: 入口の偽の入力 3 つをすべて置き換えた。新しい入口は V3TranslationAllUV3（desc3_of_step_enginesV3UU・translation_order_of_step_enginesV3UU・translation_surj_of_step_enginesV3UU、すべて緑、公理は標準 3 つ、1351 jobs）。
- hQR: 項のすべての分解を量化する OFields をやめ、展開で実際に使う段の形 FStep だけを受ける HQRInputsStepV3 にした（V3QRStepV3）。3 列の標準形で局所の欄が成り立つことを示した（V3QRStepSanity）。
- 値の変化の形: 悪い bump の呼び出しの枠では、v・o・W の変化 ψ_w(L + L) → ψ_w(L + R)（L = Ω_{w+w}、R = ψ_{w+1}(L)）が DQ の形にない。どの η でも fsD(L, η) = Ω_{w+k} なので（V3DQNotBadLeaf、Lean で証明）。悪い葉 fsD(l, η) ≤ q < l を足した DQX で書ける（V3DQX、V3DQXSanity）。
- 吸収が破れた 226 枠を列ごとに測った（tmp/claude/abs_slack.py）。◁ でなく許容 v(m) の ◁ でしか下がらない列は、悪い列 i と、6 枠での c = i − 1（i へ上げる列）だけ。回収は親の o。上げの形では許容 v(m) が親 p の添字 v(p) と違い、Lhd_{v(p)} は 6 枠中 4 枠で偽だが、v(m) の成分はすべて新しい o(c) より小さい。
- この形を Lean にした: lhd_psi_disG（許容の成分が新しい引数以下なら ψ_v で解消、V3AbsUpgLemma）、上げの形 UpgAbsShape と悪い集合 BdXU（V3AbsUpgShape）、エンジン deps_lhd_otXU（WfT2X1U）、枠の形の 5 つ目 FrameShape5（V3AbsUpgFrame）。
- hBX（t = 2）: AbsWNx を AbsWNxU（吸収 ∨ BadAbsShape ∨ UpgAbsShape）に替え、使う側の鎖を U 版に写した（WfT2X2U〜V3TranslationAbsUV3）。古い入力を反証した 41 列の行列で新しい入力が成り立つ（V3AbsUpgSanity）。
- hAbs（t = 0）: T0AbsW を T0AbsWU に替え、t = 0 のエンジンの結論を許容つきの形 PX にした（V3T0DepAbsU〜V3T0CarrierAbsU）。値が標準形であることはエンジンの順位の帰納法で同時に出す。39 列の反例で新しい入力が成り立つ（V3T0AbsUpgSanity）。
- 残り: 入口の 11 入力はどれも偽と分かっていないが、どれも測定だけで、Lean で証明していない。全射はさらに EvalFSNZ 2。

**13 回目（2026-11-01、codex）**: Inv3V3 の上に新しいトップの入口を組んだ（すべて緑、1315 jobs）。
- V3MainV3: inv3V3_all・desc3_V3・order_pres_V3・surj_V3。V3TranslationInputsV3: desc3_of_enginesV3・translation_order_of_enginesV3・translation_surj_of_enginesV3。古いトップ V3TopT2B は使わず、変えていない。
- 入口は 11 個の入力をとる: HDropV3（落とす補題の結論）、HFrameV3、t = 0 の hAbs（T0AbsW）・hSeeds、t = 1 の hQR・hQN、t = 2 の hBX（AbsWNx）・hFO・hSF・hSP・hN。全射はさらに EvalFSNZ 2。
- **このうち 3 つは偽で、それぞれ単独で入口を矛盾させる**（Lean で反証）:
  - hQR: 欄 OFields が項のすべての分解を量化していた。3 列の標準形 (0,0,0)(1,1,0)(2,2,0) で偽（V3QRLocFalse）。実際の単一末尾の証人 1 つだけに条件を課す TailFields・HQRInputsTailV3 を用意した（V3QRCanonical・V3QRCanonicalChain・V3QRQuantifiers）。まだトップには使わない。
  - hAbs（T0AbsW）: 39 列の標準形、n = 2、i = 34 で偽。悪い吸収の形 BadAbsShape に入る（V3T0AbsFalse）。
  - hBX（AbsWNx）: 41 列の標準形、i = 37 で偽。upg M 36 = 37 なので BadAbsShape から外れる（V3T2AbsXFalse）。
- 残りの入力 hSeeds・hFO・hSF・hSP・hN は、監査の途中（399 万件）で例外 0。
- 前の DQ の測定は、値が変わらない列を飛ばし、1 → 1 を返す枝を持っていた。Lean の DQC は真に小さくなることを含むので、その記録は DQC を仮定する入力の証拠にならない。測り直している。
- 次: 直した測定で HQRInputsTailV3 を全データで測り（退化した分解と η = 0 を含める）、3 列・39 列・41 列で新しい入力の束が成り立つことを Lean で先に示す。t = 0・t = 2 のエンジンも吸収の仮定のない DQ 形で書けるかを測る。

**12 回目（2026-11-01）**: すべて緑（1290 jobs）。
- 新しい偽の欄: AbsUWL（Inv3V2.auwl）が標準の 39 列の行列で偽（WfExQ12、Lean）。上げの枠の悪い呼び出し（W = last v(k) = o(r)）。新しい束 Inv3V3（WfExQ1: adn→AbsDN0、tplow→TPLoQ、ads→AbsDSX、tplos→TPLoSX、adw・auwl を外す）は、すべての接ぎ木（69 万個）と新しい族で全欄例外 0。
- t = 2: 偽の SrcC3Res を使わない新しいトップの版 trio_terminates_main_V2_curYR（WfT2R9）。T2BadRes の第 1 欄の代わりに AbsWNx の欄だけを持つ T2BelowRV2Y を受け取る。NotBumpKidX と hQlowV は証明済み。Res3T2.absN（= 偽の AbsWN M M[n]）は X 版で T2Drop2X に置き換えた。残りは T2CBadOut の枝。
- q ≠ r: 悪い閉包つきのエンジンを最後まで組み立てた（t1_main_vlocSX3、WfQnA18）。残りは不変条件の段（真の値づけでの StepT1B）と、測って例外 0 の位置の残り（hVlt・hBr・hKr・TPLoSXIn の半分・hRwin）。
- q = r: Bachmann 型の下界 DQG を証明し、o の枠の欄を PreG・LastG（測って例外 0）から出した。v_{M[1]}(r) ≤ v(r) は PV2 から証明。不変条件の段は VSFResQ と新しい枠の 8 欄が残り（WfExQ11）。
- 種: PV2 から SeedC2 を出した（qr_final4SGW2）。新しい残り UAwRA（1850 万個と接ぎ木 graftR で例外 0）。
- 全射: t = 0 の数え上げで r が根の場合を証明。HCID を 1 辺の補題（HDiagLoc・HDiagStep）に帰着。残りは 1 辺の項の補題と HCntRoot2。

**11 回目（2026-11-01）**: すべて緑（1235 jobs）。
- q = r（WfQrH1〜8）: 連鎖の仮定 hLocE を名前つきの欄に置き換えた（qr_chainH3）。hX・o(x) = Ω_{v(r)+1} などを証明。DQ の値の標準形 C_strip を DQC として形式化（DQC.ot）。古い OmSide は 1 層で満たせない（not_omSide_single）ので OmSide1 に直した。残りは、o の枠の欄（TrigN・Last・葉の判定）を M の側の事実から出すこと（試した M の側の形はすべて偽）、ω の層の 1 層の成分、v_{M[1]}(r) ≤ v(r)、Inv3V2A の展開の段 ExpStepQ。
- q ≠ r（WfQnH1〜8）: 構造の残り hu0 を証明。閉包の外で OLocal・VLocal を TPLoSX から出した（olocal_t1B、vlocal_t1_atXB）。悪い葉で (E3) を証明（leaf_E3）。入れ子の悪い呼び出しは測ったどこにもない。閉包の中の ◁ の伝播エンジン deps_lhd_otU を用意。残りはその構造の仮定と最終の組み立て。
- 種（WfSdH1〜4）: 古い fsD の形の q = r 連鎖を、弱い種 SeedC2 で動かした（qr_final4SGW）。BumpAbsCB2 は全データで例外 0。残りは ExpStepT1 の作り手の写しと、PV2 から SeedC2 を出すこと。
- t = 2 の Bad2（WfT2X1〜8）: D のエンジンを悪い列つきに（deps_lhd_otX）、T2BelowXS を FrameShapeX に、7 つの読み手のうち必要な X 版の補題を用意。偽の AbsWN 欄を外した T2BelowRV2X と、旧形からの橋を証明。残りは読み手の骨組みの写しと、構造の残り NotBumpKidX。
- 全射（WfCofH1〜3）: HRootD・HNotSucc を証明。HShiftD を Desc3 + Good3 に帰着。HEngD・HPathRD をエンジンの下界 HEngPath に帰着（0 失敗）。残りは HCID と数え上げ HCountS（t = 0・2）。

**10 回目（2026-11-01）**: 新しい形を Lean につないだ（すべて緑、1204 jobs）。
- q = r（WfQrL1〜18）: DQ の形の連鎖 qr_chainE。M[n] の真の値づけは、自分の D の値での glue に等しい（true_glue_eq）。D のすべての呼び出しで σ = DQ(古い値)（qr_engineDQ2）。残りは仮定 hLocE（o の枠の 5 形・ω の層の 3 形を M の側の欄から出すこと）と、DQ の値の標準形（条件 C_strip、測って例外 0）、Inv3V2A の展開の段。
- q ≠ r（WfBad・WfQnL1〜8）: 共通の定義 BadCall / BadSet。D の v の呼び出しは VLocal か悪い（vlocal_t1_atX）。閉包の外で真の値づけ = glue（E1_M）。悪い呼び出しの右辺 = sf(v(P₁ i) + A[ζ]) < A。根が下がる（root_N_E3）。残りは閉包の中の (E3)、入れ子の悪い呼び出し、OLocal を TPLoSX から出すこと、構造の残り hu0。
- 落とす補題（WfDrL1〜4）: PV2 は graftE（5.5 万個、PV は 901 回偽）でも例外 0、UAw2・SeedC2 も例外 0。PV を使う生きた 111 個の定数のうち 72 個を PV2 版に写した（残りは落とす補題そのもの・包み・構造の欄）。添字 0 の条件（d = 0 の列の対角の点は μ だけ）を証明（WfDrL3）。
- 全射（WfCofL1〜4）: 項の補題（対角の点で t[k] = fsD(t, γ_k)）を証明。EvalFSNZ 2 をエンジン側の名前つきの事実（HEngD・HPathRD・HShiftD・HCID・HRootD・HNotSucc・HCountS）に帰着。どれも測って例外 0。

**9 回目（2026-11-01）**: t = 1 の偽の欄（adn・tplow・adw・ads・tplos）はすべて 1 つの現象から来る。悪い形の bump の呼び出し i（P₀ i = P₁ i = m、CL i = []、i へ上げる列なし）で bump 項 W が A = o(r) そのもの、v(P₁ i) の項 q が [A[ζ], A) にあると、M では A に吸収された q が M[n] では残る。
- q = r: 真の値は fsD に残る項 Q を差し込んだ DQ（WfQrE1、例外 0）。tplow → TPLoQ（0/285 万）、adw は不要、adn → AbsDN0。
- q ≠ r: 悪い集合 B_ζ の外は今までの glue、B_ζ の上は v = v(P₁ i) + A[ζ]（WfQnE1〜3）。ads・tplos → AbsDSX・TPLoSX。古い出力の形が偽であることは Lean で示した（not_cons_glue2/3）。
- 落とす補題: PV は不変条件の欄をすべて満たす 19 個で偽。成分の条件を弱めた PV2 で落とす補題が緑（drop_all_hardW2、WfDrE1）。SeedC → SeedC2（WfDrE2）。
- 目標 5（全射）: Desc3 と EvalFSNZ 2（最後の列が 0 でないとき eval(A)[k] ≤ eval(A[k+2])）に帰着（WfCof、緑）。EvalFSNZ 2 は 72 万個と接ぎ木で例外 0。EvalFS 1 は偽。

**8 回目（2026-11-01）の監査**: Inv3V2 の全 25 欄と構造の不変条件 13 欄を Lean の形どおりに 2320 万個の行列（既存の集合と新しい族、その M[2]・M[3] の接頭辞）で検査した（tmp/wf/WfInvX/audit.py）。SRO 未満で偽なのは 5 欄だけ: adn・tplow・adw（q = r の最後の列の枠）と ads・tplos（q ≠ r の枠）。ads・tplos は 26 列の標準形で Lean で反証（WfInvX1）。tplow・adw の最小の反例は std_b の 13 列 M13 = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,0) で、使う側の結論 VLocZ（qr_vloc）そのものが偽（bump 項 W が A そのもので d ≥ 1 のとき、良い部分の項 q が [A[η], A) に残る）。ほかの欄はすべて例外 0。値づけは族の展開 426 万組ですべて下がる。
- adn は使う側の形 AbsDN0（WfInvA1、種での吸収）に替えられる（0/20 万、接ぎ木 0/58 万、q = r エンジンも緑）。
- hClR は WfInvC.T2SeedClV2W（s′ の成分を B + Ω_{s′} で押さえる）に替えられる（720 万件で例外 0、差し替えたトップの版も緑）。
- HDropU は ua の使われない連言を外し（UAw）、BumpAbsC を BadAbsShape を許す形にできるが、落とす補題の結論 PV そのものが新しい接ぎ木 19 個で偽（Python）。
- 次（9 回目）: t = 1 の 2 つのエンジンを、吸収されない項を許す形と種の位置 m = 0 の扱いに一般化する。落とす補題の弱い選択肢を作り直す。並行して目標 5 の EvalCof を始める。

**重大（2026-10-31、7 回目）: 今のトップの仮定は全体で矛盾する。** 不変条件 Inv3V2 の欄 AbsDN が、標準の 38 列の行列 N で偽（WfReM4.no_inv3V2: N には Inv3V2 を満たす値づけがない。値づけは Cons で一意）。したがって hInvV2_all の 9 個の仮定は矛盾し（WfReM4.not_hInvV2_all_hyps）、HFrameV2 も偽（not_HFrameV2）。同じ回で次も Lean で偽と示された: HDropU（BumpAbsC の連言が Bad2 の外で偽: WfReM1、ua の欄: WfReM3）、hClR = WfScout.T2SeedClV2R の qn の道の欄（WfReM2）、H7WSib・SibMCol・SibM（WfSibCex、31 列）、B2LevS（WfB2LFalse、40 列）。T2BelowXS の欄 FrameShape も 36 列の行列の M[2] で偽（WfAbsWCex.not_frameShape）。
一方、値づけ（翻訳 o）は、これらの反例 5 つとその接頭辞の展開 M → M[n]（n = 1, 2, 3）の 514 組すべてで下がる。壊れたのは翻訳ではなく、それを示すための不変条件と残りの形。次は Inv3V2（AbsDN・TPLoWs・AbsDWs の族）を、新しい反例の族（tmp/wf/WfReM の graftM36・graftM36x、tmp/wf/WfB2L の lift1・lift2、WfSib の hunt）で真になる形に作り直す。
N = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,0,0)(13,1,1)(14,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,0,0)(15,1,1)(16,1,1)(17,1,0)
（i = 31 で bump 項 W = ψ_{ψ(1)}(ψ_{ψ(1)}(ψ_{ψ(1)}(ψ(Ω_{Ω_1})))) と、v(30) の項 q0（Ω_{ψ(2)} を含む）について q0 < W だが q0 < W[1] でない。）

**注意（2026-10-31、6 回目）**: 標準の 36 列の Bad2 の行列（WfSrcC3Cex）で、SrcC3Res・SrcCRes・T2AbsNSrc の (c)・T2AbsNBad・AbsWN M M[2] が偽（StepCtxT2 を Std ∧ Cons に替えた形で Lean で反証。Python では M と M[2] で Inv3V2 の欄はすべて真）。AbsWN は T2BelowRV2 の欄で、T2BelowXResV2（トップの hBX）に入る。したがって今のトップの T2BadRes は偽の欄 SrcC3Res を含み、Bad2 の t = 2 の道（t2BelowRV2_of_src → T2BelowRV2 → T2BelowXResV2）は作り直しが要る。B2Step も偽（WfB2SFalse、28 列）で、弱い B2StepAb に替えた。
M = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,2,0)(12,0,0)(13,1,1)(14,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,1)
（x = 35、r = 34、i = 32、m = 31、k = upg m = 24、c = 26。v(c) = v(r) = ψ(1) で、c の数える子 27 は v(27) > v(r)。s = bumpW(24) は M[2] で W_{M[2]}(32) ≤ s < W_M(32) かつ s ◁ W_M(32) でない。）

| 残り | 中身 | 測定 | 消すのに要るもの |
|---|---|---|---|
| HDropU | 落とす補題の仮定（形 B）と条件のない ua | 全集合で例外 0 | 落とす補題の仮定を値の不変条件から出す（核） |
| T2BadRes WfSrcP.PLowRes | (a) と (b) に共通の低い行の場合: i の最後の bump 枝 j の最後の子 c < x−1 の o が変わり、x−1 が c の下、e1 c < e1 m（m = P₀ i = P₁ i）、かつ v(m) < τ.o(c) でない。v(m) < τ.o(c) の場合は証明済み（not_dropFail_of_lt_o） | Bad2 の (a) では毎回 j の前の子 d が e1 d ≥ e1 m（既存の補題で除かれる）。(b) の残る枠は i の子が j だけ・j の子が c だけで、v(m) ≥ W_M(i) か v(m) < W_T(i)。窓が空でない枠は 0（前回の「窓が空という主張は偽」は Bad2 でない枠だけの話だった） | m の行 1 の鎖の写し a（e1 a = e1 c）と ArgDomCore |
| T2BadRes WfTerm.TermHi | (a)・(b) の次の列の場合の終端の形（WfSrcO.Term・TermB）。q より下の起点と、q より上で添字 ≤ v(q) の起点は証明済み（v(q) は TopC で変わらない）。残りは q より上で添字 > v(q) の起点 t が窓 [W_T(i), W(i)) に入らないこと | b2fam で 790 項すべて t ≥ W(i) | （道全体の作り直し待ち） |
| T2BadRes WfSrcC2.SrcC3Res | **偽**（上の 36 列の行列）。(c) の上界 s < Bnd(v(r)) そのものが偽 | — | Bad2 の t = 2 の道を作り直す |
| T2BadRes (d) T2QNDomBad2 | 既存の V3QNDomS の残り（単純でない形） | 例外 0 | — |
| WfB2S.B2StepAb | HUACB2 の残り。旧 B2Step は偽（最後の bump 子が葉の 28 列の行列）なので、j を「子を持つ最後の bump 子」にした形。吸収がない場合は HUACB2 を証明済み（huacB2_noabs）。B2StepAb は構造の B2LevS（c の段は m か P₁ m）と値の B2UpgV（m が t へ上げるなら bumpW(k) ≤ last v(t)）から証明済み | B2LevS・B2UpgV は bump の親を持つすべての位置で例外 0（graft4・graft5 を含む） | B2LevS を構造の不変条件から、B2UpgV を写しの関係から |
| WfH7W.H7WSib | t = 0 の Bad2 の消える尾の枠で、x−1 の直前の兄弟 c は x−1 の写し。より狭い WfH7W2.SibMCol（Bad2 なし、値なし、行 1 の m ≠ 0 の条件で col c = col n）から証明済み（h7wSib_of_col）。SibMCol は大きな集合の一部でまだ測っていないので、トップは H7WSib のまま | Bad2 の枠 3441 で例外 0。SibMCol は接ぎ木で例外 0 | SibMCol を展開で運ぶ不変条件として |
| ~~T0H10Core.T0BadSeedsH10Big~~ | **最上位から外した（2026-10-29）**。偽（WfH10Cex.h10_core_false、29 列の標準の Bad2 の行列） | — | 使う側 t0_S1N_cnt（V3T0BadNode）を作り直した: v(r) > v(g) の枝は数える写しが 0 個（m = 0）でもよい（weak_seed_hiG。m = 0 では古い枠が書き換えない t0IVResC_holds ので、写しだけの状態 B は古い引数の接頭辞）。v(r) ≤ v(g) の枝では r − 1 → r の上げは起きない（v_par0_lt_of_upg_prev: P₁(r) = P₀(r) = g なので v(g) < v(r)）ので counted_first0G で数える。T0BadSeedsH2〜H6 の数える欄は「r − 1 が r へ上げ r が頭打ち」でないときだけに弱め、構造から証明（t0BadSeedsH6_of_W）。残りの 2 欄は HDropU と HUAC だけから（WfH10b.t0BadSeedsH7W_of）。置き換える残りはない |
| ~~T0BadSeedsH7W・T2QNDomBad~~ | **2026-10-31 に置き換えた**: HUACB2・H7WSib・T2QNDomBad2 から証明（WfH7W.t0BadSeedsH7W_of_sib・t2QNDomBad_of_B2） | — | — |
| ~~HUAC（HUACPositive・StepFacts3）~~ | **最上位から外した（2026-10-30、5606d012）**。HUAC そのものが偽（V3HUACFalse.not_HUAC、32 列の標準形）。StepFacts3 も偽（V3StepFacts3False、40 列） | — | 使う側 2 か所の要求を直接の残り T2QNDomBad・T0BadSeedsH7W にした |
| HFrameV2・HLeafV2 | 標準形の 1 列落としの枠・葉の欄 | 例外 0 | 欄ごとの値の議論 |
| HBumpExt | 接頭辞で bump 項が増える | 例外 0 | M[n]（不変条件のない行列）について言うので落とす補題から出ない |
| T2CBadOut | C の形で x − 1 が上げる（T2CBad）の出力 | cbadext の 10 個で例外 0 | 別の組み立て（q − 1 → q の上げで o_N(d) ≠ o_T(d)、C_frame の hval が偽） |
| hVU・hCl・hPRE・hCan・hDomQ・hVCp・hAG | t = 2 の種と写しの枠の残り（文脈 StepCtxT2 は Bad2 を含む） | Bad2・cbadext でも例外 0 | 欄ごと。hCan（隣の兄弟の v の比較）は不変条件として運ぶ必要 |

最上位は HUAC を受け取らない（HUAC は偽）。HUAC の使い道だった 2 か所は T2QNDomBad と T0BadSeedsH7W として直接の残りになっている。

一般の性質 **HUAC**（2026-10-26 に残りとして入れた）: 列 n が祖先 k へ上げるとき（k < n）、∀ u、comps u v(P₁ n) の各成分は comps u v(n) ∪ {0} のどれか以下。v(n) = v(k)・P₁(n) = P₁(k) なので、上げ先の bump 型の列 k の吸収の成分版。18 集合・約 800 万件で例外 0（上げ先が n + 1 では偽、計 81 件）だったが、32 列の標準形で偽（V3HUACFalse、2026-10-30）。T2QNDomBad と T0BadSeedsH7 (1) の共通の核（scratchpad の vcomp.py・qnweak.py）。

## 済んだこと（main）
- Bad2 で分けた（偽の欄・残りに ¬Bad2、Bad2 の行列は残り TakeBadV2・BadOutV2）。
- Bad2 を狭めた。今の形: x − 1 に上がり先 ∧ p（x − 1 の親）は g の bump 子 ∧ [（g が x の祖先 ∨ x の行 2 ≠ 0）∧ x − 1 での強い吸収 UpgAbsX が破れる ∨ P₀(x) = x − 1 ∧ x の行 1 ≠ 0 ∧ BumpAbsC が破れる]。graftB の Bad2 は 80228 → 約 513 個。
- UpgAbsXW0 の弱い選択肢の NBPar を NBParX に。TPLoW・AbsDW を実際の種の鎖の項の形 TPLoWs・AbsDWs にし、Inv3V2 の ¬Bad2 を外した。
- 詳しくは desc.md「Bad2 を x の位置で分けた測定」以下。

## 残りの中心: 強い吸収が破れる側 S（graftB の 468 個、例はすべて同じ 19 列の接頭辞＋1 列）
偽になる欄: UpgAbsXW0（468、NBParX が偽）、BumpWeakSrc（180、i の子が j と x）、古い PV（324 件、弱い列 r ≠ x − 1 が数える子 x を持つ）、t = 2 の T2UABad（72）、t = 0 の o′(r) ◁ o(r)（72、v(r) が弱く変わる）。

### 分かったこと（t = 0、例 …(4,2,0)(5,3,1)(6,3,1)(7,2,0)(6,0,0)、r = g = 16）
- M[n] の写しのうち最後以外は o = omid = ψ_{v(r)}(0)（x − 1 は M[n] で上げを保つ）、最後の写しだけ o′(r) = ψ_{w′}(0)（w′ = v′(r) < v(r)）。
- これは t = 0 のエンジンの弱い葉と同じ形で、項の補題 `s1_core_weak` と枠の補題 `t0_S1W`（V3T0Weak、L によらない）がそのまま当てはまる。弱い葉を r = x − 1 に限っているのは `lhd_or_weak_t0`（V3T0UpgAbs）だけで、その理由は古い CntX。

### 済んだ手順（2026-10-25）
1. CntX の第 3 の選言（BadPos での失敗した上げ）、古い補題は NoBad3（¬Bad2 から noBad3_of_nb2）。
2. 落とす補題の形 B（bump_dropB・drop_allB・drop_all_hardB、BumpWeakSrcB・BumpAbsCB・条件のない UpgAbsXW）。
3. 落とす補題の残りを前提なしの HDropU にまとめ（HDropV2W は定理）、TakeBadV2 は HDropU・HFrameV2・HLeafV2・根の残りから定理。
4. Bad2 の根の減少: 行 2 = 0 は root_drop_e2z、x が上げ先でも bump 子でもなければ root_drop_X。残り RootBadV2T2（行 2 ≠ 0 ∧ x が上げ先か親の bump 子）。

### 済んだ手順（2026-10-25、続き）
5. BadOutV2 の t = 0: エンジンを落とす補題の結論（T0DropF）と種の事実（T0SeedsN）から動かした（V3T0Bad）。BadOutV2 = BadOutT0（定理）＋ BadOutRest（残り）。BadOutT0 の残りは T0BadSeeds だけ。詳しくは desc.md「BadOutV2 の t = 0 を種の事実に下げた」。

### 済んだ手順（2026-10-25、さらに）
6. T0BadSeeds を M の段の 3 つの事実（T0BadSeedsH7）に下げた: S1 の節（weak_seed_hi）、S2・S3（和の段の ◁ を成分の支配から、t0_S2GW・t0_S3W）、「r は M[n] でも数える」（counted_first0G）。

### 済んだ手順（2026-10-25、t = 1）
7. Bad2 の t = 1: エンジンを G 版（落とす補題の結論 hdrop から）にして `badOutT1` で証明。q = r では r = x − 1（`t1qr_bad_xm1`）。残りは t = 2 の `BadOutT2B`。

### 済んだ手順（2026-10-25、形の直し）
8. Bad2 を展開して試験集合を増やした（b2grow1）。落とす補題の弱い源の形（HDropU・HDropV2W）が展開の写しで偽だったので弱めた（e1393cfd、desc.md「落とす補題の弱い源の形が偽だった」）。

### 次
- 残りの仮定は b2grow1・shapegrow で測り直した（desc.md）。二段目の展開（b2grow2）でも測る。
- （済、b8e5acb8: path_strict で RootBadV2T2 を定理にした）RootBadV2T2 を消す案: 根の減少を運ぶ DepX（V3Dep）には、x が i の bump 子の場合（bumpW(i) から x の項 1 が消えて v(i) が真に減る）と、i が x へ上がる場合（v(x − 1) = V + ω → V + 1）の起点がない。起点を 2 つ足した帰納型 DepY を作り、dep_strict0X・形の補題 hOS_t1X・dv_shapeX・nodep_* を写せば、hXu・hXb なしで root_take_lt が出る見込み。
  - 新しい起点の狭義の減少は短い: snb は bumpW(i) の末尾の項 1 が消える（和に 1 を足すと真に増える）、supx は v(x − 1) = v(x) = V + ω と v′(x − 1) = V + 1（v_upg_eq・v_last_take）。
  - 変わる所（V3T2D を読んだ結果）: nodep_v_qX（v(q) は D に入らない、q = P₀(x)）は snb で偽になる。使う側 uncnt_of_depvX の d = x の場合は「x が q で数えられるなら x は bump 子でも上がり先でもない」で局所の仮定に直せる（上がり先は topped なので数えない）。dep_exitX の vupg の場合 i + 1 = x（いまは hXu で除く）は、出口 c′ = x を許す形に結論を広げる必要があり、nodep_sibX・p1_depX がそれを受ける。ochild・vbump の形（OShape・dv_shape）はその上に乗る。b2grow1 では Bad2・t = 2 の 1879 個のうち 587 個が「x が親の bump 子」。
- T0BadSeedsH7 の (1)・(2) は、上げの吸収の成分の性質（祖先への上げで例外 0）と v′(P₁(x − 1)) = v(P₁(x − 1)) から出せる見込み。(3) は UpgAbsX の破れを使う値の議論が要る（構造だけでは出ない、desc.md）。
- （済、3e447cfb）BadOutT2B は `badOutT2B_of` で証明。文脈 StepCtxB（¬Bad2 なし）で t = 2 のエンジンを動かす。残りは Bad2 用の `T2BadRes`（AbsWN M M[n]・qn の t_1 ◁ v_M(q)）。次はこの 2 つを値の議論で示す。
- T2BadRes の次の手（2026-10-25 の測定、scratchpad の qnstar.py・abswn.py）:
  - T2QN1Bad（t_1 ◁ v_M(q)）: c ∈ (t_1, v_M(q)] の成分は V + ω^S の成分を押さえる（add_omega_succ_lhd）。なので
    (★d′) ∀ u, comps u ω_T の各成分が comps u (V + ω^S) ∪ {0} のどれか以下（ω_T = v_T(q) の最後の項、= ω^{S_T}）
    から t_1 ◁ v_M(q) が出る。c = v_M(q) の場合の (★d) は 4119 件すべてで成り立つ。S だけでの支配は偽（268 件、V = v(r) の成分が要る）。
    - Bad2 の qn では g = q、p は q の前の bump 子、x − 1 は p の部分木の最後の列で、M では祖先 k へ上げ、M.take x では上げを失う（v_T(x − 1) = V′ + 1、V′ = v(P₁(x − 1))、P₁(x − 1) < r）。
    - ω_T の成分は bump 子 j の子 k の o_T(k) の成分。PO の第 1 の選言（o_T(k) ⊴ o_M(k)）なら o_M(k) の成分で押さえられる。弱い k（x − 1）は o_T(x − 1) = ψ_{V′+1}(0) なので comps V′ が要る。これは T0BadSeedsH7 (1) と同じ核（上げ先が祖先のとき、W が吸収する V′ の項の成分は W と V′ の残りの成分で押さえられる、std 標本で例外 0）。
  - T2AbsNBad（AbsWN M M[n]）: 形 B の BumpAbsCB（HDropU の欄、Bad2 でも成り立つ）の第 1 の選言と T2BumpMono（HBumpExt）から、弱い道をとらない列では出る（ガードは absWN_of_absC と同じに外せる）。弱い道の列（WkVA ∧ WCSP ∧ CntX）の扱いが残る。M[n] で前件が立つのは graftBb2St の 3 件だけ（i = q、x は q の bump 子の葉）。
  - T2CBadOut: 欄 un（x − 1 が上げない）は C の形のエンジン全体（C_frame・qP_C など）で使われる。T2CBad（ext2 の 6 個）は C の形で x − 1 が上げるので、別のエンジンが要る。Bad2 ∧ T2CBad は測った集合に現れない。
- T2CBadOut を消す案（2026-10-26 の調べ）:
  - C の形のエンジンは欄 un（x − 1 が上げない）を 12 ファイル・約 60 か所で使う。核は V3T2SeedC の `qP_C`（q は M.take x で数えない）、`C_frame`（M[n] の r・q の形）、V3T2CVq の `c_vqP_of_un`（v_T(q) = qnS）。他はこれらに un を渡すだけ。
  - `C_frame` は agree_by_rank で、M[n] と M.take x の値が o(r) より順位の低いすべての列（o(q) を除く）で一致することを使う。T2CBad では x − 1 が M[n] で上げ（M と同じ、upg_NQ は x − 1 → x の上げがないことだけを要る）、M.take x では上げないので、x − 1 から q までの道で一致が崩れる。
  - 直し方の見込み: q の部分木（q < i < x）では M[n] の値を M の値と比べ（上げ・数える子・子が M と同じ）、q の部分木の外では今までどおり M.take x と比べる。v_N(q) = qnS は un なしでも成り立つ見込み（M[n] の x は bump 子でないので項が消え、p の項は M と同じ）。`qP_C` は「x − 1 が q へ上げない」で足りる見込み。
  - 残り hPRE の欄 C の `un` は T2CBad で偽なので、文脈を T2CBad に広げる前に外す必要がある。
  - T2CBad の族: cbadext（3756 個）に 10 個。
  - 確かめた結果（10 個、M[2]・M[3] の 20 件）: v_N(q) = qnS、q の部分木で M[n] の値 = M の値、q は M.take x で数えない、は成り立つ。しかし T2CBad では q − 1 が q へ上げる（10 個すべて）ので、v(q) の違いが q の前の兄弟 d（CL_T(r) の列）へ伝わり、o_N(d) は o_T(d) とも o_M(d) とも違う。C_frame の結論 hval（d ∈ CL_T(r) で o_N(d) = o_T(d)）がそもそも偽なので、一致の範囲を絞るだけの直しでは足りない。種 o_N(r) の引数が M.take x の値で書けないので、C の形とは別の組み立てが要る。
- （以下は当時の案）- BadOutT2B（t = 2）: t = 2 の仮定は Bad2 でも成り立つ（desc「t = 2 の仮定は Bad2 でも成り立つ」）。手順の案:
  1. DropResHB の定義（いま V3GlobV2）を Res3W（V3InvW）より前のファイルへ移す（HardArg・VSmallNew・BumpWeakSrcB・BumpAbsCB に依る。import の循環を先に確かめる）。Res3W の欄を DropRes から DropResHB（形 B、HDropU の欄）に替える。Res3W を使い drop_all を呼ぶ 15 ファイルで、drop_all → drop_all_hardB、argT → hard、bump_drop → bump_dropB に置き換える（作業はブランチで）。
  2. StepCtxV2 に欄 RB : DropResHB（ctx_V2 で HDropU から）を足し、⟨C.R.drop⟩ を ⟨C.RB⟩ に。
  3. 特別な使い道（QNDropV の強い BumpAbsC と NoBad3、V3T2AbW、V3T2Top、t2_dropsC の n ≤ 1）を、¬Bad2 なら旧の欄、Bad2 なら種の事実か root_drop_any に分ける。
  4. t = 2 の仮定の文脈を「¬Bad2 も Bad2 も満たす文脈」に替え（中身は Bad2 で測ってある）、最上位の Bad2・t = 2 の枝をエンジンで示して BadOutT2B を消す。
