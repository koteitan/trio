# Ytosk: 引き継ぎの作業内容（2026-10-12）

Ytosk 氏の翻訳（3 行 BMS の行列 → 拡張 Buchholz の項）が、SRO より下で正しいことを Lean 4 で証明する作業の引き継ぎ書。
経過の詳しい記録は `Ytosk/desc.md`（日本語、時系列）。この文書はその要約と、次にやることの一覧。

- SRO = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)
- 標準形 `Std` = SRO から展開でたどり着く行列（`Ytosk/lean/Ytosk/BMS.lean`）
- 展開は M[n] と書く（Lean の `expand M n`、n はコピーの個数）

## 1. 作業ツリー

✅ は、その枝に書いた作業が完了した印。子が全部完了した枝は、親に ✅ を付けて子を表示しない。
「条件付きの組み立て」と「測定」は、それぞれ完了しても、残った仮定の証明にはならない。

**Inv3V2 は目標 4 の証明で使う、値の条件をまとめた束。**
各行列でこの束が成り立つことを、基底・1 列落とし・展開で証明する。
その結果を使って、値が標準形で展開すると下がること（Desc3）を示す。
旧い束 Inv3V には偽の条件があるため、Inv3V2 に直している途中。

- ✅ **1. 値が定まる（v・o が循環しない）**
- ✅ **2. SRO より小さい標準形は SRO から届く**
- **3. 順序を保つ**
  - ✅ 目標 4 が成り立てば順序を保つ、という証明（`order_pres`、V3Order）
  - その仮定 Desc3 の証明 → **目標 4 が残っている**
- **4. 値が標準形で、展開すると下がる（Desc3）**
  - ✅ 共通の土台
  - **証明で運ぶ束を Inv3V2 に直す**
    - ✅ 新しい束と各条件の定義（V3Inv2）
    - ✅ 未測定だった条件の全数確認。TrigS の反例を見つけ、TrigS0 に修正
    - ✅ 狭めた条件から実際の使い所の条件を出す補題（`hAUζ_of_absUS`・`hTPLζ_of_tplos`・`hLo_of_TPLS`・`hYB_of_trigS0`）
    - 既存の最上位・各型の展開を Inv3V2 に接続する
    - ✅ FrameV・AbsDN・TP1C の扱いを新しい束に合わせる（FrameV2、V3FrameV2。AbsDQR・TPLoQR は全 10 集合で例外 0）
  - **各段で Inv3V2 が成り立つことを示す**
    - ✅ 基底 SRO[n]（`hBaseV2_holds`）。追加の仮定なし
    - 1 列落とし
      - ✅ 残りの条件を仮定した組み立て（`inv3V2_take`）
      - ✅ PH3cG・FC3・VSmallRAll の保存。落とす補題の結論を仮定した証明
      - 落とす補題の残り（DropRes など）。強い UpgAbsX の反例も修正する
        - ✅ UpgAbsXW（T2Ext の x − 1 の族）と落とす補題の弱い枝の一般化（WCSP の副条件を外し、WeakCS を BumpWeakSrc へ。UpgAbsXW の第 3 条件を行 1 に、SmallSelf(V + 1) を追加）。drop-wkx2 を main に入れた（2026-10-17、desc.md「drop-wkx2 を main に入れる・t = 2 の強い吸収を悪い形だけに」）
        - ✅ t = 1・q = r・L = 1 の強い UpgAbsX（hUA1・T1UpgQRV2、偽）を外した（t1-qr2、drop-wkx2 と一緒に main へ）
        - 最上位の落とす補題の残りは HDropV2W（弱い選択肢に行 1 の条件なしの UpgAbsXW0、11 集合で例外 0）。t = 0 の強い吸収は名前つきの残り T0UpgAbsV2（偽: std_a 2 件・std_b 240 件）。易しい形（r ≠ x − 1 で r はのりしろの子でない、T0Easy）ではエンジンは強い形を使わない（PO.zero_t0・CntX.nocnt_t0）。T0UpgAbsV2 は ¬T0Easy の場合だけで、偽なのは r = x − 1 の形（std_a 1・std_b 105 件）
          - ✅ r = x − 1 の弱い場合を t0_core・t0_otdS・t0_vsmallF_atC で扱う（t0_S1W・t0_S1AW・counted_first0・lhd_or_weak_t0）。T0UpgAbsV2 はのりしろの場合だけになり測って真
          - 残り `T0ArgBRes`（r = x − 1 の形の g の引数の段の ◁、11 集合で例外 0）の証明
        - DropResH の残り（HardArg・VSmallNew・BumpWeakSrc（形 ∧ WeakCS）・UpgAbsXW・BumpAbsC）と SeedR の 11 集合の測定（`tools/probe_dropres.py`、標本では例外 0）と証明。AbsSR は最上位から外れた（top）。AbsSR の t = 0 の欄 BumpAbsLo も偽で、t0 が弱い形 AbsWN に替えた（落とし側は BumpAbsC から出る）
        - ✅ AbsSR から t = 2 の欄（srow = 2 → BumpAbsS）を外した。使う所がなく、標準形で偽だった（HAbSV2 は t = 0 の BumpAbsLo だけになった）
      - 落とした行列の枠の条件（TakeFrameV2）、TP1LeafG・TP1WLeafG（最後の列が根の場合の RootP は top の `rootP0_take` で済み）
        - 10 集合と、落とした行列の追加分（`tmp/ytosk-handoff/sets_take/`）での測定（`tools/probe_frame7.py`・`tools/probe_leafg.py`）。top の `tools/probe_hframe.py` と同じ欄だが、top とは drop が測ると決めた（top は走らせない）
    - t = 0 の展開
      - ✅ 旧 Inv3V 上の条件付きエンジン（`hExp_t0_topU`）
      - ✅ Inv3V2 への接続（`t0_final_inv3V2`・`expT0V2_of2`、V3T0Inv2）。PH3cG・FC3 も接続、旧 Inv3 は使わない（V3T0C の Inv3C）
      - ✅ VSmallRAll の保存（`vsmallRAll_N_t0`、V3T0VSRAllN）。残りなし
      - N の最後の列の枠の 10 欄と葉の条件（top の共通の残り HFrameV2・HLeafV2）
      - 切り口の残り T0CutResGGC（t2 の T2CutA と同じ形）
        - ✅ 10 集合の測定（cutpos.py）。例外 0
        - 証明。局所的な形は非標準形で偽で、展開の履歴を運ぶ不変条件が要る（desc.md「T0CutResGGC の 10 集合の測定と、証明の筋の調べ」）
          - ✅ 履歴の土台 S1（兄弟の部分木は辞書式で増えない）はすべての標準形で成り立つ（`S1_std`、V3S1Std。trio の cnf_ST_TS から）
          - 兄弟の切り口の位置の値の条件（S1 だけでは出ない）
        - ✅ T0CutResGGC を使わない t = 0 の組み立て（影の枠を直接扱う。`expT0V2_of3`、V3T0Inv2S）。残りは RwClosed（書き換える枠で B < hi(y) なら B は閉じている、ClosedA）
        - ✅ 強い BumpAbsLo（標準形で偽）を弱い AbsWN（T0AbsW）に替えた組み立て `expT0V2_of4`。残り T0AbWRes（AbsWN の証明、drop の筋）
          - ✅ T0AbWRes ⟸ HDropV2 ∧ T0PrefixInv（`t0AbWRes_of`、V3T0AbW）。残り T0PrefixInv（M[n] の接頭辞の Std・Inv3V2、top に確認中）
          - 次: T0PrefixInv を最上位で出せるか（top の答え待ち）。全数の測定の再開コマンドは desc.md「t0 の停止時点」
          - ✅ RwClosed（種類 cut の枠で B は ClosedA）の 11 集合（10 集合＋std_a）の測定。例外 0
          - RwClosed の保存
            - ✅ 基底・1 列落とし・t = 0・t = 1（V3RwClDrop・V3RwClT0・V3RwClT1）
            - ✅ t = 2 の組み立て（`rwClosed_expand_t2SV`、V3RwClCopy・V3RwClSh・V3RwClSeed・V3SubstLev・V3VAnc）。残り: T2CopyK CopyLowK（P の写しの枠で前提 → ClosedLow）、T2VAncStep（M[n] の行 1 の 1 段の VAnc）、T2X1Cl（前提つき、11 集合の全数で例外 0）
              - ✅ 共有の値の条件 VDomF（t1 の T2VRAK・t2 の FDsh と共通）を写しの構造から T2VAncStep に帰着（t2CopyK_vDom_of）
              - ClSh（項だけの σ 不変性）は偽（反例は V3RwClSh の冒頭）。旧 `rwClosed_expand_t2S` は使わない
              - CopyCutK の測定（vprefix5.py）・T2X1Cl の測定（x1cl.py）
            - 最上位の帰納法で RwClosed を運ぶ（top が形を決める）
    - t = 1 の展開
      - ✅ 旧 Inv3V 上の条件付きエンジン（`hExp_t1OP`）
      - ✅ q = r の条件付き入口を Inv3V2 に接続。実際の添字を使い、旧 AbsD・TrigOmC を外す（`qr_final_inv3V2`）
      - ✅ q != r の条件付き入口を Inv3V2 に接続。旧 AbsD・AbsU・TPLo を始点の条件に替える（`qn_final_inv3V2`）
      - ✅ ExpT1OutV2 を HFrameV2・HLeafV2（top の共通の残り）だけから（`expT1Out_V2_glob`、V3T1VSRAll）。運ぶ述語は CopyCoreV2 ∧ VrLe ∧ VSmallF ∧ FrameMapT1 ∧ VrDomQ。TP1C・TP1WC は PH3cG と葉から
      - ✅ PassRootRes を S1 から証明（`passRootRes_of_S1`、V3EqSibS1・V3PassRoot）。S1 は `S1_std`（V3S1Std）
      - ✅ VSmallRAll の保存（`expStep_frameMapT1`・`vsmallRAll_of_mapT1`）。N の書き換える枠は M の枠に写り、M の VSmallRAll だけから出る
    - t = 2 の展開と下降
      - ✅ 旧 Inv3V 上の条件付きエンジン（`hExp_t2_G`・`hR2_t2_of`）
      - Inv3V2 への接続と、新しい枠の条件の証明
        - ✅ 生産者 `expT2V2_of`・`r2V2_of`（V3ExpT2V2）と最上位への差し込み（top の V3TopV2）
        - M[n] の VSmallF・FrameClosed（T2VSFCV2）
          - ✅ VSmallF（`vsmallF_expand_t2V`、V3T2VSF）。残りは種の列の枠 `T2SeedFrames QVSF M` と M.take x の VSmallF
          - ✅ FrameClosed の骨組み（`frameClosed_expand_t2`、V3T2FC）と T2VSFCV2 の生産者（`t2VSFCV2_of`、V3T2VSFC）。残りは FDsh（FrameDom の σ 不変性、項だけの主張）と種の列の枠 T2SeedVSFV2・T2SeedFCV2
          - ✅ 種の列の枠（VSmallF・FrameOT・FrameClosed）を 4 つの場合で証明（V3T2SeedFr・V3T2SeedFr2・V3T2SeedFrV2）。残りは T2SeedDomV2（qn・C の s′ の成分、9 集合で例外 0）
          - FDsh の証明（`frameDom_of_kind` により、写しの枠の s の成分の条件の σ 移送に帰着できる見込み）
      - VSmallRAll の保存（T2VRAV2）
        - ✅ 骨組み `t2VRAV2_of`（V3T2VRA、t1）: T2VRAV2 ⟸ QVRAshK K（枠の条件 K のもとでの σ 移送）∧ T2BelowXRes ∧ T2VRASeed（種の列の枠）∧ T2VRAPre（接頭辞の段は M の段）∧ T2VRACopy（意味のある写しの段は P の段で u ≤ V）∧ T2VRAK K（守られた写しの枠の条件）。最上位は K = KStepVRA（移送そのもの、qVRAshK_step）
        - ✅ T2VRAPre ⟸ T2SeedPreShape（種の列 p の枠の形）（`t2VRAPre_of`、V3T2VRAPre）
        - ✅ T2VRASeed（種の列の枠）を qr・qn・C の q で証明（`t2VRASeedG_of`、V3T2VRASeed、t2）。残りは T2VRAQNDom（9 集合・std_b で例外 0）と T2VRASeedSVC（sv・C の r の枠）
        - ✅ `qVRAshK_KVRA`（V3T2VRAK）: K = VDomF ∧ KAG のもとで σ 移送。残り T2VRAK KVRA ⟸ T2CopyK CopyVDomK（t0 と共有）∧ T2VRAK KAG（`t2VRAK_KVRA_of`）
        - 残り（t1）: T2VRAK KAG（KA・KG、11 集合で例外 0）、T2VRACopy（11 集合で例外 0）、T2SeedPreShape。最上位の K を KStepVRA から KVRA に替えるのは測定の後（VDomF 側は t0 の t2CopyK_vDom_of）
        - ✅ q = r の偽の仮定 T1UpgQRV2 を除去（t1-qr2、main に入った）
      - 始点の残り（T2SeedQRRes・QNRes・SVRes・CRes）と C の値の残り UpgSibV
        - ✅ M だけで決まる欄（qr の ks・vs、qn の vqlt・Bc、sv の decP）を証明（V3T2SeedRes）
        - ✅ sv の rw を T2SVStrict 1 つに（V3T2SeedRes2）、qn の σB を数えない子の残り QNUncRes に（V3T2QNSig、一般の V′ の closure V3T2TameG）
        - ✅ QNUncRes を UpgSibV から証明（`qnUncRes_of_sibV`、V3QNUncV、top）。最上位の種の残り T2SeedPResRC は qr・sv（T2SVStrict と lhd）・qn の base・C の T2SeedCRes
        - ✅ 構造の残り T2SeedCNext は標準形で偽（反例は desc.md、候補 UpgRun も偽）。C の欄を CRes ∧ CBig に替え、CBig を値の残り UpgSibV から証明（`t2SeedCBig_of_sibV`、V3CBigV）。UpgSibV は全 10 集合で例外 0
        - ✅ UpgSibV を難しい形 UpgSibVHard に絞った（`upgSibV_of_hard`、V3SibV。a に子がない同じ列と、b = (e0 p+1, y, 0) は S1 から証明）
        - ✅ (ii) e1 b < e1 a を次の列への上げ（upg b = b + 1、10 集合で 0 件）だけに絞った（V3SibV）
        - ✅ C の vqP を un から（`c_vqP_of_un`、V3T2CVq、t2）。C の残りは decP・un（std_b で例外 0）・rw・lhd
        - ✅ UpgSibVHard を同じ列の兄弟の値の条件 SibColW（上げの有無を問わない）に帰着（`upgSibVHard_of_col`、V3SibCol）。(ii) は v(b) = v(b+1) ≤ v(u) ≤ v(p) ≤ v(a)（u は g = P_1 b の子で p の祖先、col u = col (b+1)）
        - UpgSibVHard（旧 HSibHardV2）の証明（top）: 同じ列で a に子がある場合（一般の形 SibVCol を値の不変条件として運ぶ。lead 承認、未着手）と、(ii) の次の列への上げ（標準形で 154 件ある）
      - ✅ T2BelowXRes の切り口の仮定 T2CutA を RwClosed に替えた（V3DepRWU、t0 の影の補題を使う）。T2BelowXRes の残りは種での RClaimU・REr、AbsWN
      - ✅ T2BelowXRes を M ごとに（T2BelowXResAt・T2BelowXResV2）。V2 の文脈で T0RwRes・T2SeedPResV2・T2BelowRV2・T2SeedOTV2 に分解（`t2BelowXResV2_of`、V3T2BelowV2）
      - ✅ T2BelowRV2 ⟸ T2SeedClV2（種の閉じた条件、qn・sv・C）∧ T2BumpMonoV2（`t2BelowRV2_of`、V3T2BelowR）。種の RClaimU は類 B0・共通の接頭辞・道の段の閉じた条件から（`rclaim_of_hiB0`）、qr は dom の欄から証明。AbsWN の落とし側は BumpAbsC から（V3T2AbW）
      - ✅ 種の標準形を qr・sv で証明（V3T2SeedOTP）。残り T2SeedOTRestV2（qn・C）
      - ✅ T2SeedPreShape を qr・qn で証明（V3T2SeedPre）。残り T2SeedPreShapeSVC（sv・C）
      - ✅ sv・C の閉じた条件 T2SeedSVCl・T2SeedCCl（k ごとの σ^k X₁）を k を含まない残り T2SeedSVBase・T2SeedCBase に減らした（`t2SeedClV2_of_B`、V3T2SeedSVCl）。σ は段 u ≤ V の成分を「元の成分か σ 像」か V′ の成分に送る（`comps_sh_low`）ので、段 V と道の段で X₁ と V′ の成分が X₁ より小さければ σ^k X₁ も閉じている。C の標準形 T2SeedCOT の前半も T2SeedCBase から（残り T2SeedCOT2、`t2SeedOTRestV2_of_B`）。qn の T2SeedQNCl と標準形 T2SeedQNOT も k を含まない T2SeedQNBase から（`qn_closed_tqN`・`qn_ot_of`）。C の q の値の標準形も T2SeedCBase から（`seedCOT2_of_base`）なので、最上位の残り T2SeedOTRestV2 は消えた。最上位の残りは T2SeedClV2B（T2SeedQNBase・T2SeedSVBase・T2SeedCBase）
      - 測定: T2SeedClV2・T2SeedOTRestV2 の中身は 10 集合で例外 0（seedrr3.py）。T2BumpMono（bumpmono.py、TleN）は 11 集合で例外 0。T2SeedPreShape（preshape.py）は測定中
      - ✅ 強い T2UpgAbs（偽、11 集合で 175 件）を T2UpgAbsW（強い吸収か悪い形 T2UABad、11 集合で例外 0）に替えた。悪い形 q = r = x − 1・上げ先 k < x の n ≤ 1 は `t2_qu_take_bad`（種を r の親の o に移し、r の o・v を弱い呼び出しに。V3T2QUBad）
  - **各段をまとめて Desc3 を得る**
    - ✅ 旧 Inv3V 上の条件付き最上位の組み立て（`trio_terminates_main_GH`）
    - ✅ Inv3V2 上の最上位の組み立て（`trio_terminates_main_V2`、V3MainV2）。旧 Inv3・Inv3V を使わない
    - ✅ 落とした行列の根の RootP（`rootP0_take`）。t0 の `expT0V2_of` を差し込んだ現状の最上位（`trio_terminates_main_V2_now`）
    - ✅ 枠の 10 欄・葉の条件の行列ごとの共通の残り HFrameV2・HLeafV2 と drop・t0 への変換（V3GlobV2、`trio_terminates_main_V2_glob`）
    - ✅ t2 の expT2V2_of・r2V2_of を差し込んだ現状の最上位（`trio_terminates_main_V2_t2`、種の残りを T2SeedPResR に減らした `_t2R`、V3TopV2）
    - ✅ 全員の生産者を差し込んだ最上位（V3TopV2 の中間の形 `trio_terminates_main_V2_base`）
    - ✅ 最上位から偽の強い吸収 HAbSV2 を外した（文脈は Res3AW、t = 0 の下降は ExpT0OutV2 から。`expT0Out_of4`）
    - ✅ 最上位を 1 本 `trio_terminates_main_V2_cur`（V3TopT2B）にまとめた（2026-10-17。旧 `_t2B`・`_t2C` は消し、旧 `_cur` は中間の形 `_base` に）
    - ✅ 2026-10-19: 残りの FDsh は偽だった（`FDCut.not_FDsh`）。行列の残り `T2FDCopyRes`（写しの枠ごとの `FDshAt`）に替え、最上位は偽の仮定を含まなくなった。
    - 今の最上位 `trio_terminates_main_V2_cur` の残りを証明して閉じる。残りは 15 個（2026-10-20、T2UpgAbsW と T0UpgAbsV2 を外した）:
      - drop: HDropV2W（落とす補題の 5 欄）・HSeedV2（SeedR）
      - 共通: HFrameV2・HLeafV2（枠の 10 欄・葉の条件）、HBumpExt（標準形の接頭辞で bump 項は増える）、HSibColV2（同じ列の兄弟 SibColU）
      - t0: T0ArgBRes
      - t2 の種: T2SeedClV2B（k を含まない基 T2SeedQNBase・T2SeedSVBase・T2SeedCBase。閉じた条件・標準形・C の s′ の段 V の成分はここから）、T2SeedPResRCV2B（qr の w1・dom、sv の T2SVStrict・lhd、qn の V < t₁ と k ≥ 1 の欄、C の decP・X₁ < σX₁・lhd）、T2SeedDomV2B（T2SeedQNDom と T2SeedCDom1）
      - t2 のそのほか: T2CBadOut（悪い形の展開、大づかみ）、T2VRAKFD KAG（書き換える写しの枠で低い段すべての KAG。FrameDom の σ 不変性は V3FDCopy で証明済み）、T2VRACopy、T2VAncStep・T2VRAK KAG（写しの枠の KVRA）
      - 次の大きな仕事の候補（2026-10-18）: 手早く減らせる残りは尽きた。どれも新しい値の不変条件を帰納法で運ぶ仕事。
        - T2VAncStep: VAncStep はすべての標準形で測って真。Inv3V2 の欄にして落とし・t0・t1・t2 で運ぶ。中身は「落ちる加数の成分 ≤ Ω_h」（desc）
        - T2CBadOut: C の種を K = M[2].take (x + 1) を基準に作り直す（desc の計画）
        - T2SeedPResRCV2B の qr の w1・dom、sv・C の lhd: σ が X₁ を動かさない構造（吸収）と、σ で保たれる逃げ道
      - 消えたもの（このセッション）: T2SeedOTRestV2、T2SVc0・T2CFrRes（sv・C の種の枠: `no_chg_before_c0`・`t2SVc0'_of_drop`・`cl_C` で証明）、T2VRAQNDom（T2SeedQNDom と T2SeedQNBase から）、T2VRASeedSVC・T2SeedPreShapeSVC（T2SVc0・T2CFrRes に）、T2X1Cl・CopyLowK（偽、HRwClL に）、HRwClL（2026-10-18: 使う側 2 か所を G3 の切り口の補題 `CutClosed.shadow_hShL_from_kind` に替え、StepCtxV2 の欄 rw ごと外した。RwClosedL 自体は証明していない）
      - 残りの測定の状態（2026-10-17、lead。どれも Lean と同じ形の probe）

        | 残り | 測定 | 備考 |
        |---|---|---|
        | HDropV2W | 11 集合で例外 0 | DropResH0 の 5 欄（probe_dropres・probe_uaw1・bumpabsc.py） |
        | HSeedV2 | 11 集合で例外 0 | SeedR（probe_dropres） |
        | HFrameV2・HLeafV2 | 11 集合と落とした行列で例外 0 | probe_hframe |
        | T0ArgBRes | 11 集合と std_b で例外 0 | t0argB.py |
        | HBumpExt | 1 列の場合が 11 集合で例外 0 | bumpdrop1.py（3950 万件） |
        | T2SeedQNBase | 11 集合と ext3s で例外 0（PathLvAll の段、Lc = [] で t₁ ≤ s′ も。qn 23 万件） | qncl.py |
        | T2SeedCBase の σX₁ の欄 | 11 集合と ext3s で例外 0 | ccl.py（hiS） |
        | T2SeedSVBase・T2SeedCBase | 道の段 PathLvA の形は 11 集合と ext3s で例外 0（sv 4.5 万件・C 1.2 万件。すべての段の形は expP・ext3s で偽）。C の段を PathLvAll に強めた形も 11 集合と ext3s で例外 0 | svcbase.py。C の σX₁ の欄は ccl.py |
        | T2SeedPResRCV2B | 11 集合と std_b で例外 0（qn の V < t₁ は qncl.py、C の X₁ < σX₁ は cstrict.py で 11 集合と ext3s で例外 0） | seedqr.py・seedsvc.py。C の un は StepCtxT2 で悪い形を外した |
        | T2CBadOut | — | 悪い形（ext2 に 6 個）の t = 2 の展開。全体の主張の帰結 |
        | T2SeedDomV2B | 11 集合と std_b で例外 0 | seeddom2.py（T2VRAQNDom は T2SeedQNDom と T2SeedQNBase から） |
        | T2VRAKFD KAG | 13 集合の書き換える写しの枠 2,281,152 回（n = 2, 3）で例外 0 | fdcopy_all_frames_trio_codex.py。すべての枠の版 T2VRAKAll は KG が 24 枠で偽。前の T2FDCopyRes は証明した橋で出る。項だけの FDsh は偽（`not_FDsh`） |
        | （証明済み）T2SVc0 | 11 集合と ext3s で例外 0 だった。証明した | svpre.py |
        | （証明済み）T2CFrRes | 11 集合と ext3s で例外 0 だった。証明した | cvra.py |
        | T2VRACopy・T2VAncStep | 11 集合と ext3s で例外 0 | probe_t2vra・vanc1 |
        | T2VRAK KAG | 11 集合で例外 0 | probe_t2vrak |
        | HSibColV2 | 11 集合と std_b で例外 0 | sibcolall.py（SibColW） |
- **5. 全射**
  - ✅ 目標 4 と EvalCof が成り立てば全射、という証明（`surj`、V3Surj）
  - Desc3 の証明 → **目標 4 が残っている**
  - 項側の共終性（値を十分大きく近づけられること、EvalCof）の証明

旧 Inv3V 上の条件付き定理には、標準形で偽の条件が含まれる。このままでは目標 4 を閉じられない。
証明済みの定理の公理は propext・Classical.choice・Quot.sound の範囲。

## 2. 本題（目標 4）の現状

### 作戦

`Desc3` を、標準形についての帰納法で示す。各行列 M について、値の不変条件の束（`Inv3V`）を運ぶ。運ぶ仕組みは 4 つ。

- 基底: SRO[n]
- 1 列落とし: M → M.take x（x = 最後の列）。落とす補題 `drop_all*`。hLast とよぶ
- 展開: M → M[n]。最後の列の型 t = 0, 1, 2 ごと。hExp とよぶ
- t = 2 の残りの仮定: hR2（`Res3T2`）

構造の不変条件（行列の形だけの性質）は、すべての標準形で証明済み（`sInvXJ_std`）。残っているのは値の不変条件だけ。

### 最上位の定理（どれも仮定つき）

- **Inv3V2 の上の全体: `trio_terminates_main_V2`（V3MainV2）**。残りは V3ResV2 の 8 個の名前つきの Prop（desc.md の節「Inv3V2 の上の最上位」）
- 旧い全体: `trio_terminates_main_GH`（V3RestTakeG）。VSmallR を使わない形。偽の欄を含む Inv3V の上
- t = 0 の hExp: `hExp_t0_topU`（V3T0TopU）
- t = 1 の hExp: `hExp_t1OP`（V3TPath）。新しい条件付き入口は `qr_final_inv3V2`（q = r）と `qn_final_inv3V2`（q != r）、どちらも V3Inv2 で Inv3V2 を使用
- t = 2 の hExp: `hExp_t2_G`（V3ExpT2M4）。x より前は `t2BelowXRes_of_L`（V3T2SeedWire）
- t = 2 の hR2: `hR2_t2_of`（V3T2R3）。残りは T2BelowXRes だけ

**注意: 今の `Inv3V` には、標準形で偽の欄が入っている**（AbsD・TPLo・AbsUW・TrigOmC）。このため、上の最上位の定理は、今のままでは仮定が満たされない（何も言っていない）。これを直すのが次の仕事。

### 次の仕事: Inv3V2 への一括の移行

束の定義は `Ytosk/lean/Ytosk/V3Inv2.lean`。基底・1 列落としの組み立て・t = 1 の両方の条件付き入口から使用している。展開側と共用するため、TrigS0 の定義は `V3TrigSeed`、AbsDS・AbsUS・TPLoS とその接続の補題は `V3SeedFields` に移した。条件の内容は変えていない。既存の最上位と展開の全ての仕組みへの移行は未完。元の欄の表は desc.md の節「Inv3V2 の下書き: 欄の一覧と生産者・消費者の表」、再開後の変更は末尾の節を参照。

方針: 偽の欄を、実際に使う所が要る形に狭める。偽の欄を実際に使っているのは、どれも t = 1 の最後の列の枠だけだった。そこで「最後の列の枠の欄」に替える。枠の欄は行列ごとの主張なので、M から M[n] へ運ぶ補題が要らなくなる。

| 今の欄（Inv3V） | 新しい欄（Inv3V2） | 測定 |
|---|---|---|
| AbsD | AbsDS（q ≠ r の枠、始点での吸収） | 9 集合で例外 0 |
| AbsU | AbsUS | 10 集合の全数で反例 0 |
| TPLo | TPLoS | 10 集合の全数で反例 0 |
| AbsUW | AbsUWL ＋ AbsUW0 | 9 集合で例外 0 |
| TrigOmC | TrigS0（子 c の dOf = 0 の枠） | 旧 TrigS は T2Ext・expP で偽。修正版は全 10 集合で反例 0（2 集合を全数再走査、8 集合は旧強条件の全数確認による） |
| （大域の仮定） | PH3cG・FC3 | 8 集合で例外 0。保存はすべての仕組みで証明済み（`Ytosk.G` 名前空間） |
| （大域の仮定） | VSmallRAll（`vra`） | 10 集合の全数で反例 0。基底と 1 列落としでの保存は証明済み |
| VSmallF・FrameClosed・FrameOT・BumpKidsDec・BumpTermDec・TP1C・TP1WC・TPLoW・AbsDW・TPLoN・AbsDN・rootS・rootP・Cons・Good3・Rk | そのまま | Lean の形で真 |

始点 = o_{M.take x}(r) = `(drop1 M x rk).o r`。鎖の添字 ζ はどれも始点以上なので、始点での主張から ζ での主張が fsD の単調性で出る（例 `hADζ_of_absDS`）。

移行の手順:

1. **完了**: AbsUS・TPLoS・旧 TrigS・VSmallRAll を、必須 9 集合と ext1x の全 10 集合で全数測定。結果・再現手順は `Ytosk/inv2-measurement.md` と `Ytosk/inv2-measurement.json`。
2. **完了**: 旧 TrigS が偽だったので、実際の消費者が始点を使う `dOf c = 0` の枠の TrigS0 に狭めた。`hYB_of_trigS0` で十分性を証明し、反例のあった T2Ext・expP を全数再走査。修正版は反例 0。
3. 最上位の定理と、各仕組みの欄を作る補題を、1 回の計画した変更で `Inv3V2` に移す。消える補題・要る変更の一覧は desc.md の同じ節の末尾。主な変更:
   - `FrameV` の ad・tplo を「q = r の枠の D の列での AbsD・TPLo」に狭める
   - `expStep_absDN` が使う I.ad を AbsDS から出すか、AbsDN も枠の欄にする
   - t = 1 の TP1C の運び（`expStep_tpG`・`qr2_tpG`）を、PH3cG ＋ TP1LeafG・TP1WLeafG から出す形（`tp1C_of_ph3cG`、V3TP1CutG）に揃える。TP1ResG から TrigCutG を外す
   - `trio_terminates_main_GH` の大域の仮定 hNG（NoGapP、偽）・hP0・hD0 は AbsD・AbsU を作るためだけなので、AbsDS・AbsUS に替えれば外せる
   - **完了**: q = r の hYBs は `dOf c = 0` の枠だけ、hYB は実際の添字 `m + dOf c` に狭めた。`qr_final4S`・`qr_final_inv3V2` で TrigS0 を展開側へ接続。受け渡すだけだった AbsD もこの枝から外した
   - **完了**: q != r の hTG・hTY2 を実際の ζ にそろえた。`omega_fsD_hole_at`・`vlocal_t1_at`・`t1_main_vlocS`・`qn_final_inv3V2` で始点の AbsDS・AbsUS・TPLoS を展開側へ接続
4. VSmallRAll が t = 0・t = 1・t = 2 の展開で保たれることを示す（作る補題がまだない）。
   - t = 0 には穴が 1 つある。最後の写しで、段の鎖が g の上を通る場合に「N で書き換えるなら M.take x でも書き換える」が 2 件偽。

再開後に証明した組み立て:

- `hBaseV2_holds`（V3BaseInv2）: SRO[n] の Inv3V2 と Res3A。追加の仮定なし。
- `inv3V2_take`（V3TakeInv2）: Inv3V2 の 1 列落とし。残りは DropRes・TakeFrameV2・TP1LeafG・TP1WLeafG・最後の列が根の場合の RootP。DropRes の強い UpgAbsX はまだ変更していない。
- `hADζ_of_absDS`・`hAUζ_of_absUS`・`hTPLζ_of_tplos`・`hLo_of_TPLS`（V3SeedFields）、`hYB_of_trigS0`（V3TrigSeed）: 新しい条件を消費者で使うための補題。
- `qr_final_inv3V2`（V3Inv2）: t = 1・q = r の入口。Inv3V2 から展開の Inv3V2・値の標準性・下降を組み立てる。残りは DropRes、落とした行列の Inv3V2、始点の成分の条件、コピーを 1 個増やす各段での Inv3V2 の保存（ExpStepT1）。旧 AbsD・TrigOmC は要求しない。
- `qn_final_inv3V2`（V3Inv2）: t = 1・q != r の入口。残りは DropRes、落とした行列の Inv3V2、ExpStepT1。始点の下降は落とす補題から証明。旧 AbsD・AbsU・TPLo は要求しない。
- `expStep_closure_inv3V2`（V3ExpInv2）: t = 1 の各コピーで PH3cG・FC3 を保存。構造の条件と Inv3V2 だけを使う。`expStep_tp1_inv3V2` は葉の条件 T1LeavesV2 を仮定して TP1C・TP1WC も保存する。T1LeavesV2 自体と束全体の保存は未証明。
- `expStep_core_inv3V2`（V3ExpInv2）: コピーごとに上記 10 条件を保存。`qr_core_final_inv3V2`・`qn_core_final_inv3V2` は、その部分の束 CopyCoreV2 と値の標準性・下降を出す。DropRes、始点の Inv3V2、q = r の始点の成分の条件は残る。Inv3V2 全体の各段の保存を仮定しないが、結論も束全体ではない。
- `expStep_vsmallF_inv3V2`・`expStep_core_vsmallF_inv3V2`（V3ExpInv2）: VSFRes2 を仮定して VSmallF も保存。VSFRes2 は、変わる最後の加数の成分を抑える条件で、まだ証明していない。
- `expStep_vsmallF_pass_inv3V2`・`expStep_core_vsmallF_pass_inv3V2`（V3ExpInv2）: 旧 Inv3 を要求しない `expStep_vsmallF2S` に接続し、残りを元の行列の PassRootRes に絞った。VSFRes2 自体を証明したわけではなく、展開で与えられる Good3 も使う別経路。
- `vrle_prefix_inv3V2`（V3ExpInv2）: DropRes と始点の Inv3V2 から v(r) の始点での上限を証明。これと上記保存を使う `qr_vsmallF_final_inv3V2`・`qn_vsmallF_final_inv3V2` は、CopyCoreV2・VSmallF・値の標準性・下降を出す。束全体の保存はまだ出ない。
- PassRootRes の測定: `tools/probe_passroot.py`。全 10 集合、入力 5,375,155 行列のうち SRO より下は 5,375,152、t = 1 の評価は 2,681,874、前件を満たす 47,654 枠で反例・評価失敗 0。詳細・再現手順は `Ytosk/passroot-measurement.md` と `.json`。一般の標準形での証明ではない。
- Ytosk 全体のビルド成功。公理は許可された 3 つの範囲。既存の最上位と展開側への接続は次の仕事。

### 未解決の核（名前つきの残りの仮定）

どれも測定では例外 0。証明はまだ。

- **T0CutResGG**（t = 0 の切り口、V3T0DepT・V3T0Thr）。8 集合で例外 0。「どの切り口でも保たれる」は偽で、B の最後の加数として実際に現れる切り口だけが保たれる。閾値の補題（V3T0Thr、塔の形 ThrA・ThrV）は真。足りないのは、引数の中の切り口 ψ_a(Ω_s) を扱う入れ子の主張。T0CutKappa（切り口は Ω の葉）は偽。
- **UpgSibV**（値の主張、V3CBigV、最上位の HSibV2）: 同じ親の隣り合う子 a < b で、a が a − 1 から上げられ topped、b が b − 1 から上げられないなら v(b) ≤ v(a)。全 10 集合で例外 0。偽と分かった構造の主張 T2SeedCNext の代わり。
- **t = 2 の始点の残り**: T2SeedQRRes・QNRes・SVRes・CRes の閉じた形の性質（M と M.take x だけの主張、7 集合で例外 0）。
- **1 列落としの残り**（全体の仮定）: VSmallNew・VSmallNewR・ShadowC・UpgAbsX・Seed・BumpAbsC（弱い形）・AbsSR。測定で真、証明はまだ。
  - T2Ext の x−1 の族（16 件）では UpgAbsX が偽で、1 列落としの結論も別の形で破れる。弱い形 UpgAbsXW と、落とす補題の結論 PO の弱い枝の拡張で直す変更を作った。これはローカルのブランチ `dropfix-wkx` の作業用コミット eb0cca69（49 ファイル）にあり、main には入っていない。main に載せ直す前に、2 つの測定を 9 集合で行うこと: upgx2（「x−1 で強い吸収が破れるなら x の行 2 ≠ 0」）と newpv2（新しい形の PO・PV）。t = 2 の道では強い UpgAbsX がまだ要り、それを `Res3T2.ua`（大域の名前 `T2UpgAbs`）として表に出してある。これは T2Ext で偽なので、t = 2 側で広げる必要がある。
- **hLast の残り**: TakeRest3（M.take x の TPLo・AbsUW・AbsDN）。Inv3V2 に移れば TPLo・AbsUW は消える見込み。
- **段 0 の残り**: Z0Link・PhiX0R は偽と分かった。段 0 の扱いは Inv3V2 の枠の欄の形で考え直す。

### 偽と分かったもの（使わないこと）

AbsD・TPLo・AbsUW・TrigOmC（Inv3V の欄）、TrigS（子の dOf を制限しない旧案）、PhiX・NoGapP・NoGap0PosP・LevLeafInv・PrefLast・VKFree・Z0Link・BandLast、VSmallR（全段の形も hi ≠ 0 の形も）、旧 PH3c（cutsNS）、NoVB、t0.hG′・t0.hU、T0CutKappa、T0ThrGRes、強い BumpAbsC、BumpWeakSrc（旧形）、FrameClosedHi、TPLoN の全列の形、T2SeedCNext・UpgRun（どちらも標準形で偽）。反例は desc.md の各節にある。

本題の主張そのもの（値は標準形で、M[n] の値 < M の値）は、どの測定集合でも成り立っている。崩れているのは証明の組み立てだけ。

## 3. 測定の決まり

不変条件・残りの仮定を「測って真」とみなすのは、**次の集合すべてで例外 0 のときだけ**。今回、狭い集合で例外 0 だったものが、広い集合で何度も偽になった。

| 集合 | 中身 | ファイル |
|---|---|---|
| C′ | M[n] とその接頭辞 | `Cprime.pkl` |
| T0Ext | 標準形の接頭辞に (e0 a + 1, 0, 0) を足したもの | `t0ext.pkl` |
| d3s・deep2・deep3 | 深い標準形 | `d3s.pkl`・`deep2.pkl`・`deep3.pkl` |
| ext1 | 4 集合の長さ 13 以下に、足すと標準形になる任意の 1 列を足したもの（108 万個） | `ext1.pkl` |
| ext1x | ext1 の標本の M[2]・M[3] | `ext1x.pkl` |
| T2Ext | t = 2 の行列の M[2]・M[3] とその接頭辞（121 万個） | `t2ext.pkl` |
| ext2 | SRO から深くランダムに展開した行列と、その 1 列伸ばし（149 万個） | `ext2.pkl` |
| expP | t = 2 の行列の M[2]・M[3] の接頭辞（61 万個） | `expP.pkl` |

- ファイルの場所: `trio/tmp/ytosk-handoff/sets/`（git の対象外）。どれも SRO より下に絞ってから使う。
- 測定スクリプト: `trio/tmp/ytosk-handoff/probes/<担当名>/`（groupA・t0-exp・t1-exp・t2・drop-fix・closure）。中の集合のパスは古い一時ディレクトリを指しているので、上の場所に書き換えて使う。
- 測るプログラムの欄の定義は、Lean の今の定義と 1 行ずつ突き合わせる。古い定義で測って「偽」と誤って報告したことがある（VSmallF・FrameClosed）。
- 集合を作るときは「標準形の接頭辞に任意の標準な 1 列を足す」と「各型の M[2]・M[3] の接頭辞」を必ず入れる。
- 標準形かどうかは yaBMS（https://github.com/koteitan/yaBMS）の `bms -s` で確かめる。trio の直下に `./bms` がある。
- python の測定は、1 本あたり 4 プロセスまで、`nice -n 15`、重い実行は同時に 1 本。28 コアのマシンで、6 人が 6 プロセスずつ走らせたら全部埋まった。

## 4. 作業の決まり

- Lean の確認: leanman スキルに従う。`env --chdir=Ytosk/lean nice -n 15 leanman build Ytosk.<依存>` のあと、`env LEANMAN_TIMEOUT=900 nice -n 15 leanman check --backend lean -C Ytosk/lean <ファイル>`。
- コミットするファイルに sorry を入れない。仮定は定理の引数として明示する。公理は propext・Classical.choice・Quot.sound だけ（`#print axioms` で確かめる）。
- 新しいファイルは `Ytosk/lean/lakefile.toml` の roots に 1 か所だけ足す。ファイル全体を書き換えない。lakefile をコミットするときは、HEAD の版に自分の 1 行だけ足した blob を作って入れる。他の人の未コミットの行を混ぜない。コミットの直後に roots の数が減っていないか確かめる。
- 共有の定義を変えたら、Ytosk 全体をビルドして緑を確かめてからコミットする。
- git: `git add -A`・`git add .` は使わない。自分のファイルだけを名前で足す。コミットメッセージは日本語。
- シェルで `cd DIR && cmd` を使わない。絶対パス、`git -C`、`env --chdir` を使う。
- trio の外の公開されていないファイルを、公開する文書でローカルパスで書かない。公開先の URL で書く。
- 行列は省略せずに全部書く。例: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)。

## 5. 参照

- desc.md の節「一時停止（2026-10-12 夕方）」: 止めた時点の状態。
- desc.md の最新の節「VSmallF の残りを PassRootRes に絞る」: 再開後の到達点と残り。
- desc.md の節「Inv3V2 の下書き」: 移行の表。
- desc.md の節「訂正と 7 集合の表: Lean と同じ形の欄」: どの欄がどの集合で偽か。
- googology-lean の worktree（ブランチ feature/trio-reach）: 目標 2 の `trio_reach_sro`。googology-lean の main の作業ツリーには書かない（別の作業が進行中）。
