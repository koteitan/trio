# 現入口の11入力の証明地図（2026-11-04）

対象は `V3TranslationAllUV3.lean:22` の `desc3_of_step_enginesV3UU`。以下のファイル名はすべて `Ytosk/lean/Ytosk/` 内。Lean の変更・ビルド・新しい測定はしていない。名前の出現と定理の型を読んだ監査であり、「producer未発見」は今回確認した範囲の意味。

欄数は、外の forall・前件を除いた、入力の最上位の独立した結論の数。枝の内部の連言は補足する。`C` は `StepCtx3`（`V3MainV3.lean:15`）で、Std・SInv・Inv3V3に加えて、修正済み drop と全ての真の接頭辞の Inv3V3 も持つ。**C から出ることと、純粋な構造の不変条件だけから出ることは違う。**

Claude氏の完了報告では今回の全測定は失敗0。ただし測定は証明ではない。新しいU入力は n=2,3、frame/QN検査にも有限の m・分解・eta 探索の制限がある。以下の「未証明」は、producer自体の証明ではなく、その前提を現入口の文脈で全称的に供給する証明が残る、という意味。

| 入力 | 定義・欄数 | 既存のproducer・前提 | 残る未証明の前提 | 広い量化・注意点 | Std/Inv3V3からの見込み |
|---|---|---|---|---|---|
| hD : HDropV3 | `V3TakeV3.lean:20`。`DropV3:14` は2群（各iのPO/PV2とVSmallNew）、葉では3性質。 | `hDropV3_of_inputs` (`V3DropV3.lean:37`) : **HDropInputsV3**から。局所版 `dropV3_of_inputs:28` : SInv・Inv3V3・長さ>=2・**DropInputsV3**。後者は `:13` の5欄 hard=HardArg、vst=VSmallNew、ws=BumpWeakSrcB2、ab=BumpAbsCB2、ua=上げの際の強い窓またはWCSP2。 | HDropInputsV3の5欄をStd+Inv3V3で供給すること。既存 `drop_all_hardW2B` の適用自体は証明済み。 | 全M・Cons/Rkを含む全Inv3V3。hard/ws/abの全列・成分、uaの全i,k,W・旧値の全summand。末列を1つ落とすだけで、展開nの全称はない。 | **分からない**。修正dropエンジンは完成しているが、5つの値の前提が残る。最初は欄別に分けるのがよい。 |
| hF : HFrameV3 | `WfExQ2.lean:167`。10欄 = FrameV3の8欄（`:140`: adsx/aus/tplosx/tploq/auw0/trigs/tplon/adn0）+ TP1LeafG + TP1WLeafG。 | 現形のHFrameV3を出すglobal producerは未発見。`inv3V3_of_parts` (`WfExQ2.lean:151`) は逆にFを読む組立定理。`frameAtN_of_glob` (`WfExQ3.lean:11`) もhFを消費する。旧欄からの `tpLoQ_of_tpLoWs` (`WfExQ1.lean:49`) 等は十分条件にすぎない。 | 10欄のStd+Cons+Rk+Good3からの証明。旧Inv3V2や旧TPLoWsを仮定して済ませることはできない。 | **全標準行列**、全σ,rk。前件にInv3V3はなくGood3だけ。各欄が全末列の枠・hole・レベルを量化。TPLoQは全m、全source i,W。leaf欄も全枠。 | **分からない**。純構造だけでは値の窓をまだ出せない。全体Inv3V3の存在を先に使うと入口の帰納法と循環し得る。最大の束なので欄別に後で扱う。 |
| hAbsU : T0AtV3 T0AbsWU | 外側 `V3T0CarrierV3.lean:127`、本体 `V3T0AbsUpg.lean:17`。2欄=AbsWNxU・NotBumpKidXU（bnd=r）。 | `T0AbsW.toU` (`V3T0AbsUpg.lean:23`) : 旧T0AbsWから。旧producer `t0AbsW_of` (`V3T0AbW.lean:41`) : 接頭辞のCons τ・AbsWN(drop側)・T0BumpMono。新形のglobal producerは未発見。`AbsWNx.toU` (`V3AbsUpgShape.lean:43`) と `notBumpKidXU_of:120` も旧形からの橋。 | 全失敗列のAbsAtまたはBadAbsShapeまたはUpgAbsShape、およびBdXU全体の親の非bump。UpgAbsShapeは14欄（`:31`）。旧T0AbsWは実際に偽なので旧橋を全称的な供給源にはできない。 | 全n>=2、全Cons σ、全i<rのe1,e2非零列。AbsAtは全summandとLhdの全u/中間項。Upg形は全upgraderと全u,gの厳密上界。NotBumpKidはupgraderを含むBdXU全体。 | **分からない**。Bad/Upgの構造の分類と、compsの値の上界の両方が必要。hBXUの最後2欄と共有化できる。 |
| hSeeds | 外側 `V3TranslationAllUV3.lean:11`。`T0SeedsN` (`V3T0Bad.lean:24`) は3枝S1/S2/S3。S1は旧新oの形・新OT・Lhd・全UのRClaimUを含む。 | 局所producer `t0_S1N_x1` (`V3T0BadSeed.lean:153`) : Std,非SRO,**Inv3C,T0DropF,Bad2,L=1の枠**,n>=2,Cons N。`t0_S2_of_sum` (`V3T0BadS2.lean:284`) : **Inv3C,T0DropF,T0AbsW,特定omega和のLhd**+枠/Cons。`t0_S3_of_sum` (`V3T0BadS3.lean:202`) : **Inv3C,T0DropF,T0AbsW,app(omid,drop.o r)のLhd**+枠/Cons。 | 現C+PV2+AbsWUへの移植と、S1一般の場合・S2/S3の和のLhd。旧 `t0BadSeeds_of` (`V3T0BadSeed.lean:211`) はHDropUと旧残りを要求し、現入力の証明ではない。 | 全n>=2、全Cons σ、全g/pp、S1内の全述語U・RClaimUの全level/成分。S2/S3はbump配置のときだけ。 | **分からない**。旧補題は役立つが旧AbsW/PVを無条件に供給できない。hAbsUの修正だけでS1/S2/S3が証明されたわけではない。 |
| hQR : HQRInputsStepV3 | `V3QRStepV3.lean:246`、`QrInputsStepV3:241` の3欄ua/loc/vsf。loc=`QrLocStepV3:164` は5群（o-DQC,v-DQC,FStep,上げlastの移送,bumpW移送）。 | `hQRInputsStep_of_tail` (`V3QRStepV3.lean:308`) : **HQRInputsTailV3**。局所 `qrLocStep_of_tail:285` : C,hlen,hL,**QrLocTailV3**。`qr_chainV3f_step:94` は消費側だが、必要な構造・値の前提を細分する有用な型。前提全体を下の付録に掲載。 | ua=UAwRA、locの5群、vsf=VSFResQ。tailを経由するならTailFields/OFieldsTailを別途証明。DQC/FStepの**証人の存在**は未証明。チェーンや組立の証明と混同しない。 | 全n>=2、全Cons ρP/σ（ρPの根の上界と非零の前件あり）。全children分解L',c,R。upgradeは**全eta**に対するDQからlast-DQへの含意。bumpはあるetaから別のeta'の存在。Tail版は真のsingle非零tailの選択を含み、旧「全分解」OFieldsと違う。 | **分からない**。形の部分は既存Std補題で供給済み。残るFStep/DQCと成分の値の比較は実質的な新証明。 |
| hQN : HQNInputsV3 | `V3T1V3.lean:40`、`QnInputsV3:19` の7欄inn/vlt/before/kids/window/rest/step。rest=`WfQnA15.lean:13`の3群、step=`WfQnA8.lean:43`。 | 現形のglobal producerは未発見。`qn_carrierV3` (`V3QNCarrierV3.lean:14`) は7欄をそのまま消費。`resT1B_of` (`WfQnA15.lean:42`) は**Cons/Good3、種の形/cof/SeedOK、vlt,nonnesting,window,BumpNA,ResT1Bv**からResT1Bを作り、種の減少欄を消去する。これもrest/step自体の証明ではない。 | 7欄。特にrestのchanged-child成分上界・hard frame上界・非Bad列のAbsWNと、stepのPnV3全体の移送。inn/before/kidsの構造部分は小分けする候補。 | 全m（gamSの全レベル）、全BadSet i、全brのo(r)分解。rest/stepは全n>=2、全Cons値、off-closure glue等式を前件にした全CL分解。windowは全summandとLhd。 | **分からない**。before/kidsには構造の道がありそうだが、window/rest/stepは値の比較と不変条件の移送を含む。7欄を一括では狙わない。 |
| hBXU : T2AtV3 T2BelowAtV3U | 外側 `V3TranslationInputsV3.lean:16`、本体 `V3T2BelowV3U.lean:15` → `WfT2X4U.lean:20`。5群=seed HardA、seedのLhd/OT/子の降順、qのOT/降順、AbsWNxU、NotBumpKidXU。 | `T2BelowAtV3.toU` (`V3TranslationAbsUV3.lean:10`) : **旧T2BelowAtV3**。`T2BelowRes.toXU` (`WfT2X4U.lean:31`) : **旧T2BelowRes**。`bdxu_absX/up/F/cl` (`V3AbsUpgShape.lean:54/64/91/77`) は修正入力を仮定したengine前提のproducerであり、修正入力そのものは証明しない。 | seedの3群と新しいAbs/NotBumpの2群。旧Belowの強いAbsWNxが偽なので、旧橋から全称入力を供給できない。 | 全r,Lの終端par2枠、全n>=2。全m<nのCons→Good3とtarget suffixの全OTを前件に持つ。seed各p/q・全CL成分。最後2群の広い量化はhAbsUと同じ、bnd=x。 | **分からない**。engine本体とU化は完成済み。seedの値の比較とAbs/Upg例外の完全な分類が未証明。 |
| hFO | `V3TranslationAllUV3.lean:15` → `T2SeedFrames` (`V3ExpT2FO.lean:147`)、QFO (`:264`)。1欄=seed枠の状態を包むpsiのOT。 | `t2_seed_frames_of` (`V3PSeedAllG.lean:69`) : **Std,非SRO,Inv3W、QR/SV/QN/Cの4種のSeedFr QFO**。また `t2SeedFrames3` (`V3T2SeedFrV2.lean:35`) : **Std,非SRO,Inv3W,Res3W,hz,h2,T2SeedPRes,QNDom,CDom,接頭辞のVSF/FO/FC**からVSF/FO/FCoを一括供給。 | 第1経路では4種のSeedFr QFO。第2経路ではPRes/QNDom/CDomとRes3Wの供給。CのdropはPV2なので、Res3Wの旧PVが自動には出ない。 | 全n>=2、全過去m<n、全Cons/Good3 σ、全seed i・**全CL分解Lc,c,R**。QFOは子cvを読まないが全接頭状態を読む。 | **はい（見込み）**。target Good3も前件で、状態のOTという局所の結論。まず4配置ごとのQFOを狙う価値が高い。ただし全prefixのpsiのOTがGood3から直ちに出るとは未証明。 |
| hSF | `V3TranslationAllUV3.lean:16` → T2SeedFrames、QT2F (`V3PT2G.lean:92`)。2欄=QFO+QF3s（FC3c）。 | `seed_frames_PF` (`V3PSeedAllG.lean:117`) : **Std,非SRO,Inv3W,Res3W,source PH3cG/FC3,hz/h2、接頭辞FO/PH3cG/FC3、T2SeedPRes** → seedのQPHsとQF3s。これとhFOを結合し、`t2SeedFrames_and:167` と成分射影でQT2Fへ。汎用 `t2_seed_frames_of:69` の4配置経路もある。 | T2SeedPResのqr/sv/qn/C（CはCRes+CBig）とRes3Wの供給またはPV2版への移植。sourceと接頭辞PH/FC3/FOはCから出せるが、旧dropは別。 | T2SeedFramesの全n・全CL分解。QF3s (`V3PT2G.lean:87`) は全s,y,tailのo分解で、trigger・Lv=[]・split先頭非零のときだけFC3c。 | **分からない**。source欄とseed形はあるが、seedで新しく生じるFC3cの値の比較が残る。hSPと一緒にPResを解くと共有できる。 |
| hSP | `V3TranslationAllUV3.lean:17` → T2SeedFrames、QT2P (`V3PT2G.lean:91`)。2欄=QFO+QPHs。 | hSFと同じ `seed_frames_PF:117`（前提一覧も同じ）でQPHsを取り、hFOと `t2SeedFrames_and:167` でQT2Pへ。汎用4配置producerもある。`clField_qT2P` (`V3PT2G.lean:94`) はtargetの**Cons/FrameOT/PH3cG**から全枠へ出すが、PH3cGを得るためのseed入力の証明には循環し得る。 | hSFと共有のT2SeedPRes・Res3W接続。PH3cKindGのprefix/suffix形をseedで示すこと。 | 全n・全CL分解。QPHs (`V3PT2G.lean:81`) は全o分解、triggerかつstate非零のときPH3cKindG。 | **分からない**。source/前のコピーのPHから移す局所橋が要る。全target PHを先に仮定しない。 |
| hN : T2SmallV3 | `V3TranslationInputsV3.lean:21`。3欄=target VSF/FrameClosed/VSmallRAll。 | `t2_small_of_framesV3` (`V3T2LocalV3.lean:13`) : **C,hz,h2,旧T2BelowAtV3、seed QVSF/QFC、copy FDshAt、T2VRASeed、T2VRAPre、T2VRACopyEsc、copy CopyVDomK、path KAG**。`t2VRAK_KVRA_of` (`V3T2VRAK.lean:248`) は後ろ2条件からKVRA。前提の正確な型は付録。 | seed QVSF/QFC、FDshAt、VRA seed/pre/copy、CopyVDomK、KAG。さらにこのproducerのBelowは**旧非U版**なのでhBXUでは適用不能。U版のVSF/FC/VRA移送の組立が先に要る（新しい成分slackをVRAへ送る箇所にも注意）。 | 全n>=2、全σ,rkN（Cons/Rk/Good3/PHが前件）。VRAは全LevAtレベル・全CL分解・全成分。CopyEscの「安い成分でない」前件を省略しない。 | **分からない**。3性質のlocal consumerは多く完成済みだが、U版接続とseed/copy residualが残る。sourceの同じ3欄がtargetへ自動移送されるわけではない。 |

各行の未証明欄は「既存の型で証明を要求されているもの」の一覧。今回測った現入力に対する失敗0を、その入力より強い旧十分条件（T0AbsW、旧Below、Res3W、Tail版など）の失敗0と読み替えてはいけない。特にそれらの旧十分条件は、現データで改めて証明・測定済みとは扱っていない。

## 証明の順番の案

1. **hFOの4配置**を最初に読む。target Good3とConsを既に仮定してよく、最も小さい値の結論。QFOが済むとhSF/hSPとhNの種の部分に共有できる。
2. **hSF/hSPの共有T2SeedPRes**を欄別に進める。旧Res3Wの供給を現PV2から誤って作らず、実際に読む欄だけを移植する。qr/svの簡単な枝から。
3. **hNのvs/fc/vraを分けてU版の接続を確認**。旧 `t2_small_of_framesV3` はそのまま使えない。seed/copy仮定を消していく仕事と、U化の組立だけの仕事を別の達成として数える。
4. **hDの5欄**を個別に証明。展開nの全称がなく、成功すると全tのC.pre/dropを確実にする。ほかの入力の証明でhDを再び仮定する際は依存を明示する。
5. **hAbsUとhBXUの最後2欄を共有の一般補題へ**。AbsAtが破れた列の完全分類、UpgAbsShapeの成分上界、NotBumpKidXUの順。hBXUのseed3群とhSeedsのS1/S2/S3はそれぞれ局所に切る。
6. **hQRは実際のFStepを優先**。Tail版は十分条件であって必須ではない。forall etaのlast移送は別補題にし、存在etaのDQ検索と混同しない。
7. **hQNとhFは欄ごと**。hQNのbefore/kidsなど構造の欄を先に、rest/stepとhFの値の欄は後。hFをInv3V3全体の存在から出す循環を避ける。

この順は証明難易度の見立てであり、上の表にある未証明の前提が既に消えたという意味ではない。surjの追加入力 `EvalFSNZ 2` は今回の11入力の外。

## 型を読んで確認した接続上の注意

- 現入口の型は `T0AtV3 T0AbsWU` と `T2AtV3 T2BelowAtV3U`。単なるAbsWNxUだけではない。t2のhBXUはseed3群も含む。
- hFはC.Iから射影して終わる入力ではない。**全Std+Good3の行列**に対するglobal residualなので、それ自身を帰納法で供給する計画が要る。
- `qr_chainV3f_step` はhQRを証明するproducerではなく、hQRの局所欄を消費して展開を構成するengine。`qn_carrierV3`や`expCore0_of_seedsU`も同様。これらの証明済みという事実だけで入力を消したと数えない。
- 旧形からの橋が存在しても、旧T0AbsW/旧AbsWNxを全称的な前提に戻さない。旧Inv3V2/HDropUや旧HUACの系列も現入口の証明源として採用しない。

## 主要producerの正確な型

表でまとめた前提を省略せず確認できるよう、以下に現在のソースの型を抜き出す。暗黙のsection変数を持つqr_chainV3f_stepは、同ファイルのsectionにある hlen/hL/hA/hd0e も必要。

### V3DropV3.lean:37 — hDropV3_of_inputs

```lean
theorem hDropV3_of_inputs (h : HDropInputsV3) : HDropV3
```

### V3DropV3.lean:28 — dropV3_of_inputs

```lean
theorem dropV3_of_inputs {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V3 M ρ rk) (hl : 2 ≤ M.length) (R : DropInputsV3 M ρ rk) :
    DropV3 M ρ rk
```

### V3T0AbsUpg.lean:23 — T0AbsW.toU

```lean
theorem T0AbsW.toU {M : Mat} {r L : Nat} {ρ : Valn} (h : T0AbsW M r L ρ) :
    T0AbsWU M r L ρ
```

### V3QRStepV3.lean:308 — hQRInputsStep_of_tail

```lean
theorem hQRInputsStep_of_tail (h : HQRInputsTailV3) : HQRInputsStepV3
```

### V3QRStepV3.lean:285 — qrLocStep_of_tail

```lean
theorem qrLocStep_of_tail {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) {r L d0 : Nat} (hlen : r+L+1=M.length) (hL : 0<L)
    (hTail : QrLocTailV3 M ρ r L d0) : QrLocStepV3 M ρ r L d0
```

### V3QRStepV3.lean:94 — qr_chainV3f_step

```lean
theorem qr_chainV3f_step (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (h1x : entry M 1 (r + L) ≠ 0) (hp1 : par M 1 (r + L) = some r)
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          FStep (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c)) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k)))))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hv1 : ρ1.v r ≤ ρ.v r)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (S : SInv M) (I : Inv3V3 M ρ rkM) (hq : par M 0 (r + L) = some r)
    (hVSF : VSFResQ M r L d0 ρ)
    (hFr : FrameAtN M r L d0)
    (hP1 : PnV3 (TRIO.gexp M r L d0 0 1) ρ1) (hs1 : ρ1.o r < ρ.o r)
    (hF1 : FrameMapT1 M ρ r L (TRIO.gexp M r L d0 0 1) ρ1 ∧ VrDomQ M ρ r L (TRIO.gexp M r L d0 0 1) ρ1) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ PnV3f M ρ r L (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ
```

### V3PSeedAllG.lean:69 — t2_seed_frames_of

```lean
theorem t2_seed_frames_of {Q : T → List T → T → Prop} {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hQR : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → SeedFr Q M r L r)
    (hSV : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      upg M (r + L - 1) = some (r + L) → SeedFr Q M r L r)
    (hQN : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → ∀ i, (i = r ∨ i = q) → SeedFr Q M r L i)
    (hC : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → ∀ i, (i = r ∨ i = q) → SeedFr Q M r L i) :
    T2SeedFrames Q M
```

### V3PSeedAllG.lean:117 — seed_frames_PF

```lean
theorem seed_frames_PF {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hP : PH3cG M ρ) (hF : FC3 M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ)
    (hRes : T2SeedPRes M ρ) :
    T2SeedFrames (fun a Lv cv => QPHs a Lv cv ∧ QF3s a Lv cv) M
```

### V3T2SeedFrV2.lean:35 — t2SeedFrames3

```lean
theorem t2SeedFrames3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRes : G.T2SeedPRes M ρ)
    (hQND : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc)
    (hCD : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → G.T2SeedCDom M ρ r L q)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → VSmallF (M.take (M.length - 1)) τ ∧
      FrameOT (M.take (M.length - 1)) τ ∧ FrameClosed (M.take (M.length - 1)) τ) :
    T2SeedFrames QVSF M ∧ T2SeedFrames QFO M ∧ T2SeedFrames QFCo M
```

### V3T2LocalV3.lean:13 — t2_small_of_framesV3

```lean
theorem t2_small_of_framesV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hB : T2BelowAtV3 M ρ)
    (hVS : T2SeedFrames QVSF M) (hFC : T2SeedFrames QFC M)
    (hFD : T2CopyK FDshAt M)
    (hSeed : T2VRASeed M) (hPre : T2VRAPre M ρ) (hCopy : T2VRACopyEsc M)
    (hVD : T2CopyK CopyVDomK M) (hAG : T2VRAK KAG M) :
    ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN →
    Good3 (expand M n) σ → PH3cG (expand M n) σ →
      VSmallF (expand M n) σ ∧ FrameClosed (expand M n) σ ∧ VSmallRAll (expand M n) σ
```
