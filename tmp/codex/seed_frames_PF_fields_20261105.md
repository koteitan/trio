# G9: 種のQPHs・QF3sの欄の監査

読むだけの監査。Lean・lakefileは変更していない。
以下のファイル名は `Ytosk/lean/Ytosk/` からの相対名。
旧 `Inv3W.fc`（FrameClosed）と `FC3` は別物。後者は別引数hF、または新しい束のC.I.fc3。
G名前空間の経路を追い、Gなしの旧PH3c版と混同しない。

## 入口と実際の依存欄

入口は `G.seed_frames_PF`（V3PSeedAllG.lean:117）。
結論はQPHsとQF3sだけで、QFOそのものは含まない。
QT2P/QT2Fへの結合は同ファイル:170のt2SeedFrames_andと、:177/:194の展開補題で行う。

| 配置・直接のconsumer | Inv3Wの実読取欄（呼び先込み、下記共通入口処理を除く） | Res3Wの実読取欄・読む場所 | T2SeedPResから実際に読む欄 |
|---|---|---|---|
| qr: `G.seed_frames_qr`（V3PSeedQRG.lean:245） | cons, good, rank, fo, be, uat, z1, z2。foはsourceのQT2P/QT2F構成とqr_M_side。別引数hP/hFも読む。 | **なし**。Rはframe-data/seed_r_value/o_r_levelからt2CopyResAll_holdsへ渡り、そこで捨てられる。 | **hRes.qr.ks, w1**。w1はn=2でrewrite前件を否定。ksはn>=3のseed_last_kind/seed_last_fc3と反復値の式。**vs, domは未使用**。 |
| qn: `G.seed_frames_qn`（V3PSeedQNG.lean:266） | cons, good, rank, fo, be, r0p, sd, z1, z2, uat, uab。foと別引数hP/hFはsourceの旧い枠の移送に使用。 | **hdropだけ**。QF3sの最後の枠で使うhFCを、`t2SeedQNFC_holds → qn_take_t1`で作る経路。後者V3QNFC.lean:297で射影、:298でprefix Good3、:355でPOによるbump項の比較。**QPHsだけならこの経路は不要**。 | **hRes.qn.σB, Bc, baseの一部**。baseの「prefix状態=B+Omega(t1)」と各kのV<tqN・shift後の下界。**vqlt、およびbase末尾のk>=1でのtqNとv(q)の比較/Lhdは未使用**。別に自動生成されたT2SeedQNFCをQF3sで読む。 |
| sv: `G.seed_frames_sv`（V3PSeedSVG.lean:181） | cons, good, rank, be, r0p, sd, z1, z2, uat, uab。sourceのfo/vs/fcは読まない。prefixのFO/PH/FCはhTから。 | **既存の全経路ではhdropだけ**。`seed_frames_PF → t2SeedSVFix_holds`（V3SVFix.lean:630）、:641-642でprefix Good3を作る。seed_frames_svやframe-data自体にはRの実射影なし。 | **hRes.sv.rw**。decP/lhdは未使用。自動生成したT2SeedSVFixの**fix, hiをQPHsで読む**。QF3sの枝にはFix不要。 |
| C: `G.seed_frames_C`（V3PSeedCG.lean:55） | cons, good, rank, be, r0p, sd, z1, z2, uat, uab。sourceのfo/vs/fcは読まない。prefixのFO/PH/FCはhTから。 | **既存の全経路ではhdropだけ**。`seed_frames_PF → t2SeedCFix_of`（V3CFix.lean:789）、:809-810でprefix Good3を作る。C_frame自体はRを捨てる共通copy経路。 | 直接は**hRes.Cの第1成分のun, vqP, rw**。Fix生成ではさらに**decP**と第2成分T2SeedCBigの**big**（V3CFix.lean:852/:869）。**lhdは未使用**。生成したCFixの**fix, hiをQPHsで読む**。 |

共通入口処理（V3PSeedAllG.lean:126-135）も含めると、qr行にも
`r0p, sd` が加わる。これはprefixのRk/Consを用意するための
`counted_take_last → rk_take → cons_of_rk`の読取で、qrの閉包特有の残りではない。
sv/CのFixを直接仮定にして自動生成経路を外せば、表のhdrop依存も外れる。

4経路とも **Res3W.old/abは読まない**。
旧Inv3Wのvs/fc/kd/td/rootS/rootPも、このPF経路では読まない。
r12/r01/e00もIからの射影はない。Stdから作るSInvXに同種の構造情報があることとは区別する。

## 呼び先の確認

| 経路 | 確認箇所・読むもの |
|---|---|
| qrの値と枠 | seed_frame_data_qr（V3PSeedQRG:97）、seed_r_value_qr（V3T2SeedQRL:48）→o_r_level_qr（V3T2SeedQR:67）。qr_M_side（V3T2SeedQRL:150）→leaf_M_side（V3T2SeedQNV:129）はcons/good/fo。tame_sigmaB_std（V3Tame:616）はcons/good/rankとStdからの構造。 |
| qnの値と枠 | seed_frame_data_qn（V3PSeedQNG:20）、seed_r_value_qn（V3T2SeedQNV:152）→o_r_level_qn（V3T2SeedQN:418）→qn_frame（同:184）。v_take_of_untopped（V3T2SeedQNV:101）がr0p/sd/uab等を読む。 |
| qnのFC専用 | seed_frames_qnのV3PSeedQNG:410前後のhFC呼出し→t2SeedQNFC_holds（V3QNFC:386）→qn_take_t1（同:261）。hdropを全体のRes3Wから切り離すべき箇所は:297/:298/:355。 |
| svの値と枠 | seed_frame_data_sv（V3PSeedSVG:27）→sv_cnt/sv_agree（V3T2SeedSV:56/:130）。seed_r_value_sv（同:525）は:584でhRes.rwを使用。decP/lhdは使わない。sv_frame（同:265）→共通copy。 |
| svのFix生成 | t2SeedSVFix_holds（V3SVFix:630）→sv_main（同:138）→t_aboveA（同:42）。Rは:641-642のprefix Good3にのみ必要。残りは構造・Cons・Good3・Rkと変更列の追跡。SVRes.decPを引数にすら取らない。 |
| Cの値と枠 | V3PSeedCG:116のvqP、:128/:137のun→qP_C（V3T2SeedC:70）/C_frame（同:130）。seed_r_value_C（同:560）はun/vqP/rwを使用。 |
| CのFix生成 | t2SeedCFix_of（V3CFix:789）→c_main（同:274）→t_aboveB（同:105）/t_above0B（同:32）。:803にun、:821にvqP、:852にdecP、:869にhBig.big。rw/lhdはFix生成では読まない。 |
| 共通copy | t2CopyResAll_holds（V3ExpT2CR:53）。引数Rは冒頭の`_`で捨て、Iはcons/good/rankのみ。R不要の既存版はt2CopyResV3（V3T2CopyV3:12）。 |

T2SeedPRes.Cの第2成分は既に**T2SeedCBig**。
`t2SeedCBig_of`（V3CBig.lean:209）や、偽と分かった旧T2SeedCNextを
この経路が自動で使うわけではない。Bigを入力として読む現経路と、
さらにBigを証明しようとする別経路を混同しない。

## 今のStepCtx3から出るもの

- source Iの表中の欄はすべて `coreW C.S C.I`（V3EngineV3.lean:12）で出る。
- source hPはC.I.ph、hFはC.I.fc3（WfExQ1.lean:64-65）。
  Inv3WにPH/FC3が入っているという意味ではない。
- prefixのFO/PH/FC3/Good3/Cons/Rkは `J := C.pre x ...` の
  J.fo/J.ph/J.fc3/J.good/J.cons/J.rankで出る。
  任意Cons τへの移送はagree_of_cons（V3Congr:14）、good3_congr（同:27）、
  clField_congr（V3ExpT2FO:25）、G.ph3c_congr/G.fc3_congr（V3PIntG:18/:21）。
- **旧Res3W.hdrop全体は出ない**。旧hdropはPO+PV、新C.dropはPO+PV2。
  sv/CのFixに必要なprefix Good3はC.preから直接供給すれば旧PVを避けられる。
  qn_take_t1はそれに加えてPOの比較を使うが、POはC.dropから取れる。
  いずれも既存定理へそのままC.dropを渡せるという主張ではなく、
  読む欄を抽出した新しい補題への移植案。

## QPHs/QF3sに分けて省けるもの

以下は既存の証明の枝の切り分け。新しいLean定理を証明した意味ではない。

| 配置 | QPHsだけ | QF3sだけ |
|---|---|---|
| qr | 旧い枠はsource hPでlift。最後の枠はn=2ならw1で前件を否定、n>=3ならksによるseed_last_kind。QRRes.vs/domとsource hFは不要。QFOは別に供給できるのでclField_qT2Pの第1成分を作る必要はない。 | source hFをlift。最後の枠は前の子の列が空の場合だけ必要。w1とksは現証明で読むが、**空のLcの場合だけ**に制限できる。B=0ならσBとBcの条件は自明。source hPとQRRes.vs/domは不要。 |
| qn | rの旧い枠はsource hP、最後はhigh-only形からPHのpre枝。qは前状態0でPHの前件が空。QNResのσB/Bc/baseの最初の式と2下界が必要。**QNFCとそのR.hdrop依存、source hFは不要**。 | rの旧い枠はsource hF。最後が最初の枠であるLc=[]の場合だけQNFCを読む。qの唯一の枠は添字s'=qnSで、s'非零・last(s')≠1からFCを出す。source hPは不要。rの最後のためのbase/QNFCは空Lcに制限可能。σB/Bcも空Lcでは自明。 |
| sv | prefix hPをlift。最後はseed_ext→SeedExt→seed_kindを使うため、**rwとFix.fix/hiを読む**。Fix生成の旧hdropはprefix Good3の供給に置換可能。decP/lhdとprefix FCは不要。 | prefix hFをlift。最後の枠はCL_T(r)=[]ならX1=0、shIt_z/sh_zでrewrite前件が矛盾。**Fix全体（したがってFix生成のhdrop）とdecP/lhd、prefix PHは不要**。ただし現証明の最後の子の式hoxはseed_r_value_svを経由するためrwはまだ読む。rwまで無条件に消えるとは言えない。 |
| C | 現経路ではprefix hPをliftし、rの最後にrw・Fix.fix/hi。Fix生成を含めると**un/vqP/decP/Big.big**も必要。qは前状態0なのでPHは空。lhdとprefix FCは不要。 | prefix hFをlift。rの最後が最初ならX1=0、splitのhigh=0と前件が矛盾。**Fixとその生成専用decP/Big.big/hdrop、lhd、prefix PHは不要**。ただしhdata/反復値の式で**un/vqP/rwは残る**。qのFCはqnと同じ添字の議論。 |

重要: **Cのunは偽**であり、C2ではvqP/prefixの子のo一致も偽。
G5の結果から、上表のC経路を全C配置のproducerとして使うことはできない。
C1ではこの切り分けが使えそうだが、C2はMとの関係から別に扱う必要がある。
G8のT2C2RootRelはQFOの橋であって、QPHs/QF3sの輸送を証明していない。
「QFOと同じLhd関係があるからPH/FCも保存される」とはここでは主張しない。

## 定義の量化と注意点

| 定義 | 量化されるもの・条件 |
|---|---|
| QPHs（V3PT2G:81） | 全s,y,cでcv=psi s y c、rewriteの2不等式、前状態B≠0が前件。結論はPH3cKindG B (split y Omega_(succ s)).1 ... s。**任意の和の分解を取る定義ではない**。psiの構成子の分解は一意。splitの閾値と結果も決定的。 |
| QF3s（V3PT2G:87） | 同じ全s,y,cとrewrite条件に加え、**Lv=[]**とhigh≠0を前件にFC3c。最初の子の枠だけ。Lvが非空なら前件が偽。 |
| SeedFr（V3PSeedAllG:29） | 全n>=2、全m<nのGood3を前提に、全Cons/Good3 target値づけ、**CL_N(i)=Lc++c::Rのすべての実際の子の分割**。ゼロの子や任意の項を足した和の分解を自由に選ぶものではない。 |
| PH3cKindG（V3PDef:147） | high=Bか、highがBの非空延長か、Bが決定的cutsNSGの元かの選言。延長Rは**存在量化**。 |
| FC3c（V3PDef:102） | s=aならs非零かつlast(s)≠1。s≠aなら非零Xが存在してlev(high)=app s X。Xは存在量化。 |

Qs自体に「すべてのη」はない。ただしproducerの残りは強い量化を持つ:
QRRes.ksは全k、w1は全Cons prefix、未使用domは全k/u/g。
QNRes.baseは全Cons prefixで存在t1を取り、その**同じt1に全k**を要求。
SV/Cのrw/lhdは全Cons prefix・全k。decPは実際の最後の子を与える全分割。
Fix.fix/hiとBig.bigも全Cons prefixに関する主張。
有限のnやkだけの測定を、これらの無限の量化の証明と扱わない。

## 次に取り出す順の案

1. QF3sのsv: まず既存のrwとframe-dataだけで、Fixを受けない版に抽出。
2. QPHsのqn: QNFCと旧hdropを丸ごと避けられる。
3. qr: ks/w1だけの小さい入力にし、QF3s側は空Lcに限る。
4. C1/C2を分ける。C1のQF3sからFix/Bigを避ける。C2は別の正確な要求を測ってから。

この順は証明規模と依存の見通しであり、新しい残りの真偽を保証するものではない。
