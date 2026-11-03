# 種の枠4補題の欄の監査（2026-11-04、G3）

ファイル名は、断りがなければ `Ytosk/lean/Ytosk/` 内。Leanは書いていない。対象は既存の3結論（QVSF/QFO/QFCo）を証明する**現在の証明全体**。QFOだけを取り出す場合は後段に別記する。補題にI/Rを丸ごと渡していることと、実際にその欄を読むことを区別した。

重要な結果: qr/sv/Cの経路に実際のRes3W射影はない。共通の `t2CopyResAll_holds` がRを引数に取るが証明で捨てる。qnだけはQFCoのための `t2SeedQNFC_holds → qn_take_t1` に `R.hdrop` がある。4経路とも `R.old` と `R.ab` は読まない。

| 対象 | 実際に読むInv3Wの欄（呼び先込み） | 実際に読むRes3Wの欄 | StepCtx3 Cからの供給 | 配置の残り・実際に読む部分・測定記録 |
|---|---|---|---|---|
| `seed_frames_qr3` (`V3T2SeedFr.lean:180`) | **cons, good, rank, vs, fc, fo, be, uat, z1, z2**。直読はcons/good/vs/fc/fo。rankはseed_last_qr/seed_r_value_qr、be/uat/z1/z2はframe data/o_r_level_qr。共通copyの追加読取はcons/good/rankだけ。 | **なし**。Rは `seed_last_qr → seed_frame_data_qr / seed_r_value_qr → o_r_level_qr → t2CopyResAll_holds` と渡るが、最後で捨てられる。 | **Iの全読取欄は出る**。`coreW C.S C.I` (`V3EngineV3.lean:12`) でInv3W全体が出る。cons/good/rank/vs/fc/foはC.Iの射影、be/uat/z1/z2はC.Sから（対応名bumpE2/uat/z1c/z2）。**Res3W全体は出ない**が、この経路の実質的な要求ではない。copyはR不要の `t2CopyResV3` (`V3T2CopyV3.lean:12`) に置換可能。 | `T2SeedQRRes` (`V3T2SeedQRL.lean:27`、ks/vs/w1/domの4欄)。この3結論の証明は**ks,w1だけ**を読む。vs/domはseedのLhd側など別consumer用。Codex記録 `tmp/codex/residual-consumers.md:64` 付近にqr.w1/domの監査があるが、現定義の全4欄を測った一次結果との対応は未確認。直近hFO失敗0はこの強い残り束の測定と同じではない。 |
| `seed_frames_qn3` (`V3T2SeedFr.lean:387`) | **cons, good, rank, vs, fc, fo, r0p, z2, sd, z1, uat, uab, be**。直読はcons/good/vs/fc/fo。v_take_of_untoppedとqn_take_t1でr0p/sd/uabも読む。qnS_otはgoodだけ。 | **hdropだけ**。`seed_last_qn:259 → G.t2SeedQNFC_holds (V3QNFC.lean:386) → qn_take_t1:261 → R.hdrop:297`。ほかのRは共通copyへ渡るだけ。 | **Iの全読取欄は出る**（coreW）。**旧hdropは出ない**: C.dropはPO+PV2なのでRes3W.hdropのPO+PVをそのまま満たさない。PV→PV2は `WfDrE1.lean:106` にあるが逆向きは得ていない。ただし実際のqn_take_t1では旧PVは `good3_take` を呼ぶためにだけ使用。C.pre.goodをCons一意性で移せばGood3を別途供給でき、残りはC.dropからのPOで足りそう。これは未移植の見通しであって旧Rの証明ではない。 | `T2SeedQNRes` (`V3T2SeedQNV.lean:113`、vqlt/σB/Bc/base)。**σB,Bc,base**を読み、vqltはこの3結論では未使用。baseの列の値の式とkごとの下界/shift下界を読み、末尾のk>=1のLhd条件はここでは読まない。`T2SeedQNDom` (`V3T2SeedFr.lean:249`) は**両欄**（1=非空Lcの全level上界、2=level V上界）を読む。Codexの `residual-consumers.md:66` 付近にqn base/k条件、`:85` 付近にQNDom系の監査、`vsmallrsh-preservation-map.md:13` に現T2SeedQNDom.1の名がある。現定義全体の測定結果への対応は未確認。QNDomのソースdocstringには9集合0例外の記載あり。 |
| `seed_frames_sv3` (`V3T2SeedFr2.lean:31`) | **cons, good, rank, r0p, z2, sd, z1, uat, uab, be**。直読はgood/rank/z1/z2。v_take_of_untopped、seed_r_value_sv、sv_frame/seed_frame_data_sv、sv_agree/sv_cntを下った集合。sourceのvs/fc/foは読まない（prefix側のhTV/hTC/hTOは別引数）。 | **なし**。`seed_frame_data_sv / seed_r_value_sv → sv_frame → t2CopyResAll_holds` にRを渡すだけ。 | **Iの全欄は出る**（coreW）。prefixのhC0/hR0/hTV/hTO/hTCもC.preから出る（任意Cons τ0への移送は下記）。**Res3W全体は出ない**が実際には不要。copyをt2CopyResV3へ置換する。 | `T2SeedSVRes` (`V3T2SeedSV.lean:514`、decP/rw/lhd): この3結論で読むのは**rwだけ**。`T2SeedSVFix` (`V3PSeedSVG.lean:138`、fix/hi): **両方**読む。Codex `residual-consumers.md:66` 付近にsv.strict/lhdの監査はあるが、現SVRes/SVFix全欄の名前付き実測は今回の検索では未確認。SVFixのソースdocstringには5集合でSpotNと加数条件0例外とある。直近hFO検査0はSVFix/rwの全称証明でも直接測定でもない。 |
| `seed_frames_C3` (`V3T2SeedFr2.lean:359`) | **cons, good, rank, r0p, z2, sd, z1, uat, uab, be**。直読はgood/rank。qnS_ot/topP_C/v_take_of_untopped/seed_last_C、さらにqP_C/C_frame/seed_r_value_C、共通copyまで下った集合。sourceのvs/fc/foは読まない（prefix側hTV/hTC/hTOは別引数）。 | **なし**。`seed_last_C / seed_r_value_C → C_frame → t2CopyResAll_holds` でRを捨てる。 | **Iの全欄は出る**（coreW）。prefix3欄もC.preから出る。**Res3W全体は出ない**が実質的に不要。copyはt2CopyResV3へ。 | `T2SeedCRes` (`V3T2SeedC.lean:547`、decP/un/vqP/rw/lhd): この3結論で読むのは**un,vqP,rw**。`T2SeedCFix` (`V3PSeedCG.lean:23`、fix/hi): **両方**。`T2SeedCDom` (`V3T2SeedFr2.lean:22`): **prefBの条件付き欄とlevel V上界の両方**。Codex `residual-consumers.md:73` は旧CResR2.decP、`:90` は旧CDom1の監査。`handoff-trio-codex-20261028.md:31` の「CのDomは定理」は旧の縮約系の話で、現3残り束を無条件に測定/証明した意味ではない。現CRes/CFix全欄の名前付き実測結果は未確認。CDomのソースdocstringには9集合0例外の記載あり。 |

## 呼び先まで下った根拠

以下は本文の射影および、束をそのまま渡す箇所を読んで得た一覧。`G`の名前空間の補題と、旧い名前空間の同名補題を混同しない。frame-dataは今回のimport経路で使う `V3PSeed*G.lean` 側を確認した。

| 呼び先 | 場所 | Iの直読 | Rの行き先 |
|---|---|---|---|
| G.seed_frame_data_qr | `V3PSeedQRG.lean:97` | be,cons,good,rank,uat,z1,z2 | `:194`でt2CopyResAll_holdsへ |
| seed_r_value_qr | `V3T2SeedQRL.lean:48` | cons,fo,good,rank | o_r_level_qrへ |
| o_r_level_qr | `V3T2SeedQR.lean:67` | be,cons,good,rank,uat,z1,z2 | `:163`で共通copyへ |
| qr_M_side / tame_sigmaB_std | `V3T2SeedQRL.lean:150` / `V3Tame.lean:616` | 前者cons,fo,good、後者cons,good,rank | R引数なし |
| G.seed_frame_data_qn | `V3PSeedQNG.lean:20` | be,cons,good,rank,uat,z1,z2 | `:218`で共通copyへ |
| seed_r_value_qn / o_r_level_qn | `V3T2SeedQNV.lean:152` / `V3T2SeedQN.lean:418` | 前者rank、後者cons,good | qn_frameへ |
| qn_frame | `V3T2SeedQN.lean:184` | be,cons,good,rank,uat,z1,z2 | `:382`で共通copyへ |
| qnS_ot | `V3T2SeedQNV.lean:30` | good | なし |
| topP_C → par0_q_t2 | `V3T2SeedQNV.lean:68 → :48` | topP_C直読なし、par0_q_t2はbe,z1,z2 | なし |
| v_take_of_untopped | `V3T2SeedQNV.lean:101` | cons,good,r0p,rank,sd,uab,uat,z1,z2 | R引数なし。chg_off/chg_struct/rk_takeへ各欄を明示して渡す |
| G.t2SeedQNFC_holds → qn_take_t1 | `V3QNFC.lean:386 → :261` | 前者cons,good,rank、後者be,cons,good,r0p,rank,sd,uab,uat,z1,z2 | **`:297`でR.hdropを射影**。`:298`のgood3_takeに全hdrop、`:354`付近のbump項上界にhdropのPO側を使う。old/abはない |
| G.seed_frame_data_sv → sv_cnt/sv_agree | `V3PSeedSVG.lean:27 → V3T2SeedSV.lean:56/:130` | frame-dataはbe,cons,good,uat,z1,z2、sv_cnt/sv_agreeはuat | `V3PSeedSVG.lean:119`で共通copyへ |
| seed_r_value_sv → o_r_level_sv → sv_frame | `V3T2SeedSV.lean:525 → :381 → :265` | seed_r_valueはrank,z1,z2、sv_frameはbe,cons,good,uat,z1,z2（さらにsv_cnt/sv_agree） | `:357`で共通copyへ |
| seed_last_C → vq_eq_gexp/qP_C/C_frame/seed_r_value_C | `V3T2SeedFr2.lean:192` | direct good,rank。vq_eq_gexp (`V3ExpT2BD.lean:472`) はbe,cons,good,rank。qP_C (`V3T2SeedC.lean:70`) はbe,r0p,sd,z1,z2 | C_frame系へ |
| seed_r_value_C → o_r_level_C → C_frame | `V3T2SeedC.lean:560 → :458 → :130` | seed_r_valueはrank、o_r_levelはgood、C_frameはbe,cons,good,uat,z1,z2 | `:421`で共通copyへ |
| t2CopyResAll_holds | `V3ExpT2CR.lean:53` | **cons,good,rankのみ**（`:110,125,129,133,135`）。他の構造条件はStdからhX/hJを作って供給。 | 冒頭 `intro M ρM rk hM hS I _ hz h2` の `_` がR。**Rの射影も他への伝搬もない**。R不要版は既存 `V3T2CopyV3.lean:12` |

`Inv3W`の未使用欄は、4経路いずれもr12/r01/e00/kd/td/rootS/rootP。qrではさらにr0p/sd/uabをIから読まないが、同じ構造条件をStdから作ったhX側で使う箇所がある。これは構造条件自体が不要という意味ではない。

## StepCtx3から出るものと出ないもの

- sourceのIは `coreW C.S C.I`。`coreW`の型は `SInv M → Inv3V3 M ρ rk → Inv3W M ρ rk` (`V3EngineV3.lean:12`)。表の全I欄を供給できる。
- x=r+L=M.length-1について、`J := C.pre x (1<=x) (x<M.length)` はcanonical prefix値 `drop1 M x rk` のInv3V3。J.cons/J.rank/J.good/J.vs/J.fo/J.fcを使える。x>0はpar2の枠から従う。
- 任意の `τ0 : Cons (M.take x) τ0` が来た場合は、`agree_of_cons J.cons hC0 J.rank` (`V3Congr.lean:14`) で値の一致を得る。Good3は `good3_congr` (`:27`)、FO/FCは `clField_congr` (`V3ExpT2FO.lean:25`、QFO/QFC)、VSFは `clField_of_vsmallF → clField_congr → vsmallF_of_clField` で移す。`hR0`にはJ.rankを使える。新たに旧PVを仮定する必要はない。
- `C.drop` は `DropV3` (`V3TakeV3.lean:14`) でPO+PV2とVSmallNew。Res3W.hdrop (`V3InvW.lean:68`付近) はPO+**PV**である。PV2のWCS2をWCSに戻す一般の橋はなく、**旧hdropは出ない**。Res3W.old/abもCの欄からの供給は未確認で、今回の4経路は読まない。
- qn_take_t1を現文脈に写すなら、prefixのGood3を上記Jから受け、bump項の単調性では `C.drop` のPO側を渡す。旧 `good3_take` を使う箇所を残したままPV2を渡すことはできない。QFOだけならこのqnFC経路を丸ごと避ける方が短い。

## QFOだけを証明するために省けるもの（未実装）

ここは既存の3結論の定理をそのまま適用するのではなく、QFO枝の必要部分を新補題に抽出する案。

| 配置 | QFOが実際に使うデータ | 不要にできそうな残り |
|---|---|---|
| qr | `G.seed_frame_data_qr` のCL_N(r)=Lc+[x]、v_N(r)=v_M(r)、Lcのo一致。`seed_frames_lift` (`V3PSeedQRG.lean:216`) でsource FOを移す。QFOは新しい最後の子の値を読まない。 | seed_last_qrのYの厳密な式とnの2分岐を出す必要がない。**QRRes全部・tame_sigmaB・R**を省ける見込み。 |
| qn | `G.seed_frame_data_qn` のCL_N(r)=Lc+[q]、rのv/Lcのo一致、CL_N(q)=[x]。rはsource FOをlift、qは空prefixなのでpsi(σ.v q,0)のOT（hGN.ot_v）だけ。 | seed_last_qnのftの式・high条件・QNFCを使わない。**QNRes/QNDom/R.hdrop**を避けられる見込み。 |
| sv | `G.seed_frame_data_sv` のCL_N(r)=CL_T(r)+[x]、v_N(r)=τ0.v r、CL_T(r)のo一致。既存prefix FOを `seed_frames_liftE` (`V3PSeedSVG.lean:150`) で移す。最後の前状態はo_T(r)の引数そのものなのでprefix Good3。 | keyで証明する反復shiftの式・SeedExtはQFOに不要。**SVRes/SVFix/hTV/hTC/R**を省ける見込み（hTOとprefixGood3は残る）。 |
| C | `C_frame` のCL_N(r)=CL_T(r)+[q]とprefixのv/o一致、CL_N(q)=[x]。rはprefix FO、qは空prefixのOT。 | C_frameを現型で使うなら**CRes.unとCRes.vqP**を使ってhqPとhvq0を供給する。反復式rw/lhd、CFix/CDom、hTV/hTCはQFOには不要の見込み。un/vqPを構造/Consから出せるかが次の小さい未証明点。 |

これらの抽出はまだLeanの定理ではない。ただし上記の「その欄を読む場所」は実際の既存QFO枝とframe-dataの型から確認した。特にqnの旧PVを理由にhFO全体が必ず止まる、と判断しない。

## 測定記録の判定基準

`tmp/codex/` のmd/py/jsonを名前で検索した。今回作った `inputs_map_20261104.md` の記載は新しい監査なので、過去の測定の証拠に数えていない。既存のconsumer mapに名前や欄の説明があっても、現定義・全k/u/Cons値への測定を確認したことにはしない。

直近の `inv3v3_inputs_audit_20261101.py` はtargetのhFO/QFOを直接検査するが、QRRes/QNRes/SVRes/CRes/Fix/Domをこの名前で全欄検査する測定器ではない。現在の入口入力の失敗0と、旧producerの十分条件の失敗0を取り違えない。測定一次結果のファイルに結び付かなかったものは「未確認」とした。
