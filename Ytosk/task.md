# Ytosk: 引き継ぎの作業内容（2026-10-12）

Ytosk 氏の翻訳（3 行 BMS の行列 → 拡張 Buchholz の項）が、SRO より下で正しいことを Lean 4 で証明する作業の引き継ぎ書。
経過の詳しい記録は `Ytosk/desc.md`（日本語、時系列）。この文書はその要約と、次にやることの一覧。

- SRO = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)
- 標準形 `Std` = SRO から展開でたどり着く行列（`Ytosk/lean/Ytosk/BMS.lean`）
- 展開は M[n] と書く（Lean の `expand M n`、n はコピーの個数）

## 1. 目標と、終わったもの

目標は 5 つ。

| # | 目標 | 状態 | Lean |
|---|---|---|---|
| 1 | 値が定まる（v・o が循環しない） | 証明済み（仮定なし） | `val_std`・`rk_std`（V3Total） |
| 2 | SRO より小さい標準形は SRO から届く | 証明済み（仮定なし） | googology-lean の `trio_reach_sro`（ブランチ feature/trio-reach、TrioReach.lean）。trio 側では `std_stts`（V3Order） |
| 3 | 順序を保つ | 4 に帰着 | `order_pres : Desc3 → …`（V3Order） |
| 4 | 値が標準形で、展開で下がる（`Desc3`） | **未完（本題）** | 下の 2 節 |
| 5 | 全射 | 4 と `EvalCof` に帰着 | `surj : Desc3 → EvalCof → …`（V3Surj）。`EvalCof`（拡張 Buchholz 側の共終性）は未証明 |

項の順序の整礎性は `wf_OT`（WF.lean）で証明済み。どの定理も公理は propext・Classical.choice・Quot.sound だけ。

## 2. 本題（目標 4）の現状

### 作戦

`Desc3` を、標準形についての帰納法で示す。各行列 M について、値の不変条件の束（`Inv3V`）を運ぶ。運ぶ仕組みは 4 つ。

- 基底: SRO[n]
- 1 列落とし: M → M.take x（x = 最後の列）。落とす補題 `drop_all*`。hLast とよぶ
- 展開: M → M[n]。最後の列の型 t = 0, 1, 2 ごと。hExp とよぶ
- t = 2 の残りの仮定: hR2（`Res3T2`）

構造の不変条件（行列の形だけの性質）は、すべての標準形で証明済み（`sInvXJ_std`）。残っているのは値の不変条件だけ。

### 最上位の定理（どれも仮定つき）

- 全体: `trio_terminates_main_GH`（V3RestTakeG）。VSmallR を使わない形
- t = 0 の hExp: `hExp_t0_topU`（V3T0TopU）
- t = 1 の hExp: `hExp_t1OP`（V3TPath）
- t = 2 の hExp: `hExp_t2_G`（V3ExpT2M4）。x より前は `t2BelowXRes_of_L`（V3T2SeedWire）
- t = 2 の hR2: `hR2_t2_of`（V3T2R3）。残りは T2BelowXRes だけ

**注意: 今の `Inv3V` には、標準形で偽の欄が入っている**（AbsD・TPLo・AbsUW・TrigOmC）。このため、上の最上位の定理は、今のままでは仮定が満たされない（何も言っていない）。これを直すのが次の仕事。

### 次の仕事: Inv3V2 への一括の移行

下書きは `Ytosk/lean/Ytosk/V3Inv2.lean`（緑、まだどこからも使っていない）。欄の一覧と、各欄を作る側・使う側の表は、desc.md の節「Inv3V2 の下書き: 欄の一覧と生産者・消費者の表」にある。

方針: 偽の欄を、実際に使う所が要る形に狭める。偽の欄を実際に使っているのは、どれも t = 1 の最後の列の枠だけだった。そこで「最後の列の枠の欄」に替える。枠の欄は行列ごとの主張なので、M から M[n] へ運ぶ補題が要らなくなる。

| 今の欄（Inv3V） | 新しい欄（Inv3V2） | 測定 |
|---|---|---|
| AbsD | AbsDS（q ≠ r の枠、始点での吸収） | 9 集合で例外 0 |
| AbsU | AbsUS | 測定途中だった |
| TPLo | TPLoS | 測定途中だった |
| AbsUW | AbsUWL ＋ AbsUW0 | 9 集合で例外 0 |
| TrigOmC | TrigS | 測定途中だった |
| （大域の仮定） | PH3cG・FC3 | 8 集合で例外 0。保存はすべての仕組みで証明済み（`Ytosk.G` 名前空間） |
| （大域の仮定） | VSmallRAll（`vra`） | 標本で例外 0、全数は未測定。1 列落としでの保存は証明済み（`vsmallRAll_take`） |
| VSmallF・FrameClosed・FrameOT・BumpKidsDec・BumpTermDec・TP1C・TP1WC・TPLoW・AbsDW・TPLoN・AbsDN・rootS・rootP・Cons・Good3・Rk | そのまま | Lean の形で真 |

始点 = o_{M.take x}(r) = `(drop1 M x rk).o r`。鎖の添字 ζ はどれも始点以上なので、始点での主張から ζ での主張が fsD の単調性で出る（例 `hADζ_of_absDS`）。

移行の手順:

1. 測定途中だった AbsUS・TPLoS・TrigS を 9 集合で測る。VSmallRAll を 9 集合で全数測る。
2. どれかが偽なら、その欄を使う所が要る形をさらに狭める。
3. 最上位の定理と、各仕組みの欄を作る補題を、1 回の計画した変更で `Inv3V2` に移す。消える補題・要る変更の一覧は desc.md の同じ節の末尾。主な変更:
   - `FrameV` の ad・tplo を「q = r の枠の D の列での AbsD・TPLo」に狭める
   - `expStep_absDN` が使う I.ad を AbsDS から出すか、AbsDN も枠の欄にする
   - t = 1 の TP1C の運び（`expStep_tpG`・`qr2_tpG`）を、PH3cG ＋ TP1LeafG・TP1WLeafG から出す形（`tp1C_of_ph3cG`、V3TP1CutG）に揃える。TP1ResG から TrigCutG を外す
   - `trio_terminates_main_GH` の大域の仮定 hNG（NoGapP、偽）・hP0・hD0 は AbsD・AbsU を作るためだけなので、AbsDS・AbsUS に替えれば外せる
4. VSmallRAll が t = 0・t = 1・t = 2 の展開で保たれることを示す（作る補題がまだない）。
   - t = 0 には穴が 1 つある。最後の写しで、段の鎖が g の上を通る場合に「N で書き換えるなら M.take x でも書き換える」が 2 件偽。

### 未解決の核（名前つきの残りの仮定）

どれも測定では例外 0。証明はまだ。

- **T0CutResGG**（t = 0 の切り口、V3T0DepT・V3T0Thr）。8 集合で例外 0。「どの切り口でも保たれる」は偽で、B の最後の加数として実際に現れる切り口だけが保たれる。閾値の補題（V3T0Thr、塔の形 ThrA・ThrV）は真。足りないのは、引数の中の切り口 ψ_a(Ω_s) を扱う入れ子の主張。T0CutKappa（切り口は Ω の葉）は偽。
- **T2SeedCNext**（構造だけの主張、V3CBig）: M.take x で、r の数えない子 d の次の兄弟 dn が数える子なら、dn は dn − 1 から上げられる。7 集合で例外 0。既存の構造の不変条件から出るかは未確認。
- **t = 2 の始点の残り**: T2SeedQRRes・QNRes・SVRes・CRes の閉じた形の性質（M と M.take x だけの主張、7 集合で例外 0）。
- **1 列落としの残り**（全体の仮定）: VSmallNew・VSmallNewR・ShadowC・UpgAbsX・Seed・BumpAbsC（弱い形）・AbsSR。測定で真、証明はまだ。
  - T2Ext の x−1 の族（16 件）では UpgAbsX が偽で、1 列落としの結論も別の形で破れる。弱い形 UpgAbsXW と、落とす補題の結論 PO の弱い枝の拡張で直す変更を作った。これはローカルのブランチ `dropfix-wkx` の作業用コミット eb0cca69（49 ファイル）にあり、main には入っていない。main に載せ直す前に、2 つの測定を 9 集合で行うこと: upgx2（「x−1 で強い吸収が破れるなら x の行 2 ≠ 0」）と newpv2（新しい形の PO・PV）。t = 2 の道では強い UpgAbsX がまだ要り、それを `Res3T2.ua`（大域の名前 `T2UpgAbs`）として表に出してある。これは T2Ext で偽なので、t = 2 側で広げる必要がある。
- **hLast の残り**: TakeRest3（M.take x の TPLo・AbsUW・AbsDN）。Inv3V2 に移れば TPLo・AbsUW は消える見込み。
- **段 0 の残り**: Z0Link・PhiX0R は偽と分かった。段 0 の扱いは Inv3V2 の枠の欄の形で考え直す。

### 偽と分かったもの（使わないこと）

AbsD・TPLo・AbsUW・TrigOmC（Inv3V の欄）、PhiX・NoGapP・NoGap0PosP・LevLeafInv・PrefLast・VKFree・Z0Link・BandLast、VSmallR（全段の形も hi ≠ 0 の形も）、旧 PH3c（cutsNS）、NoVB、t0.hG′・t0.hU、T0CutKappa、T0ThrGRes、強い BumpAbsC、BumpWeakSrc（旧形）、FrameClosedHi、TPLoN の全列の形。反例は desc.md の各節にある。

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

- Lean の確認: `env --chdir=Ytosk/lean nice -n 15 lake build Ytosk.<依存>` のあと、`lake env lean <ファイル>`（または `leanman check -C Ytosk/lean <ファイル>`、`LEANMAN_TIMEOUT=900`）。
- コミットするファイルに sorry を入れない。仮定は定理の引数として明示する。公理は propext・Classical.choice・Quot.sound だけ（`#print axioms` で確かめる）。
- 新しいファイルは `Ytosk/lean/lakefile.toml` の roots に 1 か所だけ足す。ファイル全体を書き換えない。lakefile をコミットするときは、HEAD の版に自分の 1 行だけ足した blob を作って入れる。他の人の未コミットの行を混ぜない。コミットの直後に roots の数が減っていないか確かめる。
- 共有の定義を変えたら、Ytosk 全体をビルドして緑を確かめてからコミットする。
- git: `git add -A`・`git add .` は使わない。自分のファイルだけを名前で足す。コミットメッセージは日本語。
- シェルで `cd DIR && cmd` を使わない。絶対パス、`git -C`、`env --chdir` を使う。
- trio の外の公開されていないファイルを、公開する文書でローカルパスで書かない。公開先の URL で書く。
- 行列は省略せずに全部書く。例: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)。

## 5. 参照

- desc.md の最後の節「一時停止（2026-10-12 夕方）」: 止めた時点の状態と再開の続き。
- desc.md の節「Inv3V2 の下書き」: 移行の表。
- desc.md の節「訂正と 7 集合の表: Lean と同じ形の欄」: どの欄がどの集合で偽か。
- googology-lean の worktree（ブランチ feature/trio-reach）: 目標 2 の `trio_reach_sro`。googology-lean の main の作業ツリーには書かない（別の作業が進行中）。
