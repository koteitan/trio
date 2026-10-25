# 接ぎ木の悪い形 Bad2 への対応（2026-10-24）

接ぎ木の標準形（tmp/ytosk-handoff/sets/graftA.pkl・graftB.pkl、作り方 tmp/claude/gen_graft.py）で、最上位の残り HFrameV2・HDropV2W と不変条件 Inv3V2 の欄 TPLoW・AbsDW が偽だった。

## 残りの地図（2026-10-26、最上位 trio_terminates_main_V2_cur の 14 個）

| 残り | 中身 | 測定 | 消すのに要るもの |
|---|---|---|---|
| HDropU | 落とす補題の仮定（形 B）と条件のない ua | 全集合で例外 0 | 落とす補題の仮定を値の不変条件から出す（核） |
| T2BadRes | Bad2 の t = 2: T2AbsNBad（落とし側が破れる列での M[n] の弱い吸収）・T2QNDomBad（v_T(q) ⋬ v_M(q) のときの ω_T の成分の支配） | 例外 0（前件は graftBb2St 3 個・b2grow 804 件） | AbsN: M[n] の bump 項の下からの評価。QNDom: HUAC（下）＋ ω の成分の補題・和の吸収の補題 |
| T0BadSeedsH7 | Bad2 の t = 0 の種の 3 つの事実 | 例外 0 | (1) は HUAC と同じ核。(3) は UpgAbsX の破れを使う値の議論 |
| HFrameV2・HLeafV2 | 標準形の 1 列落としの枠・葉の欄 | 例外 0 | 欄ごとの値の議論 |
| HBumpExt | 接頭辞で bump 項が増える | 例外 0 | M[n]（不変条件のない行列）について言うので落とす補題から出ない |
| T2CBadOut | C の形で x − 1 が上げる（T2CBad）の出力 | cbadext の 10 個で例外 0 | 別の組み立て（q − 1 → q の上げで o_N(d) ≠ o_T(d)、C_frame の hval が偽） |
| hVU・hCl・hPRE・hCan・hDomQ・hVCp・hAG | t = 2 の種と写しの枠の残り（文脈 StepCtxT2 は Bad2 を含む） | Bad2・cbadext でも例外 0 | 欄ごと。hCan（隣の兄弟の v の比較）は不変条件として運ぶ必要 |

新しい一般の性質の候補 **HUAC**: 列 n が祖先 k へ上げるとき（k < n）、∀ u、comps u v(P₁ n) の各成分は comps u v(n) ∪ {0} のどれか以下。v(n) = v(k)・P₁(n) = P₁(k) なので、上げ先の bump 型の列 k の吸収の成分版。18 集合・約 800 万件で例外 0（上げ先が n + 1 では偽、計 81 件）。T2QNDomBad と T0BadSeedsH7 (1) の共通の核（scratchpad の vcomp.py・qnweak.py）。

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
