# 接ぎ木の悪い形 Bad2 への対応（2026-10-24）

接ぎ木の標準形（tmp/ytosk-handoff/sets/graftA.pkl・graftB.pkl、作り方 tmp/claude/gen_graft.py）で、最上位の残り HFrameV2・HDropV2W と不変条件 Inv3V2 の欄 TPLoW・AbsDW が偽だった。

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
- 残りの仮定をすべて b2grow1・shapegrow（展開＋1 列）でも測り直す。
- T0BadSeedsH7 の (1)・(2) は、上げの吸収の成分の性質（祖先への上げで例外 0）と v′(P₁(x − 1)) = v(P₁(x − 1)) から出せる見込み。(3) は UpgAbsX の破れを使う値の議論が要る（構造だけでは出ない、desc.md）。
- BadOutT2B（t = 2）: 文脈 StepCtxT2 の残りがすべて ¬Bad2 を前提にしている。t = 1 と同じく、エンジンが文脈から何を読むかを先に調べる。
