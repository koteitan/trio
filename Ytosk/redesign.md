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

### 次: BadOutV2（Bad2 の M[n]、n ≥ 2）
エンジンが ¬Bad2 に頼るのは、文脈の Res3AW（古い形の DropRes: NoBad3 つきの bump の形、NBParX つきの吸収、BumpAbsC）だけ。Bad2 版のエンジンは形 B の DropResHB と落とす補題の結論 hdrop から動く必要がある。

t = 0（側 S、P₀(x) = r ∈ {g, p, x − 1}）のエンジン t0_final_inv3V2D → t0_core で崩れる所:
- r = g（数える子 x を持って弱く変わる）: `lhd_or_weak_t0` が弱い葉を r = x − 1 に限る（NoBad3）。項の段階では t0_S1W が使えるが、`counted_first0`（r は N でも g で数える子）は r の行 2 = 0 から出しているので、r の行 2 = 1 の場合の別の理由が要る。
- r = x − 1（親 p は bump 子）: `hlB`（r の親が bump 子なら o′(r) ◁ o(r)）は側 S で偽（t0or: v(r) が弱く変わる）。hlB の使い道（bump の祖父母の枠、g0_drop_rel・v_lhd_bump_children）を作り直す。
- r = p: 弱く変わらない。NoBad3 は形式上だけ要る（PV(p) は ⊴）。
- T0AbsW（HBumpExt と BumpAbsC から）も Bad2 で確かめる。
t = 1・t = 2 は同様に、NoBad3・NBParX・BumpAbsC を使う箇所ごとに調べる。
