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

### 計画
1. CntX に第 3 の選言を足す:「数える子は x だけ ∧ UpgBad(x − 1) ∧ BadPos」（BadPos: p が g の bump 子で g が x の祖先）。¬Bad2 の文脈では、UpgBad(x − 1) は UpgAbsX の破れなので BadPos と合わせて Bad2 になり、第 3 の選言は起きない（古いエンジンはそのまま古い CntX を取り出せる）。graftB で測った広げた CntX（drop-redesign の形）で PV は例外 0。
2. UpgAbsXW0 の弱い選択肢を NBParX ∨ BadPos に、BumpWeakSrc の形を「i の子は j と x だけ」（BadPos のとき）に広げる。¬Bad2 の文脈では強い吸収が成り立つので、使う側は強い選択肢を使う。
3. 落とす補題（drop_all_hard・bump_drop）を広げた仮定で PV（新しい CntX）まで示す。
4. TakeBadV2: inv3V2_take を新しい DropRes で通す。
5. BadOutV2（t = 0）: lhd_or_weak_t0 に r ≠ x − 1 の弱い葉（CntX の第 3 の選言）を足し、V3T0M の道を Bad2 でも通す。t = 1・t = 2 は同様に調べる。
6. 新しい残りを立てるときは接ぎ木の集合（graftA・graftB、Bad2 側 graftBb2・graftBb2Sf）でも測る。
