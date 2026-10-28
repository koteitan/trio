# WfT2Abs: T2AbsNBad の作業ログ（2026-10-29）

## 目標
T2BadRes = T2AbsNBad ∧ T2QNDomBad2 の第 1 欄 T2AbsNBad（V3T2BelowR）を消すか狭める。

## 記号
M の最後の列 x = r + L、r = P2(x)。T = M.take x（評価 τ）、N = M[n] = gexp M r L d0 d1 n（評価 σ）。
W_M(i) = bumpW M ρ i、W_T(i)、W_N(i) も同様。B(v) = ψ_v(Ω_{v+1}) = psi v (psi (v+1) 0 0) 0。
「落とし側の吸収の破れ」（DropFail）: v(P1 i) の加数 q で q ≥ ψ(2)、q ≥ W_T(i)、q < W_M(i)、q ⋪ W_M(i) が在る。

## 測定 1: 分解の候補（probe_bound.py、codex の 133 件）
133 個の異なる行列（codex の t2_absn_growth の全 case）で:
- 破れる加数 q の先頭の添字 = v_M(r)（133/133）
- q < B(v_M(r))（133/133）
- v_N(r) = v_M(r)（n = 2,3,4 で 399/399）。v_T(r) ≠ v_M(r)（133/133、T では r が最後の列で上げがない）
- W_N(i) = o_N(r)（399/399）、B(v_N(r)) ≤ o_N(r) = W_N(i)（399/399）
- v(P1 i) は全件 1 つの加数。W_T の条件を外しても（q ≥ ψ(2)、q < W_M、q ⋪ W_M だけ）q < B(v_M(r))（133/133、probe_variant.py）
- 全 148 件（重複込み）で e2(r) = 0、(d0, d1) = (1, 1)。

例（最小）: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,0,0)(13,1,1)(14,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,1)
x=34, r=33, i=31=P0(P0 r), v(r)=ω。
q = v(P1 i) = ψ_ω(ψ_ω(ψ_ω(ψ_0(Ω_2)))), W_M = ψ_ω(Ω_{ω+ω}), W_T = Ω_1, W_N(n) = ψ_ω(Ω_{ω+n−1}) = o_N(r)。
B(ω) = ψ_ω(Ω_{ω+1})。q < B ≤ W_N < W_M。
なぜ Ω_{v_N(r)} ≤ W_N では足りないか: q = ψ_ω(…) > Ω_ω。必要なのは引数まで含めた ψ_{v(r)}(Ω_{v(r)+1})。

## 測定 2: 新しい集合（probe_sets.py、前件は Bad2 の必要形、L / i で絞らない）
graftBb2St_g0 2738、cbadext 3756、shapegrow 2372、ext2b2St 2133、b2grow1 6517 行列: 破れる列 0 件（反例 0）。
grow（133 件から n=1..4 の展開を 3 段、長さ 130 以下の接頭辞）ほかの結果は下の「測定 3」。

## 測定 3（probe_sets.py、T2AbsNSrc の 3 欄と展開側、n = 2,3）
- grow: 404,218 行列（標準形の展開と接頭辞）、Bad2 必要形 48,845、破れる列 1,192（codex の 133 の約 9 倍）。
  形（L = 1、i = P0(P0 r)）1192/1192、q < B(v_M r) 1192/1192、v_N(r) = v_M(r) 2384/2384、B ≤ W_N 2384/2384、目標 2384/2384。
- graftBb2St_x2: 破れる列 3、全欄真。
- b2grow2・graftBb2St_g1/g2/p0/p1/x0/x1・d3s・deep2・deep3・t2ext（120 万）・e3exp・ext3s・t0ext・ext1x・Cprime・std_a: 破れる列 0。
- 反例 0。

## 測定 4（probe_exp.py、T2AbsNExp の前件だけ＝破れで絞らない上位集合）
Bad2 必要形 ∧ P2(x) = x−1 ∧ e1 g, e2 g ≠ 0、n = 2,3 で B(v_M r) ≤ W_N(g) と v_N(r) = v_M(r):
grow 14,782 件、t2ext 851、b2grow2 27、graftBb2St_x2 2,673、Cprime 528、deep2 259。全部真（延べ 19,120 前件 × 2 n）。

## Lean（緑、03aa10bc）
Ytosk/lean/Ytosk/WfT2AbsSrc.lean:
- `WfT2Abs.Bnd v := psi v (psi (add v one) z z) z`
- `WfT2Abs.DropFail M ρ τ x i`（T2AbsNBad の破れの前件そのまま）
- 残り `WfT2Abs.T2AbsNSrc`（M 側だけ、N を含まない）:
  T2AbsNBad と同じ前件 ⇒ L = 1 ∧ (∃ p, P0 r = p ∧ P0 p = i) ∧
  ∀ s ∈ summands(v(P1 i)), ¬ s < ψ(2) → s < W_M(i) → ¬ s ◁ W_M(i) → s < Bnd(ρ.v r)
- 残り `WfT2Abs.T2AbsNExp`（展開側の計算）:
  StepCtxT2・Bad2・r + 2 = |M|・P2(r+1) = r・P0 r = p・P0 p = i・e1 i, e2 i ≠ 0 ⇒ ∀ n ≥ 2 σ, Bnd(ρ.v r) ≤ W_N(i)
- 橋 `WfT2Abs.t2AbsNBad_of : T2AbsNSrc → T2AbsNExp → T2AbsNBad`（公理 propext, Classical.choice, Quot.sound）

注意: T2AbsNSrc ∧ T2AbsNExp は T2AbsNBad より強い十分条件（同じ前件に結論を足したもの）。
得たもの: 展開 N を M 側の主張から追い出した。T2AbsNExp は計算の主張。

## T2AbsNExp を証明するときの壁（今回は証明していない）
道筋: W_N(i) ≥ ω^(o_N(r)) ≥ o_N(r) = sf ψ_{σ.v r}(o_N(r+1))、children_N r = [r+1]、
upg_N(r+1) = none（次の列は e2 が違う。ancestor の道は par1 q = r が要るので無理）なので
e2 r = 0 なら σ.v(r+1) = σ.v r + 1、o_N(r+1) ≥ Ω_{σ.v r + 1}。最後に σ.v r = ρ.v r。
壁:
1. T2AbsNBad の前件は Cons N σ だけ。sumN・sf・omega の単調性の補題は isOT が要る。
   N の前の方の列（i・p の子）の σ.o の isOT は、使う側（T2BelowRV2）でも与えられていない
   （与えられているのは σ.o r と j ≥ r+L の列の isOT だけ）。Good3 N σ はこの AbsWN を使って後で出す。
2. σ.v r = ρ.v r は agree_gexp（V3ExpT2B、e2 r = 0、UAT M・UAT N・Rk N が要る）と
   not_depS_v_self から出せそうだが、Rk N（rk_gexp_t2_final）に UAT N・BumpE2 N が要る。
