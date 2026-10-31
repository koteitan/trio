# WfSrcC3: SrcC3Res は偽（2026-10-31）

## 結論
SrcC3Res（SmallB）・SrcC2Res（o(c) < B(v(r))）・SrcC5Res・T2AbsNSrc / T2AbsNSrcW の (c)（s < B(v(r))）は、
標準形の 36 列の行列で偽。使う側の T2AbsNBad と、t2_absWN_bad の結論 AbsWN M M[2] も同じ行列で偽。

M = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)
    (6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,2,0)(12,0,0)
    (13,1,1)(14,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,1)
（graftBb2St の 35 列の枠に、c = 26 = (11,1,0) の最初の子として (12,2,0) を接いだもの。SRO から 93 手、reach_cex36.json）

- x = 35、r = 34 = P0 x = P1 x = P2 x、p = 33 は i = 32 の bump 子、Bad2 は第 2 の選言（BumpAbsC が i = 32 で破れる）。
- m = P1 i = 31、b = 31、k = upg b = 24、j = 25、c = 26。v(c) = v(r) = ψ(1)、c の数える子 27 = (12,2,0) は v(27) > v(r)。
- s = bumpW(24) = v(31) の唯一の加数、s = ψ_{ψ(1)}(Ω_{ψ(1)+1} + …) ≥ B(v(r))。
- M[2] で W_{M[2]}(32) = ψ_{ψ(1)}(Ω_{ψ(1)+1}) ≤ s < W_M(32)、s ⋪ W_M(32)（u = 0、c = W_M(32) で Ω_{ψ(2)} の成分が支配されない）。
- Python（tools/probe_inv3_prefix.inv_fields）: M と M[2] で不変条件の欄はすべて真。T2CBad でない（P0 x = r）。

## Lean（Ytosk/lean/Ytosk/WfSrcC3Cex.lean、緑、公理は propext / Quot.sound だけ）
- standard（93 手の Std.exp）、cons / consT / consN（M、M.take 35、expand M 2 の評価表）、bad2、dropFail。
- t2AbsNSrc_core_false、srcC3_core_false、t2AbsNBad_core_false: StepCtxT2（と SrcFacts）を Std ∧ Cons に替えた主張が偽。
- not_absWN、not_absWN_gexp: ¬ AbsWN M (gexp M 34 1 … 2) 35 ρ σ（t2_absWN_bad の結論の形）。

## 測定（probe_c1.py、SrcC3Res の形の枠、DropFail で絞らない）
| 集合 | 出どころ | v(m′) < v(r) | v(m′) = v(r) | v(m′) > v(r) | v(c) = v(r) |
|---|---:|---:|---:|---:|---:|
| graftBb2St | 1527 | 1514 | 12 | 1 | 3 |
| b2grow1 / b2grow2 | 31 / 27 | 全部 | 0 | 0 | 0 |
| Cprime | 148 | 144 | 4 | 0 | 0 |
| ext2 | 78 | 78 | 0 | 0 | 0 |
| t2ext | 162 | 158 | 4 | 0 | 0 |
m′ = P0 k = P1 k。v(c) ≤ v(m′)（bump_kid_le_parent）。v(c) = v(r) の枠（graftBb2St の 3 個）は c が r の写しで、
c の部分木に行 1 が大きい子を 1 本接ぐだけで SmallB が破れる（上の M）。

## 枠全体の GenSmall（probe_g1.py）も偽
k の bump 子の子 c で SmallB(v(P1 k)) c: b2grow1 で 8773/17838、graftBb2St で 28270/41784 が偽。

## 次（リードへ）
s < B(v(r)) は使う側（T2AbsNBad、AbsWN M M[n]）ごと偽なので、Bad2・t = 2 の drop 側の吸収の設計を変える必要がある。
この M では v(31) = s の吸収が M[2] で起きない。M[n] の不変条件そのもの（inv_fields）は真なので、AbsWN を経ない道が要る。
