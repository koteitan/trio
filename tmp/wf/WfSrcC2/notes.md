# WfSrcC2: (c) SrcCRes を列の v の比較に下げる（2026-10-31）

## Lean（緑、全体ビルド 1137 jobs、公理 propext / Classical.choice / Quot.sound）
- WfSrcC2a.lean
  - 項の補題: B(V) = ψ_V(Ω_{V+1}) は 1 より大きく、和（add_lt_single, sumN_lt_single）と ω 冪（omega_lt_bnd）で閉じる。
  - bumpW_lt_bnd: k の bump 子 j の子 c がすべて o(c) < B(V) なら bumpW(k) < B(V)。
  - 残り SrcC2Res: DropFail の形（WfSrcB.SrcC の前件）で、吸収されない加数 s の出どころ
    （Up1 b m、upg b = k、s = bumpW(k)、Origins の source_summand_origin）の k について、bump 子の子 c で o(c) < B(v(r))。
  - 橋 srcC_of_c2 : SrcC2Res → WfSrcB.SrcC、t2AbsNSrcW_of_c2 : SrcARem2 → SrcBNonlost2 → SrcC2Res → T2AbsNSrcW。
- WfSrcC2b.lean
  - spArg_lt_om: sp は Ω_{a+1} 未満から始めて B(a) 未満の標準形を足す限り Ω_{a+1} 未満。
  - o_lt_bnd_of_children: v(c) < V、または v(c) = V かつ数える子 d で o(d) < B(V) ⇒ o(c) < B(V)。
  - SmallB（帰納的述語、v だけ）、o_lt_bnd_of_small。残り SrcC3Res（SmallB）、橋 c2_of_c3。
  - 残り SrcC5Res（深さ 1: v(c) ≤ v(r)、c の数える子 d で v(d) < v(r)）、橋 c3_of_c5、srcC_of_c5 : SrcC5Res → WfSrcB.SrcC。
- 最上位への差し込み: WfSrcABC.t2AbsNSrcW_of hA hB hC（hC : SrcCRes）の代わりに
  WfSrcC2.t2AbsNSrcW_of_c2 hA hB (WfSrcC2.c2_of_c3 (WfSrcC2.c3_of_c5 h5))、または
  WfSrcB.t2AbsNSrcW_of (WfSrcABC.srcA_of_rem2 hA) (WfSrcB.srcBNonlost_of_2 hB) (WfSrcC2.srcC_of_c5 h5)。
  T2BadRes の第 3 欄を WfSrcC.SrcCRes から WfSrcC2.SrcC5Res に替える。

## 測定（probe_d1〜d4、DropFail の枠: grow 1192・graftBb2St_x2 3）
- 吸収されない加数は枠ごとに 1 個、添字 = v(r)、出どころは 1 つで b = m = P1 i、k の bump 子は 1 個、その子は 1 個（c1）。
- c1 は r の写し（行 1・2 と上げ先が r と同じ、v(c1) = v(r)）。c1 の数える子は行 1 が c1 より小さい。
- SrcC2Res（o(c) < B(v(r))）・SmallB・SrcC5Res（深さ 1）は 1195 枠すべてで成り立つ。
- **偽**: 部分木全体の上界 ∀ e ⊒ c, v(e) ≤ v(r)（1192 枠すべてで破れる。v = 0 の子の下で v が再び上がる）。
- 形の枠全体（DropFail で絞らない、--all）: 下の表。

## 次
SrcC5Res の中身: v(c) ≤ v(P1 k) は V3T2SrcIndex.bump_kid_le_parent（k が頭打ちでないとき）で出る。
残りは v(P1 k) ≤ v(r)（例では P1 k も r の写し）と、c の数える子 d で v(d) < v(r)（d の行 1 < c の行 1）。

### 形の枠全体（--all、DropFail で絞らない、吸収されない s < W_M(i) の出どころごと）
| 集合 | 出どころ | o(c) < B(v(r))（SrcC2Res） | SmallB（SrcC3Res） | 深さ 1（SrcC5Res） |
|---|---:|---:|---:|---:|
| graftBb2St | 1527 | 1527 | 1527 | 338（偽 1189） |
| b2grow1 | 31 | 31 | 31 | 8（偽 23） |
| b2grow2 | 27 | 27 | 27 | 9（偽 18） |
| t2ext | 162 | 162 | 162 | 162 |
| ext2 | 78 | 78 | 78 | 78 |
| expPt2 | 18 | 18 | 18 | 18 |
| Cprime | 148 | 148 | 148 | 148 |
| deep2 | 2 | 2 | 2 | 2 |

よって差し込みは SrcC3Res を推す（WfSrcC2.t2AbsNSrcW_of_c3 hA hB h3）。SrcC5Res は DropFail に頼る狭い形。
