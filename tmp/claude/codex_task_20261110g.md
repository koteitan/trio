# codex 作業 7（2026-11-10、trio-claude から）

## 目的
構造の残り `DecPShape2`（V3DecPSplit2.lean）を、もっと簡単な等式 `DecPColEq` から証明します。
`DecPColEq` は「r の子の連なり c0 ≤ w < w' ≤ q で、隣り合う兄弟は同じ列（col w' = col w）」です。測定では全件で成り立っています。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPShape.lean
- import は `Ytosk.V3DecPSplit2`、namespace と open は V3DecPSplit2.lean と同じです。
- lakefile.toml の roots の最後に "Ytosk.V3DecPShape" を足してよいです。

## 書いてほしいもの

```lean
/-- **Adjacent siblings in the chain have equal columns** (structural, measured). -/
def DecPColEq (M : Mat) (r L q : Nat) : Prop :=
  ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] → topped (M.take (r + L)) c0 = true →
    ∀ w w', w ∈ children M r → w' ∈ children M r → c0 ≤ w → w < w' → w' ≤ q →
      (∀ c ∈ children M r, ¬ (w < c ∧ c < w')) → col M w' = col M w

theorem decPShape2_of_colEq {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hce : DecPColEq M r L q) : DecPShape2 M r L q := by
  sorry
```

## 証明の手順
x := r + L とします。`intro Lc c0 hCL htop w w' hw hw' hc0w hww' hw'q hnb` として、b を作ります。

0. 準備は V3DecPSplit2.lean の `decP_of_split2` の冒頭と同じです。
   - `c_q_facts` から `hpq`（q の親は r）、`hnqT`、`hxb`（col x = bump q）が出ます。
   - c0 は r の子で x 未満です。q は r の子の中で最大です（`hmax`）。
   - `he2r : entry M 2 r = 0` は `(par2_facts I.z2 (by omega) hr).1` です。
1. **w' は T で数えない（上げ先で topped）**
   - w' ≠ c0 で、c0 は `CL (M.take x) r` の最後なので、`¬ Counted (M.take x) r w'` です。
     このために `CL (M.take x) r = Lc ++ [c0]` の後ろに w' がないことを使います。CL は children を Counted で filter したもので、children は昇順です（`children_sorted`）。
   - `col M w' ≠ bump M r` です（`I.be r w' hw'` なら e2 r = 1 になり、he2r と矛盾）。
   - よって `isUpg (M.take x) w' = true ∧ topped (M.take x) w' = true` です（Counted の定義、V3Rank.lean:14）。
2. **上げる列は w' − 1**
   - `isUpg_take` で `∃ i, i + 1 < x ∧ upg M i = some w'` が出ます。
   - `upg_spec` で `w' = i + 1 ∨ (Anc0 M w' i ∧ w' < i)` です。後者は `I.uat i w' hu (by omega) : topped M w' = false` で、次と矛盾します。
     - w' ≠ q なら `topped (M.take x) w' = topped M w'`（`topped_take_eq hlen (w' < x) (x ∉ children M w')`）です。
     - w' = q なら topped M q = true（q の最後の子は x = bump q）です。
   - よって `upg M (w' - 1) = some w'` です。
   - `upg_spec` の m は r です。col w' の e0 は e0 m + 1、w' は r の子なので e0 w' = e0 r + 1（`I.r0p`）。m は w' の祖先なので `anc0_eq_of_e0` で m = r です。
     したがって `par M 1 (w' - 1) = some r`、`col M w' = (e0 r + 1, e1 (w'-1), 1)`、`entry M 2 (w' - 1) = 0`（`upg_e12` と `I.z2`）です。
3. **w の部分木は [w, w'−1]**: `endAt_sib hw hw' hww' hnb : EndAt M w (w' - 1)`（V3SVFlowS.lean）。
4. **w は子を持つ**
   - 子がないなら w' − 1 = w です（`endAt_leaf`）。このとき e2 w = 0 です。
   - `sib_le` か `I.sd` で colLe (col w') (col w) ですが、col w' の e2 が 1、col w の e2 が 0 なので、e0・e1 が等しいところで矛盾します。
     e1 の等しさは col w' = (…, e1 (w'-1), …) = (…, e1 w, …) から出ます。
     `hce` を使って col w' = col w から矛盾させても構いません。
5. **w は topped**
   - w = c0 なら htop です。
   - w > c0 なら、手順 1 と同じ理由で w は上げ先で topped です。
   - topped を M に移すには `topped_take_eq` を使います。w ≠ q なので x は w の子ではありません。
   - 子があるので最後の子 b（`last_child`）は `col M b = bump M w` です（`topped` の定義、Eval.lean:70）。
   - `entry M 2 w = 1` です（`I.be w b hb hbb`）。b < x です。
6. **w' − 1 は b の部分木にあり、b ≠ w' − 1**
   - 部分木にあることは `endAt_last`（EndAt の範囲と b が最大の子）から出ます。
   - b ≠ w' − 1 は e2 b = 1 と e2 (w'−1) = 0 から出ます。
   - `child_toward` で、b の子 k1 で w' − 1 へ向かうもの（`Anc0 M k1 (w' - 1)`）を取ります。
7. **k1 = w' − 1**
   - `hce` から col w' = col w なので、e1 w = e1 w' = e1 (w' − 1) です。
   - `par1_between (par M 1 (w'-1) = some r) k1 (Anc0 M k1 (w'-1)) (r < k1)` から e1 (w'−1) ≤ e1 k1 です。
   - よって e1 w ≤ e1 k1 です。
   - BumpLeaf は `(sInvXJ_std hM hS).1.loc.2.2.2` で取ります（V3T0C.lean:118 と同じ）。それを w、b、k1 に当てると `children M k1 = []` が出ます。
   - `anc0_leaf`（V3InvPsi.lean:65）で w' − 1 = k1 です。
8. 結論は `⟨b, hb, hbx, hbb, (w'-1 ∈ children M b), hupg⟩` です。

## 確認
- 単体 check と全体ビルドを、どちらも exit 0 にしてください。sorry は残さないでください。
- 途中で通らない手順があれば、その手順の番号と最後のエラーを報告してください。
- 報告は chm でしてください。git は使わないでください。
