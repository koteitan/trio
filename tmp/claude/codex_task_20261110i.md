# codex 作業 9（2026-11-10、trio-claude から）

## 目的
`DecPColEq`（V3DecPShape.lean）は残りではなく、R1S から証明できます。これで decP の構造の残りが消えます。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPColEq.lean
- import は `Ytosk.V3DecPShape` です（作業 8 の V3DecPTopWire2 も使うなら、その import も足してください。下の 3. を参照）。
- lakefile.toml の roots の最後に "Ytosk.V3DecPColEq" を足してよいです。

## 書いてほしいもの

1. 証明してほしい定理:
```lean
theorem decPColEq_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) :
    DecPColEq M r L q := by
  sorry
```

2. 証明の手順。`intro Lc c0 hCL htop w w' hw hw' hc0w hww' hw'q hnb` として、`col M w' = col M w` を示します。作業 7 の手順 1〜5 をほぼそのまま使います。
   - (1)〜(2) は作業 7 と同じです。
     - w' は上げ先で topped です。
     - 上げる列は w' − 1 です。
     - `par M 1 (w' - 1) = some r`、`col M w' = (entry M 0 r + 1, entry M 1 (w' - 1), 1)`、`entry M 2 (w' - 1) = 0` です。
   - (3) `endAt_sib` で EndAt M w (w' − 1) です。
   - (4) w は子を持ちます。
     - 子がないなら w' − 1 = w で e2 w = 0 です。
     - 一方 col w' = (e0 r + 1, e1 w, 1) です（e1 (w'−1) = e1 w）。
     - SibDec（`I.sd`、隣り合う兄弟）から colLe (col w') (col w) ですが、e2 の 1 ≤ 0 が成り立たず矛盾します。
     - ここでは hce を使わないでください。e1 の等しさは w' − 1 = w から出ます。
   - (5) w は topped で、最後の子 b は bump、`entry M 2 w = 1` です（作業 7 と同じ）。
   - (6) e1 の等しさを示します。
     - R1S は `(sInvXJ_std hM hS).1.r1s : R1S M`（V3InvExpand.lean の SInvX）です。w は r の子なので `entry M 1 w ≤ entry M 1 r + 1` です。
     - `par1_entry_lt (par M 1 (w' - 1) = some r)` から `entry M 1 r < entry M 1 (w' - 1)` です。
     - `par1_between (par M 1 (w' - 1) = some r) w (Anc0 M w (w' - 1)) (r < w)` から `entry M 1 (w' - 1) ≤ entry M 1 w` です。
     - 以上から `entry M 1 w = entry M 1 (w' - 1)` です（omega）。
   - (7) col を成分で比べます。
     - e0 は両方とも e0 r + 1 です（`I.r0p`）。
     - e1 は (6) で等しいです。
     - e2 は両方とも 1 です。
     - 結論は `col M w' = col M w` です。col は (entry 0, entry 1, entry 2) の組なので、Prod.ext か `col_eq_entries` 系の補題で示してください（grep してください）。

3. 作業 8 が終わっていたら、最上位も作ります。
   - V3DecPTopWire2.lean の `SeedPFResV3R11` から `C1ce` を外した `SeedPFResV3R12` を作ります。
   - あわせて `seedPFResV3R11_of`、`SeedVFResV3R14`、`seedVFResV3R13_of`、`translation_order_res19`、`translation_surj_res19` を、このファイルに書いてください。
   - 形は作業 8 と同じです。`C1ce` には `decPColEq_holds hM hS I …` を渡します。

## 確認
- 単体 check と全体ビルドを、どちらも exit 0 にしてください。sorry は残さないでください。
- 通らない手順があれば、その番号と最後のエラーを報告してください。
- 報告は chm でしてください。git は使わないでください。
