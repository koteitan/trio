# codex 作業 10（2026-11-13、trio-claude から）

## 目的
残り `QRNoSwitch`（V3QRW1.lean）を、B' ≠ 0 の場合だけの残り `QRNoSwitchB` に狭めます。
B' = 0 の場合は、下の手順で証明できます。測定では、M で引き金が立つ 29140 件のうち 21671 件が B' = 0 です。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3QRNoSwitchB.lean
- import は最上位のファイル `Ytosk.V3DecPColEq` です（最上位も作るため）。namespace と open は V3QRW1.lean と同じです。
- lakefile.toml の roots の最後に "Ytosk.V3QRNoSwitchB" を足してよいです。

## 書いてほしいもの

1. 残りの定義（QRNoSwitch に `spArg … ≠ z` の仮定を 1 つ足しただけ）:
```lean
def QRNoSwitchB (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ L' c s y s' y', Lc = L' ++ [c] → ρ.o c = psi s y z → τ.o c = psi s' y' z →
    spArg (ρ.v r) z (sumN (L'.map ρ.o)) ≠ z →
    (lt (spArg (ρ.v r) z (sumN (L'.map ρ.o))) y = true ∧ lt (psi (ρ.v r) z z) (psi s y z) = true) →
    (lt (spArg (ρ.v r) z (sumN (L'.map ρ.o))) y' = true ∧ lt (psi (ρ.v r) z z) (psi s' y' z) = true)
```

2. 証明してほしい定理（仮定は qr_w1_of と同じ。SeedPFResV3R6 の qr 欄と同じ前提です）:
```lean
theorem qrNoSwitch_of_B {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk) {r L : Nat} {Lc : List Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    (hCL : CL M r = Lc ++ [r + L]) (hB : QRNoSwitchB M ρ r L Lc) : QRNoSwitch M ρ r L Lc := by
  sorry
```

## 証明の手順
`intro τ hτ L' c s y s' y' hLc hsy hsy' htrig` とします。B' := spArg (ρ.v r) z (sumN (L'.map ρ.o)) です。
- B' ≠ z なら `hB` をそのまま使います。
- B' = z のとき:
  1. `htrig.1 : lt z y = true` から y ≠ z です。
  2. CL_M(c) ≠ [] を示します。o_M(c) = ψ_s(y) の引数は spArg (ρ.v c) z (sumN ((CL M c).map ρ.o)) です（`o_cl_eq`、V3StrictR.lean:167、または `cl_vals`）。CL M c = [] なら引数は z で、y ≠ z と矛盾します。
  3. CL_T(c) ≠ [] を示します。CL M c の元 e は、M で c の数える子です。`counted_take_of`（V3T0Res.lean:113）で `Counted (M.take (r + L)) c e` です（e < r + L、e ≠ r、c < r + L）。children も T で同じです（`children_take`）。
  4. y' ≠ z を示します。o_T(c) = ψ_{s'}(y') の引数は spArg (τ.v c) z (sumN ((CL T c).map τ.o)) で、CL T c ≠ [] です。各 τ.o e は ψ の形なので和は z でなく、`spArg_ne_z`（V3FrameT1.lean:147）で y' ≠ z です。
  5. `t2SVc0'_of_dropV3 I Ctx hlen hr τ hτ L' c (CL_T(r) = L' ++ [c]) s' y' hsy' hy'` から、ρ.o c = psi s' yM z かつ y' ≤ yM の形が出ます（使い方は V3QRW1.lean の qr_w1_of の中、`hyM` のところを見てください）。hsy と合わせて s' = s です。
     - CL_T(r) = Lc は qr_w1_of の `hCLT` と同じ手順で示せます。必要ならその部分を補題に切り出してください。
  6. 結論: 第 1 成分は lt z y' = true（y' ≠ z から）。第 2 成分は lt (psi V z z) (psi s y' z) = true です。htrig.2 の lt (psi V z z) (psi s y z) から、添字の比較で V < s なら y' によらず成り立ち、V = s なら z < y' から成り立ちます（psi の比較の補題を grep してください）。

3. 最上位も作ります。
   - `SeedPFResV3R12`（V3DecPColEq.lean）の qr 欄を `QRNoSwitchB` にした `SeedPFResV3R13` を作り、`seedPFResV3R12_of` で戻します。
   - あわせて `SeedVFResV3R15`、`seedVFResV3R14_of`、`translation_order_res20`、`translation_surj_res20` を、このファイルに書いてください。形は V3DecPColEq.lean の res19 と同じです。

## 確認
- 単体 check と全体ビルドを、どちらも exit 0 にしてください。sorry は残さないでください。
- 通らない手順があれば、その番号と最後のエラーを報告してください。
- 報告は chm でしてください。git は使わないでください。
