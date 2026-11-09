# codex 作業 4（2026-11-10、trio-claude から）

## 目的
decP を 2 つの残りに分けました（Ytosk/lean/Ytosk/V3DecPSplit.lean の `decP_of_split`）。

- `DecPShape`（構造）
- `DecPUntop`（c0 が topped でない場合の値）

このファイルの補題を最上位につなぐ差し込みを書いてください。形は V3C1Strict.lean の後半と同じで、機械的な写しです。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPTopWire.lean
- 書き出しは次のとおりです。
  ```lean
  import Ytosk.V3DecPSplit
  namespace Ytosk.V3Main.SeedPF
  open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
  ```
- lakefile.toml の roots の最後に "Ytosk.V3DecPTopWire" を足してよいです。既存のファイルは変えないでください。

## 書いてほしいもの

1. `structure SeedPFResV3R10 (M : Mat) (ρ : Valn) : Prop`
   - V3C1Strict.lean の `SeedPFResV3R9` と同じ欄（`qr`・`C2r`）を持たせます。
   - `C1d` の代わりに、次の 2 つの欄を置きます。
     ```lean
     C1sh : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
       (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → DecPShape M r L q
     C1ut : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
       (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → DecPUntop M ρ r L q
     ```
2. `theorem seedPFResV3R9_of {M ρ rk} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (h : SeedPFResV3R10 M ρ) : SeedPFResV3R9 M ρ`
   - 中身は `⟨h.qr, fun r L q hlen hr hq hqr hncl hun => decP_of_split hM hS I Ctx hlen hr hq hqr hncl hun (h.C1sh …) (h.C1ut …), h.C2r⟩` の形です。
3. `structure SeedVFResV3R12`
   - `SeedVFResV3R11` の `pf` を `SeedPFResV3R10` に替えたものです。
   - あわせて `theorem seedVFResV3R11_of`（V3C1Strict.lean の `seedVFResV3R10_of` と同じ形）を書きます。
4. `translation_order_res16` を使う `translation_order_res17` と、`translation_surj_res16` を使う `translation_surj_res17` を書きます。
   - V3C1Strict.lean の section と同じ変数を使い、`hVF11` を `hVF12 : T2AtV3 (fun M ρ => SeedVFResV3R12 M ρ)` に替えます。
   - 中の関数は `(fun M ρ rk C hz h2 => seedVFResV3R11_of C.std C.ne (coreW C.S C.I) C (hVF12 M ρ rk C hz h2))` です。
5. ファイルの最後に `#print axioms translation_order_res17` と `#print axioms translation_surj_res17` を置きます。

## 確認
- 単体 check: `LEANMAN_TIMEOUT=900 leanman check --backend lean -C /home/koteitan/proofs/trio/Ytosk/lean <ファイル>`
- 全体ビルド: `env --chdir=/home/koteitan/proofs/trio/Ytosk/lean nice -n 5 leanman build`
- どちらも exit 0 にしてください。sorry は残さないでください。
- 終わったら chm で、ファイル名・2 つの exit・公理を送ってください。git は使わないでください。
