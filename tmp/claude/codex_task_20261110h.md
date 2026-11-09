# codex 作業 8（2026-11-10、trio-claude から）

最上位を、構造の残りを `DecPShape2` から `DecPColEq` に替えた形にしてください。V3DecPTopWire.lean と同じ形の写しです。

- 新規ファイル: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPTopWire2.lean（import Ytosk.V3DecPShape と Ytosk.V3DecPTopWire）
- `structure SeedPFResV3R11`: `SeedPFResV3R10` の `C1sh : … → DecPShape2 M r L q` を `C1ce : … → DecPColEq M r L q` に替えたもの。
- `theorem seedPFResV3R10_of (hM) (hS) (I) (h : SeedPFResV3R11 M ρ) : SeedPFResV3R10 M ρ`
  - `C1sh` には `decPShape2_of_colEq hM hS I hlen hr hq hqr hncl (h.C1ce …)` を渡します（Ctx は要らないはずです）。
- `structure SeedVFResV3R13`（`pf : SeedPFResV3R11`、ほかは `SeedVFResV3R12` と同じ）と `theorem seedVFResV3R12_of`。
- `translation_order_res18` と `translation_surj_res18`。res17 を使い、`hVF13 : T2AtV3 (fun M ρ => SeedVFResV3R13 M ρ)` を取ります。
- ファイルの最後に `#print axioms` を 2 つ置いてください。
- lakefile.toml の roots の最後に "Ytosk.V3DecPTopWire2" を足してください。
- 単体 check と全体ビルドを、どちらも exit 0 にしてください。報告は chm でしてください。git は使わないでください。
