# codex 作業 6（2026-11-10、trio-claude から）

作業 4 の V3DecPTopWire.lean を、直した形に合わせて書き換えてください。

- `C1sh` の型の `DecPShape M r L q` を `DecPShape2 M r L q` に替えます。
  `DecPShape2` は V3DecPSplit2.lean にあります。
- `seedPFResV3R9_of` の中の `decP_of_split` を `decP_of_split2` に替えます（引数の並びは同じです）。
- import を `Ytosk.V3DecPSplit2` に替えます。
- lakefile.toml の roots の最後（"Ytosk.V3DecPSplit2" の後ろ）に "Ytosk.V3DecPTopWire" を足し直してください。
  trio-claude がコミットのために一度外しました。
- 単体 check と全体ビルドを、どちらも exit 0 にしてください。
- 終わったら chm で報告してください。git は使わないでください。
