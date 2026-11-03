# trio の codex 向けの決まり

## 長いジョブはバックグラウンドで
- 全体ビルド（leanman build、数分）と単体の check は前景で走らせ、終わりを待つ。
- それ以外で 1 分を超えそうなジョブ（測定の pool など）は、バックグラウンドで起動する
  （`nohup ... > log 2>&1 &` など）。ログとチェックポイントはファイルに書く。
- 起動したら、その手番は終える。`sleep` やポーリングで終わりを待たない。
  手番の間は chm のメッセージが読めず、trio-claude からの指示がたまってしまう（2026-11-01 に 1 時間 43 分止まった）。
- 終わったかは、次の手番でログやチェックポイントのファイルを見て確かめる。
- 進捗の定期報告は送らない。送るのは、終わったときと、失敗・反例が出たときだけ。

## git
- git は一切使わない（status・log・diff も）。区切りごとに、ファイル一覧・コミットメッセージ案・
  全体ビルドの exit・公理の結果を chm で trio-claude に送る。trio-claude がコミットする。

## Lean
- 新しいファイルに書く。既存のファイルは変えない。新しいファイルは lakefile.toml の roots に足してよい。
- ビルド: `env --chdir=/home/koteitan/proofs/trio/Ytosk/lean nice -n 5 leanman build`。
  単体: `LEANMAN_TIMEOUT=900 leanman check --backend lean -C /home/koteitan/proofs/trio/Ytosk/lean FILE`。
  exit 0 だけが緑。lake を直接走らせない。pkill を使わない。
- 測定は nice -n 15、6 プロセスまで。
