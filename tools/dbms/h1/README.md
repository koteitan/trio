# 課題 H1 の道具（2026-08-28）

`../H1-NOTES.md` の測定を再現するための一式。**作業ディレクトリは
`/tmp/h1work` を前提に書いてある**（パスは file の先頭で直に書いている）。

    mkdir -p /tmp/h1work && cp *.py /tmp/h1work/
    python3 /tmp/h1work/mkprovh.py          # 決定を丸ごと記録する conv3 の写し
    python3 /tmp/h1work/h1data.py sheet     # 出典 1: シート 1354 行
    python3 /tmp/h1work/h1data.py teach 6 6 # 出典 2: ImgClosedT の目標
    python3 /tmp/h1work/h1data.py teach 7 4
    python3 /tmp/h1work/h1p0b.py prev0      # 素性のビット表を作る（h1p0.py を使う）
    python3 /tmp/h1work/h1cover.py          # fp=0 の連言で正例を覆う（集合被覆）

`h1p0.py` の `atoms()` が素性（55 個）。**行列から直に読めるものだけ**にしてある
（`st['prev']` のような持ち回る状態を使うと写しに同変でなくなる）。

**注意**: `mkprovh.py` は `rows3.py` の本文をパターン置換で写す。`rows3.py` の
該当行を変えたら置換のアンカーを直すこと。
