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

# 課題 H2 の道具

族 β（`conv3(A<n>)` が余分な写しを出す型）の教師データと、兄弟の付け場所の探索。

    python3 /tmp/h1work/h2probe.py 6 3   # T が U の部分列かを測る
    python3 /tmp/h1work/h2fail.py 6 3 4  # ImgClosedT の破れた A を pickle に
    python3 /tmp/h1work/h2beta.py 5 3    # 破れた対の証人 B = d2b3(T) を見る
    python3 /tmp/h1work/mksib.py         # 兄弟の深さを site ごとに強制できる写し
    python3 /tmp/h1work/h2sites.py       # 正例（証人）/ 負例（シート）を集める
    python3 /tmp/h1work/h2feat.py        # 素性表
    python3 /tmp/h1work/h2cover.py       # fp=0 の連言で正例を覆う
    python3 /tmp/h1work/mksib2.py        # 旗つきの写し rows3b.py（sibdd*/aw*）

**族 β の証人は `A<m+1>` ではなく `d2b3(T)`。** 長さが揃うので柱ごとに整列できる。

# 課題 H3 の道具

    python3 /tmp/h1work/h3a1.py 3 3   # A1 の像を動かして ImgClosedT が立つか（全数）
    python3 /tmp/h1work/h3ct.py       # closes_top の撃ちすぎの教師データ
    python3 /tmp/h1work/h3cov.py <pkl> 3   # 汎用: fp=0 の連言で正例を覆う
    python3 /tmp/h1work/mkctr2.py     # 縮約を止める／数える写し rows3c.py
                                      #   CX = {noctr, no_res, no_rf, max1}
                                      #   b2d3c(M) -> (像, 発火の内訳)

# 課題 H4 の道具（全射）

    python3 /home/koteitan/proofs/dbms/tools/dbms/onto.py 7   # 全射の採点（数秒）
    python3 /tmp/h1work/mkctr3.py   # 縮約の cB の深さ／梯子を旗で変える rows3d.py
    python3 /tmp/h1work/mkctr4.py   # 縮約の cB を site ごとに強制する rows3e.py
    python3 /tmp/h1work/mkctr5.py   # 縮約のどの門で落ちたかを記録する rows3g.py
    python3 /tmp/h1work/mkctr6.py   # 縮約の cB に first/force を渡す rows3h.py
    python3 /tmp/h1work/h4sites.py 7   # cB の付け場所の教師データ（**ラベルは壊れる。§24 を読むこと**）

**落とし穴**: `d2b3` は単射でない。同じ B を複数の T に返すので、
「T が外れた ⇒ B の綴りが悪い」と読むと教師データが壊れる（§24）。

# 課題 H5 の道具（縮約の門）

    python3 /tmp/h1work/mkctr7.py   # 縮約を lad0 から切り離す rows3i.py（GX = nolad0/nolad0_v/nolad0_f）
    python3 /tmp/h1work/mkctr8.py   # 縮約の pre が読む prev を差し替える rows3j.py（HX）

H5 の結論: **縮約は触らない**。全射の外れ 82 個のうち `(conv3 A)<m>` に現れるのは
1 個だけで、縮約の入口を広げても全射は直らずシートが 38 行落ちる。
`st['prev']` の読みだけは不要と分かったので rows3.py で定数にした。
