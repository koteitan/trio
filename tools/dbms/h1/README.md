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

# 課題 H6 の道具（2 択の十分性 / 素性の機械生成）

    python3 /tmp/h1work/h6coll.py 7 4        # 目標が base_s/deep/どれでもない のどれか
    python3 /tmp/h1work/h6feat.py            # 素性の機械生成（249 個、行 0/1/2 の祖先の鎖など）
    TGT=deep python3 /tmp/h1work/h6ct.py aw  # 教師データ（ct=closes_top / aw=after_w / p0=prev0）
    python3 /tmp/h1work/h6cov.py <pkl> 3     # 定数・重複を落として fp=0 の連言で被覆
    python3 /tmp/h1work/h6res.py <pkl> 5     # 残った正例だけを狙って深い連言を探す
    python3 /tmp/h1work/h6ho.py  <pkl> 3     # **ホールドアウト検定**（過学習の確認）
    python3 /tmp/h1work/mkveto.py            # closes_top の拒否権を旗で入れる rows3k.py

**教訓**: 「局所では分けられない」と思ったら**素性を疑う**。手で 66 個並べて
24/36 だったものが、祖先の鎖を機械生成したら 36/36 になった。
そして必ず `h6ho.py` でホールドアウトを取ること。

# 課題 H7 の道具（足切りの修正）

    python3 -c "import sys; sys.path.insert(0,'/tmp/h1work'); \
      from h7agree import agree; import rows3; print(len(agree(rows3.b2d3,6,4,6)))"
      -> lim=6, n<=4, m<=6 で **50762 組**、4 秒

**足切りはこれを使う**（旧: ずれ -1 だけ見る h1eqv は不十分）:

    agree(f) = { (A, n, m) : conv3(A<n>) == (conv3 A)<m> }
    1 組でも壊す条項は落とす -> lim=6 の 7 土俵と完全に一致した（veto 0 / aw5 3 / tt 9）

`h7teach.py` は「長さで対応づけて教師データを広げる」試み。**偽ラベルを作るので
使ってはいけない**（H1-NOTES §44。シート行 338 が目標を否定した）。

# 課題 H8 の道具（負例を一致から集める）

    python3 /tmp/h1work/h8big.py aw 7 3   # lim=7 の「一致する対」から負例を 591 本
    python3 /tmp/h1work/h8feat.py aw      # 素性表
    python3 /tmp/h1work/h6cov.py /tmp/h1work/h8f_aw.pkl 3

**足切りは lim=7 で回すこと**（lim=6 の一致 50762 組では `aw3` を通してしまう。
lim=7 の 305087 組なら 331 組の破れが見える）。約 140 秒。

# 課題 H9 の道具（prev を行列から導く）

    python3 /tmp/h1work/h9cmp.py  6 3        # spell と conv3 の prev を比べる（食い違い 170）
    python3 /tmp/h1work/h9cmp2.py 6 3        # conv3 の nxt を渡した版（食い違い 10）
    python3 /tmp/h1work/h9cmp3.py 6 3 root   # 切り方を「行 0 = 0」に（食い違い 1）
    python3 /tmp/h1work/mkprevmat2.py        # prev を行列から導く rows3t2.py（PM['prevmat']）

**結論**: `prev` は 99.994% 行列から決まる。残る非同変な読みは
(1) 縮約が注入する `nxt` の番兵 `NOTLAST`、(2) 行 1 の梯子 `L` から出る `tie`。

# 課題 H11 の道具（`first` / `ps` / `split0` の同変性 と 条項 `sibnb`）

    mkdir -p /tmp/h1work && cp *.py /tmp/h1work/
    python3 /tmp/h1work/mkLrec2.py             # 記録つきの写し rows3F.py
                                               #   (off, first, force, ps, pw, d, L, F, nA, ctx)
    python3 /tmp/h1work/h11m.py 6 3            # first/ps/nA を行列読みと突き合わせる
    python3 /tmp/h1work/h10img.py              # ImgClosedT の破れを img54p.pkl に（65s）
    python3 /tmp/h1work/h11x.py                # 破れの現場（**長さが揃う n を選ぶ**）
    python3 /tmp/h1work/h11d.py 5              # 1 件ずつ詳しく
    python3 /tmp/h1work/h11e.py                # 濃縮率（対照 = lim=6 の全柱）

条項 `sibnb`（旗つきの写し）と足切り:

    python3 /tmp/h1work/mksibnb.py             # rows3s.py（SBFLAGS=... で旗を立てる）
                                               #   sibnb / sibnb_cov / sibnb_cov2 / sibnb_desc
                                               #   b2d3f(M, sites=...) で発火場所を選べる
    SBFLAGS=... python3 /tmp/h1work/h11cut.py  <tag> 7 rows3s        # lim=7 の一致
    python3 /tmp/h1work/h11cut2.py <tag> 7 rows3s 5 8                # 強い版 n<=5 m<=8
    SBFLAGS=... python3 /tmp/h1work/h11all.py rows3s dohyo 6         # 7 土俵
    SBFLAGS=... python3 /tmp/h1work/h11all.py rows3s onto 7          # 全射
    SBFLAGS=... python3 /tmp/h1work/h11fix.py rows3s                 # 破れ 105 対の当たり

教師データ（正例/負例の場所）:

    python3 /tmp/h1work/h11sit.py              # シート＋ImgClosedT からラベル
    FL=... TAG=... python3 /tmp/h1work/h11neg.py   # lim=7 の一致の増減から場所を集める
    H11ALL=cov,cov2 python3 /tmp/h1work/h11feat.py # 素性表（h6feat 275 ＋ 追加 30）
    python3 /tmp/h1work/h6cov.py /tmp/h1work/h11fcov_cov2.pkl 3

**教訓**: 破れの現場を見るときは `n` を「像の長さが目標と揃うもの」で選ぶ。
最長一致で選ぶと 105 対のうち 70 対が「像が短い」に落ちて柱まで届かない。
