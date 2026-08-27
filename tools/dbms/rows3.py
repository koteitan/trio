"""3 行 z<2 の BMS -> DBMS 変換を、設計 -> 検査のループで詰めるための道具。

BMS 3 行の列は (x,y,z) で z<=y<=x、いまは z<2 に制限する。
DBMS 3 行の列は z<y<x（0 は例外）。「弱い降下」を「強い降下」にするのが変換。

**土台になる観測（2026-08-26）**

    BMS でも DBMS でも、標準形の第 y 行の値は**その行の入れ子の深さ**に等しい。
    3 行 <=6 列で BMS 8387 個・DBMS 555 個、違反 0。

だから行 1 の値は保存されるものではなく、行 1 の木に影を挟めばその分ずれる。
2 行の変換を「行 (0,1)」と「行 (1,2)」の**二重**に効かせるのが設計 v6 以降。

**検査**（`main` が回す = `check`）

  (1) 像が DBMS 標準形
  (2) 単射・順序保存。**単射はこの集合の中でしか見ていない**（`gen3(lim)` なので
      lim 列を超える相手との衝突は見えない）。それは (2b) と (5) が拾う。
  (2b) **列数をまたいだ単射**（`inj_cross`）。長い相手（双子 `twin`・展開・
      (5) が返した B）を自分で作ってから、像を辞書に貯めて衝突を数える。
      判定は `f` だけを見るので逆写像 `inv3` の正しさに依存しない。
  (3) 性質 R: 任意の n に対し、ある m と n'>=n で 像<m> = 像(M<n'>)
      **3 行では偽と確定している**（NOTES §性質 R）。目標にしてはいけないので
      **既定では回さない**（`check(..., rprop=True)` で回る）。
  (4) z=0 の断片で 2 行版 `rows2.convC` と完全一致
  (5) 逆写像 `inv3.d2b3` で戻る。落ちた分は 3 つに分ける:
      **単射性の破れ**（戻り B が BMS 標準形で f(B) が同じ像 = 列数をまたぐ衝突）、
      **逆写像が古い**（B は BMS 標準形だが f(B) は別の像 = `inv3` が
      いまの `conv3` に追いついていない）、**本当の失敗**（B が標準形ですらない）。
  (6) 共終性 C1/C2

        C1: 任意の m<=mm に ある n<=nn で  f(M)<m> <= f(M<n>)
        C2: 任意の n<=nn に ある m<=mc で  f(M<n>) <= f(M)<m>

      **証明済みの 2 行版でちょうど 0 になる**（z=0 の 3 行標準形 <=6 列
      1285 個で C1 破れ 0・C2 破れ 0）。だから C1/C2 の違反は本物の欠陥。
  (7) ImgClosedT: 任意の m>=1 に ある BMS 標準形 B で (f M)<m> = f B
      **これが RD1（3 行版 ReindexD）の要**（NOTES §3 行の証明の骨組み）。
      z=0 では破れ 0（3852 対）。既定は `imgfast.imgclosed_fast`（段 1 = 逆写像を
      1 発当てる、段 2 = 誘導つき DFS、fork 並列）。当たれば逆像の**構成的な
      証明**、外れは破れの**上界**。`fast=False` でこのファイルの逐次版に落ち、
      `imgfull=True` で `m_imgclosed` の梯子つき探索まで降りる（重い）。
      ImgClosedT は C1 より細かい: <=5 列で C1 の破れ 7 個は ImgClosedT の
      破れ 28 個に**含まれる**。

**到達点（2026-08-27, conv3 v13 = v12 ＋ wchain ＋ sibL）**

v13 で足した条項は 2 つ。旗 `V13` で 1 つずつ入れ切りでき、**全部 False に
すると v12 に戻る**（生成 <=7 列 77282 個で像の差 0 を確認した）。どちらも
「行 1 の入れ子を 1 段深く綴る」ための条項で、狙いは ImgClosedT ただ 1 つ。

  `wchain` （課題 F2, `w2.py`）`after_w` の窓は**直前 1 本**しか見ていなかった。
            「x w」の柱 (k,0,0) がもっと後ろにあって、そこから今の柱まで
            **ぜんぶその子孫**（行 0 > k）なら、直前が「x w」だったのと同じに
            扱う（`wchain_head`）。判定式は `after_w` と同じで、親を見る柱を
            (k,0,0) 本人にするだけ。距離の上限は要らない。
            逆算（`w2.step1..step5`）で「深く綴るべき 44 対」と「シートが
            浅いと言う 137 対」を完全に分ける条件がこれだった。
  `sibL`   （課題 F1, `w1.py`）行 1 の影を立てた柱の「深い側」を、子だけでなく
            **兄弟**にも渡す（段の表 `L` の第 5/6 要素）。争点 P6
            (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1) が `rule.convert` と
            同じ ...(6,2,1)(6,2,0)(7,3,1) に綴られる。素のままだと深い綴りが
            1 列短い接頭辞へ**伝染**して ImgClosedT を大きく壊すので、
            伝染止め `sib_anchbefore` が要る:

              兄弟から渡ってきた深い側は、**その柱より前にアンカー (1,1,0) が
              1 本も無いとき**にしか使えない。

            アンカーは行 1 の新しい加算ユニットの頭なので、「行 1 の最初の
            ユニットの中でだけ、影の深さは兄弟に効く」と読める。同じ点数に
            なる書き方が 3 つある（`w1.py` の `sib_anchsrc` / `sib_anchnone`）。
            `sib_anchbefore` を切ると ImgClosedT は <=6 列 88 -> 275 に**悪化**
            するので、この条項は `sibL` と一体である。

**2 つは足し合わせが効く**（ImgClosedT <=6 列 294 -> `wchain` 95 / `sibL` 285 /
両方 **88**）。像が変わるのは生成 <=7 列 77282 個のうち 302 個
（`wchain` 48 ＋ `sibL` 209、重なりぶんは打ち消し）。

| 検査 | v12 | v13（いま） |
|---|---|---|
| シート 3 行 z<=1 (1358 対) | 1354 | **1354**（不一致 4 はシート側の誤り） |
| z=0 <=9 列 295014 個: `rows2.convC` と食い違い | 0 | **0** |
| z=0 の ImgClosedT 対照（<=6 列） | 0 | **0** |
| 生成 <=7 列 77282 個: 非標準 / 順序 / 像の衝突 | 3 / 0 / 0 | **0 / 0 / 0** |
| 生成 <=8 列 781605 個: 非標準 / 像の衝突 | 84 / 0 | **3 / 0** |
| 単射（列数をまたいで, 閉包 15611 / 127182 個） | 0 / 0 組 | **0 / 0 組** |
| `d2b3` 往復（<=6 / <=7 列） | 8387/8387 / 77280/77282 | **同じ**（単射の破れ 2 / 逆写像が古い 0） |
| **ImgClosedT 破れ A**（<=5 / <=6 / <=7 列） | 26 / 294 / 3374 | **4 / 88 / 1468** |
| ImgClosedT 破れ 対（同上） | 51 / 587 / 6855 | **7 / 173 / 2876** |
| ImgClosedT 辞書引き（127182 個, `inv3` 非依存, <=6 列） | 584 | **378** |
| 共終性 C1 の破れ（<=5 / <=6 列） | 5 / 88 | **4 / 78** |
| 共終性 C2 の破れ（<=6 列） | 0 | **0** |
| sandwich の下限 f(M)<n-1> <= f(M<n>)（<=6 列 33544 対） | 264 | **235** |
| 展開閉包 22805 個: 非標準 / 潰れ / 順序違反 | 104 / 0 / 3 | **72 / 0 / 3** |

**v13 の破れ集合は真部分集合ではない**（v12 までの条項と違って両側に動く）。
内訳: ImgClosedT <=6 列は直る 217 / 新しく壊れる 11、<=7 列は直る 2085 /
新しく壊れる 179、共終性 C1 <=6 列は直る 16 / 新しく壊れる 6。
新しく壊れた 6 個の C1 はぜんぶ新しく壊れた 11 個の ImgClosedT の中にある
（C1 の破れ 78 個は 78 個とも ImgClosedT の破れ 88 個に含まれる）。
どの土俵も**数では悪化していない**ので採った。主指標は ImgClosedT である。

**その前の段（2026-08-27, conv3 v12 = v11 ＋ mark ＋ newterm）**

v12 で足した条項は 2 つ。旗 `V12` で 1 つずつ入れ切りでき、**両方 False にすると
v11 に戻る**（生成 <=8 列 781605 個で像の差 0 を確認した）。

  `mark`    （課題 E1, `z1.py`）残余なしの縮約は「写しを飲んだ印が像に残る」
            ときだけ許す。印が残らないと `M` と `M ++ (1,1,0) ++ 写し` が
            同じ像に潰れる（＝単射性の破れ）。既定は局所版
            `leaves_mark_local`（Lean に載る形）で、大域版 `leaves_mark`
            （2 通り走らせて像を比べる）と双子 3609 個・生成 <=7 列で差 0。
  `newterm` （課題 E2, `z2.py`）行 0 が 0 の柱 (0,*,*) は**新しい加算項**の
            頭なので、段の状態 `st['prev']` を持ち越さない。持ち越すと
            A ++ A の 2 つ目の写しが浅く綴られ、f が和について加法的でなくなる。

**どちらも片側にしか動かない。** 生成 <=7 列 77282 個では v11 と像が 1 ビットも
変わらない（<=8 列で変わるのは 50 個、どれも `newterm` の側）。像が変わるのは
双子（`mark`。3609 個中 24 個、全部「潰れていたものが分離した」側）と
8 列以上（`newterm`）だけである。

| 検査 | v11 | v12（いま） |
|---|---|---|
| シート 3 行 z<=1 (1358 対) | 1354 | **1354**（不一致 4 はシート側の誤り） |
| シートの `d2b3` 往復（1358 対） | 1356 / 単射の破れ 2 | 1356 / **単射の破れ 1** |
| z=0 <=9 列 295014 個: `rows2.convC` と食い違い | 0 | **0** |
| 生成 <=7 列 77282 個: 非標準 / 順序 / 像の衝突 | 3 / 0 / 0 | **3 / 0 / 0** |
| 生成 <=8 列 781605 個: 非標準 / 像の衝突 | 84 / 0 | **84 / 0** |
| 単射（列数をまたいで, 閉包 15611 / 127182 個） | 24 / 24 組 | **0 / 0 組** |
| 単射（`d2b3` 往復 <=6 / <=7 列） | 7 / 166 組 | **0 / 2 組** |
| ImgClosedT 破れ A（<=5 / <=6 / <=7 列） | 28 / 327 / 3779 | **26 / 294 / 3374** |
| 共終性 C1 の破れ（<=5 / <=6 / <=7 列） | 7 / 121 / 1572 | **5 / 88 / 1167** |
| 共終性 C2 の破れ（<=5 / <=6 / <=7 列） | 0 / 0 / 2 | **0 / 0 / 2** |
| sandwich の下限 f(M)<n-1> <= f(M<n>)（<=6 列 41930 対） | 363 | **264** |
| 展開閉包 22806 個: 非標準 / 潰れ / 順序違反 | 103 / 1 / 4 | **104 / 0 / 3** |
| `ConvDiagT3`（対角の像 v=0..20） | 一致 | **一致** |

破れの集合はどの欄も**真部分集合**（ImgClosedT・共終性 C1・sandwich の下限・
単射は「直った」だけで「新しく壊れた」は 0）。ただし 1 つだけ両側に動く欄がある:
**展開閉包の非標準が 103 -> 104**（`mark` のせい。`newterm` は 0）。増えた 1 件は

    (0,0,0)(1,1,1)(2,1,0)(3,0,0)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(4,0,0)(3,2,0)

でちょうど双子である。v11 ではこれがもとの 5 列と同じ像に**潰れて**いた
（＝単射性の破れ）。v12 は写しを綴り出して分離するが、その長い像が DBMS 非標準に
なる。潰れ 1 と順序違反 1 を減らして非標準 1 を増やす取引で、**生成の非標準
（<=7 列 3 / <=8 列 84）は 1 件も動かない**。

**ImgClosedT の採点は逆写像 `inv3.d2b3` に足を引っ張られる。** `d2b3` は v11 に
合わせて作ってあるので、`mark` を入れると目標 T に対して「双子」`W ++ (1,1,0) ++
写し` を返す。いまの `conv3` ではその像はもう T ではないので、素の速い道だと
それが破れに見える（<=6 列で 327 -> 328、<=7 列で 3374 -> 3381 に**増える**）。
`preimage_try` は外れたときに `untwin`（加算項ごとに双子を `W` に戻す）と
`B[:k]`（接頭辞）を当て直す。**当たりは f(B')==T を確かめてから返す**ので健全。
それで測ると

  ImgClosedT の破れ A（m<=3）  <=5 列  <=6 列  <=7 列
    v11                          28     327    3779
    `mark` だけ                  28     327    3779   （集合も v11 と同一）
    `newterm` だけ               26     294    3374
    v12                          26     294    3374   （v11 の真部分集合。
                                                       直った 2 / 33 / 405、
                                                       新しく壊れた 0 / 0 / 0）
  v12 の破れの列数別: 4 列 2 / 5 列 24 / 6 列 268 / 7 列 3080

`inv3` をまったく使わない辞書引き（像 -> BMS 標準形 の辞書 127182 個、`z1.py` の
`imgclosed_dict` と同じ道）でも同じ結論になる: <=6 列で v11 617 / `mark` **617**
（集合同一）/ `newterm` 584 / v12 **584**。
つまり **`mark` は ImgClosedT を 1 ビットも動かさない**。

v9 -> v10 の 4 条項（resid / L / after_w / closes_hi_unit）を 1 つずつ足した
ときのシート成績は `python3 m_residue.py fix` で再現できる:
v9 1338 / +resid 1350 / +L 1340 / resid+L 1352 / +after_w 1353 /
+closes_hi_unit 1353 / 4 つ全部（v10）1354。
v10 -> v11 は 1 行（`p == ANCHOR` での `st['prev'] = 0` を消しただけ）で、
生成 <=7 列で像は不変・共終性 C1 は <=6 列 136 -> 121・ImgClosedT は 342 -> 327
（どちらも真部分集合）だった（課題 D5, `y_fix.py`）。

z=0 の断片は **<=9 列 295014 個で 2 行版 `rows2.convC` と食い違い 0**。
z=0 は Lean で答えが確定している断片なので、ここが 0 であることが
変換器の一番強い足場である。

**残る欠陥（2026-08-27, v13 で残っている全部）**

  (a) ImgClosedT の破れ（<=5 列 4 / <=6 列 88 / <=7 列 1468。v12 は 26/294/3374）。
      v12 では破れ方が 1 種類（末尾 1 列の行 1 が 1 足りない）だったが、
      `wchain` がそれを直したので**残りは何種類かに散っている**。
      `inv3.d2b3` が返す D = d2b3(T) と目標 T の差分で数えた <=6 列 173 対:

        行 1 が 1 足りない（差分が (0,1,0) だけ）                   80 対
          うち 1 箇所だけ 36 対（末尾から 2 本目 17 / 末尾 11 / 3 本目 6 / ほか 2）
          残り 44 対は同じ形が写しごとに繰り返す（例 (-8) と (-2) の 2 箇所）
        写しの位置ごとずれる（(1,1,0) / (1,0,0) が並ぶ）            56 対
        像のほうが**深すぎる**（差分が (0,-1,0)）                   18 対
        長さが違う (+5) / D が BMS 非標準                           19 対

      足りないもの: 「写しの中の**最後でない**分岐列も深く綴る」条件
      （残る最大の族。例 A=(0,0,0)(1,1,1)(2,1,0)(2,1,0)(1,1,0) の m=2 では
      D=...(2,0,0)(3,1,1)(4,1,0)(4,1,0) の**前**の (4,1,0) だけ深くしたい）と、
      逆向きに**深くしすぎ**を止める条件（`wchain` / `sibL` が深くした当人の
      展開がこんどは 1 段足りなくなる。新しく壊れた 179 個がこれ）。
  (b) 共終性 C1 の破れ（<=5 列 4 / <=6 列 78）。C2 は 0 / 0。
      C1 の破れは 78 個とも ImgClosedT の破れ 88 個に含まれる。
      足りないものは (a) と同じ。
  (c) 単射性の破れが 2 組（<=7 列。v13 でも同じ 2 組で、v12 から動かない）。

        (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,2,0)(3,1,0)(1,1,1)                 7 列
        相手 ...(3,1,0)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(4,3,0)(4,1,0)(2,2,1) 13 列
        (0,0,0)(1,1,1)(2,2,1)(3,2,1)(3,2,0)(3,1,0)(1,1,1)                 7 列
        相手 ...(3,1,0)(1,1,0)(2,2,1)(3,3,1)(4,3,1)(4,3,0)(4,1,0)(2,2,1) 13 列

      こちらは**残余ありの縮約**（`rest2` が空でない・`deep_end` が偽）で、
      残余 (2,2,1) の像がもとの末尾 (1,1,1) の像 (3,2,1) と同じになって潰れる。
      足りないもの: 残余ありの縮約にも `mark` と同じ「印」のガード。
  (d) 像が DBMS 非標準（生成 <=7 列 **0** 件・<=8 列 **3** 件、展開閉包 22805 個
      で 72 件。v12 は 3 / 84 / 104）。`sibL` が狙いどおりここを直した
      （NOTES §課題 F3「像が DBMS 非標準になる 84 件の正しい像」で `rule.R23`
      が指していた綴りに寄った）。残る 3 件は <=8 列でしか出ず、1 族しかない:

        (0,0,0)(1,1,1)(2,1,0)(1,0,0)(2,1,1)(2,1,0)(3,2,1)X   X = (3,0,0)/(3,1,0)/(3,2,0)
          -> ...(3,2,1)(4,1,0)(1,0,0)(2,1,0)(3,2,1)(2,1,0)(3,2,1)X
             （(2,1,0)(3,2,1) を 2 度書くので非標準）

      足りないもの: **2 つ目の加算項の中**でも分岐列を「本体の横」に置く規則。
      `sibL` は行 1 の影の深い側を兄弟に渡すが、この族では影を立てた柱と
      分岐列が同じ写しの中にあるので渡らない。
  (e) 全射の穴: (0,0,0)(1,0,0)(2,1,0)(3,2,1)(3,y,0)(2,0,0) (y=0,1,2) は
      BMS <=8 列 781605 個を全数当たっても逆像が無い（NOTES §逆写像）。
  (f) 逆写像 `inv3.d2b3` は課題 F3 で v12 に追いつかせてある。v13 の 2 条項を
      入れても往復は落ちない（<=6 列 8387/8387、<=7 列 77280/77282、
      落ちる 2 件は (c) の単射性の破れだけで「逆写像が古い」は 0）。
      単射が実際に直っていることは (2b)（`inj_cross`。像を辞書に貯めて
      衝突を数えるので `d2b3` に依存しない）が閉包 15611 個・衝突 0、
      さらに `z1.build_dict` と同じ閉包 127182 個でも衝突 0 で示す。
      ImgClosedT を `inv3` に頼らず辞書 127182 個で測ると <=6 列で 378 個
      （v12 は 584 個）。速い道の 88 個より多いのは辞書が証人を持っていない
      ぶんで、どちらも**上界**である。
  (g) sandwich の下限 f(M)<n-1> <= f(M<n>) が <=6 列 33544 対で 235 件破れる
      （v12 は 264 件）。これは Lean の `SandwichL`（相手が ImgClosedT の
      出す B）とは別の、添字をそろえた自己整合の検査である。

  シート 4 件（592, 891, 897, 898）はシート側の誤りなので欠陥ではない
  （NOTES §シート行 891/897/898）。

**採らなかった規則: sibbody2 / sibbody3（x_spell.py, 2026-08-27）**

「行 1 の影を立てた柱の兄弟を、影の横（深さ d）ではなく本体の横（深さ dd）に
付ける」規則。上の系列を狙い撃ちにするので生成の非標準は減るが、**共終性を
新しく壊す**ので入れなかった。同じ土俵で測った表:

| 検査 | v10（当時の採用版） | +sibbody2 |
|---|---|---|
| シート | 1354/1358 | 1354/1358 |
| 生成 <=6 列 非標準 / 単射 / 順序 | 0 / ok / 0 | 0 / ok / 0 |
| 生成 <=7 列 非標準 | 3 | **1** |
| 生成 <=8 列 非標準 | 84 | **42** |
| 展開閉包 {M<n>: M in gen<=6, n<=4} 22805 個の非標準 | 103 | **115**（+12） |
| 共終性 C1 の破れ（<=5 / <=6 列） | 7 / 136 | **8 / 149** |
| 共終性 C2 の破れ（<=5 / <=6 列） | 0 / 0 | 0 / **4** |
| 性質 R の破れ（<=5 / <=6 列） | 58 / 646 | **59 / 663** |

破れはどれも**片側**（sibbody2 だけが壊し、直すものは 0）。
再現: `python3 x_spell.py cof 6`。
`not A`（子を持たない柱に限る）と `B[0][1] >= 1`（兄弟が行 1 を使う）を
足すと展開閉包の +12 と C2 の +4 は消える（103 / 0）が、共終性 C1 は
8 / 147 のままで +1 / +11 が残る。
壊れる代表例:

    M = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)
    v10       ...(6,2,1)(5,1,0)     C1 成立
    sibbody2  ...(6,2,1)(6,1,0)     像<2> が f(M<n>) をどの n でも追い越す

`rule.convert` はこの系列に第 3 の像 ...(6,2,1)(6,2,0)(7,3,1) を出す。
**この綴りが P6 の正解であることは決着した**（課題 D2）: M<2> = P6 のとき
DBMS 側の基本列 f(M)<2> がちょうどこの綴りになる。しかし `rule.convert`
そのものは変換器としては採れない —— 展開閉包の z=0 の部分 3961 個で
**証明済みの 2 行版 `rows2.convC` と 35 件食い違う**（直和が 1 個ぶんに潰れる）。
だから足すべきは「行 1 の入れ子を 1 段深く綴る」規則だけで、`rule.depths` の
機構ごと持ってくることではない。**v13 の `sibL` ＋ `sib_anchbefore` がそれ**:

    P6 = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)
       -> (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,2,0)(7,3,1)
          （`rule.convert` と一致）
    1 列短い M = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)
       -> ...(6,2,1)(5,1,0)   （**浅いまま**。深くすると C1 が壊れる系列）

`sibbody2` は両方を深くしてしまうので共終性を壊した。`sibL` は「兄弟に
渡った深い側」を使うので、末尾（`closes_unit` が発火する側）では浅いままに
なり、境目がちょうど合う。結果、共終性を壊さずに生成 <=8 列の非標準を
84 -> 3 に落とした（`sibbody2` の狙いも同時に達している）。

使い方:
    python3 rows3.py [列数上限] [ImgClosedT の m の上限] [full]

      python3 rows3.py 5          <=5 列（15 秒）
      python3 rows3.py 6          <=6 列（4 分）
      python3 rows3.py 6 0        ImgClosedT を回さない（速い）
      python3 rows3.py 5 3 full   ImgClosedT を梯子つき探索まで降ろす（重い）
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, expand, isstd, cmpmat
from rows2 import convC as convC2


# ---------------------------------------------------------------- 生成
def gen3(ver, lim, zcap=None):
    """`lim` 列以下の標準形を全部。接頭辞が標準形であることを使う。"""
    cur = [()]
    out = []
    for _ in range(lim):
        nxt = []
        for S in cur:
            amax = (S[-1][0] + 1) if S else 0
            for a in range(amax + 1):
                bmax = a if ver == 'BMS' else max(a - 1, 0)
                for b in range(bmax + 1):
                    cmax = b if ver == 'BMS' else max(b - 1, 0)
                    if zcap is not None:
                        cmax = min(cmax, zcap)
                    for c in range(cmax + 1):
                        T = S + ((a, b, c),)
                        if isstd(T, ver):
                            nxt.append(T)
        cur = nxt
        out.extend(nxt)
    return out


def key(m):
    return ([v for c in m for v in c], len(m))


# ---------------------------------------------------------------- 木
def split0(p, r):
    """行 0 の引数ブロックと兄弟に割る。"""
    i = 0
    while i < len(r) and p[0] < r[i][0]:
        i += 1
    return r[:i], r[i:]


def translate3(cols):
    """BMS の読み（lean/Term.lean の translate）。段は対 (行1, 行2)。"""
    if not cols:
        return ('Z',)
    p, r = cols[0], cols[1:]
    A, B = split0(p, r)
    return ('P', (p[1], p[2]), translate3(A), translate3(B))


def olt3(a, b):
    """Three の順序（添字対 -> 引数 -> 後続）。"""
    if a[0] == 'Z':
        return b[0] != 'Z'
    if b[0] == 'Z':
        return False
    if a[1] != b[1]:
        return a[1] < b[1]
    if a[2] != b[2]:
        return olt3(a[2], b[2])
    return olt3(a[3], b[3])


# ---------------------------------------------------------------- 変換 v1
def shift1(B):
    return [(a + 1, b, c) for a, b, c in B]


def units_split(p, B, qlab):
    """`B` の先頭から「深さ `p[0]` の柱＋その引数ブロック」を、
    段の対が `qlab`（＝写しの先頭が持つ段の対）に等しい柱に出会うまで取る。

    2 行版は `p` そのものの並びしか数えなかった。深さ 1 では段が 0 か 1 しか
    ないので両者は一致するが、3 行では段の対が (1,0) のような中間の兄弟が
    入りうるので、そこで切れてしまうと縮約が発火しない。
    """
    k = 0
    while k < len(B):
        if B[k][0] != p[0]:
            break
        if (B[k][1], B[k][2]) == qlab:
            break
        t = k + 1
        while t < len(B) and p[0] < B[t][0]:
            t += 1
        k = t
    return B[:k], B[k:]


def predlab(y, z):
    """段の対の順序 (0,0)<(1,0)<(1,1)<(2,0)<(2,1)<... での 1 つ前。z<2 用。"""
    if z > 0:
        return (y, z - 1)
    if y >= 2:
        return (y - 1, 1)
    return (0, 0)


def ok_place(ST, x, w):
    """深さ `x` に行 1 が `w` の柱を置けるか（行 1 の値 = 行 1 の入れ子の深さ）。"""
    if w == 0:
        return True
    if x <= w:
        return False                      # DBMS は 行1 < 行0
    for y in range(min(x, len(ST)) - 1, -1, -1):
        if ST[y][0] < w:
            return ST[y][0] == w - 1
    return False


def fit(ST, d, w):
    """深さ `d` 以上で行 1 が `w` になれる最小の深さ。無ければ None。"""
    for x in range(d, len(ST) + 1):
        if ok_place(ST, x, w):
            return x
    return None


NOTLAST = (2, 2, 0)     # 「後ろにユニットを閉じない列がある」を表す番兵
ANCHOR = (1, 1, 0)      # アンカー（新しい加算ユニットの頭）


def closes_unit(nxt):
    """次の列がこの加算ユニットを閉じるか（rule.py の closes_unit と同じ）。

    閉じるのは (a) 次が無い (b) 次が根元に戻る（行 0 <= 1 かつ 行 2 = 0）。
    アンカー (1,1,0) は (b) に含まれる。閉じるなら分岐列は浅い。
    """
    return nxt is None or (nxt[0] <= 1 and nxt[2] == 0)


def par0(m, x):
    """柱 `x` の行 0 の親（左にある、行 0 の値がより小さい直近の柱）の添字。
    無ければ -1。core.pim の第 0 列と同じものを 1 箇所ぶんだけ持つ。"""
    for q in range(x - 1, -1, -1):
        if m[q][0] < m[x][0]:
            return q
    return -1


def par0_w(m, x):
    """行 0 の親をたどるが、途中の「x w」柱 (k,0,0) は素通りする（課題 P2）。

    展開すると、加算ユニットの頭であるアンカー (1,1,0) は写しの中で (k,0,0) に
    化ける。だから写しが 1 枚増えるたびに親の鎖に「x w」柱が 1 本ずつ挟まり、
    `par0(m, x) == 0`（＝根に直付け）が写しの中で偽になる。「x w」柱を素通り
    して根に着くかを見れば、この量は写しに同変になる。
    """
    q = par0(m, x)
    while q > 0 and is_w_col(m[q]):
        q = par0(m, q)
    return q


def wdepth(m, x):
    """柱 `x` の行 0 の祖先の鎖にある「x w」柱 (k,0,0) の本数（課題 P2）。"""
    n, q = 0, par0(m, x)
    while q >= 0:
        if is_w_col(m[q]):
            n += 1
        q = par0(m, q)
    return n


def is_diag(m, x):
    """**写しに同変な**「対角柱」（課題 P2 の `hiblk`）。

    もとの `hi_block` はブロックの頭を対角柱 (a,a,z) (a>=1) で拾うが、展開すると
    行 0 だけが上がるので (1,1,1) が写しの中で (2,1,1) に化けて外れる。上がる
    ぶんはちょうど「祖先の鎖に挟まった「x w」柱の本数」なので、引いてから
    比べれば写しに同変になる。写しの中でない行列では (a,a,z) と完全に一致する。
    """
    return m[x][1] >= 1 and m[x][0] - wdepth(m, x) == m[x][1]


def closes_w(m, x, nxt):
    """次の柱が**化けたアンカー** (k,0,0) なら加算ユニットは閉じる（課題 P2）。"""
    if nxt is None or not is_w_col(nxt):
        return False
    j = x + 1
    if j >= len(m) or tuple(m[j]) != tuple(nxt):
        return False        # 番兵 NOTLAST や飛んだ先は見ない
    return par0_w(m, j) == 0


def copy_src(Mo, off):
    """`off` の柱が「直前の写しの同じ位置」に当たるなら、その添字（課題 P3）。

    写しの周期 `L` と行 0 のずらし `d0 > 0` を**接頭辞だけから**読む。
    「Mo[off-i] が Mo[off-L-i] を d0 だけ持ち上げたもの・行 2 が等しい
    （＋ `cpyd1` なら行 1 のずらしも一定）」が左端に当たるまで続けば `off-L`。
    """
    for L in range(max(1, V15['cpylmin']), off + 1):
        j = off - L
        d0 = Mo[off][0] - Mo[j][0]
        d1 = Mo[off][1] - Mo[j][1]
        if Mo[off][2] != Mo[j][2]:
            continue
        if d0 < 0 or (d0 == 0 and not (V15['cpy_d0zero'] and d1 == 0)):
            continue
        ok = True
        for i in range(1, L + 1):
            a, b = off - i, j - i
            if b < 0:
                break
            if V15['cpy_stop0'] and Mo[b][0] == 0 and Mo[a][0] != 0:
                break
            if Mo[a][0] - Mo[b][0] != d0 or Mo[a][2] != Mo[b][2]:
                ok = False
                break
            if V15['cpyd1'] and Mo[a][1] - Mo[b][1] != d1:
                ok = False
                break
        if ok:
            return j
    return None


def hi_block(m, x):
    """`x` の属するブロック（直前のアンカーより後ろ）に行 2 を使う柱があるか。

    W_(w^2) 系の regime にいるかどうかの目印（`rule.py` の hi_block と同じ）。
    段の上げ下げの規則はこの regime の内と外で違うので、分岐列の浅い／深いを
    決めるときにこれを見る。
    """
    b = max([q for q in range(x) if m[q][0] == m[q][1] and m[q][0] >= 1],
            default=0)
    return any(m[z][2] > 0 for z in range(b + 1, x))


def is_repeat(m, x):
    """m[..x] の末尾が、その直前の同じ長さの区間の逐語コピーか。

    コピーされた区間はもとの区間と同じ深さで書かれるので、段を上げ直さない。
    """
    for L in range(1, (x + 1) // 2 + 1):
        if m[x - 2 * L + 1:x - L + 1] == m[x - L + 1:x + 1]:
            return True
    return False


def is_w_col(c):
    """「x w」の柱 (k,0,0), k>=1。段を上げずに項を伸ばすだけの柱。"""
    return c is not None and c[1] == 0 and c[0] >= 1


def closes_hi_unit(c, nxt, pv, pv2, hi, rep):
    """W_(w^2) 系で (a,2,1)(a,2,0) と積んだ直後の (a,1,0) は、
    次がアンカー (1,1,1) なら段を上げずにユニットを閉じる（＝浅い）。

    ただしその区間が直前の逐語コピーなら、もとの深さを引き継ぐ（rep）。
    `rule.py` の closes_hi_unit と同じ。

    旗 `V14['chu']` で切れる（課題 G3 の測定用。既定は True = v13 のまま）。
    """
    if not V14['chu']:
        return False
    return (hi and not rep and nxt is not None and tuple(nxt) == (1, 1, 1)
            and pv is not None and tuple(pv) == (c[0], 2, 0)
            and pv2 is not None and tuple(pv2) == (c[0], 2, 1))


def Lat(L, k):
    """段の表 `L` の第 k 要素。表の外は 1 段ずつ伸ばして読む。"""
    if k < len(L):
        return L[k]
    if not L:
        return (0, 0, False, 0)
    a = L[-1]
    j = k - (len(L) - 1)
    return (a[0] + j, a[1], False, a[3] + j)


def padL(L, v):
    """段の表 `L` を長さ `v` まで `Lat` で埋めてから切る。

    もとは `L[:v]` だった。`len(L) < v` のときは黙って詰まってしまい、
    「第 v 段として継ぎ足したつもりのもの」が第 len(L) 段に化ける（表に穴があく）。
    表の外は 1 段ずつ伸ばして読む約束（`Lat`）なので、埋めてから継ぐのが正しい。
    """
    if len(L) < v:
        return tuple(Lat(L, k) for k in range(v))
    return L[:v]


def is_branch(c):
    """分岐列 (a,1,0) (a>=2)。浅い／深いを選ぶのはこの型だけ。"""
    return c[1] == 1 and c[2] == 0 and c[0] >= 2


def dmap_at(st, k):
    """もとの深さ `k` が像で何段目になるか。表の外は 1 段ずつ伸ばす。"""
    m = st['dmap']
    if not m:
        return k
    return m[k] if k < len(m) else m[-1] + (k - len(m) + 1)


def copy_shift(block, e, ps0, prev0, nxt_after):
    """`block` の写し（深さ +1、行 1 は +e）。

    行 1 が上がるのは「親の段 `ps0` より深い柱」だけ。ただし分岐列 (a,1,0) は
    浅い／深いを選べるので、状態機械を同じ順に回して 1 本ずつ決める。
    もとのブロックで浅く書かれた柱は、写しでも行 1 が上がらない。
    """
    out, prev = [], prev0
    for i, c in enumerate(block):
        nxt = block[i + 1] if i + 1 < len(block) else nxt_after
        if c == ANCHOR:
            prev = 0
        if is_branch(c):
            shallow = (prev == 0) or closes_unit(nxt)
            prev = 0 if shallow else 1
            dl = 0 if shallow else (e if c[1] > ps0 else 0)
        else:
            dl = e if c[1] > ps0 else 0
        out.append((c[0] + 1, c[1] + dl, c[2]))
    return out


def contrPre(p, U, A, e, ps0, prev0, nxt_after):
    return copy_shift([p] + list(A) + list(U), e, ps0, prev0, nxt_after)


# ---------------------------------------------------------------- v12 の 2 条項
# v11 -> v12 で足した条項。どちらも「7 つの土俵のどれも悪化させない」ことを
# 測ってから入れた（課題 E1 / E2、`z1.py` / `z2.py`）。旗を両方 False にすると
# v11 に戻る（gen<=8 の 781605 個で像の差 0 を確認済み）。
V12 = {
    'mark': True,       # 残余なしの縮約は「写しを飲んだ印が像に残る」ときだけ
    'newterm': True,    # (0,*,*) の柱は新しい加算項の頭。段の状態を持ち越さない
    'mark_global': False,   # `mark` の大域版（2 通り走らせて像を比べる。突き合わせ用）
}


# ---------------------------------------------------------------- v13 の 2 条項
# v12 -> v13 で足した条項。旗を両方 False にすると v12 に戻る
# （gen<=7 の 77282 個で像の差 0 を確認済み）。
#   `wchain`（課題 F2, `w2.py`）  `after_w` の窓を「この写しの頭まで」広げる
#   `sibL`  （課題 F1, `w1.py`）  行 1 の影を立てた柱の「深い側」を兄弟にも渡す
#     `sib_anchbefore` は `sibL` の伝染止め（`sibL` が on のときだけ効く）
V13 = {
    'wchain': True,
    'sibL': True,
    'sib_anchbefore': True,
}


# ---------------------------------------------------------------- v14 の旗
# `chu` = v10 の条項 `closes_hi_unit`。既定 True で v13 のまま。
# False にすると (a,2,1)(a,2,0)(a,1,0) の直後が (1,1,1) でも段が上がる。
# 課題 G3 の測定用（`RS_NOCHU=1` を環境変数に置くと False で起動する）。
V14 = {
    'chu': os.environ.get('RS_CHU', '') == '1',
    'wterm': os.environ.get('RS_NOWTERM', '') != '1',
    # wterm の伝染止め: 前にアンカー (1,1,0) が 1 本も無いときだけ効く
    # （`sib_anchbefore` と同じ読み）。切ると <=8 列の非標準が 2 件増える。
    'wterm_anchbefore': os.environ.get('RS_WTERM_ALL', '') != '1',
    # v14 h1（課題 H1）: 「写しの頭」`copy_head` を根と同じに読む 5 条項。
    #   `closes_top`   次の柱が写しの根の直下ならユニットを閉じる
    #   `copy_head`    親の鎖はアンカー (1,1,0) でも通る
    #   `hi_block2`    hi_block の起点を写しの頭の次まで進める
    #   `wchain_head`  鎖の頭が写しの頭なら根に当たったのと同じ（鎖が切れる）
    #   `p0deep_ok`    prev == 0 の枝を「行列から直に読む述語」で決め直す
    # `RS_NOH1=1` を環境変数に置くと v13 の綴りに戻る。
    'h1': os.environ.get('RS_NOH1', '') != '1',
}


# ---------------------------------------------------------------- v15 の候補条項
# 3 人の提案者（P1 / P2 / P3）が別々の worktree で書いた条項を、旗で 1 本ずつ
# 入れ切りできるようにしたもの。**既定は全部 off（＝ v14 と同じ像）**。
# 環境変数 `V15FLAGS=a,b,c` を置くと、その並びが旗の全指定になる。
V15 = {
    # ---- P3「像の側から決める」: 写しの中の分岐列は写しのもとの柱と同じに綴る
    'cpyspell': False,
    'cpylmin': 2,           # 写しの周期の下限（1 だと梯子を写しと読む）
    'cpyd1': True,          # 写しの見分けに「行 1 のずらしも一定」を足す
    'cpy_endshal': True,    # 行列の末尾では深くしない（浅くするのは許す）
    'cpy_d0zero': False,    # 逐語の繰り返しも写しと読む
    'cpy_stop0': False,     # 後ろ向き走査を行 0 = 0 で打ち切る
    'cpy_noanch': False,    # 間にアンカーがあったら渡さない
    'cpy_notlast': False,   # closes_unit(nxt) のときは渡さない
    'cpy_noend': False,     # 行列の末尾では何もしない
    # ---- P2「1 ビット状態機械の入力を写しに同変にする」
    'wterm_chain': False,   # wterm の par0(..)==0 を par0_w（「x w」素通し）に
    'wroot': False,         # after_w / wchain の par0(..)==0 も par0_w に
    'hiblk': False,         # hi_block の頭を写しに同変な対角柱 is_diag で拾う
    'closesw': False,       # 化けたアンカー (k,0,0) もユニットを閉じる
    # ---- P1「窓を広げる」
    'wide0_anch': False,    # p0deep_ok の第 2 項を `not is_w_col(nxt)` に広げる
    'wide0_noprev': False,  # 位置から読んで深くしたときは st['prev'] を上げない
}
if 'V15FLAGS' in os.environ:
    _on = set(x for x in os.environ['V15FLAGS'].split(',') if x)
    for _k in V15:
        if isinstance(V15[_k], bool):
            V15[_k] = _k in _on


def term_top(Mo, j, _d=0):
    """柱 `j` が「行 1 の加算項の頭」か。課題 H1。

    もとの行列では 根 `(0,*,*)` と アンカー `(1,1,0)` の 2 つ。写しの中では
    上昇で行 0 が上がるので、根は `(k,0,0)` に、アンカーは `(k,1,0)` に化ける。
    親をたどって根まで届けば、化けたものも項の頭と認める。
    """
    if _d > 64:
        return False
    c = Mo[j]
    if c[0] == 0 or tuple(c) == ANCHOR:
        return True
    if c[2] != 0:
        return False
    q = par0(Mo, j)
    if q < 0:
        return False
    if c[1] == 0:
        return term_top(Mo, q, _d + 1)          # 根の写し (k,0,0)
    if c[1] == 1:
        # アンカーの写し (k,1,0)。親が根そのものか、根の写し (k',0,0) のときだけ。
        return (Mo[q][0] == 0
                or (Mo[q][1] == 0 and Mo[q][2] == 0
                    and term_top(Mo, q, _d + 1)))
    return False


def copy_head(Mo, j):
    """柱 `j` が**写しの頭**か（もとの根 (0,*,*) が上昇して化けたもの）。課題 H1。

    BMS の展開は「悪い部分を上昇させて写す」。上昇は**行 0 に効く**ので、
    もとの根 `(0,0,0)` は写しの中で `(k,0,0)` になる。親をたどって
    「行 1 の加算項の頭」に届けば、その `(k,0,0)` は写しの頭である。

        (0,0,0)(1,1,1)(2,1,0)(2,1,0) | (1,0,0)(2,1,1)(3,1,0)(3,1,0) | (2,0,0)...
         ^根                            ^写しの頭                      ^写しの頭

    **行列から直に読める**（`st` を持ち回らない）ので写しに同変。
    """
    c = Mo[j]
    if not (c[1] == 0 and c[2] == 0 and c[0] >= 1):
        return False
    q = par0(Mo, j)
    return q >= 0 and term_top(Mo, q)


def top_level(Mo, j):
    """柱 `j` が「いまの写しの根の直下」か（もとの `nxt[0] <= 1` の写し版）。"""
    q = par0(Mo, j)
    return q < 0 or Mo[q][0] == 0 or copy_head(Mo, q)


def closes_top(Mo, off, nxt):
    """写しの中まで届く `closes_unit`。課題 H1。

    写しの中ではアンカー `(1,1,0)` が `(k,1,0)` に、根 `(0,0,0)` が `(k,0,0)` に
    化けるので `nxt[0] <= 1` が当たらない。「次の柱がいまの写しの根の直下に
    戻る」と読み替える。もとの行列（写しの頭が無い）では `closes_unit` と同じ。
    """
    if nxt is None:
        return True
    if nxt[2] != 0:
        return False
    if nxt[0] <= 1:
        return True
    j = off + 1
    if j >= len(Mo) or tuple(Mo[j]) != tuple(nxt):
        return False        # ブロックの外（番兵）なら見ない
    return top_level(Mo, j)


def hi_block2(m, x):
    """`hi_block` の写し補正。起点 `b` を「写しの頭の次の柱」まで進める。
    写しの頭が 1 つも無ければ `hi_block` と完全に同じ。課題 H1。

    旗 `V15['hiblk']`（課題 P2）を入れると、起点の対角柱の見分けも写しに
    同変な `is_diag`（行 0 から祖先の「x w」柱の本数を引いて行 1 と比べる）に
    なる。写しの中でない行列では (a,a,z) と一致するので無変化。
    """
    if V15['hiblk']:
        b = max([q for q in range(x) if is_diag(m, q)], default=0)
    else:
        b = max([q for q in range(x) if m[q][0] == m[q][1] and m[q][0] >= 1],
                default=0)
    for q in range(x):
        if q + 1 > b and copy_head(m, q):
            b = q + 1
    return any(m[z][2] > 0 for z in range(b + 1, x))


def anch_before(Mo, off):
    """`off` より前にアンカー (1,1,0) が 1 本でもあるか。"""
    return any(tuple(Mo[j]) == ANCHOR for j in range(off))


def p0deep_ok(Mo, off, p, nxt):
    """`prev == 0` でも分岐列を深く綴るか（課題 H1）。

        深い <=> nxt[0] >= p[0]
                 or（自分より前にアンカー (1,1,0) が 1 本も無く、かつ nxt[1] >= 1）

    教師データ（シート 1354 行 ＋ ImgClosedT の目標 `(conv3 A)<m>`、
    `prev == 0` の枝 9399 本）で誤り 30 本。うち「深すぎ」＝いま正しく綴れて
    いる柱を壊す向きは **0 本**。比較: `nxt[0] >= p[0]` だけなら誤り 597 本。
    """
    if nxt is None:
        return False
    if nxt[0] >= p[0]:
        return True
    # 旗 `wide0_anch`（課題 P1）: 第 2 項を `not is_w_col(nxt)` まで広げる
    # （h1 の `nxt[1] >= 1` との差は nxt == (0,0,0) の 1 例だけ）。
    ok2 = (not is_w_col(nxt)) if V15['wide0_anch'] else (nxt[1] >= 1)
    return ok2 and not anch_before(Mo, off)


def wchain_head(Mo, off):
    """`off` から後ろへ「x w」の柱 (k,0,0) をさがす（課題 F2 の `wchain`）。

    ただし**その柱から `off` までの柱がぜんぶ行 0 > k**（＝その柱の子孫）で
    なければならない。行 0 が 0 の柱（新しい加算項の頭）に当たったら諦める。
    見つからなければ None。

    直前 1 本だけを見る `after_w` を、写しの頭まで届くように広げたもの。
    `(k,0,0)(k+1,1,1)...(a,1,0)` のように「x w」で開いた写しの中で分岐列が
    末尾に来る形を拾う。距離の上限は要らない（「ぜんぶ子孫」が同じ働きをする）。
    """
    for j in range(off - 1, -1, -1):
        if is_w_col(Mo[j]):
            k = Mo[j][0]
            # v14 h1: 鎖の頭が「写しの頭」なら、根 (0,*,*) に当たったのと同じ。
            if V14['h1'] and copy_head(Mo, j):
                return None
            if all(Mo[t][0] > k for t in range(j + 1, off + 1)):
                return j
            return None
        if Mo[j][0] == 0:
            return None
    return None


def sib_ok(off, src, st):
    """兄弟から渡された深い側 `base_sd` を**使ってよいか**（`sibL` の伝染止め）。

    `sib_anchbefore`: この柱より前にアンカー (1,1,0) が 1 本も無いときだけ。
    アンカーは行 1 の新しい加算ユニットの頭なので、「行 1 の最初のユニットの
    中でだけ、影の深さは兄弟に効く」という読み方になる。同じ点数になる書き方が
    3 つある（`w1.py` の `sib_anchsrc` / `sib_anchnone` / `sib_anchbefore`）。
    """
    if V13['sib_anchbefore']:
        Mo = st['Mo']
        if any(tuple(Mo[j]) == ANCHOR for j in range(0, off)):
            return False
    return True


def _snap(st):
    # P3 `cpyspell`: 下見（`leaves_mark_local`）の決定 `dec` も巻き戻す。
    # 巻き戻さないと下見の決定が漏れて縮約の発火が変わる。
    return (st['ST'], st['prev'], list(st['dmap']), st.get('nc', 0),
            dict(st.get('dec', {})))


def _restore(st, s):
    st['ST'], st['prev'], st['dmap'], st['nc'] = s[0], s[1], list(s[2]), s[3]
    if len(s) > 4:
        st['dec'] = dict(s[4])


def leaves_mark(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, q, oA, oU):
    """残余なしの縮約が像に印を残すか（**大域版**、突き合わせ用）。

    自然な綴り（次の列 = アンカー `q`）と強制の綴り（次の列 = `na = NOTLAST`）を
    両方走らせ、像が違うときだけ縮約を許す。`st` は 2 回とも同じ状態から
    始めて戻す。`leaves_mark_local` と gen<=7 の 77282 個で像の差 0。
    """
    s0 = _snap(st)
    rec0 = dict(st['rec'])
    a1 = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
               U[0] if U else na, oA)
    u1 = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na, oU)
    _restore(st, s0)
    a2 = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
               U[0] if U else q, oA)
    u2 = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, q, oU)
    _restore(st, s0)
    st['rec'] = rec0
    return (a1, u1) != (a2, u2)


def leaves_mark_local(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, oA, oU,
                      ob):
    """残余なしの縮約が像に印を残すか（**局所版**、Lean に載せられる形）。

    縮約は「写しを書かない代わりに、本体の末尾の分岐列を番兵 `NOTLAST` で
    深く綴る」ことだけで写しを記録する。ところが本体の末尾がもともと深く
    綴られていると（`after_w` の上書きなどで）、深くしても像は 1 ビットも
    変わらず、写しが像から消える。すると `M` と `M ++ q ++ 写し` が同じ像に
    潰れる（＝単射性の破れ。<=7 列で 166 組のうち 164 組がこれ）。

    印が残る条件は局所に書ける。`q` はアンカー (1,1,0) なので
    `closes_unit(q)` はつねに真、したがって上書きが無ければ

        自然な綴り = 浅い、  強制の綴り = 深い <=> 決める直前の段 prev != 0

    上書きは 2 つ（`after_w` と `closes_hi_unit`）で、どちらも 2 通りで
    **同じ**結論を出すので、firing したら印は残らない。よって

        印が残る <=> prev != 0 かつ after_w も closes_hi_unit も firing しない

    （`prev` は None / 0 / 1 の 3 値。`'tie'` は浅い／深いの選択肢が
    そもそも無かった柱で、そのときも印は残らない。）
    """
    s0 = _snap(st)
    rec0 = dict(st['rec'])
    conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
          U[0] if U else na, oA)
    conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na, oU)
    prev_in = st['rec'].get(ob, 'none')
    _restore(st, s0)
    st['rec'] = rec0
    if prev_in == 0 or prev_in == 'tie' or prev_in == 'none':
        return False        # prev==0 なら強制でも浅い / tie なら選択肢が無い
    Mo = st['Mo']
    c = Mo[ob]
    pv = Mo[ob - 1] if ob >= 1 else None
    pv2 = Mo[ob - 2] if ob >= 2 else None
    onx = Mo[ob + 1] if ob + 1 < len(Mo) else None
    if prev_in == 1 and is_w_col(pv) and closes_unit(onx):
        return False                     # after_w が両方を同じにする
    if closes_hi_unit(c, onx, pv, pv2, hi_block(Mo, ob), is_repeat(Mo, ob)):
        return False                     # closes_hi_unit が両方を浅くする
    return True


def conv3(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
          st=None, nx=None, off=0):
    """設計 v10: 二重の梯子 ＋ 分岐列 (a,1,0) の 1 ビット状態機械。

    `L[k]` もとの行 1 の深さ `k` の祖先について
           (深い側の行 1, その行 2, 子に渡す force1, 浅い側の行 1)
           行 1 の影を立てると「深い側」だけが影の値に置き換わる。
    `F[k]` 行 1 の深さ `k` の次の柱がその行 1 ブロックの先頭か
    `st`   線形に持ち回る状態 {'ST': 祖先の鎖, 'prev': 直前の分岐列の選択,
           'dmap': もとの深さ -> 像の深さ, 'Mo': もとの行列まるごと}
    `nx`   このブロックの**後ろ**に来る列（ブロック分割で見失うので持ち回る）
    `off`  この `M` がもとの行列 `st['Mo']` の何列目から始まるか。
           `M` はつねに `Mo` の連続部分なので、これで前後の列が引ける。

    分岐列 (a,1,0) (a>=2) だけが浅い／深いを選ぶ（NOTES §6 の観測）。
        浅い <=> prev == 0 / 行列の末尾 / 次がアンカー (1,1,0)
                 / after_w（直前が「x w」でユニットの端）
                 / closes_hi_unit（(a,2,1)(a,2,0)(a,1,0) の次が (1,1,1)）
    アンカー (1,1,0) を通過するたびに prev := 0。

    **v9 -> v10 で足した 4 条項**（どれも `m_residue.py` で 1 つずつ測った）

      resid    縮約の残余は「開始深さ 1 つの木」ではなく**もとの深さを保った森**。
               残余の先頭より浅い柱で切って再帰する（`conv_resid`）。
      L        `L[:v]` は `len(L) < v` のとき黙って詰まる。`padL` で長さ v
               まで `Lat` で埋めてから継ぐ。
      after_w  直前が「x w」の柱 (k,0,0) でユニットの端なら段は落ちる。
               W_(w^2) 系で直前が根に付いていないときだけ段が残る。
      closes_hi_unit
               (a,2,1)(a,2,0)(a,1,0) の直後が (1,1,1) なら段を上げずに閉じる。

    after_w と closes_hi_unit は**直前 2 本の柱**を見る規則なので、ブロックに
    切ってしまうと見えなくなる。`st['Mo']` ともとの添字 `off` を持ち回って引く。

    1 本の BMS 列は最大 3 本の柱になる:
        (d,   pw0,  pw1)       行 0 の影
        (dd,  base, pl2)       行 1 の影
        (dd', e1,   e2)        本体
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
              'rec': {}}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)
    oA, oB = off + 1, off + 1 + len(A)      # 引数ブロック / 兄弟の先頭の添字

    src = None
    if v == 0:
        base_d = base_s = base_sd = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
        # v13 sibL: 第 5 要素 = 兄弟だけが使える深い側、第 6 要素 = それを
        # 書いた柱のもとの添字。無ければ深い側と同じ（＝ v12 のまま）。
        base_sd = (e[4] if len(e) > 4 else e[0]) + 1
        src = e[5] if len(e) > 5 else None
    first1 = F[v] if v < len(F) else True

    # v12 newterm（課題 E2）: 行 0 が 0 の柱 (0,*,*) は**新しい加算項**の頭。
    # ユニットが変わるのだから、直前の分岐列の選択は次の項に持ち越さない。
    # 持ち越すと A ++ A の 2 つ目の写しで段が浅く綴られ、f が和について
    # 加法的でなくなる（ImgClosedT と共終性 C1 の破れ）。実測（`z2.py`）:
    #   gen<=7 の 77282 個で像の差 0、gen<=8 の 781605 個で 50 個だけ変わる
    #   C1 の破れ <=5/<=6/<=7 列  7/121/1572 -> 5/88/1167（破れ集合は真部分集合）
    #   ImgClosedT の破れ A       28/327/3779 -> 26/294/3374（同）
    #   新しく壊れたものは 0
    if V12['newterm'] and p[0] == 0:
        st['prev'] = None
    # v14 wterm（試作, 既定 off）: 根に直付けの「x w」の柱 (k,0,0) も
    # 新しい加算項の頭なので段の状態を持ち越さない。生成 <=8 列の非標準 3 件
    # （`(0,0,0)(1,1,1)(2,1,0)(1,0,0)(2,1,1)(2,1,0)(3,2,1)X`）を狙う。
    elif (V14['wterm'] and is_w_col(p)
            and (par0_w if V15['wterm_chain'] else par0)(st['Mo'], off) == 0
            and not (V14['wterm_anchbefore']
                     and any(tuple(c) == ANCHOR for c in st['Mo'][:off]))):
        st['prev'] = None

    # v11: アンカー (1,1,0) での段のリセット `st['prev'] = 0` は**やめた**。
    # 写しの中のアンカーで prev が 0 に戻ると、もとで「深い」と綴られた分岐列が
    # 写しでは「浅い」と綴られ、f(M<n>) が像の展開に追いつかない（C1 の型D）。
    # 課題 D5 の測定（2026-08-27）:
    #   gen<=7 の 77282 個で像は 1 ビットも変わらない（7 列の 68895 個で差 0）
    #   展開閉包 28158 個で像が変わるのは 45 個だけ。非標準 / 潰れ / 順序違反は
    #     103 / 1 / 4 で v10 と同数
    #   共終性 C1 の破れ（<=6 列）136 -> 121。破れ集合は 121 ⊂ 136（片側だけ）
    #   ImgClosedT の速い道の外れ（<=6 列）342 -> 327 個、集合は 327 ⊂ 342
    #   直った 15 個は逆像 B を実際に持っている（構成的）
    if is_branch(p):
        nxt = M[1] if len(M) > 1 else nx
        # v13 sibL（課題 F1）: 深い側の候補は、兄弟から渡ってきた `base_sd` を
        # 使ってよければそれ。門は「浅い側 != 深い側の候補」で開く。
        # v12 では門が `base_s != base_d` だったので、`base_sd` を入れると
        # 門の判定にも `base_sd` が要る（さもないと選択肢が消える）。
        deep = base_d
        if V13['sibL'] and base_sd != base_d and sib_ok(off, src, st):
            deep = base_sd
        if base_s != deep:
            # v12 mark: 局所版のガードのために「決める直前の段」を残す。
            st['rec'][off] = st['prev']
            shallow = (st['prev'] == 0) or closes_unit(nxt)
            # ここから先はもとの行列 Mo を直接見る。ブロックに切ってしまうと
            # 「直前の柱」が見えなくなるが、段の規則は直前 2 本を見て決まる。
            Mo = st['Mo']
            pv = Mo[off - 1] if off >= 1 else None
            pv2 = Mo[off - 2] if off >= 2 else None
            onx = Mo[off + 1] if off + 1 < len(Mo) else None
            hi = hi_block(Mo, off)
            # v14 h1（課題 H1）: 写しの中で「段が 1 だけ浅い」と綴る病
            # （ImgClosedT の族 α）を直す。どれも `Mo` と `off` と次の柱だけで
            # 決まる（＝写しに同変）。
            _w0 = False       # 位置から読んで深くしたか（P1 `wide0_noprev`）
            if V14['h1']:
                hi = hi_block2(Mo, off)
                cw = closes_top(Mo, off, nxt)
                if V15['closesw'] and closes_w(Mo, off, nxt):
                    cw = True     # P2 `closesw`: 化けたアンカーも閉じる
                if cw:
                    shallow = True
                elif st['prev'] == 0 and not closes_unit(nxt):
                    _w0 = p0deep_ok(Mo, off, p, nxt)
                    shallow = not _w0
            # after_w（rule.py）: 直前が「x w」の柱 (k,0,0) で、しかもユニットの
            # 端にいるなら、段はふつう 1 に落ちる（浅い）。W_(w^2) 系（hi）で
            # 直前の柱が根に付いていないときだけ、段が残る（深い）。
            _p0 = par0_w if V15['wroot'] else par0
            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)
            # v13 wchain（課題 F2）: `after_w` の窓は**直前 1 本**しかない。
            # 「x w」の柱がもっと後ろにあって、そこから今までがぜんぶその子孫
            # なら、直前が「x w」だったのと同じに扱う（判定式は after_w と同じ、
            # 親を見る柱だけ (k,0,0) 本人にする）。`after_w` が発火するときは
            # そちらが優先（elif）。
            elif V13['wchain'] and st['prev'] == 1 and closes_unit(onx):
                j = wchain_head(Mo, off)
                if j is not None:
                    shallow = not (hi and not (_p0(Mo, j) == 0))
            # closes_hi_unit（rule.py）: (a,2,1)(a,2,0)(a,1,0) と積んだ直後が
            # アンカー (1,1,1) なら、段を上げずにユニットを閉じる（浅い）。
            if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
                shallow = True
            # P3 `cpyspell`: 写しの中の分岐列は、写しのもとの柱と同じに綴る。
            # 縮約が飲んだ写しは決定を残さないので、写しの鎖をさかのぼる。
            if (V15['cpyspell']
                    and not (V15['cpy_notlast'] and closes_unit(nxt))
                    and not (V15['cpy_noend'] and nxt is None)):
                dec = st.setdefault('dec', {})
                j, seen = copy_src(Mo, off), 0
                while j is not None and j not in dec and seen < len(Mo):
                    j, seen = copy_src(Mo, j), seen + 1
                if j is not None and j in dec and not (
                        V15['cpy_noanch']
                        and any(tuple(c) == ANCHOR for c in Mo[j:off])):
                    if not (V15['cpy_endshal'] and nxt is None and not dec[j]):
                        shallow = dec[j]
            if V15['cpyspell']:
                st.setdefault('dec', {})[off] = shallow
            base = base_s if shallow else deep
            # P1 `wide0_noprev`: 位置から読んで深くしたときは、深さは像に出るが
            # 1 ビットの状態は 0 のまま置く（`prev == 1` は「ユニットがまだ
            # 閉じていないので深く綴った」の意味で、`after_w` / `wchain` は
            # それを見て発火する）。
            if not (V15['wide0_noprev'] and not shallow
                    and st['prev'] == 0 and _w0):
                st['prev'] = 0 if shallow else 1
        else:
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep
    else:
        base = base_d

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    ST = st['ST']
    cols = []
    if lad0:
        cols.append((d, pw[0], pw[1]))
        ST = ST[:d] + ((pw[0], pw[1]),)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        ST = ST[:dd] + ((base, pl2),)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    ST = ST[:dd] + ((e1, e2),)
    st['ST'] = ST
    st['dmap'] = st['dmap'][:p[0]] + [dd]      # もとの深さ -> 像の深さ

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    # 行 1 の影を立てたら、その影が「もとの行 1 の深さ v-1」の祖先を置き換える。
    # 浅い側（影を使わない選択肢）はもとの値を残しておく。
    if e1 == base + 1 and v >= 1:      # 行 1 が水増しされた（影を書いたかは問わない）
        Lb = padL(L, v - 1) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v) + ((e1, s2, fc, e1),)
    if V13['sibL']:
        # 第 5/6 要素は**子には渡さない**（渡すとアンカーを素通りして
        # 次の加算ユニットまで深い綴りが届いてしまう）。
        LA = tuple(t[:4] for t in LA)
    FA = F[:v] + (False,)
    # v13 sibL: 行 1 の影を立てたら、そのあとの**兄弟**にも「深い側」を渡す。
    if V13['sibL'] and Lb is not L:
        eo = Lat(L, v - 1)
        LS = (padL(L, v - 1) + ((eo[0], eo[1], eo[2], eo[3], base, off),)
              + tuple(L[v:]))
    else:
        LS = L

    if lad0:
        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])
            U, B2 = units_split(p, B, qlab)
            if not B2:
                continue
            oU, oq = oB, oB + len(U)
            q, r2 = B2[0], B2[1:]
            if (q[1], q[2]) != qlab or q[0] != p[0]:
                continue
            Aq, Bq = split0(q, r2)
            oAq, oBq = oq + 1, oq + 1 + len(Aq)
            # 写しの終わりの分岐列は、写しが吸収されるぶん深く書かれることがある。
            # 素直な「次の列 = q」と「深い側」の 2 通りを試す。
            for na in (q, NOTLAST):
                pre = contrPre(p, U, A, e, ps[0], st['prev'], na)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            blk = [p] + list(A) + list(U)
            # 残りが「深く書かれた分岐列」で終わるか（NOTES §7 strip_lift の条件）
            deep_end = is_branch(blk[-1]) and pre[-1][1] > blk[-1][1]
            rest2 = list(Aq[len(pre):])
            oR = oAq + len(pre)
            if rest2:
                if rest2[0][0] < p[0] + 1:
                    continue
                if (rest2[0][0] == p[0] + 1
                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):
                    continue
            elif e == 0 or not deep_end:
                # 残余なしの縮約は「行 1 ずれ」かつ「残りが分岐列で終わる」ときだけ
                # （NOTES §7 の strip_lift の適用条件と同じ）
                continue
            elif V12['mark'] and not (
                    leaves_mark(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st,
                                na, q, oA, oU)
                    if V12['mark_global'] else
                    leaves_mark_local(A, U, dd, d, LA, L, FA, v, s2, e1, e2,
                                      st, na, oA, oU, off + len(blk) - 1)):
                # v12 mark（課題 E1）: 残余なしの縮約は「写しを飲んだ印が像に
                # 残る」ときだけ許す。印が残らないと `M` と `M ++ q ++ 写し` が
                # 同じ像に潰れる（単射性の破れ）。実測（`z1.py`）:
                #   gen<=7 の 77282 個で像の差 0（変わるのは長い双子だけ）
                #   双子 3609 個で 24 個の像が変わり、24 個ぜんぶが「潰れて
                #   いたものが分離した」側。閉包 127182 個で衝突 24 -> 0
                #   シート 1354 / z=0 / 非標準 / 順序 / ImgClosedT / 共終性は不変
                continue
            Lr = padL(L, v) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ。
            # 何も無くても「レベルが後で綴られている」ので末尾扱いにはしない。
            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                       U[0] if U else na, oA)
            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                       oU)
            # 写しの真下（もとの深さ p[0]+1）なら影の位置、さらに深ければ
            # 「もとの深さ -> 像の深さ」の表で決める。
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            # 残余は 1 本の木ではなく**森**。深さをそろえずに読む（conv_resid）。
            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)
            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)
            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数
            return cols + cA + cU + cR + cB

    # ここで「行 1 の影を立てた柱の兄弟を、影の横（深さ d）ではなく本体の横
    # （深さ dd）に付ける」規則（x_spell.py の sibbody2/3）を試したが、
    # **採らなかった**。gen<=7 の非標準を 3->1、gen<=8 を 84->42 に減らす代わりに、
    # 共終性 C1 を 1 件（<=5 列）・11 件（<=6 列）新しく壊す。詳しくは
    # モジュール docstring の「採らなかった規則」。
    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB


def conv_resid(rest, rd, Lr, ps, pw, st, nx, off):
    """縮約の残余を「もとの深さを保った森」として読む。

    残余（写しに吸われずに残った列）は 1 本の木とは限らず**森**でありうる。
    まるごと深さ `rd` の 1 本の木として読むと、残余の先頭より行 0 が小さい
    ＝もっと浅い柱まで `rd` にそろえてしまい、木の形が変わる。
    先頭より浅い柱のところで切り、もとの深さの差だけ浅くして読み直す。
    """
    out = []
    while rest:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        head, tail = rest[:i], rest[i:]
        nx2 = tail[0] if tail else nx
        out += conv3(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                     st, nx2, off)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))   # もとの深さの差だけ浅くする
        off += i
        rest = tail
    return out


def b2d3n(M):
    """(像, 縮約が発火した回数) の対。回数は逆写像 `inv3.d2b3` の
    既知の穴（縮約は像から列が落ちるので読み戻せない）を数えるのに使う。"""
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    return tuple(conv3(list(M), st=st)), st['nc']


def b2d3(M):
    return b2d3n(M)[0]


# ---------------------------------------------------------------- 検査
def pad(M2):
    return tuple((a, b, 0) for a, b in M2)


def two(M3):
    return [(c[0], c[1]) for c in M3]


def twin(M):
    """双子: `M ++ (1,1,0) ++ M[1:] の写し`（行 0 は +1、行 1 は 0 でなければ +1）。

    単射の破れの相手はほとんどこの形（<=7 列の 166 組のうち 143 組がぴったり、
    残り 23 組も「もと ++ アンカー ++ 写し」の変種。課題 E1 の実測）。
    `M` より**倍近く長い**ので、`gen3(lim)` の中だけで比べても見つからない。
    """
    return tuple(M) + ((1, 1, 0),) + tuple(
        (a + 1, (b + 1 if b > 0 else 0), c) for a, b, c in M[1:])


def inj_cross(f, lim=6, tlim=6, elim=5, en=6, seeds=(), verbose=3):
    """**列数をまたいだ**単射の検査（逆写像 `inv3` に頼らない）。

    `check` の (2) は `gen3(lim)` の中でしか比べていないので、`lim` 列を超える
    相手との衝突が見えない（実例: 6 列と 12 列が同じ像）。ここでは長い相手を
    自分で作ってから、像を辞書に貯めて衝突を数える:

        S1 = gen3(<=lim)                        短いほう
        S2 = {twin(M) : M in gen3(<=tlim)}      長いほう（<=2*tlim 列）
        S3 = {M<n> : M in gen3(<=elim), n<=en}  展開したもの
        S4 = seeds                              外から渡した相手

    `seeds` は「長い相手の候補」を外から足す口。`check` は (5) の逆写像
    `d2b3` が返した B を渡す。`twin` の形から外れた相手（分岐列を 1 本だけ
    浅く綴った変種など）は S2 では作れないので、この口で拾う。**衝突の判定
    そのものは `f` だけを見る**ので、`d2b3` が正しいかどうかには依存しない。

    返り値 (|S|, 衝突した (M, B, 像) の並び)。
    """
    S = set()
    for T in seeds:
        T = tuple(T)
        if T and isstd(T, 'BMS') and all(c[2] <= 1 for c in T):
            S.add(T)
    for M in gen3('BMS', lim, zcap=1):
        S.add(tuple(M))
    for M in gen3('BMS', tlim, zcap=1):
        T = twin(M)
        if isstd(T, 'BMS') and all(c[2] <= 1 for c in T):
            S.add(T)
    for M in gen3('BMS', elim, zcap=1):
        for n in range(1, en + 1):
            T = tuple(expand(tuple(M), n))
            if all(c[2] <= 1 for c in T):
                S.add(T)
    core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    seen, col = {}, []
    for i, M in enumerate(sorted(S, key=key)):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        N = tuple(f(list(M)))
        if N in seen:
            col.append((seen[N], M, N))
        else:
            seen[N] = M
    return len(S), col


def terms0(B):
    """行 0 が 0 の柱で切った**加算項**の並び。"""
    out, cur = [], []
    for c in B:
        if c[0] == 0 and cur:
            out.append(cur); cur = []
        cur.append(c)
    if cur:
        out.append(cur)
    return out


def untwin(B):
    """`B` の各加算項が `twin(W)` の形なら `W` に戻したもの（`inv3` の当て直し用）。

    `V12['mark']` を入れる前の `d2b3` は「双子」`W ++ (1,1,0) ++ 写し` を返す。
    いまの `conv3` では双子の像は長くなるので、正しい逆像はたいてい `W` の側。
    加算項ごとに独立に戻す（`d2b3` は `W ++ W` に対して `twin(W) ++ twin(W)` を
    返すので、末尾を切るだけでは戻らない）。
    """
    out, hit = [], False
    for Z in terms0(B):
        Z = tuple(Z)
        for j in range(2, len(Z)):
            if tuple(Z[j]) == ANCHOR and Z == twin(Z[:j]):
                Z, hit = Z[:j], True
                break
        out.extend(Z)
    return tuple(out) if hit else None


def preimage_try(f, T, d2b3):
    """目標 `T` の逆像を安く 1 つ。`d2b3(T)` を当て、外れたらその**接頭辞**も試す。

    逆写像 `inv3.d2b3` は `conv3` の版に合わせて作られているので、`conv3` を
    変えると古くなる。実際 `V12['mark']` を入れると `d2b3` は「双子」
    `W ++ (1,1,0) ++ 写し` を返すが、いまの `conv3` ではその像は長くなる。
    正しい逆像はたいていその `W` の側なので、`untwin`（加算項ごとに双子を
    戻す）と `B[:k]`（接頭辞）を当て直す。**当たりは `f(B')==T` を確かめてから
    返す**ので、この再挑戦は健全（偽の当たりを作らない）。

    返り値 逆像 B'（無ければ None）。
    """
    try:
        B = d2b3(T)
    except Exception:
        B = None
    if not B:
        return None
    if (isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
            and tuple(f(list(B))) == tuple(T)):
        return tuple(B)
    cands = []
    U = untwin(B)
    if U:
        cands.append(U)
    cands.extend(tuple(B[:k]) for k in range(2, len(B)))
    for P in cands:
        if (isstd(P, 'BMS') and all(c[2] <= 1 for c in P)
                and tuple(f(list(P))) == tuple(T)):
            return P
    return None


def imgclosed_fast(f, A, mmax=3, d2b3=None):
    """ImgClosedT の**速い道**（逆写像 `inv3.d2b3` を 1 発当てるだけ）。

        ImgClosedT: 任意の BMS 標準形 A (|A|>1) と m>=1 に対し、ある BMS
                    標準形 B があって  (f A)<m> = f B

    T = (f A)<m> に `d2b3` を当て、出た B が BMS 3 行 z<2 標準形で
    f(B) == T なら**逆像の存在の証明**（B そのものを持っている）。
    外れは「この道では見つからなかった」だけなので破れの**上界**である。
    ただし <=5 列 x m<=3 の 3051 対では、外れ 55 対が `m_imgclosed` の
    梯子つき全数探索の破れ 55 対（相異なる A が 28 個）と**ちょうど一致**した
    （2026-08-27 実測）。本物の破れかどうかは `m_imgclosed.py` で確かめる。

    返り値 (当たり, 対の総数, 外れた A の集合)。"""
    if d2b3 is None:
        try:
            from inv3 import d2b3
        except Exception:
            return 0, 0, set()
    ok, tot, bad = 0, 0, set()
    for i, M in enumerate(A):
        if len(M) < 2:
            continue
        if i % 500 == 0:
            # `d2b3` は `isstd` を大量に呼ぶ。<=7 列（77282 個）でここを
            # 2000 ごとにすると RSS が 2.5GB を超えた（2026-08-27 実測）。
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        N = f(M)
        for m in range(1, mmax + 1):
            T = tuple(expand(N, m))
            tot += 1
            if preimage_try(f, T, d2b3) is not None:
                ok += 1
            else:
                bad.add(tuple(M))
    return ok, tot, bad


def check(f, A, nr=6, mm=10, nn=24, verbose=3, inv=True, mc=40,
          rprop=False, imgc=3, imgfull=False, injx=(6, 6, 5, 6), fast=True):
    """(1) 像が DBMS 標準形 (2) 単射・順序保存 (4) z=0 で 2 行版と一致
    (5) 逆写像 `inv3.d2b3` で戻る (6) 共終性 C1/C2 (7) ImgClosedT。

    (3) 性質 R（添字まで一致）は **3 行では偽と確定している**（NOTES §性質 R）。
    目標にしてはいけないので `rprop=True` のときだけ回す（既定は回さない）。
    代わりに要るのは (6) と (7):

        C1: 任意の m<=mm に ある n<=nn で  f(M)<m> <= f(M<n>)
        C2: 任意の n<=nn に ある m<=mc で  f(M<n>) <= f(M)<m>
        ImgClosedT: 任意の m>=1 に ある BMS 標準形 B で  (f M)<m> = f B

    C1/C2 は**証明済みの 2 行版でちょうど 0** になる（z=0 の 3 行標準形
    <=6 列 1285 個で破れ 0）。ImgClosedT も z=0 では破れ 0（3852 対）。
    だからどちらの違反も変換器の本物の欠陥である。ImgClosedT は C1 より
    細かい: <=5 列で C1 の破れ 7 個は ImgClosedT の破れ 28 個に**含まれる**。

    (2) の単射は `A` の中でしか比べていない。`A` は `gen3(lim)` なので
    **lim 列を超える相手との衝突は見えない**（実例: 6 列と 12 列が同じ像。
    NOTES §逆写像）。それは (5) が拾う: 往復が落ちて、しかも戻り B が
    BMS 標準形で f(B) が同じ像なら、それは**単射性の破れの証拠**である。

    `imgc` は ImgClosedT の m の上限（0 で回さない）。`imgfull=True` なら
    `m_imgclosed` の梯子つき探索（速い道が外れたものだけ・**重い**）。
    `fast=True` なら `imgfast.imgclosed_fast`（fork 並列 ＋ 誘導つき DFS の
    救出。<=5 列で 10 分 -> 44 秒。答えは `m_imgclosed` と食い違い 0）を使う。

    `injx=(lim, tlim, elim, en)` は **(2b) 列数をまたいだ単射**（`inj_cross`）。
    `A` の中だけの (2) では見えない「もと ++ アンカー ++ 写し」の衝突を拾う。
    `None` で回さない。
    """
    W = [f(M) for M in A]
    ns = [(M, N) for M, N in zip(A, W) if not isstd(N, 'DBMS')]
    inj = len(set(W)) == len(W)
    ordbad = [i for i in range(len(A) - 1) if cmpmat(W[i], W[i + 1]) >= 0]
    z0bad = [(M, N) for M, N in zip(A, W)
             if all(c[2] == 0 for c in M) and N != pad(convC2(two(M)))]
    rbad, c1bad, c2bad = [], [], []
    for i, M in enumerate(A):
        if len(M) < 2:
            continue
        if i % 2000 == 0:
            # 展開のメモは M ごとに独立なので、ときどき捨てないと
            # <=7 列（77282 個）で RSS が 10GB を超える。
            core._exp_memo.clear()
            core._isstd_memo.clear()
            core._flat_memo.clear()
        N = f(M)
        E = [tuple(expand(N, m)) for m in range(1, mc + 1)]
        G = [tuple(f(expand(M, np))) for np in range(1, nn + nr + 1)]
        if rprop:
            img = set(E[:mm])
            for n in range(1, nr + 1):
                if not any(g in img for g in G[n - 1:n + nn]):
                    rbad.append((M, n, N))
                    break
        # (6) 共終性。
        if any(not any(cmpmat(E[m], g) <= 0 for g in G[:nn]) for m in range(mm)):
            c1bad.append((M, N))
        if any(not any(cmpmat(g, e) <= 0 for e in E) for g in G[:nn]):
            c2bad.append((M, N))
    # (5) 逆写像。`inv3` は `rows3` を import するので、ここで遅延 import する。
    rtbad, rtbad2, rtinj, d2b3 = [], [], [], None
    if inv:
        try:
            from inv3 import d2b3
        except Exception:
            d2b3 = None
    if d2b3 is not None:
        for M, N in zip(A, W):
            B = d2b3(N)
            if B == tuple(M):
                continue
            if (B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
                    and tuple(f(list(B))) == tuple(N)):
                rtinj.append((M, B, N))   # 別の BMS 標準形が同じ像 = 単射の破れ
            else:
                rtbad.append((M, N))
                rtbad2.append((M, N, B))
    # (7) ImgClosedT
    icok = ictot = 0
    icbad, iccap = set(), []
    if imgc:
        icf = None
        if fast:
            try:
                from imgfast import imgclosed_fast as icf
            except Exception:
                icf = None
        if icf is not None:
            # `imgfast` の段 1 にも `preimage_try`（接頭辞の当て直し）を通す。
            # そうしないと古い `d2b3` のせいで破れが水増しされる（<=6 列で +1）。
            icok, ictot, icbad = icf(
                f, A, imgc,
                (lambda T: preimage_try(f, T, d2b3)) if d2b3 else None)
        else:
            icok, ictot, icbad = imgclosed_fast(f, A, imgc, d2b3)
        if imgfull and icbad:
            # 速い道が外れたものだけ梯子つき探索に降ろす。梯子は **安いほう**
            # （`LADDER_SCAN`）。既定の `LADDER` は 1 件あたり 54 万節点まで
            # 歩くので、<=4 列でも 5 分・RSS 5GB を超えた（2026-08-27 実測）。
            # 「なし」と出ても打ち切りが付いていれば探索不足の疑いが残る。
            from m_imgclosed import find, LADDER_SCAN
            still, iccap = set(), []
            for M in sorted(icbad, key=key):
                for m in range(1, imgc + 1):
                    T = tuple(expand(f(M), m))
                    _, B, _, _, cap = find(M, m, f=f, ladder=LADDER_SCAN, T=T)
                    core._isstd_memo.clear(); core._flat_memo.clear()
                    if B is None:
                        still.add(tuple(M))
                        if cap:
                            iccap.append((tuple(M), m))
            icbad = still
    print('  対象 %d 個' % len(A))
    print('  (1) 像が DBMS 非標準 : %d' % len(ns))
    for M, N in ns[:verbose]:
        print('        %-34s -> %s' % (show(M), show(N)))
    print('  (2) 単射（この集合の中で） : %s   順序保存の違反 : %d'
          % (inj, len(ordbad)))
    for i in ordbad[:verbose]:
        print('        %-34s -> %s' % (show(A[i]), show(W[i])))
        print('        %-34s -> %s' % (show(A[i + 1]), show(W[i + 1])))
    xcol = []
    if injx:
        # (5) の `d2b3` が返した相手も種に足す（判定は `f` だけを見る）。
        seeds = [B for _, B, _ in rtinj] + [b for _, _, b in rtbad2 if b]
        nS, xcol = inj_cross(f, *injx, seeds=seeds)
        print('  (2b) 単射（列数をまたいで, 閉包 %d 個） : 衝突 %d 組'
              % (nS, len(xcol)))
        for a, b, N in xcol[:verbose]:
            print('        %-34s と' % show(a))
            print('        %-34s が同じ像 %s' % (show(b), show(N)))
    if rprop:
        print('  (3) 性質 R の違反 : %d   （3 行では偽。目安どまり）' % len(rbad))
        for M, n, N in rbad[:verbose]:
            print('        %-30s -> %s  (n=%d で覆えない)' % (show(M), show(N), n))
    else:
        print('  (3) 性質 R : 回さない（3 行では偽。rprop=True で回る）')
    print('  (4) z=0 で 2 行版と食い違い : %d' % len(z0bad))
    for M, N in z0bad[:verbose]:
        print('        %-34s -> %-30s (2 行版 %s)'
              % (show(M), show(N), show(pad(convC2(two(M))))))
    stale = sum(1 for M, N, B in rtbad2
                if B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B))
    print('  (5) d2b3(b2d3(M)) != M : %d   （うち単射性の破れ %d = 別の '
          'BMS 標準形が同じ像 / 逆写像が古い %d = 戻り B は BMS 標準形だが '
          'f(B) が別の像）' % (len(rtbad) + len(rtinj), len(rtinj), stale))
    for M, N in rtbad[:verbose]:
        print('        %-34s -> %-30s (戻り %s)' % (show(M), show(N), show(d2b3(N))))
    for M, B, N in rtinj[:verbose]:
        print('        %-34s と %s が同じ像 %s' % (show(M), show(B), show(N)))
    print('  (6) 共終性 C1 の破れ : %d   C2 の破れ : %d' % (len(c1bad), len(c2bad)))
    for M, N in (c1bad + c2bad)[:verbose]:
        print('        %-34s -> %s' % (show(M), show(N)))
    if imgc:
        print('  (7) ImgClosedT（m<=%d, %s）: 逆像あり %d / %d   '
              '破れた A %d 個%s'
              % (imgc, '梯子つき全数' if imgfull else '速い道のみ',
                 icok, ictot, len(icbad),
                 '   うち打ち切り %d' % len(iccap) if imgfull else ''))
        for M in sorted(icbad, key=key)[:verbose]:
            print('        %-34s -> %s' % (show(M), show(f(M))))
    return (len(ns) + len(ordbad) + len(rbad) + len(z0bad) + len(rtbad)
            + len(rtinj) + len(c1bad) + len(c2bad) + len(icbad) + len(xcol))


def main(lim=5, imgc=3, imgfull=False, rprop=False):
    t0 = time.time()
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d  (%.1fs)' % (lim, len(A), time.time() - t0))
    n = check(b2d3, A, imgc=imgc, imgfull=imgfull, rprop=rprop)
    print('合計違反 %d  (%.1fs)' % (n, time.time() - t0))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5,
         imgc=int(sys.argv[2]) if len(sys.argv) > 2 else 3,
         imgfull=len(sys.argv) > 3 and sys.argv[3] == 'full')
