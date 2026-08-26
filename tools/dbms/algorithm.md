# BMS 2 行標準形 -> DBMS 標準形の変換 `conC`

対象は 2 行のバシク行列（BM4）の標準形、つまり `psi_0(Omega_omega)` 未満。
実装は [`rows2.py`](rows2.py)（参照実装）と [`bms2dbms.py`](bms2dbms.py)（CLI）、
形式化は [`lean/Dbms.lean`](../../lean/Dbms.lean) と
[`lean/DbmsStd.lean`](../../lean/DbmsStd.lean)。

## 0. なぜ変換が要るのか

BMS と DBMS は**展開規則が同じ**で、**対角だけが違う**。

```
BMS : diag[x][y] = x
DBMS: diag[x][y] = max(x - y, 0)
```

2 行で言うと、列 `(a, b)` の `a` が深さ、`b` が段。標準形が許す段の上限が違う。

```
BMS  は 段 <= 深さ        (a, a) を書ける
DBMS は 段 <  深さ        (a, a) は書けない（a = 0 を除く）
```

**これが違いのすべてである。** 変換の仕事は「段が深さに追いついている列を、
1 つ深いところへ押し下げる」ことに尽きる。

## 1. 共通の的 — 読み `translate`

両方の行列が指す先を、入れ子の木 `Three` として取り出す。

```
inductive Three
  | Z                                 葉
  | P : N -> Three -> Three -> Three  (段, 引数, 兄弟)
```

BMS の読みは素直な構造再帰である。先頭の列より深い列が引数、それ以外が兄弟。

```
translate []          = Z
translate (p :: rest) = P p.2 (translate 引数) (translate 兄弟)

  引数 = rest の中で深さが p.1 より大きい最長の接頭辞
  兄弟 = その残り
```

変換の正しさは「**変換しても読んだ木が変わらない**」という形で述べる。

```
     BMS 標準形 M  --conC-->  DBMS 標準形
         |                       |
      translate               readCon
         |                       |
         v                       v
        Three   ============   Three
```

## 2. 芯 — `convD`

`translate` とまったく同じ 2 分岐で書ける。持ち回るのは 4 つ。

| | |
|---|---|
| `d` | いま書いているブロックの深さ |
| `plev` | 親の段 |
| `first` | ブロックの先頭の列か |
| `force` | 「影の形で書け」という親からの指示 |

```
convD [] d plev first force = []
convD (p :: rest) d plev first force =
    let s    = p.2
    let A, B = 引数, 兄弟
    let lad  = first && s == plev + 1 && (d <= s || force)
    let dd   = if lad          then d + 1
               else if s > 0 && d <= s then s + 1
               else                          d
    let cols = if lad then [(d, plev), (d + 1, s)] else [(dd, s)]
    cols ++ convD A (dd + 1) s True  ((not lad) && first && s == plev)
         ++ convD B d        s False False
```

深さの決め方 `dd` が 3 通りある。

**(a) 素通り** — 段が 0、または既に `d > s` なら、そのまま深さ `d` に書ける。

**(b) 段へ跳ぶ** — 段 `s > 0` の列は DBMS では深さ `s + 1` 以上に居なければならない。
`d <= s` なら深さを `s + 1` へ持ち上げる。

**(c) 梯子** — ブロックの先頭で段が親のちょうど +1 のときは、跳ぶわけにいかない。
木の形が変わってしまうからである。そこで**影の列を 1 本立てて**深さを稼ぐ。

```
(d, plev)      影。段は親と同じなので読みでは無視される
(d + 1, s)     本体
```

`force` は「親の列が影と読まれてしまう危険があるから、影の形で書け」という指示で、
引数ブロックへ降りるときだけ渡る。

ここまでは `translate` と 1 対 1 に対応していて、特別扱いは無い。

## 3. 継ぎ足し — 縮約（梯子の二役）

`convD` の像は DBMS 標準形になり切らない。`<=9` 列の BMS 標準形 5351 個のうち
**78 個**で像が非標準になる（`(0,0)(1,1)(1,0)(2,1)(2,0)` 型）。

原因は、同じ梯子を 2 度立てる形が現れることである。DBMS では 1 本の柱が
「親の段」と「子の段」を**兼ねられる**ので、2 度目を書かないのが正しい。
これを縮約と呼ぶ。

発火の条件は 4 つ全部が揃ったとき。

```
1. いま梯子を立てている                     lad
2. 兄弟のユニット列 U のあとに q が来て、
   q の段が s - 1、q の深さが p と同じ       q.2 + 1 == s, q.1 == p.1
3. q の引数の頭が、いま書いた分とそっくり同じ
       contrPre p U A = [(p.1+1, p.2)] ++ shift1 A ++ shift1 U
4. その続き rest2 の頭が深さ p.1+1 で段が下がる
```

揃ったら、`q` とその前置きを**まるごと書かず**に中身だけを続ける。

```
cols ++ convC A     (dd+1) s False   引数
     ++ convC U     (d+1)  s False   兄弟のユニット列
     ++ convC rest2 dd     s False   q の引数の残り（前置きを飛ばした先）
     ++ convC Bq    d      s False   q の兄弟
```

ここで**ユニット**とは「1 本の柱 + その引数ブロック」のこと。数えるのが
`units_split` である。旧版は柱が並ぶ本数しか数えておらず、兄弟が引数を持つと
そこで切れて縮約が発火しなかった。11 列の反例で見つかった。

```
(0,0)(1,1)(2,2)(1,1)(2,1)(1,0)(2,1)(3,2)(2,1)(3,1)(2,0)
```

**この枝 1 本が、標準形性の証明を 15000 行にした。** それ以外は素直に閉じる。

## 4. 読み戻し `readCon`

DBMS 側の読みは `translate` に節を足したものである。

**影を捨てる節** — 先頭が「段が親と同じで、次の列が `(p.1+1, p.2+1)`」なら、
その列は梯子の影なので読み飛ばす。

**二役の節** — さらにその先に「深さが同じで段が下がる列」が続くなら、
1 本の柱が 2 つの節点を兼ねている。ほどいて 2 つに戻す。このために `readK` は
継続 `k`（読み切った先に置く項）を持ち回る。

逆変換はこの読みを経由する。

```
conC^{-1} = untranslate . readCon
untranslate Z            = []
untranslate (P s A B) d  = [(d, s)] ++ untranslate A (d+1) ++ untranslate B d
```

`conC` の単射性は証明済みだが**全射性は未証明**なので、逆変換の結果は往復で
確かめる必要がある（`bms2dbms.py -r` は自動でやる）。実測では DBMS 標準形
`<=7` 列の 1740 個すべてに逆像がある。Naruyoko 氏が `Trans`（PSS -> ブーフホルツ）で
使った道 — 逆写像を作らず**両側の共終性**だけで全単射を出す — がそのまま使えるはずで、
その 2 条件は `cofinal_check.py` が `<=7` 列 7256 個で違反 0 を確認している。

## 5. 証明されていること

すべて `sorry` なし、`sorryAx` なし、公理は `[propext, Classical.choice, Quot.sound]` のみ。

| 命題 | 場所 |
|---|---|
| `readC_conC_ST : ST_PS M -> readCon (conC M) = translate M` | `Dbms.lean` |
| `ST_D_conC_final : ST_PS M -> ST_D (conC M)` | `DbmsStd.lean` |
| `conC_olt_iff_seqlex : readCon (conC M) <o readCon (conC N) <-> seqlex M N` | `Dbms.lean` |
| `conC_injective : conC M = conC N -> M = N` | `Dbms.lean` |

`ST_PS` は BMS 2 行標準形、`ST_D` は DBMS 標準形、`<o` は項の順序、
`seqlex` は行列の順序。仮定は `ST_PS M` だけである。
**全射性（`ST_D N -> exists M, ST_PS M /\ conC M = N`）はまだ証明されていない。**

要になったのは次の補題で、これを無条件に証明するのが一番重かった。

```
ReindexD : ST_PS A -> 1 < |A| -> forall n >= 1,
    exists m >= 1, exists n' >= n,  (conC A)[m] = conC (A[n'])
```

「像の基本列は、もとの基本列の像で（添字をずらせば）覆える」。
これがあれば整礎帰納で標準形性が降りてくる。

## 6. 実測

| | |
|---|---|
| 読みの一致 | BM4-Analysis シートの 547 例で `#guard` |
| `ReindexD` | 標準形 `<=10` 列 2073826 個で違反 0 |
| 像の標準形性 | 同上 |
| 縮約が発火する例 | 同 2073826 個のうち 180 個 |
