# 成果の概略

1. **3 行 DBMS（DTSS, `z ≤ 1`）の器が Lean で立ち、変換 `conv3` が定義として
   実装されているが、間違いを含んでいる。**
   対角・標準形・降下・主定理の骨組みがあり、Lean の `Conv3.conv3` は Python の
   `bms2dbms/tools/rows3.py` と同じ像を出す（`≤7` 列全数と、7 列で像が変わる 18 個に `#guard`）。
   間違いの所在は `ImgClosedT` の破れ（`≤5` 列で 2 個、`≤6` 列で 54 個）と、
   下の 2-2 / 2-3 が現在の `conv3` では偽であること。

   **付記（器の性質）**: この器は、**整礎性を BMS 側でなく DBMS 側で取ってよい**形になっている。
   `ST_D3_descend` が整礎性を使うのは 1 か所だけで、そこは
   `(conv3 A)⟦m⟧ = conv3 B` により DBMS 側の基本列で置き換えられる。したがって

   * **もし** DBMS 側の整礎性 `WellFounded RD3` が証明できれば、
     `ST_D3_conv3_of_parts_D` は BMS 側の残核（`TowerGraft2` / `TowerExp`）を使わない。
   * **もし** さらに `conv3` が完成して 2-1〜2-6 が全部成り立てば、
     `TRIO_terminates_of_dbms_wf_parts` により BMS 3 行 (`z ≤ 1`) の停止性が出る。

   `WellFounded RD3` は未証明であり、`conv3` も未完成なので、いずれも現時点では条件つきである。

2. **変換に必要な性質が 7 本に確定した。**

   **2-1 `ImgCofinalT3 conv3`** — 未証明

   ```lean
   ∀ A, ST_TS A → 1 < A.length → ∀ m0, ∃ m, m0 ≤ m ∧ ∃ B, ST_TS B ∧ (conv3 A)⟦m⟧ = conv3 B
   ```
   意味: **像を展開したものが、また別の標準形の像になっている** ——
   そういう展開回数 `m` が**いくらでも大きく取れる**。
   （「すべての `m` で」（`ImgClosedT3`）より弱く、必要なのはこちらだけ。）

   **2-2 `OrderT3 conv3`** — **偽**（`len ≤ 11` の 1,882,196 個で両向き各 24 件）

   ```lean
   ∀ M N, ST_TS M → ST_TS N → (translate M <o translate N ↔ seqlex (conv3 M) (conv3 N))
   ```
   意味: **変換が順序を保つ** —— BMS 側の順序数の大小と、DBMS 側の辞書式順序が一致する。

   **2-3 `SandwichUT3 conv3`** — **偽**（`≤7` 列 386,405 対で 8 件）

   ```lean
   ∀ A, ST_TS A → 1 < A.length → ∀ n ≥ 1, sle3 (conv3 (A⟦n⟧)) ((conv3 A)⟦n+1⟧)
   ```
   意味: **展開してから写したものは、写してから 1 手多く展開したもの以下** ——
   像の基本列が元の基本列を上から挟む。

   **2-4 `ImgBlockT3 conv3`** — 未証明（`≤7` 列 77,282 個で破れ 0）

   ```lean
   ∀ A, ST_TS A → blockok 0 (conv3 A)
   ```
   意味: **像がブロック形をしている** —— 行 0 が 0 から始まり、隣り合う柱の行 0 の段差が 1 以下。

   **2-5 `ImgLenT3 conv3`** — **証明ずみ**（`ImgLenT3_b2d3`）

   ```lean
   ∀ A, ST_TS A → 1 < A.length → 1 < (conv3 A).length
   ```
   意味: **変換が潰れない** —— 入力が 2 列以上なら像も 2 列以上。

   **2-6 `ConvDiagT3 conv3`** — **証明ずみ**（`ConvDiagT3_b2d3`）

   ```lean
   ∀ v, conv3 (diagSeqT 0 v) = if v = 0 then ddiagSeqT 0 else ddiagSeqT (v + 2)
   ```
   意味: **基準点が合っている** —— BMS の対角の像が、DBMS の対角になる。

   **2-7 整礎性** — どちらも未証明

   ```lean
   BMS 側: Wset.TowerGraft2 ∧ Wset.TowerExp
   DBMS 側: WellFounded RD3        （RD3 x y := ST_D3 x ∧ ST_D3 y ∧ seqlex x y）
   ```
   意味: **無限に小さくなり続けることはない** —— 降下の帰納を回すための根拠。
   `RD3` は「DBMS 標準形の上の辞書式順序」。

   偽である 2-2 / 2-3 を使わない形が用意されている。これらから出る弱い 3 本:

   * **`Inj3 conv3`** : `∀ M N, ST_TS M → ST_TS N → conv3 M = conv3 N → M = N`
     — **変換が単射**。像が同じなら元も同じ。順序とは無関係。
   * **`OrderReindexT3 conv3`** : `(conv3 A)⟦m⟧ = conv3 B` を満たす `B` にだけ相手を限り、
     **DBMS 側の順序から BMS 側の順序を出す**（(←) の向きだけ）。
   * **`SandwichUReindexT3 conv3`** : 同じ制限のもとでの挟み撃ちの上。

   に置き換えた `ST_D3_conv3_of_parts'''` / `ST_D3_conv3_of_parts_D` がある
   （弱化が出ることは Lean で証明ずみ）。この 3 本の真偽は未測定。

3. **3 行 DBMS の対角が「`z` を 1 で頭打ちした形」だと確定した。**
   `ddiagSeqT v = ((j, j-1, min (j-2) 1))_{j=0..v}`。素の `(j, j-1, j-2)` は
   `z ≥ 2` に出るのでこの断片の対角にならない。


# 成果の場所

| ファイル | 内容 |
|---|---|
| `bms2dbms/lean/Dbms3.lean` | 3 行 DBMS の器、`Conv3.conv3` の Lean 実装、7 仮定、主定理、反証 |
| `bms2dbms/lean/lakefile.toml` | `path = "../../lean"` で BMS 側（`trio`）を参照 |
| `bms2dbms/lean/L14Read.lean` | `read3` / `dok` の設計（`OrderT3` の律速） |
| `bms2dbms/lean/H12Probe.lean` | `Dbms3` の作業ファイル |
| `bms2dbms/tools/rows3.py` | Python の `conv3`（正） |
| `bms2dbms/tools/imgfast.py` | `ImgClosedT` の破れを列挙 |
| `bms2dbms/tools/teach.py` | 教師データの生成 |
| `bms2dbms/tools/sheet3.py` | BM4-Analysis シートの読み込み |
| `bms2dbms/tools/core.py` | BMS / DBMS 共通の展開エンジン（対角だけが違う） |
| `bms2dbms/tools/h1/` | `copy_head` 系の道具 |
| `bms2dbms/tools/BRIEF-v14.md` | 現在地と残る的 |
| `bms2dbms/tools/H1-NOTES.md` | 作業ノート（本体） |
| `bms2dbms/tools/NOTES.md`, `R1-NOTES.md` | 同上 |

`leanman build -C bms2dbms/lean` で緑（808 jobs）。
BMS 側（`../lean` の `trio`）に対する依存は一方向で、循環はない。

分岐前から存在するもの（このプロジェクトの成果ではない）:
`Dbms.lean` / `DbmsStd.lean` / `DbmsConv.lean` / `DbmsSheet.lean`（2 行 = `PairSeq` 側）。
そちらの主定理 `DBMS.ST_D_conC_final : ST_PS M → ST_D (conC M)` は仮定なしで証明ずみ。


# 成果の詳細

## 1. 3 行 DBMS の器

BMS と DBMS は**展開規則が完全に同一**で、違うのは標準形の対角だけである。

```
対角 diag[x][y]   BMS: x            DBMS: max(x - y, 0)
```

`z < 2` の断片では、BMS 側の対角は `z` を 1 で頭打ちした
`diagSeqT 0 v = ((j, j, min j 1))_{j=0..v}`。その像を測ると

```
b2d3 (0,0,0)(1,1,1)                = (0,0,0)(1,0,0)(2,1,0)(3,2,1)
b2d3 (0,0,0)(1,1,1)(2,2,1)         = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)
b2d3 (0,0,0)(1,1,1)(2,2,1)(3,3,1)  = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)(5,4,1)
```

なので DBMS 側の対角も **`z` を 1 で頭打ちした**

```lean
def ddiagSeqT (v : ℕ) : TrioSeq   -- ((j, j-1, min (j-2) 1))_{j=0..v}
```

である。素の `(j, j-1, j-2)` は `z ≥ 2` に出るのでこの断片の対角にならない。
頭打ち対角が本物の DBMS 対角の一手展開であることも確認ずみ:
`D5 = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,2)` について `D5⟦n⟧ = ddiagSeqT (n+2)`（`n ≥ 1`）。

対応する順序数:

```
(0,0,0)(1,0,0)                     = w
(0,0,0)(1,0,0)(2,1,0)              = eps_0
(0,0,0)(1,0,0)(2,1,0)(3,2,1)       = psi_0(Omega_w)
```

## 2. 変換に課す 7 つの性質

```lean
def ImgCofinalT3 (conv3) : Prop   -- 像は展開で共終
def OrderT3      (conv3) : Prop   -- translate M <o translate N ↔ seqlex (conv3 M) (conv3 N)
def SandwichUT3  (conv3) : Prop   -- sle3 (conv3 (A⟦n⟧)) ((conv3 A)⟦n+1⟧)
def ImgBlockT3   (conv3) : Prop   -- blockok 0 (conv3 A)
def ImgLenT3     (conv3) : Prop   -- 1 < |A| → 1 < |conv3 A|
def ConvDiagT3   (conv3) : Prop   -- conv3 (diagSeqT 0 v) = ddiagSeqT …
```

に加えて整礎性が 1 本。組み立ては

```lean
theorem ST_D3_conv3_of_parts (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    (hI) (hO) (hU) (hb) (hlen2) (hd) (hM : ST_TS M) : ST_D3 (conv3 M)
```

### 状態

| 性質 | 状態 |
|---|---|
| `ConvDiagT3 Conv3.b2d3` | **証明ずみ**（`ConvDiagT3_b2d3`） |
| `ImgLenT3 Conv3.b2d3` | **証明ずみ**（`ImgLenT3_b2d3`、`conv3_ne_nil` 経由） |
| `ImgBlockT3` | 未 |
| `ImgCofinalT3` | 未 |
| `OrderT3` | **偽**（`len ≤ 11` の 1,882,196 個で両向き各 24 件） |
| `SandwichUT3` | **偽**（`≤7` 列 386,405 対で 8 件、`v≤4 len≤8` で 12 件） |

`OrderT3` が偽になる機構は、**分岐列 `(a,1,0)` の綴りが次の列に依存する**こと
（末尾なら深く `(6,2,0)`、後ろに `(5,1,0)` が来ると浅く `(5,1,0)`）。
41 件中 39 件で縮約は発火していないので、縮約が原因ではない。

## 3. 偽の 2 本を使わない形

`OrderT3` / `SandwichUT3` から出る弱い 3 本に置き換えられる（弱化はいずれも証明ずみ）。

```lean
def Inj3               (conv3) : Prop   -- 単射性（順序と無関係）
def OrderReindexT3     (conv3) : Prop   -- (←) だけ、相手は像の展開の逆像に限る
def OrderReindexT3'    (conv3) : Prop   -- その第 1 成分だけ
def SandwichUReindexT3 (conv3) : Prop   -- 挟み撃ちの上、相手は同上

theorem ST_D3_conv3_of_parts''' (h2) (he)
    (hI : ImgCofinalT3) (hj : Inj3) (hO : OrderReindexT3)
    (hU : SandwichUReindexT3) (hb : ImgBlockT3) (hlen2 : ImgLenT3) (hd : ConvDiagT3)
    (hM : ST_TS M) : ST_D3 (conv3 M)
```

## 4. 循環の切断 —— DBMS 側の整礎性で足りる

`ST_D3_descend` は BMS の整礎性を仮定していたが、`wf` が使われるのは 1 か所だけで、
再帰の根拠は `translate B <o translate A` である。`B` は `(conv3 A)⟦m⟧ = conv3 B` を
満たすので、DBMS 側では `conv3 B` が `conv3 A` の基本列の元になる。そこで整礎性を
**DBMS の `seqlex`** で取り、`InvImage` で `A` の帰納に載せ替える。

```lean
def RD3 : TrioSeq → TrioSeq → Prop        -- BMS 側 (ST_TS, translate <o) の DBMS 版

theorem ST_D3_conv3_D (wfD : WellFounded RD3) (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3)
    (hM : ST_TS M) : ST_D3 (conv3 M)
theorem ST_D3_conv3_of_parts_D (wfD : WellFounded RD3)
    (hI : ImgCofinalT3) (hj : Inj3) (hO : OrderReindexT3') (hU : SandwichUReindexT3)
    (hb : ImgBlockT3) (hlen2 : ImgLenT3) (hd : ConvDiagT3) (hM : ST_TS M) : ST_D3 (conv3 M)
```

副産物として、再帰の根拠の 3 つ目 `seqlex (conv3 B) (conv3 A)` は
`ImgBlockT3 ＋ ImgLenT3` から `seqlex_oper` で出るので、
**`OrderReindexT3` の第 2 成分が仮定から消える**。
`translateD` も DBMS 版 `m_step_decreases` も DBMS 版 `trio_cofinality` も要らない。

## 5. DBMS の停止性から BMS の停止性へ

`ReindexT1D` は `(conv3 B_i)⟦m⟧ = conv3 B_{i+1}` を**等式で**与えるので、DBMS 側の列は
定義から展開列になる。よって `conv3` の順序は一度も登場しない。無限降下列を作らず、
`Acc` の入れ子で直に書ける。

```lean
theorem acc_olt_of_accD (H : ReindexT1D conv3) :
    ∀ C, Acc RD3 C → ∀ A, ST_TS A → ST_D3 (conv3 A) → conv3 A = C →
      Acc (fun a b => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) A
theorem wf_olt_ST_TS_of_dbms (wfD : WellFounded RD3) (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3) :
    WellFounded (fun a b => ST_TS a ∧ ST_TS b ∧ translate a <o translate b)
theorem TRIO_terminates_of_dbms_wf (wfD : WellFounded RD3) (H) (hd) : WellFounded stepRel
theorem TRIO_terminates_of_dbms_wf_parts (wfD : WellFounded RD3)
    (hI) (hj) (hO : OrderReindexT3') (hU) (hb) (hlen2) (hd) : WellFounded stepRel
theorem no_infinite_expansion_of_dbms_wf (wfD) (H) (hd) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1))
```

`Final.lean` の残核（`TowerGraft2` / `TowerExp`）を一切使わない。

## 6. `ImgClosedT3` の `ImgCofinalT3` への弱化

`ReindexT1_of_block` が `ImgClosedT3` から実際に使うのは `m := n + 1` ただ 1 つである。
よって「すべての `m` で逆像がある」は要らず、「いくらでも大きい `m` で逆像がある」で足りる。
差は `oper` の展開指数の単調性で埋まる（`../lean/Cofidx.lean`、前提なし）。

```lean
theorem oper_succ_append (M) (n) : ∃ R, M⟦n + 1⟧ = M⟦n⟧ ++ R
theorem oper_le_append (h : j ≤ k) : ∃ R, M⟦k⟧ = M⟦j⟧ ++ R
theorem oper_mono_idx  (h : j ≤ k) : …
```

## 7. 変換器 `conv3` の実装

Python（`bms2dbms/tools/rows3.py`）と Lean（`Dbms3.lean` §8 `Conv3.conv3`）の両方にある。
Lean 版は Python の v14 h1 相当（`copy_head` 系 5 条項を含む）で、`#guard` 461 本、`sorry` 0。

BMS の展開は「悪い部分を上昇させて写す」。上昇は行 0 に効くので、もとの根 `(0,0,0)` は
写しの中で `(k,0,0)` になる。写しをもう一度写せばその親もまた `(k',0,0)`。したがって

```
copy_head(Mo, j) ⟺ Mo[j] が (k,0,0)（k ≥ 1）で、行 0 の親をたどると
                    根 (0,*,*) まで「x w」の柱（とアンカー）だけで届く
```

これは `Mo` と添字だけで決まるので**写しに同変**である。この `copy_head` を軸に、
写しに同変でなかった 5 つの道具を直した:

```
term_top     項の頭 = 根 / アンカー (1,1,0) / 根の写し (k,0,0) / アンカーの写し (k,1,0)
closes_top   closes_unit の写し版
hi_block2    hi_block の起点を「写しの頭の次の柱」まで進める
wch_chead    wchain の鎖は写しの頭で切れる
p0deep       prev == 0 の枝の深さ判定
```

写しの頭が 1 本も無い行列ではすべて元の定義に戻るので、`≤6` 列（8,387 個）では像が
1 つも変わらず、**7 列で初めて 18 個が変わる**。その 18 個には `#guard` がある。

### 成績

| 土俵 | v13 | v14 h1 |
|---|--:|--:|
| BM4-Analysis シート（正しい 1354 行） | 1354 | **1354** |
| 非標準 / 順序 / 交差衝突 / z0 / `d2b3` 往復 | 0 | **0** |
| `SandwichU`（要件 C2） | 0 | **0** |
| `ImgClosedT` の破れ（`≤5` 列） | 4 | **2** |
| `ImgClosedT` の破れ（`≤6` 列） | 87 | **54** |
| 教師データの外れ（`≤7` 列 49,781 本） | 2,715 | **123** |

教師データの検算: ラベル付き 62,714 本 → 相異なるサイト 44,800 個。
**シートの正解と `ImgClosedT` の目標が矛盾する例は 0 件**。
誤りの向きは（浅い → 深い）3,032 本、（深い → 浅い）0 本。

### 残る的（`BRIEF-v14.md` 追記 5）

1. **族 β（A1 / A2）**: `conv3(A⟦n⟧)` が余分な影の写しを出し、長さが揃わない。

   ```
   A1 = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(1,1,1)
   A2 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)     （シート行 300、conv3 A2 は正しい）
   ```

   `f(A)⟦m⟧` は `f(A⟦m+1⟧)` から写しを何組か抜いたものになる。母集団 25,158 対
   （標準形 8,386 個 × `m ∈ {2,3,4}`）で、長さが一致する族 α は 16.21% で
   **そのすべてが完全一致**。族 β は 83.79% で、そのうち **99.79% が部分列**。
   抜けるのは 1 区間が 99.29%、長さ `< |f(A)|` が 99.97%。
   A1 は `[(7, 5)]` が `m = 2..5` で一定、A2 は開始が等差 5（= `|f(A2)|`）で
   長さ 2 が `m-1` 個 ＋ 末尾 7 が 1 個。

2. **`after_w/shallow` の誤り**: `≤6` 列 × `m ≤ 6` で 5 本、`≤7` 列 × `m ≤ 4` で 63 本。
   直前の柱はどれも写しの頭ではないので `copy_head` では分けられない。

3. **`prev0` の残り**: `≤7` 列 × `m ≤ 4` で 24 本。`nxt = (p0-1,1,0)` か `(p0-1,1,1)`。

## 8. 反証（Lean で緑）

```lean
example : ¬ ResidHeadT
example : ¬ ResidHeadT'
example : ¬ ResidSideT
example : ¬ DmapInT
```

`ImgBlockT3_of_resid` は `DmapInT ＋ ResidSideT` を仮定するので空虚。
`ResidHeadT` を仮定する `dm10_aux` / `dm10_holds` / `dm10_at_U` / `dmST_step` も同様。

いずれも「`st'` を無制限に全称化していて `rest` と結ぶものが無い」という同じ形で、
`st'.dmap = []`, `m = 0`, `rest = [(5,0,0)]` のとき `Dm10 (d+1) 0 st'` が
`j < 0` で空虚に真になり、結論が `5 ≤ 0` になる。off-by-one を直した形（`5 ≤ 1`）でも、
`dmap ≠ []` を足した形（`5 ≤ 2`）でも偽。

制限版は仮定ゼロで証明ずみ:

```lean
theorem ResidSideR / DmapInR
theorem steps1_head_le_getLast   -- steps1 (U ++ rest) ⟹ (rest.headI).1 ≤ (U.getLast).1 + 1
theorem ResidHeadR               -- ResidHeadT の正しい制限版（st' を直前ブロック U の出力で書く）
theorem residHeadR_of_dmLenLo    -- DmLenLo ⟹ ResidHeadR
```

残る中身は `DmLenLo : (M.getLast).1 ≤ |(conv3 M …).2.dmap|`。
機構は `|st1.dmap| = min p.1 |st.dmap| + 1` なので、最後に処理した柱の深さ `q.1` に対して
`|res.dmap| = q.1 + 1` になるはず、というもの。

## 9. 逆写像

`d2b3`（DBMS → BMS）は `m ≥ 2` で全滅する。往復（`d2b3 ∘ b2d3`）は 0 破れ。
