# 成果の概略

1. **3 行トリオ数列（BM4 の `z ≤ 1` 断片）の停止性が、未証明の閉包命題 1 本に還元された。**
   `WellFounded stepRel` は `Wset.TowerExp` 1 本、または `L105.MTowerClosedS` 1 本から出る。
   分岐時点では `TowerGraft2` と `TowerExp` の 2 本が必要だった。差を埋めたのは
   `TowerGraft2Single`（`TowerGraft2` を `|R| = 1` に落とした形）が定理であること。
   残る 1 本は未証明なので、停止性はいずれも条件つきの形でしか出ていない。

2. **その 1 本に十数通りの十分条件が与えられ、含意関係がすべて Lean で証明された。**
   `TowerOK` / `LiftTie` / `LiftTieSelf` / `LiftTieCore` / `LiftTieCoreRow2` /
   `WConvexLift1` / `MliftR` / `Row1DownLocal ∧ Row1DownRoot0` / `TowerExpBigRow2` /
   `MTowerClosedS` / `MTowerClosedRow2` のいずれからも `WellFounded stepRel` が出る。

3. **`MTowerClosedS` は「根の行 0 が 0」に制限してよく、さらに「塔に 1 列 snoc する」1 手に還元される。**
   その 1 手について、辞書式測度 `(|Q|, e, d)` の整礎帰納の枠と、
   `oper` の場合分けを測度の減少に変換する部品が揃っている。

4. **`Lift1`（行 1 の錐つき持ち上げ）と `oper`（展開）の可換性について、
   成立する境界が定まった。** `(Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t` は一般には偽で、
   悪根が根でない（`parent ≠ 0`）ときに成り立つ。悪根が根のときは右辺が `glift` になる。


# 成果の場所

| ファイル | 内容 |
|---|---|
| `lean/Final.lean` | 停止性の入口。`TRIO_terminates_of_*` が全部ここに並ぶ |
| `lean/L105Cap.lean` | `TowerExp` への集約、`MTowerClosedS` とその `Based` 版（§77.5）、`TowerGraft2Single` |
| `lean/L106.lean` | `TowerSnocStep(Based)` への還元、辞書式測度、`oper` の場合分けの部品 |
| `lean/H12Export.lean` | 塔の構造補題（親の位置、窓の上界、`Lift1` の不変量） |
| `lean/H12H2.lean` | 同上の作業ファイル |
| `lean/L53Subst.lean` | `LiftTie` への置換補題、`MliftR` / `Row1Down` 経路 |
| `lean/L51Tower.lean` | 一般塔 `gTower Q e d n` と `(e,d)` による分類 |
| `lean/Cofidx.lean` | `oper` の展開指数についての単調性（`oper_mono_idx`） |
| `lean/CORES.md` | 核の一覧と、各核の強さ・依存関係 |
| `lean/LEMMA-INDEX.tsv` | 全補題の索引 |
| `tools/` | 測定スクリプト（338 本） |

すべて `leanman build -C lean` で緑（807 jobs、warning 0）。


# 成果の詳細

## 1. 停止性の還元先

```lean
theorem TRIO_terminates_of_towerExp (he : Wset.TowerExp) : WellFounded stepRel
theorem TRIO_terminates_of_mTowerClosedS (htow : L105.MTowerClosedS) : WellFounded stepRel
```

いずれも `Final.lean`。経路は

```
仮定 ⟹ Wstar2s（または Wstar）の Aop 閉性
     ⟹ Wset.wf_olt_ST_TS_of_cofinality（trio_cofinality は無条件）
     ⟹ WellFounded (ST_TS 上の translate <o)
     ⟹ wf_Rnf_of_wf_TS ⟹ step_terminates
```

`trio_cofinality`（`Core.lean:4602`）は仮定なしの定理なので、
残っているのは閉性の 1 本だけである。

`TowerExp`（`Wset.lean:4507`）:

```lean
def TowerExp : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) →
    hasParent ((0, v, z) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → ((0, v, z) :: R)⟦n⟧ ∈ W a
```

意味: **根 `(0,v,z)` の上に「良い引数 `R`」を載せた行列を展開しても、まだ良いまま**。
「良い引数」とは、全列の行 0 が正（`argOK`）で、末尾に親があり（`hasParent`）、
`R` 自身のどの展開も `Wstar` にいるもの。`W a` は段 `a` の良い行列の集合で、
`2v + z ≤ a` が段の条件。

`MTowerClosedS`（`L105Cap.lean:5622`）は 5 量化 / 2 前提:

```lean
def MTowerClosedS : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    mTower Q d e n ∈ W u
```

意味: **良い行列 `Q` から塔を積んでも、良いまま**。
`mTower Q d e n` は `Q` を `n` 段積んだもので、段が上がるごとに行 0 を `+d`、
行 1 を根の錐の中だけ `+e` する。2 番目の前提は「`Q` の根が行 0 で狭義にいちばん浅い」。

## 2. 入口の一覧（`Final.lean`）

| 仮定 | 定理 |
|---|---|
| `Wset.TowerExp` | `TRIO_terminates_of_towerExp` |
| `Wset.TowerOK` | `TRIO_terminates_of_towerOK` |
| `L53.LiftTie` ＋ `TowerExp` | `TRIO_terminates_of_liftTie` |
| `L105.LiftTieSelf` ＋ `TowerExp` | `TRIO_terminates_of_liftTieSelf` |
| `L105.LiftTieCore` ＋ `TowerExp` | `TRIO_terminates_of_liftTieCore` |
| `L105.LiftTieCoreRow2` ＋ `TowerExp` | `TRIO_terminates_of_liftTieCoreRow2` |
| `L105.WConvexLift1` ＋ `TowerExp` | `TRIO_terminates_of_convexLift1` |
| `L53.MliftR` ＋ `TowerExp` | `TRIO_terminates_of_mliftR` |
| `L53.MliftR` ＋ `L53.GraftFromExp` | `TRIO_terminates_of_mliftR_graft` |
| `L53.Row1DownLocal` ＋ `Row1DownRoot0` ＋ `TowerExp` | `TRIO_terminates_of_row1down` |
| `L105.TowerExpBigRow2` | `TRIO_terminates_of_towerExpBigRow2` |
| `L105.MTowerClosedS` | `TRIO_terminates_of_mTowerClosedS` |
| `L105.MTowerClosedRow2` | `TRIO_terminates_of_mTowerClosedRow2` |

`LiftTie` と `LiftTieSelf` は同値（`R2LT.lean` の `liftTie_iff_liftTieSelf`）。

## 3. `MTowerClosedS` の内部構造

### 3.1 `based` への制限（`L105Cap.lean` §77.5）

`MTowerClosedS` の 2 つの消費者（`liftTower1_of_shiftTowerClosedS` と
`liftTowerExp2_of_mTowerClosedS`）に渡る `Q` は、どちらも
`Lift1 ((0, v, z) :: R.dropLast) t` の形で、`entry Q 0 0 = 0` を満たす。したがって

```lean
def MTowerClosedBased : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    entry Q 0 0 = 0 → mTower Q d e n ∈ W u

theorem wstar2s_closed_of_mTowerClosedBased (htow : MTowerClosedBased) :
    ∀ u0 R, Aop W u0 Wstar2s R → R ∈ Wstar2s
```

意味: **`MTowerClosedS` を「根の行 0 がちょうど 0 の `Q`」に限ってよい**。
本線に出てくる `Q` はもともとその形なので、制限しても `Final` まで届く。
`W` の行 0 の**下**シフト閉性は不要である
（`W_shift`（`Wset.lean:1320`）が言うのは上シフトだけ）。

### 3.2 snoc 1 手への還元（`L106.lean` §307/§308）

```lean
theorem mTowerClosedS_of_towerSnocStep (h : TowerSnocStep) : L105.MTowerClosedS
theorem mTowerClosedBased_of_towerSnocStepBased (h : TowerSnocStepBased) :
    L105.MTowerClosedBased
```

意味: **「塔全体が良い」を「塔に 1 列足しても良いまま」1 手に落とせる**。
`TowerSnocStep(Based)` は「塔 ＋ ブロックの `take j`」が `W u` にいるとき、
そこに `take (j+1)` の 1 列を snoc しても `W u` にいる、という命題。
証明は `L105Cap.prefixTowerClosed_of_snocStepPar` を接頭辞 `A = []` で流したもの。
その中で、snoc する列が孤児（`¬ hasParent`）の場合は `snoc_orphan_W` が引き取るので、
`TowerSnocStep` には**親を持つ列だけ**が渡る。

### 3.3 辞書式測度（`L106.lean` §314–§317）

```lean
def lexMeas (Q : TrioSeq) (e d : ℕ) : ℕ × ℕ × ℕ := (Q.length, e, d)
def LexLt : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
theorem lexLt_wf : WellFounded LexLt

def MTowerClosedAt (u : ℕ) (Q : TrioSeq) (e d : ℕ) : Prop :=
  Q ∈ W u → (根が狭義に最浅) → entry Q 0 0 = 0 → ∀ n, mTower Q d e n ∈ W u

theorem mTowerClosedBased_of_at (h : ∀ u Q e d, MTowerClosedAt u Q e d) :
    L105.MTowerClosedBased
theorem mTowerClosedBased_of_lexStep (u : ℕ)
    (hstep : ∀ Q e d, (∀ 小さい測度で MTowerClosedAt) → MTowerClosedAt u Q e d) :
    ∀ Q e d, MTowerClosedAt u Q e d
```

場合分けを測度の減少に変換する部品（すべて前提なし）:

```lean
theorem lexLt_of_fst / lexLt_of_snd / lexLt_of_trd
theorem lexLt_of_cases      -- 3 択をそのまま場合分けに
theorem lexLt_of_srow_zero  -- srow = 0 ⟹ (e', d') = (0, 0)、d > 0 なら減る
theorem lexLt_of_srow_one   -- srow = 1 ∧ e > 0 ⟹ e' = 0 < e
theorem lexLt_of_window     -- |V| < |Q| なら (e', d') に依らず減る
theorem window_lt_of_offset_pos {L n c} (hn : 0 < n)
    (hge : (n - 1) * L < c) (hlt : c < n * L) : n * L - c < L
theorem lexLt_of_offset_pos
```

意味: **測度 `(|Q|, e, d)` は自然数 3 つ組の辞書式順序なので整礎**（`lexLt_wf`）。
`MTowerClosedAt u Q e d` は `MTowerClosedBased` を `(Q, e, d)` ごとに切ったもので、
`mTowerClosedBased_of_lexStep` は「測度がより小さいものすべてで成り立つと仮定して
`(Q, e, d)` で示せ」という形に変える。`lexLt_of_*` は、`oper` の場合分けの結果
（`srow` の値、窓の長さ）から測度の減少を作る部品。
`window_lt_of_offset_pos` は「親のブロック内オフセットが 1 以上なら窓は `|Q|` 未満」
という算術（`窓 = |Q| - オフセット`）。

### 3.4 `oper` の 2 つの `if` から出る等式（`L106.lean` §309/§311、前提なし）

`oper` の新しい段差は `d' := if 0 < srow then … else 0`、`e' := if 1 < srow then … else 0`。
したがって

```lean
theorem oper_d0_eq_zero_of_srow_zero (h : srow M t = 0) : (新しい d) = 0
theorem oper_de_of_srow_zero        (h : srow M t = 0) : (新しい d) = 0 ∧ (新しい e) = 0
theorem oper_d1_eq_zero_of_srow_le_one (h : srow M t ≤ 1) : (新しい e) = 0
```

### 3.5 「最小なら孤児」（`L106.lean` §309/§310/§312、前提なし）

```lean
theorem no_parent_of_shallowest (hmin : ∀ c < t, entry M 0 t ≤ entry M 0 c) (i : ℕ) :
    ¬ hasParent M i t
theorem no_parent1_of_row1_min (hmin : ∀ c < t, entry M 1 t ≤ entry M 1 c) : ¬ hasParent M 1 t
theorem no_parent2_of_row2_min                                              : ¬ hasParent M 2 t
theorem no_parent2_of_row1_min                                              : ¬ hasParent M 2 t
theorem no_parent_of_srow_min      -- srow が何であれ、その行で最小なら孤児
theorem no_parent_ge_one_of_row1_min (hi : 1 ≤ i)                           : ¬ hasParent M i t
```

意味: **ある行で（弱く）最小の列は、その行で親を持てない**。
行 0 で最浅なら `nextrel0`（狭義の不等号）が張れず、`nextrel1` / `nextrel2` は
どちらも `le0` を含むので張れない、というのが `no_parent_of_shallowest` の内容。
親を持たない列（孤児）は `snoc_orphan_W` が無料で引き取るので、この形の補題は
そのまま「この場合は考えなくてよい」に使える。

### 3.6 行 2 の親の必要十分条件（`L106.lean` §303/§304）

`z ≤ 1` の下で、行 2 の親は「錐の中の `z = 0` の列」と同値:

```lean
theorem hasParent2_iff_zero_in_cone (hz) (ht) (ht1 : entry M 2 t = 1) :
    hasParent M 2 t ↔ ∃ c, c < t ∧ entry M 2 c = 0 ∧ le1 M c t
theorem hasParent2_mTower_iff / row2_zero_mTower_iff / zle1_mTower   -- 塔への持ち込み
```

また行 2 が定数なら塔は無条件に閉じる:

```lean
theorem mTowerClosedS_of_nonconst (h : MTowerClosedNonconst) : L105.MTowerClosedS
theorem constRow2_oper (h : ∀ p ∈ M, p.2.2 = c) (n) : ∀ p ∈ M⟦n⟧, p.2.2 = c
```

## 4. 塔の構造補題（`H12Export.lean`）

`mTower Q d e n` の第 `n` ブロックの根を `t`、その行 0 の親を `c0` とする。

```lean
theorem blockRoot_shallow_mTower           -- d > 0 ⟹ ブロック根はそこから先の全列より狭義に浅い
theorem nextrel0_blockRoot_src_ge_prev     -- d > 0 ⟹ 行 0 の親は (n-1)|Q| 以降
theorem nextrel0_blockRoot_in_prev_block   -- d > 0 ∧ n > 0 ⟹ (n-1)|Q| ≤ c0 < n|Q|
theorem nextrel0_src_ge_blockRoot_mTower   -- ブロック内部が的なら親は同じブロックの中
theorem window_le_of_blockRoot             -- 窓 ≤ |Q|
theorem window_lt_of_blockInner            -- 窓 < |Q|
theorem no_nextrel0_blockRoot_of_d_zero    -- d = 0 ⟹ ブロック根に行 0 の親は無い
theorem no_nextrel2_blockRoot_of_gap       -- d ≤ 段差 ⟹ ブロック根に行 2 の親は無い
theorem no_nextrel1_blockRoot_of_gap       -- d ≤ 段差 ∧ e = 0 ⟹ 行 1 の親も無い
theorem no_hasParent_blockRoot_of_gap      -- 上の 2 つを合わせて i ≥ 1 で孤児
theorem le0_ancestor_blockRoot             -- d ≤ 段差 ⟹ ブロック根の le0 祖先は前のブロック根だけ
```

ここで `段差 := min_{i ≥ 1} (entry Q 0 i - entry Q 0 0)`（`Q` の根と、根以外の列との
行 0 の差の最小値）。`d ≤ 段差` は「塔の段差が `Q` の内部の凹凸より浅い」という条件で、
このとき塔のブロック根の親はちょうど 1 つ前のブロック根になる。

行 1 / 行 2 の親については、`nextrel1` の源が `le0` 祖先、`nextrel2` の源が `le1` 祖先である
ことを使って、行 0 の結果から移す:

```lean
theorem nextrel1_src_ge_of_row0_parent_low   -- 行 0 の親 c0 の行 1 が的より低い ⟹ 行 1 の親は c0 以降
theorem nextrel2_src_ge_of_le1_ancestor_low  -- le1 祖先 x の行 2 が的より低い ⟹ 行 2 の親は x 以降
theorem src_ge_of_ancestor_low               -- 行 1 版・行 2 版を 1 本に
theorem nextrel1_src_ge_prev_of_low_ancestor -- 直前ブロックに低い le0 祖先があれば親も直前ブロック内
theorem nextrel1_blockRoot_src_ge_prev       -- d > 0 ∧ e > 0 ⟹ 行 1 の親も (n-1)|Q| 以降
theorem nextrel2_blockRoot_src_ge_prev       -- e > 0 ⟹ 行 2 の親も同様
theorem window_le_of_blockRoot_row1 / window_lt_of_blockRoot_row1_gap / window_le_of_low_ancestor
```

意味: **行 1 / 行 2 の親の位置は、行 0 の親の位置から移せる**。
`nextrel1` の源は `le0` 祖先、`nextrel2` の源は `le1` 祖先なので、
「行 0 の親（または `le1` 祖先）が的より低ければ、それが最小性の候補になり、
親はそれ以降にしか来られない」という形で下界が得られる。

`nextrel1 M j0 j1` の最小性条項は `∀ j, j0 < j ∧ le0 M j j1 → entry M 1 j1 ≤ entry M 1 j`
であり、これは「`j0` は行 1 が的より小さい `le0` 祖先のうち**添字が最大**のもの」を意味する。

## 5. `Lift1` と `oper` の可換性（`H12Export.lean`）

```lean
theorem lift_oper_comm_of_hr0
    (hL : M.length - 1 ≠ 0) (hz : ¬ 末尾が全零) (hpM : hasParent M (srow …) …)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hj0pos : 0 < parent M (srow M (M.length - 1)) (M.length - 1)) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t
theorem lift_oper_comm_of_hr0_full   -- 写しを作らない 3 分岐も込み
theorem lift_oper_comm_of_no_copy    -- |M| ≤ 1 ∨ 末尾が全零 ∨ 末尾に親が無い ⟹ 可換
theorem zeroLast_Lift1_iff           -- 全零テストは Lift1 で保たれる
```

一般には偽で、最小の反例は `M = (0,0,0)(1,0,0)`、`t = 1`、`n = 2`:
`(Lift1 M 1)⟦2⟧ = (0,1,0)(0,1,0)` に対し `Lift1 (M⟦2⟧) 1 = (0,1,0)(0,0,0)`。
悪根が根（`parent = 0`）のときは `Wset.oper_Lift1_root`（`Wset.lean:3384`）が
右辺を `glift M (|M|-1) 0 t (M⟦n⟧)` にする。

`Lift1` が足すのは行 1 だけで、行 0 と行 2 は動かない（`Wset.lean:927`）。

## 6. `Lift1` / `shiftr01` の不変量（`H12Export.lean`）

```lean
theorem oper_inputs_Lift1_invariant   -- oper の入力 10 成分が Lift1 で不変
theorem wd0_Lift1_invariant / wd1_Lift1_invariant
theorem Lift1_dropLast : Lift1 X.dropLast d = (Lift1 X d).dropLast
theorem cone_of_le1_to_cone / rtg0_ancestor_split / rtg1_ancestor_split
theorem le1_append_left / le0_append_left / cone_prefix_stable / cone0_prefix_stable
```

`段差` は `Lift1 ∘ shiftr01` で不変（`shiftr01` は行 0 に定数を足すだけで差が相殺し、
`Lift1` は行 0 を触らない）。

## 7. 塔の `oper` の形（`H12Export.lean`）

```lean
theorem oper_mTower_eq_dropLast   -- 塔の末尾が孤児なら (mTower Q d e n)⟦m⟧ = dropLast
theorem dropLast_mTower_succ
    : (mTower Q d e (n+1)).dropLast = mTower Q d e n ++ (最後のブロック).dropLast
theorem entry0_mTower_last_pos    -- 末尾の行 0 は正（全零テストを外せる）
```

## 8. 一般塔の分類（`L51Tower.lean`）

シートのラダーで最初に落ちる 3 行は、どれも `Q = (0,0,0)(1,1,1)` の一般塔
`gTower Q e d n` で、違うのは `(e, d)` だけである。

| 行 | 行列 | 対応 | `(e, d)` |
|---|---|---|---|
| 275 | `(0,0,0)(1,1,1)(1,0,0)` | `psi(W_w) * w` | `(0, 0)` |
| 284 | `(0,0,0)(1,1,1)(1,1,0)` | `psi(W_w + W)` | `(1, 0)` |
| 316 | `(0,0,0)(1,1,1)(1,1,1)` | `psi(W_w * 2)` | `(1, 1)` |

`(e, d) = (0, 0)` は `Wset.W_flatMap_copies` で既に取れている。

## 9. `TowerGraft2` の縮小（`L105Cap.lean` §37/§38）

```lean
theorem towerGraft2Single_of_towerGraft2 (h : TowerGraft2) : TowerGraft2Single
theorem towerOK_of_exp (he : TowerExp) (h1 : TowerGraft2Single) : TowerOK
theorem towerOK_of_towerExp (he : TowerExp) : TowerOK
```

`TowerGraft2` は `|R| = 1` の場合（`TowerGraft2Single`）だけになり、それが定理なので
`TowerExp` 1 本が残る。

## 10. `oper` の展開指数の単調性（`Cofidx.lean`、前提なし）

```lean
theorem oper_succ_append (M : TrioSeq) (n : ℕ) : ∃ R, M⟦n + 1⟧ = M⟦n⟧ ++ R
theorem oper_le_append  (h : j ≤ k) : ∃ R, M⟦k⟧ = M⟦j⟧ ++ R
theorem oper_mono_idx   (h : j ≤ k) : …
```

`oper` の定義が `M.take j0 ++ (List.range n).flatMap g` の形をしていることから出る。
`bms2dbms` 側で `ImgClosedT3` を `ImgCofinalT3` に弱めるために使う。
