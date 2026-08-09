# trio / PROOF-STATUS (authoritative)

3 行バシク（BM4, `z<2` 断片）の停止性 Lean 形式化の現状。
`GRAFTALL-PLAN.md` は 3700 行の設計ログなので、**現状はこの文書を見る**。

- build: 800 jobs 緑 / **自前 40850 行に `sorry` 0**（取り込んだ `Pair/` 込み） /
  全 top-level の axioms = `[propext, Classical.choice, Quot.sound]`
- 取り込んだ `YAPSS.PSS_terminates_unconditional` も trio のビルド内で axioms clean
- 主目標: `Final.TRIO_terminates_of_revive_self`
- 残核を Lean 抜きで読める形にしたもの: **`RESIDUE-PROBLEM.md`**

## 1. 残核はただ 1 本（段量詞なし）

```lean
Final.TRIO_terminates_of_revive_self : Subst1gReviveSelf → WellFounded stepRel
Final.no_infinite_expansion_of_revive_self : Subst1gReviveSelf → ¬ ∃ 無限展開列
```

```
Wself := {M | M ∈ W (lev M 0)}                        -- 段は根のレベルで決まる

Subst1gReviveSelf :
  S ∈ Wself → p < |S| → C ≠ [] → C ∈ Wself → lev C 0 ≤ lev S p →
  entry C 0 0 = entry S 0 p →            -- ブロックの根はその列と同じ深さ
  (∀ q ∈ C, entry S 0 p ≤ q.1) →         -- 他の列はそれ以上の深さ（非厳格）
  R := S.take p ++ C ++ S.drop (p+1) の末尾列が R では親を持つ →
  かつ その列が自分のブロック内（D=[] なら C、そうでなければ D）では孤児 →
  R.dropLast に行 2 > 0 の列がある →       -- 行 2 ≡ 0 なら無料（snoc_zeroRow2）
  R ∈ Wself
```

**意味**: 「`W` 元の 1 列の下に `W` ブロックを吊るしてよい」を、**文脈が
ブロック内の孤児を復活させる場合**に限ったもの。`Aop` の節 3
（末尾列に段 `lev-1` のブロックを graft）と比べた差は **ブロックの段が
`lev-1` か `lev` か**の 1 点だけ（GRAFTALL-PLAN 4.002）。

## 2. 核から目標までの鎖（すべて Lean 済み）

```
Subst1gReviveSelf
  --subst1gRevive_of_self-->  Subst1gRevive        （mem_Wself_iff で段を復元）
  --subst1g_of_revive------>  Subst1g              （mirror / orphan / 端置換）
  --substClosedG_of_subst1g→  SubstClosedG
       ├── shiftTowerClosedS_of_substG → ShiftTowerClosedS = (TOW)
       │      └── liftStageParented_of_tower → liftStage_of_parented → (WL) LiftStage
       ├── cons_mem_W_of_substG          → TowerExp の m < a 枝
       └── substClosed_of_substClosedG   → SubstClosed
              └── towerExp2Root_of_subst (+ (WL)) → TowerExp2Root
                     └── towerExp2Low_of_root     → TowerExp2Low
  --towerExp_of_substG----->  Wset.TowerExp
  --TRIO_terminates_of_tower→ WellFounded stepRel
```

* **ペア数列の停止性は内部で解消済み**。lean-yapss 11 モジュールを `lean/Pair/`
  に取り込み、`Pair/Bridge.lean` の `emb` で橋渡し。`TowerExp2Root` の `|R| = 1`
  基底 `diag_mem_W`（`z=0`）と二列定理 `two_col_mem_W` で使う。
* **`z = 0` 断片は完全に済んでいる**（`zeroRow2_mem_Wself`）。yapss の無条件
  `mem_W_maxr1` ＋ `W_root_stage` で、行 2 が恒等的に 0 の trio 列は無条件に
  `Wself`。trio の難所は**行 2 の列だけ**にある。
* **`(CAT)` は消えた**（v0.118.122）。旧経路 `TRIO_terminates_of_cat_*` /
  `TRIO_terminates_of_snoc` も生きているが、こちらが広い。

## 3. `W` の構造定理（この階層は見かけより単純）

| 定理 | 内容 |
|---|---|
| `Wset.lev_root_le_of_mem_W` | `M ∈ W u → lev M 0 ≤ u` |
| `Wset.W_root_stage` | `M ∈ W u → M ≠ [] → M ∈ W (lev M 0)` — **段はちょうど根のレベル** |
| `mem_Wself_iff` | `M ∈ W u ↔ M ∈ Wself ∧ lev M 0 ≤ u` — 添字族は 1 集合＋側条件に潰れる |
| `Wset.W_take` / `W_dropLast` | 接頭辞閉 |
| `W_drop` | `M ∈ W u → M.drop j ∈ W (lev M j)` — **接尾辞閉**（接尾辞自身の根レベルで） |
| `W_segment` | 任意の連続区間で閉じる |
| `Wset.oper_one_eq_dropLast` | `M⟦1⟧ = M.dropLast`（1 コピーは剥離） |
| `Wset.oper_prefix_of_le` | `n' ≤ n → M⟦n'⟧ は M⟦n⟧ の接頭辞` — `oper` はコピー数について単調 |
| `Wset.W_oper_mono` | 大きい `n` での所属は小さい `n` でも成り立つ（接頭辞閉から） |
| `zeroRow2_mem_Wself` | **行 2 が恒等的に 0 の列は全部 `Wself`** — ペア定理そのもの |
| `snoc_zeroRow2` | **行 2 ≡ 0 のブロックの末尾に任意の 1 列を継いでよい** — `oper` は末尾列をコピーせず行 2 も増やさないので展開が行 2 ≡ 0 のまま |
| `snoc_orphan` | 孤児のままの 1 列を継ぐのは無料（`oper` が剥がす）⟹ `(LOW)` の孤児半分が落ちる（`lowerLast_of_parented`）|
| `dropLast_mem_Wself` | `Wself` は末尾除去で閉じる |
| `two_col_mem_W` | `[(0,v,z), t] ∈ W a`（`2v+z ≤ a`、`t` は**任意**）— `snoc_zeroRow2` の `|M'| = 1` |
| `Wset.W_shiftl0` | `M ∈ W u → 全列が深さ ≥ d → shiftl0 d M ∈ W u` — **`W_shift` の逆向き**（再基底化） |
| `drop_rebase_mem_W` | 部分木を深さ 0 に戻すと `based` な `W (lev M j)` 元（節 3 の graft 引数の形） |
| `Wtower2.coneV_of_le1` | **`le1` 錐 ⊆ `amin` 錐**（無条件、`1 ≤` 根の行 1）— BM4 の添字マスクは値マスクに収まる |
| `Wtower2.Lift1_eq_mlift_of_tieFree` | タイが無ければ根リフト `Lift1` ＝ 証明済みのマスクリフト `mlift` |
| `Wtower2.liftStage_of_tieFree` | **(WL) はタイのない根の上では核なしで成立**（`mlift_mem_W` 経由） |
| **`Wslift.ulift_mem_W`** | **(ULIFT): 行 1 の一様シフトは `W` を `+2d` で運ぶ** — `Stair.zero` を使わない新法則 |
| `Wtower2.Lift1_eq_shiftr1_of_window` | 根が行 1 でも狭義最小なら `Lift1` ＝ 一様シフト（`le1_zero_iff`） |
| **`Wtower2.liftStage_of_window`** | **★★ (WL) は行 1 の窓があれば核なしで成立**（`v0 = 0` でも可） |
| **`Wtower2.Row1Mono` / `liftStage_of_row1mono`** | **★★★ (WL) はマスク一致を使わず `(ROW1MONO)`（`W a` は行 1 の引き下げで閉じる）から出る** |
| **`Final.TRIO_terminates_of_row1mono`** | **`Row1Mono → TowerExp → WellFounded stepRel`**（axioms clean） |
| **`Wtower2.flat_mem_W`** | **深さを全部 0 に潰した列は無条件に `W a`**（`nextrel0` が空 ⟹ 全列孤児 ⟹ 展開は `dropLast`） |
| ⚠ `Wtower2.Row0Free` / `Final.TRIO_terminates_of_row0free` | **`(ROW0FREE)` は停止性と同値**（行 0 を補題として使うなという記録） |
| `Wset.W_shift` / `W_mono` / `W_add`(rsum) | 既存 |

⚠ 旧メモ「接尾辞閉包は偽」は**撤回**（段を固定していたため）。

📌 **lean-yapss に移せる可能性**: `W_root_stage` / `W_drop` の証明は `A2'` と
`oper_take_prefix` / `oper_append_inner` しか使っておらず、ペア側でもそのまま
通るはず（`Wset-ja.md` の D.W と trio の `Wf`/`W` は逐語的に同じ構成）。
`Wset-4-ja.md` の `mem_W_of_bound` より鋭い「段＝根のレベル」が得られる。

## 4. 計測（probe）

| 命題 | 例数 | 違反 |
|---|---|---|
| `(SUBST1g)` 網羅 | 210201 | 0 |
| `(SUBST1g)` 非厳格 | 165768 | 0 |
| `(SUBST1)` | 62151 | 0 |
| 残差のみ・反証型乱択 | 78885 | 0 |
| 残差のみ・**狭めた核の領域**（行2 が `R.dropLast` に、別シード・広レンジ） | 13616 | 0 |
| `(LOW)` 末尾レベル下げ | 5544711 | 0 |
| 段＝根レベル | 211880 | 0 |
| 接尾辞閉 / 区間閉 | 237099 / 470712 | 0 |
| `(REPL)` 接尾辞差し替え | 1097675 | 0 |
| **`(TOW)` 段なし形**（残核の最もきれいな顔） | **1642293** | 0 |
| `(GC)` graft 閉包 | 12217217 | 0 |
| **行 0 の順序型だけで決まるか**（rank/stretch/affine/random） | **3290952 + 134200** | 0 |
| `le1` 錐 ⊆ `amin` 錐（無条件） | 64808 | 0 |
| `Lift1` と `oper` の可換性・孤児枝 | 210204 | 0 |
| `Lift1` と `oper` の可換性・親あり枝 | 192996 | **47718 不可換** |
| **実 ST_TS の行 2 コピー塊のタイ**（`v0 ≥ 1`） | **134505** | 0 |
| 同・`v0 = 0` | 5409 | （タイ 24 例はすべてここ） |
| **(ULIFT) 一様行 1 シフト**（現在は Lean で証明済み） | **378075** | 0 |
| 実 ST_TS の行 2 悪い部分が**行 1 の窓**か | 53642 | 8（すべて `v0 = 0`） |
| **実 ST_TS の行 2 悪い部分（`v0 ≥ 1`）のタイ**（深い閉包） | **40444281** | 0 |
| 既知不変量だけでタイが消えるか | 9611 | **1552（消えない）** |
| 残核 `Subst1gReviveSelf` 再監査（小型網羅・別実装） | 1201307 | 0（未判定 273562） |
| **(INS) 1 列挿入**（位置・列とも無制限＝`(SNOC)` の最短形） | **1603817** | 0 |
| 同・`S[p]` の下に挿入する制限版 | 1268993 | 0 |
| **(ROW1MONO) 行 1 引き下げ**・多列同時 | **369068** | 0 |
| 同・単列 / **反証型**（悪い根・その錐・末尾を狙う） | 106763 / **773483** | 0 / 0 |
| 同・**塔型ホスト**（行0ずらし×行1リフトのコピー塔、末尾列あり／なし） | **258507** | 0 |
| (C) ゲート: `take`/`drop-rebase`/**`oper`** 閉包でタイは出るか | 72561 | 0 |
| ⚠ 行 0 の任意の上げ下げで `W` は閉じるか（＝定理と同値） | 390293 / 337510 | 0 / 0 |
| 証明済み ST_TS 不変量 `cnf` はタイを排除するか | — | **⛔ 25 例でタイ** |

**打ち切りの検証**: 全プローブの `inW` は `n ∈ {1,2}` しか展開しない過大近似。
⚠ `oper_prefix_of_le` より `M⟦n'⟧` は `M⟦n⟧` の接頭辞なので、**大きい `n` ほど
条件が強い**。つまり `n ∈ {1,2}` は**最も緩い**チェックであり、検証が効く。
`n ∈ {1,2,3}` と突き合わせた結果 **判定 2209 例すべて一致・不一致 0**
（未判定 275）。さらに小さい母集団（長さ ≤ 2 の基づく列 114 本）で
`n <= 4` まで入れても **524 例すべて一致・不一致 0**。
この範囲では打ち切りは無害（`tools/check_inw_ns.py`）。

⚠ **実 ST_TS 行列は `inW` で判定不能**（判定すること自体が停止性問題）。
確認型監査 `audit_subst1g_stts.py` は判定 651 例で頭打ち。反証型
`probe_subst1g_adv.py` はランダム小タプル領域（`|S| ≤ 5`, `|C| ≤ 4`,
展開は `n ∈ {1,2}` 近似）。**決定的な監査ではない**。

## 5. 壁

残核は「文脈が死んだ孤児を復活させる」＝ 装置 γ と同型。分解では進まない:

* `(LOW)` の難枝 → `W u` 元の接尾辞上のガード付き塔 → `TowerExp` 経由で**循環**
* `(REPL)` で位置を `p = 0` に正規化できるが、核が 1→2 に増え、(REPL) 自身も
  同じ復活枝で止まる

**BM4 展開への新しい数学的入力が要る。** 直近で得た入力は 4 つ:
`W_root_stage`（段の階層は偽の複雑さ）、`W_drop`（接尾辞閉）、
`zeroRow2_mem_Wself`（`z=0` 断片はペア定理で完了）、
`snoc_zeroRow2`（行 2 ≡ 0 の上に任意の末尾列）。
⟹ 残差は「行 2 の列が **`R.dropLast` の中に** ある」場合だけになった（`|R| ≥ 3`）。

⚠ 次の一段（末尾 2 列 `[t1, t2]`）は通らない: `t1` の行 2 = 1 だとコピーが
行 2 = 1 の列を複製するので `snoc_zeroRow2` の前提が壊れる。`zle1` を仮定しても
（`t2` の行2 親は行2 = 0 なので `M'` 内 ⟹ コピーが `t1` を含む）救われない。

## 5.5 `zle1` を核まで通す改修 — 可否だけ判定済み（未着手）

「行 2 <= 1 なら行 2 = 1 の列の親は必ず行 2 = 0」＝**行 2 木の深さは 1 段**、
という構造事実はまだ Lean 上で一度も使っていない。使うには `zle1` を
`Wstar` → `TowerOK` → `TowerExp` → `Subst*` → 核まで通す必要がある。

**可否（調査済み）**: 原理的には通る。
* MASTER `mem_of_Aclosed_aux` は既に `zle1 M` を仮定に持つ。
* `Wstar` を `zle1` ガード付きに変えると、`Aop` 節 3 の義務
  `∀ z ∈ W m, based z → graft M z ∈ X` は**弱くなる**ので閉包側は問題ない。
* 使う側は `zle1 (graft M z)`（⟸ `zle1 M` ＋ `zle1 z`）を供給する必要があるが、
  塔の構成要素は全て `zle1` の断片から作られるので供給できる。

### `zle1` が具体的に買うもの（2026-08-09 に判明）

レベルは `lev = 2*row1 + row2` で、`zle1` なら `row2 ∈ {0,1}`。したがって

```
lev が等しい  <->  row1, row2 が等しい     （2b+c = 2b'+c', c,c' <= 1 ⟹ mod 2 で c=c'）
```

つまり **`zle1` の下ではレベルが列を一意に決める**。残核の仮定は
`lev C 0 <= lev S p` と「`C` の根の深さ = 列 `p` の深さ」なので:

| 場合 | 意味 |
|---|---|
| `lev C 0 = lev S p` | **`C 0` = 列 `p` そのもの**（＝ 頭一致形 `Subst1`） |
| `lev C 0 < lev S p` | `C ∈ W (lev S p - 1)` ＝ **`Aop` 節 3 と同じ段** |

⟹ `zle1` の下で残核は「**頭一致形**」＋「**節 3 と同じ段の場合**」に分かれる。
後者（`lev C 0 < lev S p`）は、**`W_shiftl0` で `C` を深さ 0 に戻せば
`Aop` 節 3 の graft 引数そのもの**になる: `S` の `Aop` データが節 3
（`domT S m`, `m = lev(S 末尾) - 1`）なら
`graft S (shiftl0 x C) = S.dropLast ++ C ∈ W u` が即出る。
⚠ ただし `S ∈ W u` から取れるデータが節 3 である保証は無い（節 2 かもしれない）。
残るのは「節 2 データしか無い場合」と「レベルが等しい場合」。
`(SUBST1g)` の g-性（頭が違ってよい）が要るのは `(TOW)` の定数対角ホストだけで、
そこは後者の場合に当たる。

⚠ **着手していない理由**: 影響範囲が定義・証明ともほぼ全チェーン（30k 行規模）。
上の分解は「核が 1→2 に増える」ので、それだけでは改修を正当化しない
（probe-before-formalize / explain-before-mass-edit）。

## 6. 却下済み（再挑戦禁止）

* `Aop` 節 2 の `natDom` ガード（全変種）— 反証
* ⚠ **`(GC)` は「反証」ではない（2026-08-09 訂正）**:
  `(GC) : S ∈ W u → domT S m → ∀ z ∈ W m, based z → graft S z ∈ W u`
  は **1221万例・違反 0**（`tools/probe_gc.py`、未判定 467847）。
  `|S| = 1` では `graft [c] z = shift z` なので `W_shift` で即。
  過去に却下されたのは `Wstar`/`GX` 機構内の別定式化であり、この `W u` 版は
  未証明なだけ。⛔ ただし**前進には使えない**: `z` のデータで帰納すると
  「文脈 `S.dropLast` が `z` の末尾孤児を復活させる」枝が出て、これは残核の
  `lev C 0 < lev(S 末尾)` 半分と**同値**（`W_shiftl0` で再基底すれば
  `graft S (shiftl0 x C) = S.dropLast ++ C`）

  **`(GC)` の節 3 の場合は自明**（`Y := {S | S ∈ W u ∧ (graft 閉包)}` で `A2'`
  すると、節 3 のデータ `hgr z hz hbz : graft S z ∈ Y` の第 1 成分がそのまま
  目標。`domT` は `m` を一意に決めるので `m` の食い違いも起きない。節 1 は
  `lev(末尾) = m+1 > 0` と矛盾して不可能）。よって

  つまり `(GC)` を証明するときは **節 2 の場合だけ考えればよい**
  （`S = A ++ [dominant terminal]`, `A ∈ W u`）。言い換えると
  「dominant terminal を 1 つ下の段のブロックに置き換えてよい」。

  ⚠ **ただしこれは命題の狭まりではない**: 節 2 で余分に手に入る
  `S.dropLast ∈ W u` は `W_dropLast` で最初から無料なので、仮定に足しても
  同じ命題。得られたのは「**証明の場合分けが 1 本で済む**」という情報だけ。
  ⛔ その節 2 の場合を `z` のデータで帰納するとやはり復活枝が残る。
* 前置だけの界面 / `InfEquip` — 反証
* 詳細は `GRAFTALL-PLAN.md` §5 と memory `trio-wset-redesign.md`

## 5.7 ★ 壁の最も鋭い言い換え: **添字マスク vs 値マスク**（2026-08-09）

trio が pair と違うのは**行 2 の崩壊が行 1 をリフトすること**だけである
（pair の `oper_cons_tower` は素の接ぎ木塔、trio の `srow=2` はリフト付き塔）。
そのリフト法則が (WL) `LiftStage`。ここに次の対立がある:

| | マスク | `oper` との可換性 |
|---|---|---|
| BM4 が実際に行う `Lift1` | `le1 X 0 ·`（悪い根の**添字**の子孫錐） | **不可換**（親あり枝 192996 例中 47718 例） |
| 証明済みの `slift` / `mlift` | `coneV`＝`amin` 上方集合（行 1 の**値**） | 可換（`slift_oper`、無条件） |

不可換の機構は測定で確定した: `(Lift1 X d)⟦n⟧` は**すべてのコピー**をリフトするが
`Lift1 (X⟦n⟧) d` は**最初のコピーだけ**をリフトする。`amin` は `oper` 不変
（`amin_oper_mir`）なのに、**添字**で決まる錐はコピーで壊れる（コピー `k` は自分
自身の錐を持つ）からである。

2 つのマスクの差はちょうど**行 1 のタイ**（根と行 1 の値が等しく `amin` も等しい
列）だけ。`le1` 錐 ⊆ `amin` 錐は Lean で**無条件に証明済み**（`coneV_of_le1`、
`le1_chain_window` から）。したがって

```
タイ無し ∧ 根の行 1 ≥ 1  ⟹  Lift1 X d = mlift X (v0-1) d ∈ W (m+2d)   -- 核なし
```
（`Wtower2.liftStage_of_tieFree`、`sorry` 0）。

**実 ST_TS での測定**（`tools/probe_tiefree_stts.py`、閉包の 460427 本、
行 2 コピー塊 139914 個）: タイは **24 例だけで、すべて `v0 = 0`**。
`v0 ≥ 1` の 134505 例では**タイ 0**。つまり実標準形では (WL) の 96% が無料。

⚠ **ただし一般の行列ではタイは起きる**: `X = [(0,1,0),(6,1,0)]`（`v0 = 1`）は
`two_col_mem_W` で `Wself` に入るがタイを持つ。よって `Wstar` が全 `argOK` ブロックを
量化している現在の枠組みでは `TieFree` を呼び出し地点で**捨てられない**。
使うには枠組みを ST_TS に制限する必要があり、それは大改修（未着手）。
### ★ (ULIFT): `Stair.zero` は `W` の輸送には不要（2026-08-09、証明済み）

`mlift` の閾値は自然数なので、`v0 = 0` のマスク `{amin ≥ 0}`＝全体には**原理的に
届かない**（閾値 `-1` が要る）。そこを埋めるのが

```
(ULIFT)  X ∈ W m  ⟹  shiftr01 0 d X ∈ W (m + 2d)          -- Wslift.ulift_mem_W
```

**`Stair.zero`（`φ 0 = 0`）は `slift_oper`（可換性）には本当に必要だが、`W` の
輸送には不要だった。** 一様シフトが `srow` を上げるのは末尾列が `srow = 0` の
ときだけで、そのとき持ち上げ後の末尾列の行 1 値はちょうど `d`・他は `≥ d` なので
**必ず孤児**になり、展開は `dropLast = X⟦1⟧` に潰れて節 2 の `n = 1` の帰納法
仮定で閉じる。計測 378075 例 0 違反 → Lean で証明済み（`sorry` 0）。

これで **`v0 = 0` も込みで** (WL) が無料になる十分条件が得られた:

```
根が行 0 で狭義最浅 ∧ 行 1 でも狭義最小  ⟹  Lift1 X d = shiftr01 0 d X ∈ W (m+2d)
```
（`Wtower2.liftStage_of_window`、`Lcone.le1_zero_iff` で錐が全体になる）。
実 ST_TS では行 2 崩壊の悪い部分 53642 個のうち **53634 個がこの行 1 の窓**を
満たす（破れる 8 例はすべて `v0 = 0`）。

⚠ ただし窓条件も一般の行列では成り立たないので、`Wstar` が全 `argOK` ブロックを
量化している限り呼び出し地点で捨てられない点は `TieFree` と同じ。

### ⛔ (WL) の残差は **ST_TS 到達可能性** に帰着する（2026-08-09、決定的）

タイ無しが呼び出し地点で落とせるかを最後まで詰めた結果:

| 測定 | 結果 |
|---|---|
| 実 ST_TS の行 2 悪い部分（`v0 ≥ 1`）にタイはあるか | **40444281 例、0** （閉包 depth 16 / `n ≤ 4` / 長さ ≤ 160 / 40 万列） |
| 平坦祖先対（`row1(a)=row1(z) ≥ 1`）は ST_TS にあるか | **520173 例 ある**（悪い部分の中にだけ無い） |
| **既知不変量 `r1ok ∧ z0ok ∧ noninc ∧ zle1` はタイを排除するか** | **⛔ しない**（9611 例中 **1552 例でタイ**、`tools/probe_tie_invariants.py`） |
| その最小反例 `[(0,0,0),(1,1,0),(2,1,0),(2,2,1)]` は ST_TS か | **⛔ 違う**（接頭辞も含め 25 万列の閉包に不在） |

⟹ **タイ無しは ST_TS 到達可能性そのもの**であり、`Invariant.lean` が既に通して
いる局所不変量からは出ない。すなわち **(WL) の残差は本丸と同じ壁**（memory
`h0clause-oper-step-status` の「ST_PS forest-reachability」と同型）であって、
別種の困難ではない。

**ただし帰納法のクラスからは外れない**（重要な切り分け）: MASTER
`mem_of_Aclosed_aux` が実際に降りるのは `take` と `split_lastMin` 尾部の
`shiftl0` 再基底化だけなので、必要なクラスは **ST_TS の take/drop-rebase 閉包**。
その閉包（122万列）で行 2 悪い部分 **411600 例、タイ 0**。つまり
「帰納で ST_TS を外れるから駄目」ではない。

⛔ 真の障害は別のところ: `Wstar` は `A2'` の A-閉集合として使われるため、
塔の議論は**すべての** `argOK` ブロックについて必要で、クラス制限が入らない。
`S := Wstar ∩ 𝒞` としても `Aop` データからは `𝒞` 所属が出ない。
（クラス側は無害: `take`/`drop-rebase`/`oper` の閉包 60 万列でも行 2 悪い部分
72561 例でタイ 0。証明済み ST_TS 不変量 `cnf` はタイを排除しない — 25 例で反例。）

### ★★★ (WL) はマスクを迂回できた: `(ROW1MONO)`（2026-08-10）

上の障害は**マスクを比較しようとしたこと**に由来する。比較は要らない:

```
Lift1 X d  =  shiftr01 0 d X（＝一様シフト、(ULIFT) で証明済み）の
              行 1 を、根の錐の外の列でだけ d 下げたもの
```

したがって **`W a` が行 1 の引き下げで閉じてさえいれば** `(WL)` が出る:

```
(ROW1MONO)  M ∈ W a → 行 0・行 2 が同じで行 1 が各列 ≤ の M' → M' ∈ W a
```
`Wtower2.liftStage_of_row1mono` / `Final.TRIO_terminates_of_row1mono`
（`sorry` 0、axioms clean）。**マスク・錐・タイは命題から完全に消える。**

計測（合計 **1507821 例 0 違反**、`tools/probe_row1mono.py`）: 多列同時 369068、
単列 106763、**反証型**（悪い根・その `le1` 錐・末尾を狙って引き下げ）773483、
**塔型ホスト**（A_x1≡1/W2ok/spanOK/dichOK を偽らせた形）258507。

⛔ **素直な帰納は反証済み**（再挑戦禁止）。`A2'` の節 2 を通すには
「`∀n ∃n'  M'⟦n⟧ ≤₁ (M⟦n'⟧).take |M'⟦n⟧|`」（`W_take` は既証）が要るが、
**296121 例中 26396 例（8.9%）で偽**。引き下げは末尾列の `srow` を下げるので
「孤児なら剥がす」が「コピーする」に化け、`M'⟦n⟧` が**どの `M⟦n'⟧` より長く**
なることがある（例: `S=[(0,4,1),(0,2,0),(0,4,1),(3,5,1),(3,2,0)]` の末尾を
行1=0 に下げると剥離がコピーに変わる）。

📌 **ヒント（必要なのは全一般の引き下げではない）**: 実際に要る 1 段は

```
Lift1 (X⟦n⟧) d   ≤₁   (Lift1 X d)⟦n⟧   ≤₁   shiftr01 0 d (X⟦n⟧)
```

の**サンドイッチの中央**だけ。下端は節 2 の帰納法仮定、上端は `(ULIFT)` で
どちらも `W` に入っている。しかも `Lift1` と `shiftr01 0 d` は `nextrel1` を
どちらも保つので**枝データ（`j0`/`Lb`/`d0`/`d1`）が完全に一致**する。
⟹ 「行 1 の**マスク付き**引き下げ（＝行 1 子孫錐の合併の上でだけ `d` 下げる）」
に限った版で十分。一般の `(ROW1MONO)` より弱い。

⟹ (WL) 側の残差は `(ROW1MONO)` 1 本になった。本丸は依然 `Subst1gReviveSelf`。

### ⚠ 同じ手は**行 0 では使えない**（`(ROW0FREE)` は定理と同値）

「証明済みの上界 ＋ 単調性」を行 0 でやると同値になる。深さを全部 0 に潰した列は
`nextrel0` が空で全列が孤児なので展開が `dropLast` に潰れ、**根のレベルさえ
収まれば無条件に `W a`**（`Wtower2.flat_mem_W`、`sorry` 0）。したがって

```
(ROW0FREE) 行 1・行 2 が同じなら行 0 は W 所属に効かない  ⟺  trio 停止性
```
（`Final.TRIO_terminates_of_row0free`、axioms clean）。計測でも行 0 の任意の
上げ下げは 0 違反（RAISE 390293 / LOWER 337510）だが、それは定理を測っている
だけ。⛔ **行 0 の単調性や §6.5 の (DEPTHORD) を「補題」として使おうとしないこと。**

## 6.5 ★ 未証明だが強く測れている予想: **深さは順序型しか効かない**

```
予想 (DEPTHORD) : 行 0 を順序（と等号）を保つ写像で置き換えても W 所属は変わらない
```
計測 3290952 + 134200 例、不一致 0（`tools/probe_depth_norm.py`）。
`lev` は行 1,2 だけなので段は不変、親判定 `nextrel0` と no-dip 節も純粋に順序的。

⚠ **`oper` は同変ではない**。`M = [(0,0,0),(5,0,0),(1,1,0)]` の展開は順序型
`0,3,1,4,2,5`、その rank 圧縮の展開は `0,2,1,3,2,4` で**別物**。したがって
可換図式では証明できず、別の機構（双模倣的な議論）が要る。

**使い道の候補**: 真なら深さを正規形（`d0 = 1` など）に落とせるので、
`(TOW)` の `|Q| >= 2` が有限族の問題に近づく。⚠ ただし未証明なので依存禁止。

## 7. 次の一手の候補（評価済み・未着手）

| 候補 | 内容 | 評価 |
|---|---|---|
| **A. `zle1` を核まで通す** | 行 2 木の深さ 1 段を使えるようにする | 可否 OK（§5.5）。**ただしアイデアが無い**。30k 行規模 |
| **B. 残差に帰納の文脈を渡す** | `S ∈ W u` の代わりに `∀k, SubstProp u (S.take k)` と `∀n≥1, SubstProp u (S⟦n⟧)` も仮定に加える | 核は**弱くなる**（＝良い）が命題が汚くなり紙上で扱いにくい。実装は小さい |
| **C. (REPL) で位置を 0 に正規化** | `A ++ X ∈ W u`, `Y ∈ W (lev X 0)` ⟹ `A ++ Y ∈ W u`（計測 1097675 例 0 違反） | 核が 1→2。(REPL) 自身も同じ復活枝で止まる |
| **D. 多ブロック版で帰納** | `SubstProp` を多ブロック化 | 検討済み: 場合分けの構造は同じで、復活枝は残る（利得なし） |
| **E. 順序数側からの入力** | ψ 崩壊など | 本プロジェクトは構文的ルートを選択している。方針転換になる |

⛔ 循環が確認された経路（再挑戦の前に §5 を読むこと）:
`(LOW)` の節2枝 / `(REPL)` / `(TOW)` / 多ブロック化 — いずれも `TowerExp` 経由で
自分に戻る。

### 多ブロック化 + `(WL)` の詳細（2026-08-09 検討・循環）

残差の最大枝「コピー領域内への挿入」（実測 78885 中 46529 / 13616 中 9521）は、
帰納の対象を**多ブロック版**にすると次のように閉じる:

- `S` と `R` のバッドルートが共通の `j0 < p` なら、`R[n]` は `S[n]` を
  ホストとする多ブロック置換になる（コピー `k` ごとに列 `p` の像の下に `C` の
  シフト・リフト版が入る）
- コピー `k` のホスト列のレベルは `lev S p + 2*k*d1`、
  ブロックは `(WL) LiftStage` により `W (lev C 0 + 2*k*d1) ⊆ W (lev S p + 2*k*d1)`
  ⟹ **ちょうど一致する**

⛔ しかし `(WL)` は `(TOW)` 経由で**核から導かれている**ので循環。
`(TOW)` を独立に証明しようとしても、`shTower` は「最後のコピーの根が最深」で
`rsum` が立たず `W_add` が使えない。`(SNOC)` を `(WL)` ＋ 対角ホスト
（ペア定理）から出そうとしても、対角ホスト上の置換がまさに核。

**実装コストが最小で確実に核を弱められるのは B。** アイデア探索を続けるなら
A の前に B を入れておくと、探索中に使える仮定が増える。
