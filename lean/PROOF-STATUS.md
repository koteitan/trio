# trio / PROOF-STATUS (authoritative)

3 行バシク（BM4, `z<2` 断片）の停止性 Lean 形式化の現状。
`GRAFTALL-PLAN.md` は 3700 行の設計ログなので、**現状はこの文書を見る**。

- build: 800 jobs 緑 / **自前 40850 行に `sorry` 0**（取り込んだ `Pair/` 込み） /
  全 top-level の axioms = `[propext, Classical.choice, Quot.sound]`
- 取り込んだ `YAPSS.PSS_terminates_unconditional` も trio のビルド内で axioms clean
- 主目標: `Final.TRIO_terminates_of_revive_self`

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
| `zeroRow2_mem_Wself` | **行 2 が恒等的に 0 の列は全部 `Wself`** — ペア定理そのもの |
| `snoc_zeroRow2` | **行 2 ≡ 0 のブロックの末尾に任意の 1 列を継いでよい** — `oper` は末尾列をコピーせず行 2 も増やさないので展開が行 2 ≡ 0 のまま |
| `two_col_mem_W` | `[(0,v,z), t] ∈ W a`（`2v+z ≤ a`、`t` は**任意**）— `snoc_zeroRow2` の `|M'| = 1` |
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
| `(LOW)` 末尾レベル下げ | 5544711 | 0 |
| 段＝根レベル | 211880 | 0 |
| 接尾辞閉 / 区間閉 | 237099 / 470712 | 0 |
| `(REPL)` 接尾辞差し替え | 1097675 | 0 |

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

⚠ **着手していない理由**: 影響範囲が定義・証明ともほぼ全チェーン（30k 行規模）で、
かつ **`zle1` を使う証明アイデアがまだ無い**。アイデアが立つ前に大改修はしない
（probe-before-formalize / explain-before-mass-edit）。

## 6. 却下済み（再挑戦禁止）

* `Aop` 節 2 の `natDom` ガード（全変種）— 反証
* `(GC)`「後続データが graft 閉包に格上げ」— `|R|=1` で目標に退化
* 前置だけの界面 / `InfEquip` — 反証
* 詳細は `GRAFTALL-PLAN.md` §5 と memory `trio-wset-redesign.md`

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

**実装コストが最小で確実に核を弱められるのは B。** アイデア探索を続けるなら
A の前に B を入れておくと、探索中に使える仮定が増える。
