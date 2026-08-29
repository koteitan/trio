# 現在地（2026-08-29 夜）

**3 行 z<2 バシク行列の停止性は、Lean 上で仮定 `TowerOK` 1 本に帰着している。**
そして `TowerOK` の残る債務は **「無タイ条件の伝播」1 本**だけである。

詳細は `SESSION-2026-08-28.md`（§40 以降）。以下は 5 分で現在地に戻るための要約。

---

## 0. 検算（team-lead が自分で回した、2026-08-29）

    leanman check -C /home/koteitan/proofs/dbms/lean lean/Final.lean  ⟹ **exit 0（緑）**
    `trio_cofinality`（`Core.lean:4602`）は仮定が `ST_TS M` / `ST_TS N` だけ ＝ **無条件**
    `lean/` で `sorry` を含むのは **`Dbms.lean` 1 本だけ**（別路線。この連鎖に入らない）

    連鎖: `TowerOK` → `Wstar_closed` → `wf_olt_ST_TS_of_cofinality`（＋無条件の共終性）
          → `wf_Rnf_of_wf_TS` → `step_terminates` → **`WellFounded stepRel`**
    併せて `no_infinite_expansion_of_towerOK`:
      **¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i+1))**
      ＝ 「z<2 の標準形に無限展開列は無い」そのもの

## 1. 到達点

    lean/Final.lean
      **TRIO_terminates_of_towerOK (htow : Wset.TowerOK) : WellFounded stepRel**
      （`leanman check` exit 0 / sorry 0、commit `ff2bdff`）

`Wstar` 路線（2 行の完成証明 `lean/Pair/Wset.lean` と同じ道筋）では
**共終性 `trio_cofinality` は無条件**、`Wstar` の閉性が `TowerOK` だけを要求する。

## 2. `TowerOK`（`lean/Wset.lean:4365`）の場合分けと状態

| 枝 | 状態 | 根拠 |
|---|---|---|
| `srow = 1` | **証明ずみ** | `towerOK1_of_clause3` |
| `srow = 2`, `z = 1` | **起きない** | `tower2_root_z_zero` |
| `srow = 2`, `z = 0`, 無タイ | 根リフトは全 `v` で通る | `liftStage_of_noTie` |
| ↑ の `n` の帰納 | 債務 1・2 は済み、**債務 3 が残り** | `L53Subst.lean` |
| `srow = 2`, `z = 0`, タイ有り | 分解で割れる（実測 2474/2474）| `split_lastTie` |

### 残る核は **2 本**（§107。還元は §114 で不動点に達した）

    **`Subst1gRevive`**  既存の残核（`Wtower2.lean`）
    **`WSnoc`**          既存の核（`Wtower2.lean:2049`）。**効く先が 2 つ**:
                          持ち上げ側 `WSnoc → WCat → … → LiftStage`（鎖は全部既存・緑）
                          連結側 `WstarSnoc`（`GraftFromExp` の「宿主の 1 段」）

    ⚠ **`WSnoc` ⟸ `PrefixCopies` ＋ `WSnocOpen1`、そして
    `PrefixCopies` ⟺ `WSnoc` の `srow=0` 枝**（§114）
    ⟹ **互いに還元し合う ＝ 還元だけでは進めない。明日からは「証明」が要る。**
    `PrefixCopies` が残核に落ちるのはラダーで **18.8%** だけ（§115）

    到達点: **`towerOK_of_wsnoc_graft`**（`L53Subst.lean`、緑）

    **検算（R1、§104）: 3 本そろえてラダー 20415/20415、1 本でも欠ければ 9（＝ strict）。**
    **⟹ 分解に穴は無い。**

    今日新しく作った核（`LiftTie` / `MliftR` / `Row1DownLocal` / `Row1DownRoot0` /
    `WConvex1` / `WstarCat` / `GraftFromExp` / `AminROper`）は、
    **すべて「既存の 2 本に落ちる」か「偽」かのどちらかに決着した**（§107.4）。

⚠ **「タイは 0.5%」は別の量**（§92）。`Wstar` は `∀v` なので、`R ≠ []` なら
`v` を `R` の行 1 の値に取れば**必ずタイになる**（20345/20345 = 100%）。
⟹ `towerOK2_of_tie` は**隅の場合ではない**。

### 実測はすべて通った

    伝播（`graft R (Lift1 (X⟦n⟧) t)` が `argOK` かつ無タイ）
      … **20000 件・n=1..12 で破れ 0**（対照つき、§78）。`argOK_Lift1` は緑
    タイ側の帰納 … 分解 100% 通る ＋ **最大 3 段**で無タイに帰着。`split_lastTie_len` で長さの帰納

**独立な裏づけ**: `Wstar` の神託だけ（連結は `split_lastMin` の 1 通り）で
**BM4-Analysis ブック全 7 シート 20415 行が 100%**（天井 `ψ(K·ω)` まで）、
さらに **`D_1` .. `D_12` も覆う**。**対照（strict）は 9 行・`D_1` のみ**（§91、§104 で 4 → 9 に訂正）。

## 3. 主要な補題（全部証明ずみ）

    lean/Wset.lean
      Wstar :2684 / **Wstar_closed (htow : TowerOK) :4372** / mem_Wstar :4646
      mem_W_of_bound :4732 / W_membership :4749 / wf_olt_ST_TS_of_cofinality :4757
      oper_cons_nat :2041 / oper_cons_succ :2392
      oper_cons_tower1 :2789 / **oper_cons_tower2 :3231**
      W_shift :1320 / W_shiftl0 :2246 / W_add :1682 / W_flatMap_copies :2552
      argOK :1314 / graft_cons :2545 / rsum_self_cons :2539
    lean/Wtower2.lean
      Le1 :333 / **liftStage_of_window :128** / Lift1_eq_mlift_of_tieFree :76
      snoc_zeroRow2 :3127 / snoc_orphan :3053 / snoc_flat_root :2208
      W_drop :2870 / W_segment :2981 / mem_Wself_iff :2991
    lean/Wslift.lean
      **ulift_mem_W :461**（`shiftr01 0 d X ∈ W (m+2d)`）
    lean/Lcone.lean
      **le1_zero_iff :36**
    lean/Pair/Wset.lean（2 行の完成証明）
      **split_lastMin :512** / Wstar :840 / Wstar_closed :1310 / mem_W_of_bound :1537
    lean/L53Subst.lean（今日書いたもの）
      comm_of_noRevive / split_lastMin（3 行版）/ tree_shift3 / argOK_normalize / Wstar3
      towerOK1_of_clause3 / tower2_root_z_zero / tower2_stage_fits / tieSyn_holds
      liftStage_of_window 系 / liftStage_of_noTie / **split_lastTie**

## 4. 順序数の地図（`bms -c` と BM4-Analysis ブックで確定）

    `(0,0,0)(1,1,1)` = **ψ(Ω_ω)** ＝ 2 行 BMS の極限（`psiI.json` 行 267）
    ── ブック全 7 シート（`ψ(I)` … `ψ(K)` … `ψ(K·ω)`）が**まるごとこの間に入る** ──
    **`(0,0,0)(1,1,1)(2,2,1)` = `D_2`** ＝ ブックのどの行列よりも大きい
    `(0,0,0)(1,1,1)(2,2,2)[v]` を展開すると `D_{v+1}`（yaBMS で確認）

## 5. 計器（進捗指標）

    `tools/dbms/ladder.py` … シートを先頭から連続で何行覆えたか（**`JUNCTION_RSUM=True` が健全**）
    `tools/dbms/wcert2.py` / `r66.py` / `r68.py` … R1 の証明書エンジン
    `tools/dbms/h1/h4*.py` … H11 の構造測定

**公式スコア（証明書エンジン路線）**: Lean 換算 **9 行**、C13 込み 10 行。
⚠ この指標は `W_add` で組み上げる路線のもの。**`Wstar` 路線の進捗指標ではない**（§69.1）。

## 6. 今日の教訓（11-16）

    11 母集団の定義が結論を決める（ランダム小行列の 71% はシートで 0.2%）
    12 計器が命題より強いことがある
    13 手法レベルで不可能なことがある（反証器は原理的に鳴らない）
    **14 神託は「証明したい定理の文」と 1 対 1 に対応させる**
       （`A ++ X ∈ W` を仮定すると連結が黙って入る。覆い 100% → 0.2%）
    **15 兄弟プロジェクトの越え方は、壁を特定した直後に見に行く**
       （CLAUDE.md に「lean-yapss に倣う」と書いてあるのに 1 日追ってから見た）
    **16 母集団を広げるときは、広げ方が仮定の量詞と合っているかを先に確かめる**
       （`Wstar_closed` の `v` は `R` と独立の全称なのに、シートの行から作ると `v=0` 固定）

## 7. 明日の最初の一手

    1. **無タイ条件の伝播**を測る（H11 の H50）。保たれるなら `towerOK2_of_noTie` が閉じる
    2. 閉じたら **タイ側**（`split_lastTie` の帰納、実測 2474/2474）
    3. `Final.lean` の 20 本の含意地図（R1 の R71）で `TowerOK` の位置を確認
