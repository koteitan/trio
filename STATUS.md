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

### 残る核（§120 で §116・§117 を訂正）

⚠ **`TowerOK2` 単独では足りない。** `towerOK1_of_clause3` は**節 3 の与件**を要求するので、
**節 2 から来る `:4447` の枝では `TowerOK1` が落ちない**（R1 の R83）。

    `Wset.lean:4461`（節 3 / `srow=2`）… `TowerOK1` は落ちる。**`TowerOK2` が残る**
    **`Wset.lean:4447`（節 2）… `TowerOK1` も `TowerOK2` も残る**

`natDom` のガードで `:4447` を消す道は **`:4470`（dead root の逃げ道）を塞ぐので不可**（§119・§120）。
**理由は行 2 に段の上界が無いこと** —— 行 1 の孤児は自動的に根の段より下だが、行 2 は違う。
**これが 2 行 / 3 行の非対称性の正体。**

### （旧）残る核は `TowerOK2` 1 本 —— §120 で訂正

    `srow = 1`         **証明ずみ**（`towerOK1_of_clause3`）
    `srow = 2`, `z=1`  **起きない**（`tower2_root_z_zero`）
    `srow = 2`, 狭義   **証明ずみ・仮定ゼロ**（`towerOK2_of_strict'`）
    `srow = 2`, 無タイ **証明ずみ・仮定ゼロ**（`towerOK2_of_noTie'`）
    **`srow = 2`, タイ  残り**

⚠ **§107 の「`Subst1gRevive` ＋ `WSnoc` の 2 本」は過剰還元だった**（§116）。
2 行の `Wstar_closed` は**仮定ゼロ**で、鍵は `rsum_self_cons`（根の深さ 0 で自明）と
`oper_cons_nat`（末尾が `R` 内で親を持てば cons が保たれコピーが出ない）。
⟹ **「接頭辞つきコピー」は `Wstar` の道筋に原理的に現れない。**
3 行にも道具は全部あるので、**2 行の分岐を逐語で移せば `TowerOK2` だけが残るはず**。

今日作った `PrefixCopies` / `WSnocOpen1` / `WstarSnoc` / `MliftR` / `WConvex1` は
**道筋に現れない経路のもの**。道具として残すだけでよい。

### 実測はすべて通った

    伝播（`graft R (Lift1 (X⟦n⟧) t)` が `argOK` かつ無タイ）
      … **20000 件・n=1..12 で破れ 0**（対照つき、§78）。`argOK_Lift1` は緑
    タイ側の帰納 … 分解 100% 通る ＋ **最大 3 段**で無タイに帰着。`split_lastTie_len` で長さの帰納

**独立な裏づけ（§117、確定形）**:

> **`TowerOK2`（`srow = 2` の枝、しかもタイの場合だけ）を証明すれば、
> BM4-Analysis ブック全 7 シート 20415 行（`ψ(Ω_ω)` から `ψ(K·ω)` まで）と
> 対角生成元 `D_1..D_12` が、Lean で証明ずみの規則だけで `Wself` に入る。**

    `TowerOK2` だけ … **20415 / 20415**（予算 20000 でも 200000 でも同じ）
    対照 strict     … **9**
    `Subst1gRevive` ＋ `WSnoc` を足しても**変わらない**（§107 の 2 本は不要だった）

⚠ 門は含意地図を符号化したものなので、これは**地図が正しいことの帰結**であって
地図の独立検証ではない（R1 の但し書き、§117.1）。

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
