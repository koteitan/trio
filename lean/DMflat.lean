/-
DMflat.lean: 平坦族 (0,0,0) :: Rc4^n ∈ W 0 を「荷多重集合の DM」経路
(wf_LdDM / Bml / PcB / GOK_twoPayZ_DM)で証明できるかの検証。

## 結論(検証済み)
実働の DM 経路は **荷がすべて `Bok`(= Flat 行1=行2=0 かつ根の高さ 0)** の
水平鎖しか扱えない。psiI の展開ブロック Rc4 = (1,1,1)(2,1,1)(3,1,0) は
行1=1・z=1・根の高さ=1 なので `Bok` 荷になれず、この経路では表現できない。

## 根拠(コード上の事実)
- `PcB`(Small:10870) / `ChNN`(Small:10848): 鎖 `ChL L` の全荷 Z に `Bok Z` を要求。
- `GOK_twoPayZ_DM`(Small:10674): 荷 Y に `Bok Y`、置換荷 Y' にも `Bok Y'` を要求
  (A2' 帰納 `W 0 ⊆ {Y | Bok Y → ...}` の全分岐で `hYb.root` / `hYb.zroot` を使う)。
- 橋 `GoodFb_snoc_innerJs0` / `GoodFb_snoc_dupJs0`(SmallA:18920,18943): 荷 Y に `Bok Y`。
- 頂点 `ZApp2c_true`(Small:10947) → `R375m61_mem`(Small:10977): 荷が全部 Flat の
  junk 鎖の W0 メンバーを **W0 に直接**(rowJ_mem_genF → SegA.reapp、Wstarv/Wg 非経由)証明する。
  つまり DM 経路は「平坦荷だけの junk 世界」で閉じている。

## なぜ Rc4 は表現できないか(構文的理由)
jk1 文法(nil/pay/one/two)で z=1 の列が出るのは:
  - colJ ヘッド `(a+1,b+1,1)`(1 つの far-word につき 1 個、鎖内では a,b 固定)、または
  - pay 荷(shiftr01 は z を保存する)。だが荷は `Bok` = Flat なので z=0。
∴ 1 本の colJ far-word は「z=1 ヘッド 1 個 + z=0 本体」。Rc4 は連続する 2 つの
z=1 列 (1,1,1)(2,1,1) を持つ **入れ子 far-word** なので、単一 colJ でも鎖の 2 本でも表せない。
入れ子 z=1 を pay 荷に入れると非 Bok(非 Flat)荷が要り、その荷閉包 = 保護付き
far-word 閉包(BwT / GT / Wstarv)= Lift1 の壁に戻る。

## このファイルの内容(検証済み・sorry 無し)
1. `LdDM_step_W0`: DM の減少ステップは荷に `Bok` でなく `∈ W 0` だけで足りる
   (元 `LdDM_step` は `Bok` を要求するが実際は `.mem` しか使っていない)。
   → 壁は DM の順序側ではなく、荷の平坦性(pay 表現 / GoodFb 橋)側にあることを局所化。
2. `not_flat_Rc4` / `not_bok_Rc4` / `not_bok_Trc4`: psiI の遠い語ブロックが
   Flat でも Bok でもないという具体事実。
-/
import Small
import Cpsi

namespace TRIO

open Wset Small

/-! ## 1. DM 減少ステップの荷条件を `Bok` から `∈ W 0` へ弱める

`LdDM_step`(Small:10369) は `Bok Y` を仮定するが、証明中で使うのは
`Acc_Rex'_of_Bok hY = Acc_Rex' hY.mem`、すなわち `Y ∈ W 0` だけ。
よって仮定を `Y ∈ W 0` に弱められる。これで DM の整礎性・減少は
任意の W0 荷を受け付ける(平坦性は不要)ことが分かる。 -/

theorem LdDM_step_W0 {Y Y' : TrioSeq} (hY : Y ∈ W 0) (hlt : Rex' Y' Y) (m : ℕ)
    (L : List TrioSeq) :
    Multiset.IsDershowitzMannaLT (LdMS (List.replicate m Y' ++ L)) (LdMS (Y :: L)) := by
  refine ⟨LdMS L, Multiset.replicate m (mkLd Y'), {mkLd Y}, by simp, ?_, ?_, ?_⟩
  · rw [LdMS_rep_append]
  · rw [LdMS_cons]
  · intro y hy
    rw [Multiset.eq_of_mem_replicate hy]
    exact ⟨mkLd Y, by simp,
      Ld_lt_iff.mpr ⟨Acc_Rex' hY, Relation.TransGen.single hlt⟩⟩

theorem LdDM_tree_W0 {Y Y' : TrioSeq} (hY : Y ∈ W 0) (hlt : Rex' Y' Y) (m : ℕ) (N : Jk1) :
    Multiset.IsDershowitzMannaLT (LdOf (twoIt N (Jk1.pay Jk1.nil Y') m))
      (LdOf (Jk1.two N (Jk1.pay Jk1.nil Y))) := by
  refine ⟨LdOf N, Multiset.replicate m (mkLd Y'), {mkLd Y}, by simp, ?_, ?_, ?_⟩
  · rw [LdOf_twoIt_pay]
  · show LdOf N + (LdOf Jk1.nil + {mkLd Y}) = _
    simp [LdOf]
  · intro y hy
    rw [Multiset.eq_of_mem_replicate hy]
    exact ⟨mkLd Y, by simp,
      Ld_lt_iff.mpr ⟨Acc_Rex' hY, Relation.TransGen.single hlt⟩⟩

/-! ## 2. psiI の遠い語ブロック Rc4 は Bok 荷になれない(具体事実)

Rc4 = (1,1,1)(2,1,1)(3,1,0)。
- `entry Rc4 0 0 = 1 ≠ 0` なので `Bok.root` が偽 → `¬ Bok Rc4`。
- 列 (1,1,1) は行1=1 なので `¬ Flat Rc4`(荷を根の高さ 0 に戻しても Zroot が偽)。
Trc4 = (1,1,1)(2,1,0)(= rcol の中身)も同様。 -/

theorem not_flat_Rc4 : ¬ Flat Cpsi.Rc4 := by
  intro h
  have := (h ((1, 1, 1) : ℕ × ℕ × ℕ) (by simp [Cpsi.Rc4])).1
  simp at this

theorem not_bok_Rc4 : ¬ Bok Cpsi.Rc4 := by
  intro h
  exact absurd h.root (by decide)

theorem not_flat_Trc4 : ¬ Flat Cpsi.Trc4 := by
  intro h
  have := (h ((1, 1, 1) : ℕ × ℕ × ℕ) (by simp [Cpsi.Trc4])).1
  simp at this

theorem not_bok_Trc4 : ¬ Bok Cpsi.Trc4 := by
  intro h
  exact absurd h.root (by decide)

end TRIO
