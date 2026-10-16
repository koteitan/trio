/-
**3 行・t = 2: hExp の t = 2 の部分の現在の形（`hExp_t2_v2`・`hExp_t2_of_last`）。**

証明済みの欄: Good3（T2BelowXRes のもとで）、FrameOT（種の列の枠のもとで）、RootP、BumpKidsDec・BumpTermDec、rootS。
残り: `T2BelowXRes`、FrameOT の種の列の枠 `foSeed`、そのほかの欄（`T2Rest2`）、N の Res3A。
接頭辞 M.take x の不変条件は 1 列落とし（`hLast`）から。
-/
import Ytosk.V3ExpT2BD
import Ytosk.V3ExpT2RP
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

theorem bumpKidsDec_congr {N : Mat} {σ τ : Valn} (h : BumpKidsDec N σ) (hA : Agree N σ τ) :
    BumpKidsDec N τ := by
  intro i h1 h2 j hj hjb
  rw [List.map_congr_left (fun k hk => ((hA k (mem_children hk).2).1).symm)]
  exact h i h1 h2 j hj hjb

theorem bumpTermDec_congr {N : Mat} {σ τ : Valn} (h : BumpTermDec N σ) (hA : Agree N σ τ) :
    BumpTermDec N τ := by
  intro i h1 h2
  have : (children N i).map (bumpTerm N τ i) = (children N i).map (bumpTerm N σ i) := by
    apply List.map_congr_left
    intro j hj
    unfold bumpTerm
    split
    · rw [List.map_congr_left (fun k hk => ((hA k (mem_children hk).2).1).symm)]
    · rfl
  rw [this]; exact h i h1 h2

/-- **The remaining value fields of `N = M[n]`** (`t = 2`), with `FrameOT` reduced to its seed frames. -/
structure T2Rest2 : Prop where
  vs : T2Field VSmallF
  fc : T2Field FrameClosed
  ad : T2Field AbsD
  au : T2Field AbsU
  tp1 : T2Field TP1C
  tplo : T2Field TPLo
  tp1w : T2Field TP1WC
  tplow : T2Field TPLoW
  auw : T2Field AbsUW
  adw : T2Field AbsDW
  trig : T2Field TrigOmC
  tplon : T2Field TPLoN
  adn : T2Field AbsDN
  res : T2Res3A
  foSeed : ∀ M ρ rk, Std M → M ≠ SRO → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → T2SeedFrames QFO M

/-- **`hExp` for `t = 2`** with the prefix invariants given. -/
theorem hExp_t2_v2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk) (hRest : T2Rest2)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
      ∃ τ rkT, Inv3 (M.take j) τ rkT ∧ Res3A (M.take j) τ rkT)
    (n : Nat) (hn : 2 ≤ n) :
    ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  have hCN := cons_of_rk hRN
  set σ := rhsIt (expand M n) (rkBound (expand M n) rkN) with hσ
  have hGN := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2) n (by omega) σ hCN
  -- the prefix `M.take x`
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hRk1 : Rk (M.take (M.length - 1)) rk :=
    rk_take (by omega) I.rank (counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat)
  obtain ⟨τ, rkT, IT, _⟩ := hT (M.length - 1) (by omega)
    (fun h => by rw [h] at hRk1; exact not_val_SRO _ (val_of_rk hRk1))
    (fun h => by
      have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left (by omega)] at this
      simp only [List.length_nil] at this; omega)
  have hAg : ∀ τ', Cons (M.take (M.length - 1)) τ' → Agree (M.take (M.length - 1)) τ τ' :=
    fun τ' h => agree_of_cons IT.cons h IT.rank
  have hfo := frameOT_expand_t2 hB hM hS I R hz h2
    (fun τ' h => clField_congr (Q := QFO) IT.fo (hAg τ' h)) (hRest.foSeed M ρ rk hM hS I R hz h2) n (by omega) σ hCN
  have hbd := bumpFields_expand_t2 hB hM hS I R hz h2
    (fun τ' h => ⟨bumpKidsDec_congr IT.kd (hAg τ' h), bumpTermDec_congr IT.td (hAg τ' h)⟩)
    (t2SeedBump_holds hM hS I hz h2) n (by omega) σ hCN
  have hrp := rootP_expand_t2 hB hM hS I R hz h2 n hn σ hCN
  have hctx : T2Ctx M ρ rk n σ rkN := ⟨hM, hS, I, R, hz, h2, hn, hCN, hRN, hGN⟩
  have F := fun {G : Mat → Valn → Prop} (h : T2Field G) => h M ρ rk n σ rkN hctx
  exact ⟨σ, rkN, ⟨hCN, hGN, hRN, F hRest.vs, F hRest.fc, hfo, hbd.1, hbd.2, F hRest.ad, F hRest.au,
    F hRest.tp1, F hRest.tplo, F hRest.tp1w, F hRest.tplow, F hRest.auw, F hRest.adw, F hRest.trig,
    F hRest.tplon, F hRest.adn, rootS_of_good hCN hGN, hrp⟩, hRest.res M ρ rk n σ rkN hctx⟩

/-- **`hExp` for `t = 2` in the shape of the top theorem**, with the prefix invariants from the one-column
drop `hLast`. -/
theorem hExp_t2_of_last
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hB : T2BelowXRes) (hRest : T2Rest2) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h2 n hn
  apply hExp_t2_v2 (hB M ρ rk) hRest hM hS I.toW R.toW hz h2 _ n hn
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
