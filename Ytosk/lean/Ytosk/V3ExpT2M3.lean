/-
**3 行・t = 2: hExp の t = 2 の部分を M[n] の Inv3V だけの形で（`hExp_t2_V`）。**

V3ExpT2M2 の形から、チームの分解に合わせて:
- N の Res3 の欄は出さない（trio_terminates_main_G では大域の仮定 hDR・hSeed・hVSR から）。
- AbsD・AbsU は NoGapP N ∧ PhiX0R N から（`phiX_of_noGapR`・`absD_of_phiX`・`absU_of_phiX`）。
- TPLoW・AbsDW は同じ行列の TPLo・AbsD と LevFree から（t1-exp の `tplow_of_lf`・`absDW_of_lf`）。
-/
import Ytosk.V3ExpT2M2
import Ytosk.V3ExpT1L
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The remaining value fields of `N = M[n]`** (`t = 2`), in the team's current decomposition. -/
structure T2Rest3 : Prop where
  vs : T2Field VSmallF
  fc : T2Field FrameClosed
  tp1 : T2Field TP1C
  tplo : T2Field TPLo
  tp1w : T2Field TP1WC
  auw : T2Field AbsUW
  trig : T2Field TrigOmC
  tplon : T2Field TPLoN
  adn : T2Field AbsDN
  noGap : T2Field NoGapP
  phi0 : T2Field PhiX0R
  tplowLF : T2Field TPLoWLF
  tplow0 : T2Field TPLoW0
  adwLF : T2Field AbsDWLF
  adw0 : T2Field AbsDW0
  foSeed : ∀ M ρ rk, Std M → M ≠ SRO → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → T2SeedFrames QFO M

/-- **`hExp` for `t = 2`** (`Inv3V` of `M[n]`) with the prefix invariants given. -/
theorem hExp_t2_V (hB : T2BelowXRes) (hRest : T2Rest3) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
      ∃ τ rkT, Inv3 (M.take j) τ rkT ∧ Res3A (M.take j) τ rkT)
    (n : Nat) (hn : 2 ≤ n) :
    ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  have hCN := cons_of_rk hRN
  set σ := rhsIt (expand M n) (rkBound (expand M n) rkN) with hσ
  have hGN := good3_expand_t2 hM hS I R hz h2 (t2BelowXAll_of hB M ρ rk hM hS I R hz h2)
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
  have hphi : PhiX (expand M n) σ := phiX_of_noGapR (F hRest.noGap) (F hRest.phi0)
  have had : AbsD (expand M n) σ := absD_of_phiX hphi
  have hau : AbsU (expand M n) σ := absU_of_phiX hCN hGN hphi
  have hSN : SInv (expand M n) := (sInvX_expand hX n).toSInv
  have hFV : FrameV (expand M n) σ := ⟨hSN, hCN, hGN, hbd.1, hbd.2, had, F hRest.tplo⟩
  exact ⟨σ, rkN, ⟨hCN, hGN, hRN, F hRest.vs, F hRest.fc, hfo, hbd.1, hbd.2, had, hau,
    F hRest.tp1, F hRest.tplo, F hRest.tp1w, tplow_of_lf hFV (F hRest.tplowLF) (F hRest.tplow0), F hRest.auw,
    absDW_of_lf hFV (F hRest.adwLF) (F hRest.adw0), F hRest.trig,
    F hRest.tplon, F hRest.adn, rootS_of_good hCN hGN, hrp⟩⟩

/-- **`hExp` for `t = 2`, `Inv3V` form, with the prefix invariants from `hLast`.** -/
theorem hExp_t2_of_lastV
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hB : T2BelowXRes) (hRest : T2Rest3) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h2 n hn
  apply hExp_t2_V hB hRest hM hS I.toW R.toW hz h2 _ n hn
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
