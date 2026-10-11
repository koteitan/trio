/-
**3 行・t = 0: 難しい枠の残り T0HardRes を M の不変条件 VSmallRP に替えた最上位（2026-10-12、t0-exp）。**

t0_otdU（V3T0DepU）は RClaim を段の集合 U に制限して運ぶので、難しい枠の HardArgN を自分で出す。
残りの M 側の仮定は VSmallRP（D の道の上の段だけの VSmallR、`T0VSPRes`）と、
書き換えの一致に使う M の PH3c と T0CutResG。
-/
import Ytosk.V3T0DepU
import Ytosk.V3T0TopH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Residual: `VSmallRP` of `M`** at the last column of type `t = 0`. -/
def T0VSPRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    VSmallRP M (r + L) r ρ

/-- **`T0DF` without `VSmallR` and without `T0HardRes`.** -/
theorem t0DF_ofU (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hCut : T0CutResG) (hVP : T0VSPRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) :
    T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.2 r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have h := t0_otdU hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (hVP M ρ rk r L hM hS I R hlen hL hp he1) (hPH M ρ rk hM hS I R) (hCut M ρ rk r L hM hS I R hlen hL hp he1)
    (t0_shape3 hM hS I R hlen hL hp he1) (t0IVRes_holds M ρ rk r L hM hS I R hlen hL hp he1) n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩

/-- **`hExp` for `t = 0` with `VSmallRP` in place of `T0HardRes`**: as `hExp_t0_topH`. -/
theorem hExp_t0_topU
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hAD : T0Field AbsD) (hAU : T0Field AbsU) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hPHN : ∀ N σ, Std N → N ≠ SRO → Cons N σ → GoodOT N σ →
      PH3c N σ ∧ TP1Leaf N σ ∧ TP1WLeaf N σ ∧ TrigCut N σ)
    (hCut : T0CutResG) (hVP : T0VSPRes) (hTPR : T0TPLoRes) (hAUWR : T0AbsUWRes) (hADNR : T0AbsDNRes) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz hs0 n hn2
  have hIV := t0IVRes_holds
  have hFF := t0_frameFieldsF hFrm hAD (t0_tplo hTPR)
  have H2 : T0RestNV := ⟨hAD, hAU, t0_tplo hTPR, t0_absUW hAUWR, hFF.2.2, t0_absDN hADNR, hFF.1, hFF.2.1⟩
  have hDF := t0DF_ofU hPH hCut hVP hM hS I R
  apply hExp_t0B hDF.toH (t0_vsmallF_at (t0VSD_at hDF.toH) hIV) H2
    (fun N σ hN hNS hC hO => by
      obtain ⟨h1, h2, h3, h4⟩ := hPHN N σ hN hNS hC hO
      exact ⟨tp1C_of_ph3c hC hO h1 h2, tp1WC_of_ph3c hC hO h1 h3, trigOmC_of_ph3c hC hO h1 h4⟩)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
