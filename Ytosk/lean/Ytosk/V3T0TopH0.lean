/-
**3 行・t = 0: PH3c(M) と T0CutResG を使わない最上位（2026-10-12）。**

t0_dep_otH では、木の位置の閾値の一致（PH3c(M) と T0CutResG が要る）は RE を運ぶためだけに使い、
RE は影の枠の還元（hExp_t0_topS）だけが使う。hExp_t0_topH は N の TP1C・TP1WC・TrigOmC を
V3TP1Cut から取るので RE は要らない。ここでは RE を外した t0_otdH0（V3T0DepH0）から T0DFH を出し、
hExp_t0_topH と同じ組み立てで `hExp_t0_topH0` を作る。
-/
import Ytosk.V3T0DepH0
import Ytosk.V3T0TopH
import Ytosk.V3TP1CutG

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`T0DFH` without `VSmallR`, `PH3c M` or `T0CutResG`.** -/
theorem t0DFH_of (hHard : T0HardRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) :
    T0DFH M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.lo r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  exact t0_otdH0 hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (hHard M ρ rk r L hM hS I R hlen hL hp he1)
    (t0_shape3 hM hS I R hlen hL hp he1) (t0IVRes_holds M ρ rk r L hM hS I R hlen hL hp he1) n hn σ hCN

/-- **`hExp` for `t = 0` without `VSmallR`, `PH3c M` and `T0CutResG`.** -/
theorem hExp_t0_topH0
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hAD : T0Field AbsD) (hAU : T0Field AbsU) (hFrm : FrmLF)
    (hPHN : ∀ N σ, Std N → N ≠ SRO → Cons N σ → GoodOT N σ →
      PH3cG N σ ∧ TP1LeafG N σ ∧ TP1WLeafG N σ ∧ TrigCutG N σ)
    (hHard : T0HardRes) (hTPR : T0TPLoRes) (hAUWR : T0AbsUWRes) (hADNR : T0AbsDNRes) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz hs0 n hn2
  have hIV := t0IVRes_holds
  have hFF := t0_frameFieldsF hFrm hAD (t0_tplo hTPR)
  have H2 : T0RestNV := ⟨hAD, hAU, t0_tplo hTPR, t0_absUW hAUWR, hFF.2.2, t0_absDN hADNR, hFF.1, hFF.2.1⟩
  have hDF := t0DFH_of hHard hM hS I R
  apply hExp_t0B hDF (t0_vsmallF_at (t0VSD_at hDF) hIV) H2
    (fun N σ hN hNS hC hO => by
      obtain ⟨h1, h2, h3, h4⟩ := hPHN N σ hN hNS hC hO
      exact ⟨tp1C_of_ph3cG hC hO h1 h2, tp1WC_of_ph3cG hC hO h1 h3, trigOmC_of_ph3cG hC hO h1 h4⟩)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
