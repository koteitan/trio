/-
**3 行・t = 0: T0CutResGG を閾値の残りに替えた最上位（2026-10-12、t0-exp）。**

t0_otdT（V3T0DepT）は ThrA を運ぶので、切り口の残り T0CutResGG の代わりに
- `T0CutKappa`（M だけ）: 切り口 κ（B = P + κ、κ ∈ cutsNSG s t）は Ω_u で、u は c の行 0 の祖先（c を含む）の v の上の塔（高さ 1 以上、TowSet）、
- `T0ThrVRes`: v が変わる D の列 e で、親の TowSet の w は v(e) より小さければ v_N(e) より小さい、
- `T0ThrGRes`: g（r の親）の引数の右端の変化で g の TowSet の Ω_w が保たれる、
をとる。
-/
import Ytosk.V3T0DepT
import Ytosk.V3T0TopU
import Ytosk.V3TP1CutG

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Residual (M only): the cut is `Ω_u` with `u` a tower over `v` of a row-0 ancestor of `c`.** -/
def T0CutKappa : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      ∀ P a x, y = app P (psi a x z) →
      ∀ κ ∈ cutsNSG s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ →
        ∃ u, TowSet M ρ c u ∧ κ = psi u z z

/-- **Residual: the thresholds of a changed `v`.** -/
def T0ThrVRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ e, e < r → DepX M (r + L) false e → ∀ i, par M 0 e = some i → ThrV (TowSet M ρ i) (ρ.v e) (σ.v e)

/-- **Residual: the thresholds at `g`.** -/
def T0ThrGRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      ∀ X X', ρ.o g = psi (ρ.v g) X z → σ.o g = psi (ρ.v g) X' z → X' ≠ X → ThrA (TowSet M ρ g) X X'

theorem t0DF_ofT (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3cG M ρ)
    (hKap : T0CutKappa) (hTV : T0ThrVRes) (hTG : T0ThrGRes) (hVP : T0VSPRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) :
    T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.2 r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have h := t0_otdT hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (hVP M ρ rk r L hM hS I R hlen hL hp he1) (hPH M ρ rk hM hS I R) (hKap M ρ rk r L hM hS I R hlen hL hp he1)
    (hTV M ρ rk r L hM hS I R hlen hL hp he1) (hTG M ρ rk r L hM hS I R hlen hL hp he1)
    (t0_shape3 hM hS I R hlen hL hp he1) (t0IVRes_holds M ρ rk r L hM hS I R hlen hL hp he1) n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩

/-- **`hExp` for `t = 0` with the threshold residuals in place of `T0CutResGG`.** -/
theorem hExp_t0_topT
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hAD : T0Field AbsD) (hAU : T0Field AbsU) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3cG M ρ)
    (hPHN : ∀ N σ, Std N → N ≠ SRO → Cons N σ → GoodOT N σ →
      PH3cG N σ ∧ TP1LeafG N σ ∧ TP1WLeafG N σ ∧ TrigCutG N σ)
    (hKap : T0CutKappa) (hTV : T0ThrVRes) (hTG : T0ThrGRes) (hVP : T0VSPRes)
    (hTPR : T0TPLoRes) (hAUWR : T0AbsUWRes) (hADNR : T0AbsDNRes) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz hs0 n hn2
  have hIV := t0IVRes_holds
  have hFF := t0_frameFieldsF hFrm hAD (t0_tplo hTPR)
  have H2 : T0RestNV := ⟨hAD, hAU, t0_tplo hTPR, t0_absUW hAUWR, hFF.2.2, t0_absDN hADNR, hFF.1, hFF.2.1⟩
  have hDF := t0DF_ofT hPH hKap hTV hTG hVP hM hS I R
  apply hExp_t0B hDF.toH (t0_vsmallF_at (t0VSD_at hDF.toH) hIV) H2
    (fun N σ hN hNS hC hO => by
      obtain ⟨h1, h2, h3, h4⟩ := hPHN N σ hN hNS hC hO
      exact ⟨tp1C_of_ph3cG hC hO h1 h2, tp1WC_of_ph3cG hC hO h1 h3, trigOmC_of_ph3cG hC hO h1 h4⟩)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
