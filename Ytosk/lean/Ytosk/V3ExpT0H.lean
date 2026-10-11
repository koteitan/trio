/-
**3 行・t = 0: N = M[n] の残り Res3A を drop-fix の弱い形 Res3H に。**

`T0Res3A` は N の Inv3V のもとで N の Res3A を求める。`Res3A.ofH` で Res3H から Res3A が戻るので、
残りは `T0Res3H`（N の Res3H、落とす補題の argT を HardArg に狭めた形）でよい。
-/
import Ytosk.V3T0Sh1
import Ytosk.V3DropH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The residual `Res3H` of `N = M[n]`** (`t = 0`), given the value invariants of `N`. -/
def T0Res3H : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → Inv3V (TRIO.gexp M r L 0 0 n) σ rkN →
    Res3H (TRIO.gexp M r L 0 0 n) σ rkN

/-- `M[n]` (`t = 0`) is a standard matrix. -/
theorem std_gexp_t0 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (I : Inv3 M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    (n : Nat) : Std (TRIO.gexp M r L 0 0 n) := by
  have he2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hx : M.length - 1 = r + L := by omega
  have he0 : entry M 0 (r + L) ≠ 0 := by have := I.r0p _ _ hp; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨h0, _, _⟩
    rw [← entry_eq, hx] at h0; exact he0 h0
  have hs0 : TRIO.srow M (M.length - 1) = 0 := by
    unfold TRIO.srow
    rw [← entry_eq, ← entry_eq, hx, he1, he2]; rfl
  have he := expand_eq_gexp_t0 M n (by omega) hzT (by rw [hs0, hx]; exact hp) hs0
  rw [show M.length - 1 - r = L by omega] at he
  rw [← he]; exact Std.exp n hM

theorem t0Res3A_of_H (h : T0Res3H) : T0Res3A := by
  intro M ρ rk r L n σ rkN hctx V
  obtain ⟨hM, _, I, _, hlen, hL, hp, he1, _, hn2, _⟩ := id hctx
  have hNE : TRIO.gexp M r L 0 0 n ≠ [] := by
    intro he
    have := congrArg List.length he
    rw [lenN0 hlen (show 1 ≤ n by omega)] at this
    have hpos : 0 < n * L := Nat.mul_pos (by omega) hL
    simp only [List.length_nil] at this; omega
  exact Res3A.ofH hNE (sInv_std (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk V.rank)) V (h _ _ _ _ _ _ _ _ hctx V)

/-- `T0Rest` with the residual `Res3H` in place of `Res3A`. -/
structure T0RestH : Prop where
  vs : T0Field VSmallF
  ad : T0Field AbsD
  au : T0Field AbsU
  tplo : T0Field TPLo
  auw : T0Field AbsUW
  tplon : T0Field TPLoN
  adn : T0Field AbsDN
  tplow : T0Field TPLoW
  adw : T0Field AbsDW

theorem T0RestH.toRest (h : T0RestH) : T0Rest :=
  ⟨h.vs, h.ad, h.au, h.tplo, h.auw, h.tplon, h.adn, h.tplow, h.adw⟩

/-- **`hExp` for `t = 0`, the current residuals**: `T0ShapeR2`, `T0RestH` (value fields and `Res3H`), and the
shadow frames `T0RWResC`. -/
theorem hExp_t0_mainH
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hS : T0ShapeR2) (hRest : T0RestH) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  hExp_t0_mainR2 hLast hS hRest.toRest hC1 hC1W hCT

end Ytosk
