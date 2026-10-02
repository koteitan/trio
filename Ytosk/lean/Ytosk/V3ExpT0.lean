/-
**3 行・t = 0: 最上位の帰納法の仮定 hExp のうち t = 0 の分（n ≥ 2）。**

N = M[n] = TRIO.gexp M r L 0 0 n（r = P_0(x)、x = r + L、Δ = 0）の評価 σ（`t0_core` が作るもの）について、
`Inv3V N σ rkN ∧ Res3A N σ rkN` を組み立てる。

- `t0_core` から: Cons・Rk・Good3・FrameOT・BumpKidsDec・BumpTermDec・根の順序。rootS は Good3 から。
- 残り（明示した仮定）:
  - `T0OTD`: r より前の D の列の o の値が標準形（`t0_core` の `hOTD`）。
  - `T0Rest`: 値の不変条件の残りの欄（VSmallF・FrameClosed と 11 項目）と N の `Res3A`。
    文脈として M の不変条件と、接頭辞 M.take x の不変条件（帰納法で 1 列落としから出る）を渡す。
-/
import Ytosk.V3T0OT
import Ytosk.V3T0Last
import Ytosk.V3IndV

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The shape of a `t = 0` matrix**: the last column `x = r + L` has row 1 equal to 0 and row-0 parent `r`,
and every expansion is the copy expansion `TRIO.gexp M r L 0 0 n`. -/
theorem t0_shape {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0) :
    ∃ r L, r + L + 1 = M.length ∧ 0 < L ∧ par M 0 (r + L) = some r ∧ entry M 1 (r + L) = 0 ∧
      ∀ n, expand M n = TRIO.gexp M r L 0 0 n := by
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hrx : r < M.length - 1 := par_lt M _ _ r hr
  rw [hs0] at hr
  have he1 : entry M 1 (M.length - 1) = 0 := by
    unfold TRIO.srow at hs0
    rw [← entry_eq, ← entry_eq] at hs0
    split_ifs at hs0 <;> omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hz
    rw [col_eq_entries, entry_eq, entry_eq, entry_eq, h0, h1, h2]
  refine ⟨r, M.length - 1 - r, by omega, by omega, by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact hr,
    by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact he1, fun n => ?_⟩
  exact expand_eq_gexp_t0 M n (by omega) hzT (by rw [hs0]; exact hr) hs0

/-- **The residual `hOTD`** of `t0_core`: the `o` values of the `D` columns before `r` are standard. -/
def T0OTD : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → DepX M (r + L) true i → isOT (σ.o i) = true

/-- **The class residuals** of the `D` frames of `N = M[n]` (`t = 0`), which give `T0OTD` (`t0_otd`):
at a frame before `r` whose last counted child `c` keeps its `v`, the pair of arguments of `c` is of class
A, B (with a rewrite of the old frame also one of the new) or C; and at `g = P_0(r)` when no middle copy
root counts, the arguments drop by `◁` (C′ の標本で例外 0). -/
def T0Shape : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      ClsABC (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y' y
        (Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y)) ∧
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧ Lhd z X' X ∧ isOT X' = true)

/-- **`T0OTD` from the class residuals.** -/
theorem t0OTD_of_shape (h : T0Shape) : T0OTD := by
  intro M ρ rk r L n hM hS I R hlen hL hp he1 hn σ hCN
  obtain ⟨h1, h2⟩ := h M ρ rk r L hM hS I R hlen hL hp he1
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  exact t0_otd hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    h1 h2 n hn σ hCN

/-- **The remaining value fields of `N = M[n]`** (`t = 0`) and its `Res3A`, for the valuation built by
`t0_core` (which already has `Cons`, `Rk`, `Good3`, `FrameOT`, `BumpKidsDec`, `BumpTermDec`). The context
includes the invariants of the prefix `M.take x` (from the one-column drops in the induction). -/
def T0Rest : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT) →
    2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ → FrameOT (TRIO.gexp M r L 0 0 n) σ →
      BumpKidsDec (TRIO.gexp M r L 0 0 n) σ → BumpTermDec (TRIO.gexp M r L 0 0 n) σ →
      let N := TRIO.gexp M r L 0 0 n
      VSmallF N σ ∧ FrameClosed N σ ∧ AbsD N σ ∧ AbsU N σ ∧ TP1C N σ ∧ TPLo N σ ∧ TP1WC N σ ∧
        TPLoW N σ ∧ AbsUW N σ ∧ AbsDW N σ ∧ TrigOmC N σ ∧ TPLoN N σ ∧ AbsDN N σ ∧ Res3A N σ rkN

/-- **`hExp` for `t = 0`** (`n ≥ 2`), from the residuals `T0OTD` and `T0Rest`, with the invariants of the
prefix `M.take x` given. -/
theorem hExp_t0 (hOTD : T0OTD) (hRest : T0Rest) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0)
    (hT : ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
      ∃ τ rkT, Inv3 (M.take j) τ rkT ∧ Res3A (M.take j) τ rkT)
    (n : Nat) (hn2 : 2 ≤ n) :
    ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shape I hz hs0
  rw [hexp n]
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hcore := t0_core hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (fun n hn σ hCN => ⟨hOTD M ρ rk r L n hM hS I R hlen hL hp he1 hn σ hCN,
      t0_vsmallNewN hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.cons I.good I.rank hn hCN⟩)
    n hn2
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hKDN, hTDN, hpN, _⟩ := hcore
  -- the prefix `M.take x`
  have hTx : ∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT := by
    apply hT (r + L) (by omega)
    · intro h
      have hRk1 : Rk (M.take (r + L)) rk :=
        rk_take (by omega) I.rank (by
          have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
          rwa [show M.length - 1 = r + L by omega] at this)
      rw [h] at hRk1; exact not_val_SRO _ (val_of_rk hRk1)
    · intro h
      have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left (by omega)] at this
      simp only [List.length_nil] at this; omega
  obtain ⟨hvs, hfc, had, hau, htp1, htplo, htp1w, htplow, hauw, hadw, htrig, htplon, hadn, hRN'⟩ :=
    hRest M ρ rk r L n hM hS I R hlen hL hp he1 hTx hn2 σ rkN hCN hRN hGN hFON hKDN hTDN
  exact ⟨σ, rkN, ⟨hCN, hGN, hRN, hvs, hfc, hFON, hKDN, hTDN, had, hau, htp1, htplo, htp1w, htplow, hauw,
    hadw, htrig, htplon, hadn, rootS_of_good hCN hGN, hpN⟩, hRN'⟩

/-- **`hExp` for `t = 0` in the shape of the top theorem**, with the prefix invariants from the
one-column drop `hLast` (`hTake_of_last`). -/
theorem hExp_t0_of_last
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hOTD : T0OTD) (hRest : T0Rest) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz hs0 n hn2
  apply hExp_t0 hOTD hRest hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
