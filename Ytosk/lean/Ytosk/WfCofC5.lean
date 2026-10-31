/-
**WfCofC5 (2026-11-01): `HCntPath0` from the count bound at `g = P_0(r)` and a one-edge step.**

`t = 0`, `r` not a root, `g = P_0(r)`: in `A[k+2]` the children of `g` are those of `A` before `r`, then the copies
`r, r + L, …` (siblings, `t0_core`), so the hole `ψ_{v(r)}(Y0)` is counted at `g`.

- `HCntAtG0`  : `fsD(o_A(g), k) ≤ o_{A[k+2]}(g)`.
- `HCntStep0` : one edge `c = P_0(d)`, `d` a strict ancestor of `r`: the bound at `d` gives the bound at `c`.
- `hCntPath0_of : HCntAtG0 → HCntStep0 → HCntPath0` (up the path from `g` to the last root).
-/
import Ytosk.WfCofC4

namespace Ytosk.WfCofC5

open T Ytosk Ytosk.WfCofH2 Ytosk.WfCofH3 Ytosk.WfCofC1

set_option linter.unusedSectionVars false

/-- **The count bound at `g = P_0(r)`** (`t = 0`). -/
def HCntAtG0 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 0 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ k σ rk, Cons (expand A (k + 2)) σ → Rk (expand A (k + 2)) rk →
    ∀ g, par A 0 r = some g → fsD (ρA.o g) (natT k) ≤ σ.o g

/-- **One edge of the path** (`t = 0`): the count bound moves from `d` to `c = P_0(d)`. -/
def HCntStep0 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 0 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ k σ rk, Cons (expand A (k + 2)) σ → Rk (expand A (k + 2)) rk →
    ∀ c d, par A 0 d = some c → Anc0 A d r → d < r →
      fsD (ρA.o d) (natT k) ≤ σ.o d → fsD (ρA.o c) (natT k) ≤ σ.o c

theorem hCntPath0_of (hG0 : HCntAtG0) (hSt : HCntStep0) : HCntPath0 := by
  intro A hAs hS hNE hz ht tA hv a b hSA r hr ρA rkA hCA hRA k σ rk hCN hRN c hcx hcr _
  have hr0 : par A 0 (A.length - 1) = some r := by
    have := hr; unfold BRoot at this; rw [ht] at this; exact this
  have hrA : Anc0 A r (A.length - 1) := anc0_of_par A 0 r _ hr0
  have hcrA : Anc0 A c r := anc_between hcx r hcr.le hrA.le
  -- `c` is an ancestor of `g = P_0(r)`
  obtain ⟨g, hg, hcg⟩ : ∃ g, par A 0 r = some g ∧ Anc0 A c g := by
    cases hcrA with
    | refl => omega
    | step hp hab => exact ⟨_, hp, hab⟩
  have hgr : g < r := par_lt A 0 r g hg
  have hgrA : Anc0 A g r := anc0_of_par A 0 g r hg
  have key : ∀ m c', g - c' = m → Anc0 A c' g → fsD (ρA.o c') (natT k) ≤ σ.o c' := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro c' hm hc'
      by_cases hcg' : c' = g
      · subst hcg'
        exact hG0 A hAs hS hNE hz ht tA hv a b hSA r hr ρA rkA hCA hRA k σ rk hCN hRN c' hg
      · obtain ⟨d, hd, hdg⟩ := WfCofC2.anc0_child hc'
          hcg'
        have hcd : c' < d := par_lt A 0 d c' hd
        have hdg' := hdg.le
        have ihd := ih (g - d) (by omega) d rfl hdg
        have hdr : Anc0 A d r := Anc0.step hg hdg
        exact hSt A hAs hS hNE hz ht tA hv a b hSA r hr ρA rkA hCA hRA k σ rk hCN hRN c' d hd hdr
          (by omega) ihd
  exact key (g - c) c rfl hcg

/-- **Surjectivity** with `HCntPath0` split. -/
theorem surj_of_C5 (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (hDL : WfCofC2.HDiagLoc) (hDS : WfCofC2.HDiagStep) (hG0 : HCntAtG0) (hSt : HCntStep0)
    (h1 : WfCofC3.HNoSucc1) (hC : WfCofC3.HCntRoot2) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  WfCofC4.surj_of_C4 hD hG hT hE hRS hDL hDS (hCntPath0_of hG0 hSt) h1 hC hot hvN hlt

end Ytosk.WfCofC5
