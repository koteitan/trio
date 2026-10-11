/-
**3 行・t = 0: 共通の不変条件 VSmallRA（t2 の V3DepRWU）から VSmallRP を出す（2026-10-12、t0-exp）。**

PathLv（D の道の上）は PathLvA（すべての書き換える枠）に含まれるので、VSmallRA ⇒ VSmallRP。
-/
import Ytosk.V3DepRWU
import Ytosk.V3T0TopU

namespace Ytosk

open T

theorem PathLv.toA {M : Mat} {x r : Nat} {ρ : Valn} {i : Nat} {u : T}
    (h : PathLv M x r ρ i u) : PathLvA M ρ i u := by
  induction h with
  | top _ _ hcl _ _ hsy ht => exact PathLvA.top hcl hsy ht
  | step _ _ hcl _ _ hsy ht _ ih => exact PathLvA.step hcl hsy ht ih

theorem VSmallRA.toP {M : Mat} {ρ : Valn} (h : VSmallRA M ρ) (x r : Nat) : VSmallRP M x r ρ :=
  fun k c Lc s y _ _ hcl _ _ hsy ht hhz u hu => h k c Lc s y hcl hsy ht hhz u (hu.imp id PathLv.toA)

/-- **`T0VSPRes` from the shared invariant `VSmallRA`.** -/
theorem t0VSPRes_of_RA (h : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → VSmallRA M ρ) :
    T0VSPRes :=
  fun M ρ rk r L hM hS I R _ _ _ _ => (h M ρ rk hM hS I R).toP (r + L) r

end Ytosk
