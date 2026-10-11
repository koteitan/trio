/-
**基底 SRO[n] とその接頭辞 `Mlen L` の PH3cG・FC3（closure、2026-10-11）。**

基底の枠は書き換えない（`no_trig`）ので、どちらも空で成り立つ。
-/
import Ytosk.V3BaseI
import Ytosk.V3PDef
import Ytosk.V3PKindG

namespace Ytosk.G

open T

section
variable {L : Nat} {β : T} (hF : BaseFit L β)
include hF

theorem base_ph3c : PH3cG (Mlen L) (bval L β) := by
  intro i hi L' c R h s y ho _ htr
  obtain ⟨_, hc, _⟩ := CL_split hF h
  exact absurd (no_trig hF (by simpa using hi) hc ho htr.1 htr.2) id

theorem base_fc3 : FC3 (Mlen L) (bval L β) := by
  intro i hi c R h s y ho hy htr
  obtain ⟨_, hc, _⟩ := CL_split hF (L' := []) (by simpa using h)
  have h1 : lt z y = true := by cases y with
    | z => exact absurd rfl hy
    | psi => rfl
  exact absurd (no_trig hF (by simpa using hi) hc ho h1 htr) id

end

end Ytosk.G
