import Ytosk.V3SubstC
import Ytosk.V3SVFix
import Ytosk.TwoRowL

namespace Ytosk

open T

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

theorem lt_sh_of_shf {s y c : T} (hVs : V < s) (h : s < shf V V' s) :
    psi s y c < sh V V' (psi s y c) := by
  rw [sh_psi_gt hVs, T.psi_lt_psi]
  exact Or.inl h

theorem succ_lt_shf_succ : succ V < shf V V' (succ V) := by
  rw [shf_succ hV hV' hVV hV (le_refl V), shf_self]
  exact succ_lt_succ' hVV

theorem omega_lt_sh {W : T} (hW : isOT W = true) (h : W < sh V V' W) :
    omega W < sh V V' (omega W) := by
  rw [sh_omega hV hV' hVV hW]
  exact omega_lt_omega hW (isOT_sh hV hV' hVV hW) h

theorem add_lt_sh_of_right {B t : T} (hB : isOT B = true) (ht : isOT t = true)
    (h : t < sh V V' t) : add B t < sh V V' (add B t) := by
  rw [sh_add hV hV' hVV hB ht]
  exact lt_of_lt_of_le (add_lt_add_left B h)
    (add_le_add_right _ (isOT_sh hV hV' hVV hB) (isOT_sh hV hV' hVV ht)
      (le_sh hV hV' (le_of_lt hVV) hB))

theorem sumN_snoc_lt_sh {l : List T} {t : T} (hl : ∀ u ∈ l, isOT u = true)
    (ht : isOT t = true) (h : t < sh V V' t) :
    sumN (l ++ [t]) < sh V V' (sumN (l ++ [t])) := by
  rw [sumN_snoc_add hl ht]
  exact add_lt_sh_of_right hV hV' hVV (isOT_sumN l hl) ht h

theorem shf_lt_of_omega {A W : T} (hA : isOT A = true) (hW : isOT W = true)
    (hVA : V ≤ A) (h : W < sh V V' W) :
    sf (add A (omega W)) < shf V V' (sf (add A (omega W))) := by
  rw [← shf_add_omega hV hV' hVV hA hW hVA,
    sf_ot (isOT_add hA (isOT_omega hW)),
    sf_ot (isOT_add (isOT_shf hV hV' hVV hA) (isOT_omega (isOT_sh hV hV' hVV hW)))]
  exact lt_of_lt_of_le
    (add_lt_add_left A (omega_lt_omega hW (isOT_sh hV hV' hVV hW) h))
    (add_le_add_right _ (isOT_shf hV hV' hVV hA)
      (isOT_omega (isOT_sh hV hV' hVV hW)) (le_shf_self hV hV' (le_of_lt hVV) hA hVA))

theorem H_lt_sh {s y : T} (hy : isOT (psi s y z) = true) (hVs : V < s)
    (hlo : (split y (psi (succ s) z z)).2 ≠ z)
    (h : psi s y z < sh V V' (psi s y z)) : H s y < sh V V' (H s y) := by
  have hp : isOT (split y (psi (succ s) z z)).1 = true := by
    apply isOT_app_left (y := (split y (psi (succ s) z z)).2)
    rw [split_app]
    exact isOT_arg hy
  have hge : ∀ q ∈ summands (split y (psi (succ s) z z)).1, head (psi s y z) ≤ q := by
    intro q hq
    apply le_of_lt
    apply lt_of_lt_of_le (b := psi (succ s) z z)
    · change psi s y z < psi (succ s) z z
      rw [psi_lt_psi_z_iff]
      exact Or.inl (lt_succ_self s)
    · exact le_of_not_gt (split_fst_ge _ _ q hq)
  have heq : H s y = add (split y (psi (succ s) z z)).1 (psi s y z) := by
    rw [H_eq hy, if_neg hlo, add_eq_app (isOT_app_of hp hy hge)]
  rw [heq]
  exact add_lt_sh_of_right hV hV' hVV hp hy h

end

#print axioms lt_sh_of_shf
#print axioms succ_lt_shf_succ
#print axioms omega_lt_sh
#print axioms add_lt_sh_of_right
#print axioms sumN_snoc_lt_sh
#print axioms shf_lt_of_omega
#print axioms H_lt_sh

end Ytosk
