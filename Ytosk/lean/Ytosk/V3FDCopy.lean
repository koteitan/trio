/-
Real-copy FrameDom: partial reductions after replacing the false pure FDsh.
No additional residual or term guard is introduced. The n>=3 old-V ancestor
bound uses the existing T2VAncStep hypothesis at n-1. The n=2 prefix case and
retained low interval transport remain separate proof obligations.
-/
import Ytosk.V3T2VSFC
import Ytosk.V3FDCut
import Ytosk.V3T2CutDom

namespace Ytosk.FDCopy
open T

/-- The old source matrix has VAnc at every guarded copy pair once its
expansion index is at least two. No invariant of the target N is extracted. -/
theorem old_vAnc_of_t2VAncStep {M : Mat} (hVS : T2VAncStep M)
    {n r i : Nat} (hn : 3 ≤ n) {ρP : Valn}
    (hCP : Cons (expand M (n - 1)) ρP) (hGP : Good3 (expand M (n - 1)) ρP)
    (hg : TRIO.le1 (expand M (n - 1)) r i) : VAnc ρP r i :=
  vAnc_of_step hCP hGP (hVS (n - 1) (by omega) ρP hCP) hg

/-- Same application interface at the actual source matrix G2. The equality
is available from expand_eq_gexp in the standard t2 context. -/
theorem old_vAnc_copy {M : Mat} (hVS : T2VAncStep M)
    {n r L i : Nat} (hn : 3 ≤ n)
    (he : expand M (n - 1) = G2 M r L (n - 1)) {ρP : Valn}
    (hCP : Cons (G2 M r L (n - 1)) ρP) (hGP : Good3 (G2 M r L (n - 1)) ρP)
    (hg : TRIO.le1 (G2 M r L (n - 1)) r i) : VAnc ρP r i := by
  rw [← he] at hCP hGP hg
  exact old_vAnc_of_t2VAncStep hVS hn hCP hGP hg

/-- At a single low level already covered by the existing KA conjunct,
old VAnc components are cheap: below the new child's Omega or a new parent
component. This lemma does not extend the level range of T2VRAK. -/
theorem old_vAnc_component {ρP : Valn} {r i : Nat} {V' s u g : T}
    (hAnc : VAnc ρP r i)
    (hfa : ρP.v i ≤ shf (ρP.v r) V' s)
    (hKA : ∀ d ∈ comps u (ρP.v i),
      d ≤ psi (shf (ρP.v r) V' (ρP.v i)) z z ∨
        ∃ d' ∈ comps u (shf (ρP.v r) V' (ρP.v i)), d ≤ d')
    (hfas : shf (ρP.v r) V' (ρP.v i) ≤ shf (ρP.v r) V' s)
    (hg : g ∈ comps u (ρP.v r)) :
    g ≤ psi (shf (ρP.v r) V' s) z z ∨
      ∃ d ∈ comps u (shf (ρP.v r) V' (ρP.v i)), g ≤ d := by
  have om_mono : ∀ {a b : T}, a ≤ b → psi a z z ≤ psi b z z := by
    intro a b hab
    rcases (le_iff _ _).mp hab with hab | rfl
    · exact psi_le_psi_of (Or.inl hab)
    · exact le_refl _
  rcases hAnc u g hg with h | ⟨d, hd, hgd⟩
  · exact Or.inl (le_trans h (om_mono hfa))
  · rcases hKA d hd with h | ⟨d', hd', hdd'⟩
    · exact Or.inl (le_trans hgd (le_trans h (om_mono hfas)))
    · exact Or.inr ⟨d', hd', le_trans hgd hdd'⟩

#print axioms old_vAnc_of_t2VAncStep
#print axioms old_vAnc_copy
#print axioms old_vAnc_component
end Ytosk.FDCopy
