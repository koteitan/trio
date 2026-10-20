import Ytosk.V3FDCopyRoot

namespace Ytosk.VRACopyPath
open T Classical

/-- An unguarded copy preserves its own level, with no u<=V requirement. -/
theorem unguarded_own_level {N P : Mat} {σ ρ : Valn} {r L i : Nat}
    {V' u : T} {g : Nat → Prop}
    (hF : CopyFacts N P σ ρ r L V' g) (hri : r ≤ i) (hi : i < P.length)
    (hng : ¬ g i) (hu : u = σ.v (i + L)) : LevAt P ρ i u := by
  exact Or.inl (hu.trans ((hF i hri hi).2.2 hng).1)

/-- The entire unguarded frame transfers unchanged at an arbitrary fixed level.
Neither a KAG callback nor a bound on u is required. -/
theorem unguarded_frame {N P : Mat} {σ ρ : Valn} {r L i : Nat}
    {V' u : T} {g : Nat → Prop}
    (hF : CopyFacts N P σ ρ r L V' g) (hri : r ≤ i) (hi : i < P.length)
    (hng : ¬ g i)
    (hQ : ∀ Lc c R, CL P i = Lc ++ c :: R →
      QVRAt (ρ.v i) (Lc.map ρ.o) (ρ.o c) u) :
    ∀ Lc c R, CL N (i + L) = Lc ++ c :: R →
      QVRAt (σ.v (i + L)) (Lc.map σ.o) (σ.o c) u := by
  intro Lc c R hCL
  obtain ⟨hcl, _, hngc⟩ := hF i hri hi
  rw [hcl] at hCL
  obtain ⟨Lc0, rest, hsplit, hLc, hrest⟩ := List.map_eq_append_iff.mp hCL
  obtain ⟨c0, R0, hrest0, hc, _⟩ := List.map_eq_cons_iff.mp hrest
  rw [hrest0] at hsplit
  subst hLc; subst hc
  obtain ⟨hv, hd⟩ := hngc hng
  have hmap : Lc0.map (σ.o ∘ (· + L)) = Lc0.map ρ.o := by
    apply List.map_congr_left
    intro d hd'
    apply hd
    rw [hsplit]
    exact List.mem_append_left _ hd'
  rw [List.map_map, hv, hmap, hd c0 (by rw [hsplit]; simp)]
  exact hQ Lc0 c0 R0 hsplit

/-- Step 1 at the actual consumer: old VSmallRAll supplies the unguarded
own-level frame directly; no copy-level residual is read. -/
theorem unguarded_own_frame {N P : Mat} {σ ρ : Valn} {r L i : Nat}
    {V' u : T} {g : Nat → Prop}
    (hF : CopyFacts N P σ ρ r L V' g) (hri : r ≤ i) (hi : i < P.length)
    (hng : ¬ g i) (hu : u = σ.v (i + L)) (hVP : VSmallRAll P ρ) :
    ∀ Lc c R, CL N (i + L) = Lc ++ c :: R →
      QVRAt (σ.v (i + L)) (Lc.map σ.o) (σ.o c) u := by
  apply unguarded_frame hF hri hi hng
  intro Lc c R hCL
  exact (vsmallRAll_iff.mp hVP) i Lc c R hCL u
    (unguarded_own_level hF hri hi hng hu)

#print axioms unguarded_own_frame
end Ytosk.VRACopyPath
