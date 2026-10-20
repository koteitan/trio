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

/-- At a high level fixed by f, source bounds transport at that same level.
The forward parent witness uses high_index_sh; no low KAG is read. -/
theorem high_fixed_bound {V V' a B s u : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hB : isOT B = true) (hs : isOT s = true)
    (hVa : V ≤ a) (hVs : V < s) (has : a ≤ s)
    (hu : isOT u = true) (hVu : V < u) (hua : u ≤ shf V V' a)
    (hfix : shf V V' u = u) (hVD : VDomF V V' a)
    (hQ : ∀ d ∈ comps u s, d ≤ psi s z z ∨ d ≤ B ∨ ∃ e ∈ comps u a, d ≤ e) :
    ∀ d ∈ comps u (shf V V' s),
      d ≤ psi (shf V V' s) z z ∨ d ≤ sh V V' B ∨
      ∃ e ∈ comps u (shf V V' a), d ≤ e := by
  have hOm : psi (shf V V' a) z z ≤ psi (shf V V' s) z z :=
    psi_le_psi_z (ClShLGuarded.shf_le_right hV hV' hVV ha hVa has)
  intro d hd
  change d ∈ comps u (add V' (sh V V' (sub s V))) at hd
  rcases comps_add u V' (sh V V' (sub s V)) d hd with hd | hd
  · rcases hVD u (not_lt.mpr hua) d hd with h | h
    · exact Or.inl (le_trans h hOm)
    · exact Or.inr (Or.inr h)
  · have hd' : d ∈ comps (shf V V' u) (sh V V' (sub s V)) := by rwa [hfix]
    obtain ⟨e, he, rfl⟩ := comps_sh hV hV' hVV hu (le_of_lt hVu)
      (isOT_sub_sfx hs V) d hd'
    have hes := comps_sub_sub u s V he
    have heOT := isOT_of_mem_comps u hs hes
    rcases hQ e hes with h | h | ⟨f, hf, hef⟩
    · left
      have h' := sh_le_sh hV hV' (le_of_lt hVV) heOT (isOT_psi_zz hs) h
      simpa only [sh_psi_gt hVs, sh_z] using h'
    · exact Or.inr (Or.inl (sh_le_sh hV hV' (le_of_lt hVV) heOT hB h))
    · exact Or.inr (Or.inr ⟨sh V V' f,
        ClShLGuarded.high_index_sh hV hV' hVV ha hu hVu (by rw [hfix]) hf,
        sh_le_sh hV hV' (le_of_lt hVV) heOT (isOT_of_mem_comps u ha hf) hef⟩)

#print axioms high_fixed_bound
#print axioms unguarded_own_frame
end Ytosk.VRACopyPath
