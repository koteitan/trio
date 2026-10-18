/-
FDshCopy retains the qFCo_sh term premises, FrameOT and the PH3cKindG shape.
Those premises are insufficient: both zero-state and nonzero proper-prefix
counterexamples below satisfy every premise and refute the proposed transport.
The old parent's large component is lost by f(a) and retained by f(s).
The positive zero_FrameDom_of_shared_level handles the 21 low-level interval
exceptions in the real-copy measurement without any transport hypothesis.
-/
import Ytosk.V3T2FC
import Ytosk.V3ClShLV
import Ytosk.V3RwClCut
import Ytosk.V3CutClosed

namespace Ytosk.FDCut
open T
set_option linter.unusedVariables false

/-- Exact moving rewrite case requested by qFCo_sh, with FrameOT and
PH3cKindG retained from the matrix context. The proposition is false; see
PrefixCounterexample.counterexample. -/
def FDshCopy : Prop := ∀ {V V' a B s y : T} {Lv : List T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [psi s y z], Single t)
    (hp : (Lv ++ [psi s y z]).Pairwise (fun p q => q ≤ p))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [psi s y z], V < lev t)
    (hB : B = spArg a z (sumN Lv))
    (hFO : isOT (psi a B z) = true)
    (hKind : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hVs : V < s)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hFD : FrameDom a B s (H s y)),
    FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
      (H (shf V V' s) (sh V V' y))

/-- Proposed repair with VDomF and old-parent retention at every low level.
This is a statement, not a proved consequence of the path-restricted top guards. -/
def FDshCopyVDKA : Prop := ∀ {V V' a B s y : T} {Lv : List T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [psi s y z], Single t)
    (hp : (Lv ++ [psi s y z]).Pairwise (fun p q => q ≤ p))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [psi s y z], V < lev t)
    (hB : B = spArg a z (sumN Lv))
    (hFO : isOT (psi a B z) = true)
    (hKind : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hVs : V < s)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hVD : VDomF V V' a)
    (hKA : ClShLGuarded.KA V V' a)
    (hFD : FrameDom a B s (H s y)),
    FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
      (H (shf V V' s) (sh V V' y))

/-- Stronger proposed repair, also retaining KG at every low level.
T2VRAK supplies this only at LevAt levels, not automatically at every u<=V. -/
def FDshCopyKVRA : Prop := ∀ {V V' a B s y : T} {Lv : List T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [psi s y z], Single t)
    (hp : (Lv ++ [psi s y z]).Pairwise (fun p q => q ≤ p))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [psi s y z], V < lev t)
    (hB : B = spArg a z (sumN Lv))
    (hFO : isOT (psi a B z) = true)
    (hKind : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hVs : V < s)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hK : ∀ u, u ≤ V → KVRA V V' a Lv (psi s y z) u)
    (hFD : FrameDom a B s (H s y)),
    FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
      (H (shf V V' s) (sh V V' y))

/-- A zero state needs no transport when the upper endpoint has the child's
own leading index. This handles the measured low-level interval exceptions. -/
theorem zero_FrameDom_of_shared_level {a s Y : T} (has : a ≤ s) :
    FrameDom a z s (psi s Y z) := by
  intro u hua C _ hOC hCX g hg
  rcases hg with hg | hg
  · simp [comps] at hg
  · obtain ⟨d, hd, hgd⟩ := ClShLGuarded.persistent_of_shared_level
      (le_trans (not_lt.mp hua) has) hg C hOC hCX
    change d ∈ z :: comps u C at hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d
      exact ⟨C, List.mem_cons_self .., le_trans hgd (z_le _)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ hd), hgd⟩

#print axioms zero_FrameDom_of_shared_level

namespace ZeroStateCounterexample
abbrev num := ClShLGuarded.RootGuardCounterexample.num
def om (t : T) : T := psi t z z
def D : T := om (om (num 5))
def V : T := psi one D z
def V' : T := om (num 2)
def a : T := app V one
def s : T := app V V
def B : T := z
def y : T := om (om (num 3))
def af : T := app V' one
def sf : T := app V' V

theorem seed_components {u g : T} (hg : g ∈ comps u s) : g ∈ comps u a := by
  change g ∈ comps u (app V V) at hg
  rw [comps_app, List.mem_append] at hg
  have h : g ∈ comps u V := hg.elim id id
  change g ∈ comps u (app V one)
  rw [comps_app]
  exact List.mem_append_left _ h

theorem old_FrameDom : FrameDom a B s (H s y) := by
  intro u _ C _ _ _ g hg
  rcases hg with hg | hg
  · simp [B, comps] at hg
  · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ (seed_components hg)), le_refl _⟩

theorem images : shf V V' a = af ∧ shf V V' s = sf ∧ sh V V' y = y ∧ H sf y = y := by
  refine ⟨?_, ?_, ?_, by decide⟩
  all_goals simp [shf, a, s, V, V', af, sf, y, D, om, sh, sub, add, lt, num, ClShLGuarded.RootGuardCounterexample.num, app, one]

/-- The missing old-component retention condition fails already at u=0. -/
theorem not_KA : ¬ ClShLGuarded.KA V V' a := by
  intro h
  have hd := h z (by decide) D (by decide)
  rw [images.1] at hd
  exact (show ¬ (D ≤ psi af z z ∨ ∃ d ∈ comps z af, D ≤ d) by decide) hd

theorem new_not_FrameDom : ¬ FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
    (H (shf V V' s) (sh V V' y)) := by
  rw [images.1, images.2.1, images.2.2.1, images.2.2.2]
  rw [B, sh_z]
  intro h
  have hd := h z (by decide) y (by decide) (by decide) (le_refl _) D (Or.inr (by decide))
  exact (show ¬ ∃ d ∈ y :: (comps z y ++ comps z af), D ≤ d by decide) hd

theorem counterexample : ¬ FDshCopy := by
  intro h
  apply new_not_FrameDom
  apply h (V := V) (V' := V') (a := a) (B := B) (s := s) (y := y) (Lv := [])
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro t ht
    have he : t = psi s y z := by simpa using ht
    subst t
    exact ⟨by decide, ⟨s, y, rfl⟩⟩
  · simp
  · exact Or.inl (by decide)
  · decide
  · decide
  · intro hn; exact False.elim (hn rfl)
  · decide
  · decide
  · exact old_FrameDom

#print axioms counterexample
end ZeroStateCounterexample

namespace PrefixCounterexample
abbrev num := ClShLGuarded.RootGuardCounterexample.num
abbrev om := ZeroStateCounterexample.om
abbrev D := ZeroStateCounterexample.D
abbrev V := ZeroStateCounterexample.V
abbrev V' := ZeroStateCounterexample.V'
abbrev a := ZeroStateCounterexample.a
abbrev s := ZeroStateCounterexample.s
abbrev af := ZeroStateCounterexample.af
abbrev sf := ZeroStateCounterexample.sf
def p : T := om (num 3)
def B : T := om p
def y : T := app B (app B one)
def C : T := app B B

theorem kind : PH3cKindG B (split y (psi (succ s) z z)).1
    (split y (psi (succ s) z z)).2 s := by
  right
  exact ⟨by decide, Or.inl ⟨B, by decide, by decide⟩⟩

theorem old_FrameDom : FrameDom a B s (H s y) := by
  intro u _ E _ _ _ g hg
  rcases hg with hg | hg
  · have h0 := comps_anti (z_le u) hg
    have hz : g = z := by
      simpa [B, p, om, ZeroStateCounterexample.om, num,
        ClShLGuarded.RootGuardCounterexample.num, comps, lt] using h0
    subst g
    exact ⟨E, List.mem_cons_self .., z_le _⟩
  · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _
      (ZeroStateCounterexample.seed_components hg)), le_refl _⟩

theorem state_image : sh V V' B = B := by
  simp [B, p, om, ZeroStateCounterexample.om, V, V', ZeroStateCounterexample.V,
    ZeroStateCounterexample.V', ZeroStateCounterexample.D, num,
    ClShLGuarded.RootGuardCounterexample.num, sh, sub, add, lt, one]

theorem arg_image : sh V V' y = y := by
  rw [y, sh_app, state_image, sh_app, state_image]
  congr 2
  simp [one, sh, lt]

theorem new_not_FrameDom : ¬ FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
    (H (shf V V' s) (sh V V' y)) := by
  rw [ZeroStateCounterexample.images.1, ZeroStateCounterexample.images.2.1,
    state_image, arg_image]
  intro h
  have hd := h z (by decide) C (by decide) (by decide) (by decide) D (Or.inr (by decide))
  exact (show ¬ ∃ d ∈ C :: (comps z C ++ comps z af), D ≤ d by decide) hd

/-- Nonzero-state counterexample: the frame is a genuine proper-prefix kind. -/
theorem counterexample : ¬ FDshCopy := by
  intro h
  apply new_not_FrameDom
  apply h (V := V) (V' := V') (a := a) (B := B) (s := s) (y := y) (Lv := [B])
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro t ht
    rcases List.mem_cons.mp ht with ht | ht
    · subst t; exact ⟨by decide, ⟨p, z, rfl⟩⟩
    · have he : t = psi s y z := by simpa using ht
      subst t; exact ⟨by decide, ⟨s, y, rfl⟩⟩
  · decide
  · exact Or.inl (by decide)
  · decide
  · decide
  · exact fun _ => kind
  · decide
  · decide
  · exact old_FrameDom

#print axioms counterexample
end PrefixCounterexample

/-- The pure residual currently assumed at top level is false. -/
theorem not_FDsh : ¬ FDsh := by
  intro h
  apply ZeroStateCounterexample.new_not_FrameDom
  apply h ZeroStateCounterexample.V ZeroStateCounterexample.V'
    ZeroStateCounterexample.a ZeroStateCounterexample.B
    ZeroStateCounterexample.s ZeroStateCounterexample.y
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [ZeroStateCounterexample.B, summands]
  · decide
  · decide
  · exact ZeroStateCounterexample.old_FrameDom

#print axioms not_FDsh

end Ytosk.FDCut
