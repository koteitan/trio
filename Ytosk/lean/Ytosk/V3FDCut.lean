/-
FDshCopy retains the qFCo_sh term premises, FrameOT and the PH3cKindG shape.
Those premises are insufficient: both zero-state and nonzero proper-prefix
counterexamples below satisfy every premise and refute the proposed transport.
The old parent's large component is lost by f(a) and retained by f(s).
The positive zero_FrameDom_of_shared_level handles the 21 low-level interval
exceptions in the real-copy measurement without any transport hypothesis.
All-low KVRA is also insufficient: AllLowKVRACounterexample satisfies every
VD/KA/KG guard but loses old-V domination in the retained low component case.
not_FDsh refutes the pure residual used by the previous top theorem.
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

/-- Every old component above V transports through FrameDom's interval.
Unlike the low copy guards, this lemma needs no LevAt predicate or KA/KG. -/
theorem frameDom_sh_high_component {V V' a B s X w u g C : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hB : isOT B = true) (hs : isOT s = true)
    (hX : isOT X = true) (hVs : V < s)
    (hw : isOT w = true) (hVw : V < w) (hwa : w ≤ a)
    (hu : u ≤ shf V V' w) (hFD : FrameDom a B s X)
    (hg : g ∈ comps w B ∨ g ∈ comps w s)
    (hBC : sh V V' B < C) (hSC : psi (shf V V' s) z z < C)
    (hCX : C ≤ sh V V' X) :
    ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), sh V V' g ≤ d := by
  have hgo : isOT g = true := hg.elim
    (isOT_of_mem_comps w hB) (isOT_of_mem_comps w hs)
  have key : ∀ m, isOT m = true → B ≤ m → psi s z z ≤ m → sh V V' m < C →
      ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), sh V V' g ≤ d := by
    intro m hm hBm hSm hmC
    obtain ⟨r, hmr, hrc, hdom⟩ := ClShLGuarded.shift_interval_coinitial
      hV hV' hVV hw hVw hu hm C hmC
    have hrX : r ≤ X := by
      by_contra hn
      have hXr : X < r := lt_of_not_ge hn
      exact not_lt_of_ge (le_trans hrc hCX)
        (ClShLGuarded.sh_lt_right hV hV' hVV hX hXr)
    obtain ⟨d, hd, hgd⟩ := hFD w (not_lt.mpr hwa) r
      (lt_of_le_of_lt hBm hmr) (lt_of_le_of_lt hSm hmr) hrX g hg
    rcases List.mem_cons.mp hd with hd | hd
    · subst d
      exact ⟨C, List.mem_cons_self ..,
        le_trans (ClShLGuarded.sh_le_right hV hV' hVV hgo hgd) hrc⟩
    · rcases List.mem_append.mp hd with hdr | hda
      · obtain ⟨e, he, hde⟩ := hdom d (List.mem_cons_of_mem _ hdr)
        have hge := le_trans (ClShLGuarded.sh_le_right hV hV' hVV hgo hgd) hde
        change e ∈ z :: comps u C at he
        rcases List.mem_cons.mp he with he | he
        · subst e
          exact ⟨C, List.mem_cons_self .., le_trans hge (z_le _)⟩
        · exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_left _ he), hge⟩
      · exact ⟨sh V V' d, List.mem_cons_of_mem _ (List.mem_append_right _
          (ClShLGuarded.high_index_sh hV hV' hVV ha hw hVw hu hda)),
          ClShLGuarded.sh_le_right hV hV' hVV hgo hgd⟩
  by_cases h : B < psi s z z
  · apply key (psi s z z) (isOT_psi_zz hs) (le_of_lt h) (le_refl _)
    simpa [sh_psi_gt hVs, sh_z] using hSC
  · exact key B hB (le_refl _) (not_lt.mp h) hBC

#print axioms frameDom_sh_high_component

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
  all_goals simp [shf, a, s, V, V', af, sf, y, D, om, sh, sub, add, lt, num, ClShLGuarded.RootGuardCounterexample.num, app, one, succ]

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

namespace AllLowKVRACounterexample
abbrev num := ClShLGuarded.RootGuardCounterexample.num
def om (t : T) : T := psi t z z
def D : T := om (om (om (om (om (num 5)))))
def V : T := psi z D z
def V' : T := om (num 2)
def a : T := om one
def p : T := om (succ V)
def s : T := psi p V z
def A : T := psi p a z
def B : T := z
def y : T := om A
def af : T := app V' a
def pf : T := om (app V' one)
def sf : T := psi pf V z
def Af : T := psi pf a z
def yf : T := om Af

private theorem single_components {q x u g : T} (h : g ∈ comps u (psi q x z)) :
    g = x ∨ g ∈ comps u x ∨ g ∈ comps u q := by
  by_cases hqu : lt q u = true
  · simp [comps, hqu] at h
  · simpa [comps, hqu, or_assoc] using h

private theorem D_components {u g : T} (h : g ∈ comps u D) : g = z := by
  have h0 := comps_anti (z_le u) h
  simpa [D, om, num, ClShLGuarded.RootGuardCounterexample.num, comps, lt] using h0

private theorem V_components {u g : T} (h : g ∈ comps u V) :
    (u = z ∧ g = D) ∨ g = z := by
  by_cases hzu : lt z u = true
  · simp [V, comps, hzu] at h
  · have hu : u = z := le_antisymm (not_lt.mp hzu) (z_le _)
    subst u
    rcases single_components h with rfl | h | h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (D_components h)
    · simp [comps] at h

private theorem p_components {u g : T} (h : g ∈ comps u p) :
    (u = z ∧ g = D) ∨ g = z := by
  rcases single_components h with rfl | h | h
  · exact Or.inr rfl
  · simp [comps] at h
  · change g ∈ comps u (app V one) at h
    rw [comps_app, List.mem_append] at h
    rcases h with h | h
    · exact V_components h
    · right
      rcases single_components h with h | h | h
      · exact h
      · simp [comps] at h
      · simp [comps] at h

private theorem s_components {u g : T} (h : g ∈ comps u s) :
    g = V ∨ (u = z ∧ g = D) ∨ g = z := by
  rcases single_components h with rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (V_components h)
  · exact Or.inr (p_components h)

theorem old_FrameDom : FrameDom a B s (H s y) := by
  have hend : H s y = y := by decide
  rw [hend]
  intro u _ C _ hOC hCX g hg
  rcases hg with hg | hg
  · simp [B, comps] at hg
  rcases s_components hg with rfl | ⟨rfl, rfl⟩ | rfl
  · exact ⟨C, List.mem_cons_self ..,
      le_trans (show V ≤ psi s z z by decide) (le_of_lt hOC)⟩
  · cases C with
    | z => exact False.elim (not_lt_z _ hOC)
    | psi q e t =>
      have hsq : s ≤ q := by simpa [lev] using lev_le_of_le (le_of_lt hOC)
      have hqA : q ≤ A := by simpa [y, om, lev] using lev_le_of_le hCX
      have hpD : D ∈ comps z p := by decide
      have hDq : ∃ d ∈ Gc z q, D ≤ d := by
        by_cases hqs : q = s
        · subst q
          exact ⟨D, List.mem_cons_of_mem _ (show D ∈ comps z s by decide), le_refl _⟩
        · exact ClShLGuarded.persistent_of_shared_level (z_le p) hpD q
            (lt_of_le_of_ne hsq (Ne.symm hqs)) hqA
      obtain ⟨d, hd, hDd⟩ := hDq
      change d ∈ z :: comps z q at hd
      rcases List.mem_cons.mp hd with hd | hd
      · subst d
        exact ⟨psi q e t, List.mem_cons_self .., le_trans hDd (z_le _)⟩
      · have hdC : d ∈ comps z (psi q e t) := comps_psi_mem_of
          (not_lt.mpr (z_le q)) (Or.inr (Or.inr (Or.inl hd)))
        exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ hdC), hDd⟩
  · exact ⟨C, List.mem_cons_self .., z_le _⟩

theorem images : shf V V' a = af ∧ shf V V' s = sf ∧ sh V V' y = yf ∧ H sf yf = yf := by
  refine ⟨?_, ?_, ?_, by decide⟩
  all_goals simp [shf, a, s, V, V', af, sf, pf, y, yf, A, Af, p, D, om,
    sh, sub, add, lt, num, ClShLGuarded.RootGuardCounterexample.num, app, one, succ]

private theorem a_components {u g : T} (h : g ∈ comps u a) : g = z := by
  have h0 := comps_anti (z_le u) h
  simpa [a, om, one, comps, lt] using h0

private theorem V'_components {u g : T} (h : g ∈ comps u V') : g = z := by
  have h0 := comps_anti (z_le u) h
  simpa [V', om, num, ClShLGuarded.RootGuardCounterexample.num, comps, lt] using h0

theorem vdom : VDomF V V' a := by
  intro u _ g hg
  have hz := V'_components hg
  subst g
  exact Or.inl (z_le _)

theorem ka : ClShLGuarded.KA V V' a := by
  intro u _ g hg
  have hz := a_components hg
  subst g
  exact Or.inl (z_le _)

private theorem AN_zero (u : T) (n : Nat) : compsAN V u n z = [] := by
  cases n <;> rfl

private theorem AN_one (u : T) (n : Nat) : compsAN V u n one = [] := by
  cases n with
  | zero => rfl
  | succ n => simp [one, compsAN, show lt V z = false by decide, AN_zero]

private theorem AN_V (u : T) (n : Nat) : compsAN V u n V = [] := by
  cases n with
  | zero => rfl
  | succ n =>
    change compsAN V u (n + 1) (psi z D z) = []
    simp only [compsAN, show lt V z = false by decide, Bool.false_eq_true,
      and_false, if_false, AN_zero, List.append_nil]

private theorem AN_p {u g : T} : ∀ n, g ∈ compsAN V u n p → g = z := by
  intro n hn
  cases n with
  | zero => simp [compsAN] at hn
  | succ n =>
    have hsub : sub (succ V) V = one := by decide
    simp only [p, om, compsAN] at hn
    split_ifs at hn with h
    · simp only [AN_zero, hsub, AN_one, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hn
      exact hn
    · simp only [AN_zero, List.append_nil, List.not_mem_nil] at hn

private theorem AN_s {u g : T} : ∀ n, g ∈ compsAN V u n (sub s V) → g = V ∨ g = z := by
  have hsub : sub s V = s := by decide
  rw [hsub]
  intro n hn
  cases n with
  | zero => simp [compsAN] at hn
  | succ n =>
    have hsubp : sub p V = p := by decide
    simp only [s, compsAN] at hn
    split_ifs at hn with h
    · simp only [AN_V, hsubp, AN_zero, List.nil_append, List.append_nil,
        List.mem_cons] at hn
      exact hn.elim Or.inl (fun h => Or.inr (AN_p n h))
    · simp only [AN_zero, List.append_nil, List.not_mem_nil] at hn

/-- The old root components are not controlled by the old parent index.
VDomF controls V', so it does not supply this distinct missing condition. -/
theorem not_old_root_dom : ¬ (∀ u g, g ∈ comps u V →
    g ≤ psi a z z ∨ ∃ d ∈ comps u a, g ≤ d) := by
  intro h
  have hd := h z D (by decide)
  exact (show ¬ (D ≤ psi a z z ∨ ∃ d ∈ comps z a, D ≤ d) by decide) hd

theorem all_low_KVRA : ∀ u, u ≤ V → KVRA V V' a [] (psi s y z) u := by
  intro u hu
  refine ⟨vdom, (fun g hg => ka u (not_lt.mpr hu) g hg), ?_⟩
  intro s0 y0 he _ n g hg
  simp only [psi.injEq] at he
  obtain ⟨rfl, rfl, _⟩ := he
  rcases AN_s n hg with rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inl (z_le _)

theorem new_not_FrameDom : ¬ FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
    (H (shf V V' s) (sh V V' y)) := by
  rw [images.1, images.2.1, images.2.2.1, images.2.2.2, B, sh_z]
  intro h
  have hd := h z (by decide) yf (by decide) (by decide) (le_refl _) D (Or.inr (by decide))
  exact (show ¬ ∃ d ∈ yf :: (comps z yf ++ comps z af), D ≤ d by decide) hd

/-- Every proposed copy guard holds, at ALL low levels, but transport fails. -/
theorem counterexample : ¬ FDshCopyKVRA := by
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
    subst t; exact ⟨by decide, ⟨s, y, rfl⟩⟩
  · simp
  · exact Or.inl (by decide)
  · decide
  · decide
  · intro hn; exact False.elim (hn rfl)
  · decide
  · decide
  · exact all_low_KVRA
  · exact old_FrameDom

#print axioms counterexample
end AllLowKVRACounterexample

theorem not_FDshCopyVDKA : ¬ FDshCopyVDKA := by
  intro h
  apply AllLowKVRACounterexample.counterexample
  intro V V' a B s y Lv hV hV' hVV ha hVa hs hp hlev hB hFO hKind hVs ht hK hFD
  exact h hV hV' hVV ha hVa hs hp hlev hB hFO hKind hVs ht
    (hK z (z_le V)).1
    (fun u hu => (hK u (not_lt.mp hu)).2.1) hFD

#print axioms not_FDshCopyVDKA

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
