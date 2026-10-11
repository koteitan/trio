/-
**σ と G3 の切り口: 演算で「動かないか切り口」が保たれる（closure、2026-10-12）。**

σ = σ_{V,V′}（V < V′）、s = V′。項 t について CR(t): σ t = t か t ∈ cutsHG s (σ t)。
切り口は「最後の加数の中の 1 か所を Ω_s 型に置き換え、その後ろを捨てる」形なので、
σ で動かない項 g との大小は t と σ t で同じ（σ は単調で g は不動点）。これを使って
- `add_cut`: 動かない B に切り口の加数を足しても切り口、
- `cut_prefix_fix`・`last_cut`: 切り口の前の加数は動かない、最後の加数は切り口、
- `H_cut`・`step_cut`: sp の 1 段（書き換え H を含む）で切り口が保たれる、
- `omega_cut`: ω^x も同じ、
を示す。T2SeedSVFix（M.take x の r の引数 X₁ は動かないか切り口）を順位の帰納法で運ぶための部品。
-/
import Ytosk.V3PSeedOG

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

theorem le_true_of_le {s a : T} (h : s ≤ a) : le s a = true := by
  simp only [le, Bool.or_eq_true, beq_iff_eq]
  rcases (le_iff _ _).mp h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Cuts in front of a common prefix whose summands are at level `≥ s`. -/
theorem app_cutsHG {s : T} : ∀ (P : T) {X Y : T}, (∀ g ∈ summands P, s ≤ lev g) → X ∈ cutsHG s Y →
    app P X ∈ cutsHG s (app P Y)
  | z, _, _, _, h => by simpa using h
  | psi a x c, X, Y, hP, h => by
    simp only [app_psi]
    have ha : s ≤ a := by simpa using hP (psi a x z) (by simp [summands])
    exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨le_true_of_le ha, app c X,
      app_cutsHG c (fun g hg => hP g (by simp [summands, hg])) h, rfl⟩)))

/-- `ω^x` for `x ≥ E0` with head `ψ_w(b)`. -/
theorem omega_big {w b c : T} (h : ¬ lt (psi w b c) (psi z (psi one z z) z) = true) :
    omega (psi w b c) = psi w (add (split b (psi (add w one) z z)).1
      (sub (psi w b c) (psi w (split b (psi (add w one) z z)).1 z))) z := by
  unfold omega; rw [if_neg h]

theorem mem_summands_form : ∀ {t g : T}, g ∈ summands t → ∃ a y, g = psi a y z
  | z, _, h => by simp [summands] at h
  | psi a y c, g, h => by
    simp only [summands, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, y, rfl⟩
    · exact mem_summands_form h

/-- The summands kept by `split · Ω_{w+1}` are at level `> w`. -/
theorem split_lev {w : T} (b : T) : ∀ g ∈ summands (split b (psi (succ w) z z)).1, succ w ≤ lev g := by
  intro g hg
  have h := split_fst_ge (psi (succ w) z z) b g hg
  by_contra hlt
  apply h
  obtain ⟨a, y, rfl⟩ := mem_summands_form hg
  simp only [lev_psi] at hlt
  exact psi_lt_psi_z_iff.mpr (Or.inl (lt_of_not_ge hlt))



theorem omega_Om {w : T} (h : ¬ lt (psi w z z) (psi z (psi one z z) z) = true) : omega (psi w z z) = psi w z z := by
  rw [omega_big h]
  have hs : (split z (psi (add w one) z z)).1 = z := rfl
  rw [hs, sub_psi_self]; rfl

/-- `add p X = app p X` when `p`'s summands are above `Ω_{w+1}` and `X`'s head is below it. -/
theorem add_split_app {w : T} (b : T) {X : T} (hp : isOT (split b (psi (succ w) z z)).1 = true)
    (hX : X = z ∨ head X < psi (succ w) z z) :
    add (split b (psi (succ w) z z)).1 X = app (split b (psi (succ w) z z)).1 X := by
  by_cases hpz : (split b (psi (succ w) z z)).1 = z
  · rw [hpz]; rfl
  apply add_eq_app_of_last hp
  rcases hX with rfl | hX
  · exact z_le _
  · have hl := split_fst_ge (psi (succ w) z z) b _ (last_mem_summands hpz)
    exact le_of_lt (lt_of_lt_of_le hX (not_lt.mp hl))

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- A fixed point of `σ` compares the same with `t` and `σ t`. -/
theorem le_fix_iff {g t : T} (hg : isOT g = true) (hgf : sh V V' g = g) (ht : isOT t = true) :
    t ≤ g ↔ sh V V' t ≤ g := by
  constructor
  · intro h
    have := sh_le_sh hV hV' (le_of_lt hVV) ht hg h
    rwa [hgf] at this
  · intro h
    exact le_trans (le_sh hV hV' (le_of_lt hVV) ht) h

/-- The parts of a fixed term are fixed. -/
theorem sh_fix_parts {a x c : T} (h : sh V V' (psi a x c) = psi a x c) :
    sh V V' (psi a x z) = psi a x z ∧ sh V V' c = c := by
  rw [sh_psi_app] at h
  obtain ⟨a', x', h1⟩ := sh_single (V := V) (V' := V') a x
  rw [h1, app_psi, app_z] at h
  simp only [psi.injEq] at h
  obtain ⟨rfl, rfl, h3⟩ := h
  exact ⟨h1, h3⟩

/-- **Adding a cut summand to a fixed term**. -/
theorem add_cut : ∀ {B : T}, isOT B = true → sh V V' B = B → ∀ {t : T}, isOT t = true →
    (∃ u y, t = psi u y z) → t ∈ cutsHG V' (sh V V' t) → add B t ∈ cutsHG V' (add B (sh V V' t))
  | z, _, _, t, _, _, h => by simpa [add] using h
  | psi a1 b1 c1, hB, hfix, t, ht, htf, h => by
    obtain ⟨u, y, rfl⟩ := htf
    obtain ⟨hg, hc⟩ := sh_fix_parts hV hV' hVV hfix
    obtain ⟨u', y', hs⟩ := sh_single (V := V) (V' := V') u y
    have hgo : isOT (psi a1 b1 z) = true := isOT_head hB
    have hso : isOT (psi u' y' z) = true := by rw [← hs]; exact isOT_sh hV hV' hVV ht
    have hiff := le_fix_iff hV hV' hVV hgo hg ht
    rw [hs] at hiff h ⊢
    have e1 : add (psi a1 b1 c1) (psi u y z) =
        if lt (psi a1 b1 z) (psi u y z) then psi u y z else psi a1 b1 (add c1 (psi u y z)) := rfl
    have e2 : add (psi a1 b1 c1) (psi u' y' z) =
        if lt (psi a1 b1 z) (psi u' y' z) then psi u' y' z else psi a1 b1 (add c1 (psi u' y' z)) := rfl
    rw [e1, e2]
    by_cases hl : lt (psi a1 b1 z) (psi u y z) = true
    · have hl' : lt (psi a1 b1 z) (psi u' y' z) = true := by
        by_contra hn
        have h1 : psi u' y' z ≤ psi a1 b1 z := not_lt.mp hn
        exact absurd hl (not_lt.mpr (hiff.mpr h1))
      rw [if_pos hl, if_pos hl']; exact h
    · have hle : psi u y z ≤ psi a1 b1 z := not_lt.mp hl
      have hl' : ¬ lt (psi a1 b1 z) (psi u' y' z) = true := not_lt.mpr (hiff.mp hle)
      rw [if_neg hl, if_neg hl']
      have hsa : V' ≤ a1 := by
        have h1 := cutsHG_lev h
        have h2 := lev_le_of_le (hiff.mp hle)
        simp only [lev_psi] at h1 h2
        exact le_trans h1 h2
      have hrec := add_cut (isOT_rest hB) hc (t := psi u y z) ht ⟨u, y, rfl⟩ (by rw [hs]; exact h)
      rw [hs] at hrec
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨le_true_of_le hsa, _, hrec, rfl⟩)))

/-- **A cut of its own image, split into head and rest**: with a nonzero rest, the head is fixed and the
rest is a cut of its image. -/
theorem cut_rest {a x c : T} (hc : c ≠ z) (h : psi a x c ∈ cutsHG V' (sh V V' (psi a x c))) :
    sh V V' (psi a x z) = psi a x z ∧ le V' a = true ∧ c ∈ cutsHG V' (sh V V' c) := by
  obtain ⟨a', x', h1⟩ := sh_single (V := V) (V' := V') a x
  rw [sh_psi_app, h1, app_psi, app_z] at h
  rcases mem_cutsHG_psi.mp h with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨hs, u, hu, he⟩
  · simp only [psi.injEq] at he; exact absurd he.2.2 hc
  · simp only [psi.injEq] at he; exact absurd he.2.2 hc
  · simp only [psi.injEq] at he; exact absurd he.2.2 hc
  · simp only [psi.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨h1, hs, hu⟩

/-- **The prefix of a cut is fixed**. -/
theorem cut_prefix_fix : ∀ (P : T) {R : T}, R ≠ z → app P R ∈ cutsHG V' (sh V V' (app P R)) →
    sh V V' P = P ∧ (∀ g ∈ summands P, V' ≤ lev g)
  | z, _, _, _ => ⟨sh_z, by simp [summands]⟩
  | psi a x c, R, hR, h => by
    rw [app_psi] at h
    have hcR : app c R ≠ z := by
      intro h0; cases c with
      | z => exact hR h0
      | psi _ _ _ => simp at h0
    obtain ⟨h1, hs, h2⟩ := cut_rest hV hV' hVV hcR h
    obtain ⟨h3, h4⟩ := cut_prefix_fix c hR h2
    refine ⟨by rw [sh_psi_app, h1, h3]; rfl, fun g hg => ?_⟩
    simp only [summands, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simpa using le_of_le_bool hs
    · exact h4 g hg

/-- **The last summand of a cut is a cut**. -/
theorem last_cut : ∀ {t : T}, t ∈ cutsHG V' (sh V V' t) → last t ∈ cutsHG V' (sh V V' (last t))
  | z, h => h
  | psi a x z, h => h
  | psi a x (psi a2 x2 c2), h => by
    obtain ⟨_, _, h2⟩ := cut_rest hV hV' hVV (by simp) h
    show last (psi a2 x2 c2) ∈ cutsHG V' (sh V V' (last (psi a2 x2 c2)))
    exact last_cut (t := psi a2 x2 c2) h2

/-- **`H` keeps a cut of the argument** (at a fixed level `u ≥ V′`). -/
theorem H_cut {u y : T} (hy : isOT (psi u y z) = true) (hVu : V < u) (hfu : shf V V' u = u)
    (hsu : V' ≤ u) (hc : y ∈ cutsHG V' (sh V V' y)) :
    H u y ∈ cutsHG V' (H u (sh V V' y)) := by
  have hyo := isOT_arg hy
  have huo := isOT_sub hy
  have hy' : isOT (psi u (sh V V' y) z) = true := by
    have := isOT_shTop hV hV' hVV hy (le_of_lt hVu); rwa [hfu] at this
  have htt : ∀ a b, isOT (psi a b z) = true →
      (sh V V' (psi a b z) < psi (succ u) z z ↔ psi a b z < psi (succ u) z z) := by
    intro a b hab
    have := sh_lt_om_succ hV hV' hVV huo hVu a b hab
    rwa [hfu] at this
  have hsp := sh_split hV hV' hVV htt hyo
  rw [H_eq hy, H_eq hy', hsp]
  have happ := split_app (psi (succ u) z z) y
  set hi := (split y (psi (succ u) z z)).1 with hhi
  set lo := (split y (psi (succ u) z z)).2 with hlo
  by_cases hl : lo = z
  · have hl' : sh V V' lo = z := by rw [hl]; exact sh_z
    rw [if_pos hl, if_pos hl', app_z_right, app_z_right]
    rw [hl, app_z_right] at happ
    rw [happ]; exact hc
  · have hl' : sh V V' lo ≠ z := fun h => hl (sh_eq_z_iff.mp h)
    rw [if_neg hl, if_neg hl']
    rw [← happ] at hc
    obtain ⟨hfix, hlev⟩ := cut_prefix_fix hV hV' hVV hi hl hc
    rw [hfix]
    apply app_cutsHG hi hlev
    rw [happ] at hc
    exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_true_of_le hsu, y, hc, rfl⟩)))

/-- **One step of `sp` keeps a cut** of the summand, from a fixed state `B`. The level `a` may move to
`a′` as long as the comparison with the summand is the same. -/
theorem step_cut {a a' B u y u' y' : T} (hB : isOT B = true) (hBf : sh V V' B = B)
    (ht : isOT (psi u y z) = true) (hσ : sh V V' (psi u y z) = psi u' y' z)
    (hc : psi u y z ∈ cutsHG V' (psi u' y' z))
    (hlvl : lt (psi a z z) (psi u y z) = true ↔ lt (psi a' z z) (psi u' y' z) = true) :
    step a B u y z ∈ cutsHG V' (step a' B u' y' z) := by
  have hto' : isOT (psi u' y' z) = true := by rw [← hσ]; exact isOT_sh hV hV' hVV ht
  have hadd : add B (psi u y z) ∈ cutsHG V' (add B (psi u' y' z)) := by
    have := add_cut hV hV' hVV hB hBf ht ⟨u, y, rfl⟩ (by rw [hσ]; exact hc)
    rwa [hσ] at this
  have hnorw : y = z → y' = z → step a B u y z ∈ cutsHG V' (step a' B u' y' z) := by
    intro h1 h2
    subst h1; subst h2
    unfold step
    rw [if_neg (fun h => T.not_lt_z _ h.1), if_neg (fun h => T.not_lt_z _ h.1)]
    exact hadd
  have hy'z : y = z → y' = z := by
    intro h0
    subst h0
    by_cases hVu : V < u
    · rw [sh_psi_gt hVu] at hσ; simp only [psi.injEq] at hσ; rw [← hσ.2.1]; exact sh_z
    · rw [sh_psi_le hVu] at hσ; simp only [psi.injEq] at hσ; exact hσ.2.1.symm
  rcases mem_cutsHG_psi.mp hc with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨hs, w, hw, he⟩ | ⟨_, w, hw, _⟩
  · simp only [psi.injEq] at he
    exact hnorw he.2.1 (hy'z he.2.1)
  · simp only [psi.injEq] at he
    exact hnorw he.2.1 (hy'z he.2.1)
  · -- the argument
    simp only [psi.injEq] at he
    obtain ⟨hu, hyw, -⟩ := he
    subst hu; subst hyw
    have hsu : V' ≤ u := le_of_le_bool hs
    have hVu : V < u := lt_of_lt_of_le hVV hsu
    rw [sh_psi_gt hVu] at hσ
    simp only [psi.injEq] at hσ
    obtain ⟨hfu, hyy, -⟩ := hσ
    subst hyy
    have hBy : lt B y = true ↔ lt B (sh V V' y) = true := by
      have h1 := le_fix_iff hV hV' hVV hB hBf (isOT_arg ht)
      constructor
      · intro h; by_contra hn
        have h2 : sh V V' y ≤ B := not_lt.mp (show ¬ B < sh V V' y from hn)
        exact (not_lt.mpr (h1.mpr h2)) h
      · intro h; by_contra hn
        have h2 : y ≤ B := not_lt.mp (show ¬ B < y from hn)
        exact (not_lt.mpr (h1.mp h2)) h
    unfold step
    by_cases hrw : lt B y = true ∧ lt (psi a z z) (psi u y z) = true
    · have hrw' : lt B (sh V V' y) = true ∧ lt (psi a' z z) (psi u (sh V V' y) z) = true :=
        ⟨hBy.mp hrw.1, hlvl.mp hrw.2⟩
      rw [if_pos hrw, if_pos hrw']
      exact H_cut hV hV' hVV ht hVu hfu hsu hw
    · have hrw' : ¬ (lt B (sh V V' y) = true ∧ lt (psi a' z z) (psi u (sh V V' y) z) = true) := by
        intro h; exact hrw ⟨hBy.mpr h.1, hlvl.mpr h.2⟩
      rw [if_neg hrw, if_neg hrw']
      exact hadd
  · simp [cutsHG] at hw


/-- **`ω^x` keeps a cut**. -/
theorem omega_cut {x : T} (hx : isOT x = true) (hc : x ∈ cutsHG V' (sh V V' x)) :
    sh V V' (omega x) = omega x ∨ omega x ∈ cutsHG V' (sh V V' (omega x)) := by
  by_cases hsmall : lt x (psi z (psi one z z) z) = true
  · left
    have : omega x = psi z x z := by unfold omega; rw [if_pos hsmall]
    rw [this, sh_psi_le (T.not_lt_z _), sh_z]
  cases x with
  | z => exact absurd (show lt z (psi z (psi one z z) z) = true from T.z_lt_psi _ _ _) hsmall
  | psi w b c =>
  by_cases hVw : V < w
  swap
  · left
    rw [omega_big hsmall, sh_psi_le hVw, sh_z]
  right
  have hσx : sh V V' (psi w b c) = psi (shf V V' w) (sh V V' b) (sh V V' c) := by
    rw [sh_psi_gt hVw]
  rw [sh_omega hV hV' hVV hx, hσx]
  have hbig' : ¬ lt (psi (shf V V' w) (sh V V' b) (sh V V' c)) (psi z (psi one z z) z) = true := by
    intro h
    rw [← hσx] at h
    exact hsmall (lt_of_le_of_lt (le_sh hV hV' (le_of_lt hVV) hx) h)
  have hwo : isOT w = true := isOT_sub hx
  have hbo : isOT b = true := isOT_arg hx
  rw [hσx] at hc
  rcases mem_cutsHG_psi.mp hc with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨hs, u, hu, he⟩ | ⟨hs, u, hu, he⟩
  · simp only [psi.injEq] at he
    obtain ⟨_, hb, hc0⟩ := he
    subst hb; subst hc0
    simp only [sh_z] at hbig' hc ⊢
    rw [omega_Om hsmall, omega_Om hbig']; exact hc
  · simp only [psi.injEq] at he
    obtain ⟨_, hb, hc0⟩ := he
    subst hb; subst hc0
    simp only [sh_z] at hbig' hc ⊢
    rw [omega_Om hsmall, omega_Om hbig']; exact hc
  · -- the argument of the head
    simp only [psi.injEq] at he
    obtain ⟨hfw, hbu, hc0⟩ := he
    subst hbu; subst hc0
    have hfw' : shf V V' w = w := hfw.symm
    have hsw : V' ≤ w := by rw [← hfw']; exact le_of_le_bool hs
    simp only [sh_z, hfw'] at hbig' hc ⊢
    rw [omega_big hsmall, omega_big hbig', add_one_eq_succ hwo]
    have htt : ∀ a y, isOT (psi a y z) = true →
        (sh V V' (psi a y z) < psi (succ w) z z ↔ psi a y z < psi (succ w) z z) := by
      intro a y hay
      have := sh_lt_om_succ hV hV' hVV hwo hVw a y hay
      rwa [hfw'] at this
    rw [sh_split hV hV' hVV htt hbo]
    have happ := split_app (psi (succ w) z z) b
    have hpo : isOT (split b (psi (succ w) z z)).1 = true := isOT_app_left (by rw [happ]; exact hbo)
    have hθ : ∀ y, psi w y z < psi (succ w) z z := fun y => psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self w))
    by_cases hlo : (split b (psi (succ w) z z)).2 = z
    · rw [hlo, app_z_right] at happ
      have hsplit : split b (psi (succ w) z z) = (b, z) := Prod.ext happ hlo
      rw [hsplit]
      simp only [sh_z]
      rw [sub_psi_self, sub_psi_self]
      simp only [sub_z_right, add_z_right]
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_true_of_le hsw, b, hu, rfl⟩)))
    · rw [← happ] at hu
      obtain ⟨hpf, hplev⟩ := cut_prefix_fix hV hV' hVV _ hlo hu
      rw [happ] at hu
      rw [hpf]
      have hpb : (split b (psi (succ w) z z)).1 < b := by
        nth_rewrite 2 [← happ]; exact lt_app_of hlo
      have hpb' : (split b (psi (succ w) z z)).1 < sh V V' b :=
        lt_of_lt_of_le hpb (le_sh hV hV' (le_of_lt hVV) hbo)
      rw [sub_psi_psi, sub_psi_psi, if_pos (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hpb⟩)),
        if_pos (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hpb'⟩)),
        add_split_app b hpo (Or.inr (show head (psi w b z) < _ from hθ b)),
        add_split_app b hpo (Or.inr (show head (psi w (sh V V' b) z) < _ from hθ _))]
      refine mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_true_of_le hsw, _, app_cutsHG _ hplev ?_, rfl⟩)))
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_true_of_le hsw, b, hu, rfl⟩)))
  · -- the rest
    simp only [psi.injEq] at he
    obtain ⟨hfw, hbb, hcu⟩ := he
    subst hcu
    have hfw' : shf V V' w = w := hfw.symm
    have hbb' : sh V V' b = b := hbb.symm
    have hsw : V' ≤ w := by rw [← hfw']; exact le_of_le_bool hs
    simp only [hfw', hbb'] at hbig' hc ⊢
    rw [omega_big hsmall, omega_big hbig', add_one_eq_succ hwo, sub_psi_psi, sub_psi_psi]
    have hpo : isOT (split b (psi (succ w) z z)).1 = true := by
      have happ := split_app (psi (succ w) z z) b
      exact isOT_app_left (by rw [happ]; exact hbo)
    have hθ : psi w b z < psi (succ w) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self w))
    have hlev : ∀ g ∈ summands (split b (psi (succ w) z z)).1, V' ≤ lev g :=
      fun g hg => le_trans hsw (le_trans (le_of_lt (lt_succ_self w)) (split_lev b g hg))
    have hσo : isOT (psi w b (sh V V' c)) = true := by
      have := isOT_sh hV hV' hVV hx; rwa [hσx, hfw', hbb'] at this
    by_cases hpb : psi w (split b (psi (succ w) z z)).1 z < psi w b z
    · rw [if_pos hpb, if_pos hpb, add_split_app b hpo (Or.inr (show head (psi w b c) < _ from hθ)),
        add_split_app b hpo (Or.inr (show head (psi w b (sh V V' c)) < _ from hθ))]
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_true_of_le hsw, _, app_cutsHG _ hlev hc, rfl⟩)))
    · rw [if_neg hpb, if_neg hpb, sub_z_right, sub_z_right]
      have h1 : head c ≤ psi w b z := (isOT_psi_iff.mp hx).2.2.2.1
      have h2 : head (sh V V' c) ≤ psi w b z := (isOT_psi_iff.mp hσo).2.2.2.1
      rw [add_split_app b hpo (Or.inr (lt_of_le_of_lt h1 hθ)), add_split_app b hpo (Or.inr (lt_of_le_of_lt h2 hθ))]
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_true_of_le hsw, _, app_cutsHG _ hlev hu, rfl⟩)))

end

end Ytosk.G
