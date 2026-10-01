/-
**落とす補題: 枠 1 段で親が標準形のままであること。**

`node_lhd` と同じ仮定の下で、新しい親 ψ_a(step a B c′) も標準形（`node_ot`）。場合分けは `node_lhd` と同じ:
- 引数どうしの ◁ がある道（書き換えなし同士・c′ だけ書き換え（B = 0）・高い部分が同じ書き換え同士）は
  `ot_parent_lhd`（Buchholz の補題 3.4）。
- 小さい道（s′ < s・c だけ書き換え）は `ot_parent_small`。
- 書き換え同士・添字が同じ・高い部分が違う場合は、y′ の段 a の成分を X′ 以下と示す（`comps_le_tt_diff`）。
  a = s なら ψ_s(y′) の標準形から出る。a < s では子の ψ の段の ◁ だけでは足りず、引数どうしの ◁ y′ ◁ y を
  仮定する（補題 3.4 の帰納法で、間の項 C ≤ hi(y) には C 自身、C > hi(y) には hi(y) を使う）。
-/
import Ytosk.V3StepOT

namespace Ytosk

open T

/-- **Both rewrite, same subscript, different high parts**: the components of `y'` at the level `a` are
at most `X' = H(s, y')`, given the argument-level `y' ◁ y` and the old parent standard. -/
theorem comps_le_tt_diff {a s y' y : T} (hc' : isOT (psi s y' z) = true) (hc : isOT (psi s y z) = true)
    {η : T} (hl : Lhd η y' y) (hη : ∀ d ∈ comps a η, d ≤ H s y')
    (hot : isOT (psi a (H s y) z) = true)
    (hhi : (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1) :
    ∀ g ∈ comps a y', g ≤ H s y' := by
  have hHX := H_eq hc
  rw [H_eq hc'] at hη ⊢
  rw [hHX] at hot
  set θ := psi (succ s) z z
  have ey := split_app θ y
  have ey' := split_app θ y'
  set hi := (split y θ).1
  set lo := (split y θ).2
  set hi' := (split y' θ).1
  set lo' := (split y' θ).2
  set X' := app hi' (if lo' = z then z else psi s y' z)
  have hy'X' : y' ≤ X' := by
    by_cases hl' : lo' = z
    · simp only [X', if_pos hl']; rw [← ey', hl']
    · simp only [X', if_neg hl']
      exact le_of_lt (lt_of_eq_of_lt ey'.symm (app_lt_app_left hi' (split_lo_lt hc' hl')))
  have hy'hi : y' < hi := by
    rw [← ey']; exact app_lt_of_lt_hi hhi (split_fst_ge θ y) (split_snd_head θ y')
  have hhiy : hi ≤ y := by rw [← ey]; exact le_app_self _ _
  have key : ∀ n, ∀ g, size g = n → g ∈ comps a y' → g ≤ X' := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro g hgn hg
      by_contra hbad
      have hX'g : X' < g := lt_of_not_ge hbad
      have hy'g : y' < g := lt_of_le_of_lt hy'X' hX'g
      have hgz : ∀ d ∈ Gc a η, ¬ g ≤ d := by
        intro d hd hgd
        simp only [Gc, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact T.not_lt_z _ (lt_of_lt_of_le hX'g hgd)
        · exact hbad (le_trans hgd (hη d hd))
      by_cases hghi : g ≤ hi
      · obtain ⟨d, hd, hgd⟩ := hl.2 a g hy'g (le_trans hghi hhiy) g hg
        rcases List.mem_append.mp hd with hd | hd
        · have := ih (size d) (hgn ▸ size_comps hd) d rfl (comps_trans hg d hd)
          exact hbad (le_trans hgd this)
        · exact hgz d hd hgd
      · have hhig : hi < g := lt_of_not_ge hghi
        obtain ⟨d, hd, hgd⟩ := hl.2 a hi hy'hi hhiy g hg
        rcases List.mem_append.mp hd with hd | hd
        · have hdX : d < app hi (if lo = z then z else psi s y z) := by
            apply comps_lt hot
            rw [comps_app]; exact List.mem_append_left _ hd
          have := comps_lt_prefix hd hdX
          exact lt_irrefl' _ (lt_of_lt_of_le (lt_trans this hhig) hgd)
        · exact hgz d hd hgd
  exact fun g hg => key (size g) g rfl hg

/-- **One frame keeps the new parent standard.** -/
theorem node_ot {a B s' y' s y : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z))
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hsub : SubSmall a s) (hsub' : SubSmall a s')
    (hBcl : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → Closed a B)
    (hy : s' = s → lt a s = true → y' ≠ y → ∃ η, Lhd η y' y ∧ ∀ d ∈ comps a η, d ≤ H s y')
    (hot : isOT (psi a (step a B s y z) z) = true) (hBot : isOT (psi a B z) = true) :
    isOT (psi a (step a B s' y' z) z) = true := by
  have ha := isOT_sub hBot
  have hX'ot : isOT (step a B s' y' z) = true := isOT_step (isOT_arg hBot) hc'
  rcases hrel with h | hl
  · simp only [psi.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact hot
  by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- both rewrite
      have hst : step a B s y z = H s y := by unfold step; rw [if_pos ht]
      have hst' : step a B s' y' z = H s' y' := by unfold step; rw [if_pos ht']
      rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨hs, hyy⟩
      · obtain ⟨hcomp, hyle⟩ := comps_le_of_sub_lt hl hss hsub'
        rw [hst', H_of_le_om hc' (ne_z_of_lt ht'.1) hyle] at hX'ot ⊢
        exact ot_parent_small ha hX'ot (closed_of_le_om hcomp a (lt_irrefl' a))
      · subst s'
        rw [hst] at hot
        rw [hst'] at hX'ot ⊢
        rcases split_mono (psi (succ s) z z) hyy with hhi | ⟨hhi, hlo⟩
        · -- different high parts
          have has := le_of_trig ht.2
          have hcy : ∀ g ∈ comps a y', g ≤ H s y' := by
            by_cases has' : lt a s = true
            · have hne : y' ≠ y := fun h => by subst h; exact absurd hhi (lt_irrefl' _)
              obtain ⟨η, hl', hη⟩ := hy rfl has' hne
              exact comps_le_tt_diff hc' hc hl' hη hot hhi
            · have has2 : a = s := le_antisymm has (not_lt.mp has')
              subst has2
              intro g hg
              exact le_trans (le_of_lt (comps_lt hc' g hg))
                (y_le_step (B := B) hc' (fun q hq => le_trans (le_of_lt hl.1) (hBc q hq))
                  (lt_irrefl' _) |>.trans (le_of_eq hst'))
          apply ot_parent_small ha hX'ot
          have hOm := om_le_H hc' (ne_z_of_lt ht'.1)
          intro g hg
          have hsu : ¬ s < a := not_lt.mpr has
          have hHX := H_eq hc'
          rw [hHX] at hg
          rw [comps_app] at hg
          rcases List.mem_append.mp hg with hg | hg
          · apply hcy
            have e := split_app (psi (succ s) z z) y'
            have : g ∈ comps a (app (split y' (psi (succ s) z z)).1 (split y' (psi (succ s) z z)).2) := by
              rw [comps_app]; exact List.mem_append_left _ hg
            rwa [e] at this
          · split at hg
            · simp [comps] at hg
            · rw [comps_psi_z_of_ge hsu] at hg
              simp only [List.mem_cons, List.mem_append] at hg
              rcases hg with rfl | hg | hg
              · exact y_le_step (B := B) hc' (fun q hq => le_trans (le_of_lt hl.1) (hBc q hq))
                  (not_lt.mpr has) |>.trans (le_of_eq hst')
              · exact hcy g hg
              · exact le_trans (hsub a (lt_irrefl' a) g hg) hOm
        · -- same high part: argument-level `◁`
          have hlo0 : (split y (psi (succ s) z z)).2 ≠ z := by
            intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
          apply ot_parent_lhd hot hX'ot
          rw [H_eq hc', H_eq hc, if_neg hlo0, hhi]
          by_cases hl' : (split y' (psi (succ s) z z)).2 = z
          · rw [if_pos hl', app_z_right]; exact lhdE_prefix _ _
          · rw [if_neg hl']; exact lhdE_app _ (Or.inr hl)
    · -- only the new child rewrites: `B = 0`, `X' = c'`, `X = c`
      have hac : psi a z z < psi s y z := lt_trans (show psi a z z < psi s' y' z from ht'.2) hl.1
      have hyB : ¬ B < y := fun h => ht ⟨h, hac⟩
      rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨rfl, hyy⟩
      · obtain ⟨_, hyle⟩ := comps_le_of_sub_lt hl hss hsub'
        by_cases hBz : B = z
        · subst hBz
          have hyz : y = z := by
            by_contra h; exact hyB (lt_of_le_of_ne (z_le _) (Ne.symm h))
          subst hyz
          have hst' : step a z s' y' z = psi s' y' z := by
            unfold step; rw [if_pos ht', H_of_le_om hc' (ne_z_of_lt ht'.1) hyle]
          have hst : step a z s z z = psi s z z := by unfold step; rw [if_neg ht]; rfl
          rw [hst] at hot
          rw [hst'] at hX'ot ⊢
          exact ot_parent_lhd hot hX'ot (Or.inr hl)
        · exfalso
          have hcB : psi s y z ≤ B := le_trans (hBc _ (head_mem_summands hBz)) (head_le_self B)
          have hy'c : y' ≤ psi s y z :=
            le_trans hyle (le_trans (psi_le_psi_arg (z_le y')) (le_of_lt hl.1))
          exact lt_irrefl' B (lt_of_lt_of_le (show B < y' from ht'.1) (le_trans hy'c hcB))
      · exact absurd (lt_trans (show B < y' from ht'.1) hyy) hyB
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- only the old child rewrites: the small route
      have hst' : step a B s' y' z = app B (psi s' y' z) := by
        unfold step; rw [if_neg ht', step_add (fun q hq => le_trans (le_of_lt hl.1) (hBc q hq))]
      rw [hst'] at hX'ot ⊢
      exact ot_parent_small ha hX'ot
        (closed_tn hl ht' ht hBc (hBcl ht' ht) hsub hsub' a (lt_irrefl' a))
    · -- no rewrite
      exact ot_parent_lhd hot hX'ot (lhdE_step_nn' (Or.inr hl) ht' ht hBc)

end Ytosk
