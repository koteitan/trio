/-
**ω^ は ◁ を保つ**（落とす補題ののりしろの枠で使う）。

- 両方 ψ_0(Ω_1) 未満なら ω^x = ψ_0(x)（`omega_lhd_small`）。
- 先頭の添字 s が同じなら ω^X = ψ_s(Y) の間の d = ψ_s(D)+R で D ≥ Y′。X′ の成分は、D ≤ b なら ψ_s(D)、
  D > b（D = hi + e）なら ψ_s(hi) + e か e を X′ と X の間に置いて ◁ で押さえる（`omega_lhd_same`）。
- 先頭の添字が上がると成り立たない: Ω_1·2 ◁ Ω_2 だが ω^(Ω_1·2) = ψ_1(Ω_1) は Ω_2 の下に ◁ で入らない
  （`omega_lhd_counterexample`）。
-/
import Ytosk.V3DropV

namespace Ytosk

open T

/-- `1 ≤ ω^X`. -/
theorem one_le_omega {X : T} (hX : isOT X = true) : one ≤ omega X := by
  by_cases h : X = z
  · subst h; right; rfl
  · have := omega_lt_omega (x := z) rfl hX (by cases X with | z => exact absurd rfl h | psi => exact T.z_lt_psi _ _ _)
    exact Or.inl this

/-- **The emptied sum**: `ω^0 = 1 ⊴ ω^X`. -/
theorem omega_lhd_z {X : T} (hX : isOT X = true) : LhdE (omega z) (omega X) :=
  lhdE_one (one_le_omega hX)

/-- **Case 1, below `ψ_0(Ω_1)`**: `ω^x = ψ_0(x)`. -/
theorem omega_lhd_small {X' X : T} (h : LhdE X' X) (hX' : X' < E0) (hX : X < E0) :
    LhdE (omega X') (omega X) := by
  rw [omega_small hX', omega_small hX]; exact lhdE_psi z h

/-- **Case 2, tail change**: the same leading summand `ψ_s(b)`, the tails `c′ ⊴ c`. -/
theorem omega_lhd_tail {s b c' c : T} (hX' : isOT (psi s b c') = true) (hX : isOT (psi s b c) = true)
    (hE : ¬ psi s b z < E0) (hc : LhdE c' c) : LhdE (omega (psi s b c')) (omega (psi s b c)) := by
  have hE' : ∀ {e}, ¬ psi s b e < E0 := fun he => hE (by
    obtain ⟨rfl, hb⟩ := below_E0 he
    unfold E0; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, hb⟩))
  rw [omega_big hX' hE', omega_big hX hE']
  by_cases hlo : (split b (psi (succ s) z z)).2 = z
  · rw [if_pos hlo, if_pos hlo]; exact lhdE_psi s (lhdE_app _ hc)
  · rw [if_neg hlo, if_neg hlo]
    apply lhdE_psi s; apply lhdE_app
    have := lhdE_app (psi s b z) hc
    simpa using this

/-! ## 先頭の添字が同じ場合 -/

/-- `x ≤ ω^x` above `ψ_0(Ω_1)`. -/
theorem le_omega_big {s b c : T} (hx : isOT (psi s b c) = true) (h : ¬ psi s b c < E0) :
    psi s b c ≤ omega (psi s b c) := by
  rw [omega_big hx h]
  have hbpl := split_app (psi (succ s) z z) b
  by_cases hlo : (split b (psi (succ s) z z)).2 = z
  · rw [if_pos hlo]
    rw [hlo, app_z_right] at hbpl
    by_cases hc : c = z
    · subst hc; rw [app_z_right, hbpl]
    · apply le_of_lt; rw [T.psi_lt_psi]; refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      conv_lhs => rw [← hbpl]
      exact lt_app_of hc
  · rw [if_neg hlo]
    apply le_of_lt; rw [T.psi_lt_psi]; refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    conv_lhs => rw [← hbpl]
    apply app_lt_app_left
    exact lt_of_lt_of_le (split_lo_lt hx hlo) (head_le_self (psi s b c))

/-- Domination of the components of `X′` through an intermediate `c ∈ [X′, X]`. -/
theorem dom_via {X' X c u : T} {L : List T} (hl : Lhd z X' X) (h1 : X' ≤ c) (h2 : c ≤ X)
    (hcL : ∀ g ∈ comps u c, ∃ y ∈ L, g ≤ y) (hz : z ∈ L) :
    ∀ g ∈ comps u X', ∃ y ∈ L, g ≤ y := by
  rcases (le_iff _ _).mp h1 with h1 | rfl
  · intro g hg
    obtain ⟨y, hy, hgy⟩ := hl.2 u c h1 h2 g hg
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨y', hy', hyy'⟩ := hcL y hy; exact ⟨y', hy', le_trans hgy hyy'⟩
    · simp [Gc, comps] at hy; subst hy; exact ⟨z, hz, hgy⟩
  · exact hcL

/-- The high part has no low part. -/
theorem split_hi_self (θ b : T) : split (split b θ).1 θ = ((split b θ).1, z) := by
  have h2 : (split (split b θ).1 θ).2 = z := split_snd_z_of_ge (split_fst_ge θ b)
  have h1 := split_app θ (split b θ).1
  rw [h2, app_z_right] at h1
  exact Prod.ext h1 h2

/-- **Case 3, the same leading subscript** (`◁` form). -/
theorem omega_lhd_same_lhd {s b' c' b c : T} (hX' : isOT (psi s b' c') = true)
    (hX : isOT (psi s b c) = true) (hE : ¬ psi s b' c' < E0) (hl : Lhd z (psi s b' c') (psi s b c)) :
    Lhd z (omega (psi s b' c')) (omega (psi s b c)) := by
  have hE2 : ¬ psi s b c < E0 := fun h => hE (lt_trans hl.1 h)
  refine ⟨omega_lt_omega hX' hX hl.1, ?_⟩
  have hle' := le_omega_big hX' hE
  rw [omega_big hX hE2]
  rw [omega_big hX' hE] at hle' ⊢
  have hbpl := split_app (psi (succ s) z z) b
  have hbpl' := split_app (psi (succ s) z z) b'
  have hlohd := split_snd_head (psi (succ s) z z) b
  have hhis := split_hi_self (psi (succ s) z z) b
  generalize psi (succ s) z z = θ at hbpl hbpl' hlohd hhis hle' ⊢
  generalize hW : (if (split b θ).2 = z then c else psi s b c) = W
  generalize hW' : (if (split b' θ).2 = z then c' else psi s b' c') = W' at hle' ⊢
  intro u d h1 h2
  obtain ⟨D, R, rfl, hD1, hD2⟩ := between_psi h1 h2
  have hsub : ∀ w ∈ comps u (psi s D z), w ∈ comps u (psi s D R) := by
    intro w hw; simp only [comps, List.mem_append] at hw ⊢; left; simpa using hw
  suffices key : ∀ g ∈ comps u (psi s (app (split b' θ).1 W') z),
      ∃ y ∈ comps u (psi s D z) ++ Gc u z, g ≤ y by
    intro g hg
    obtain ⟨y, hy, hgy⟩ := key g hg
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨y, List.mem_append_left _ (hsub y hy), hgy⟩
    · exact ⟨y, List.mem_append_right _ hy, hgy⟩
  by_cases hsu : lt s u = true
  · simp [comps, hsu]
  have hcD : comps u (psi s D z) = D :: (comps u D ++ comps u s) := by simp [comps, hsu]
  have hzL : z ∈ comps u (psi s D z) ++ Gc u z := by simp [Gc]
  have hLD : ∀ g ∈ comps u (psi s D z), ∃ y ∈ comps u (psi s D z) ++ Gc u z, g ≤ y :=
    fun g hg => ⟨g, List.mem_append_left _ hg, le_refl _⟩
  -- the components of `X′` are dominated
  have hX'dom : ∀ g ∈ comps u (psi s b' c'), ∃ y ∈ comps u (psi s D z) ++ Gc u z, g ≤ y := by
    by_cases hDb : D ≤ b
    · refine dom_via hl ?_ ?_ hLD hzL
      · refine le_trans hle' ?_
        rcases (le_iff _ _).mp hD1 with h | h
        · apply le_of_lt; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩
        · rw [h]
      · rcases (le_iff _ _).mp hDb with h | h
        · apply le_of_lt; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩)
        · rw [h]; exact head_le_self (psi s b c)
    · have hbD : b < D := lt_of_not_ge hDb
      obtain ⟨e, rfl, he1, he2⟩ := between_app (A := (split b θ).1) (x := (split b θ).2) (y := W)
        (by rw [hbpl]; exact hbD) hD2
      have hcL : ∀ g ∈ comps u (psi s (split b θ).1 e),
          ∃ y ∈ comps u (psi s (app (split b θ).1 e) z) ++ Gc u z, g ≤ y := by
        intro g hg
        have hc' : comps u (psi s (split b θ).1 e) =
            (split b θ).1 :: (comps u (split b θ).1 ++ comps u s) ++ comps u e := by simp [comps, hsu]
        rw [hc'] at hg
        rw [hcD]
        simp only [List.mem_append, List.mem_cons] at hg
        rcases hg with (rfl | hg | hg) | hg
        · exact ⟨app (split b θ).1 e, by simp, le_app_self _ _⟩
        · exact ⟨g, by simp [comps_app, hg], le_refl _⟩
        · exact ⟨g, by simp [hg], le_refl _⟩
        · exact ⟨g, by simp [comps_app, hg], le_refl _⟩
      have hcX : psi s (split b θ).1 e ≤ psi s b c := by
        by_cases hlo : (split b θ).2 = z
        · rw [hlo, app_z_right] at hbpl
          rw [← hW, if_pos hlo] at he2
          rw [hbpl]
          rcases (le_iff _ _).mp he2 with h | h
          · exact le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
          · rw [h]
        · apply le_of_lt; rw [T.psi_lt_psi]; refine Or.inr (Or.inl ⟨rfl, ?_⟩)
          conv_rhs => rw [← hbpl]
          exact lt_app_of hlo
      by_cases hX'c : psi s b' c' ≤ psi s (split b θ).1 e
      · exact dom_via hl hX'c hcX hcL hzL
      have hlt : psi s (split b θ).1 e < psi s b' c' := lt_of_not_ge hX'c
      have hX'X : psi s b' c' ≤ psi s b c := le_of_lt hl.1
      rw [T.psi_lt_psi] at hlt
      rcases hlt with hlt | ⟨_, hlt⟩ | ⟨_, hb', hlt⟩
      · exact absurd hlt (lt_irrefl' _)
      · -- `hi < b′ ≤ b`: `b′` has the same high part and a low part, so `X′ ≤ e`
        have hb'b : b' ≤ b := by
          rcases (le_iff _ _).mp hX'X with h | h
          · rw [T.psi_lt_psi] at h
            rcases h with h | ⟨_, h⟩ | ⟨_, h, _⟩
            · exact absurd h (lt_irrefl' _)
            · exact le_of_lt h
            · rw [h]
          · simp only [psi.injEq] at h; rw [h.2.1]
        obtain ⟨l2, rfl, hl21, hl22⟩ := between_app (A := (split b θ).1) (x := z) (y := (split b θ).2)
          (by rw [app_z_right]; exact hlt) (by rw [hbpl]; exact hb'b)
        have hlo : (split b θ).2 ≠ z := by
          intro h; rw [h] at hl22; exact absurd (lt_of_lt_of_le hl21 hl22) (lt_irrefl' _)
        have hl2 : l2 ≠ z := by rintro rfl; exact lt_irrefl' _ hl21
        have hhd : head l2 < θ := by
          rcases hlohd with h | h
          · exact absurd h hlo
          refine lt_of_le_of_lt ?_ h
          rcases (le_iff _ _).mp hl22 with h' | h'
          · exact head_le_of_lt h'
          · rw [h']
        have hsp : split (app (split b θ).1 l2) θ = ((split b θ).1, l2) := by
          rw [split_app_low (Or.inr hhd), hhis]; simp
        rw [hsp] at hW' hD1
        simp only at hW' hD1
        rw [if_neg hl2] at hW'
        rw [← hW'] at hD1
        have hX'e : psi s (app (split b θ).1 l2) c' ≤ e :=
          le_of_not_gt (fun h => absurd (lt_of_le_of_lt hD1 (app_lt_app_left _ h)) (lt_irrefl' _))
        have heX : e ≤ psi s b c := by rw [← hW, if_neg hlo] at he2; exact he2
        refine dom_via hl hX'e heX ?_ hzL
        intro g hg; exact ⟨g, by rw [hcD]; simp [comps_app, hg], le_refl _⟩
      · -- `b′ = hi`, `e < c′`: then `ω^X′ = ψ_s(hi + c′)` is above `ψ_s(hi + e)`
        subst hb'
        rw [hhis] at hW' hD1
        simp only at hW' hD1
        rw [if_pos trivial] at hW'
        rw [← hW'] at hD1
        exact absurd (lt_of_le_of_lt hD1 (app_lt_app_left _ hlt)) (lt_irrefl' _)
  intro g hg
  have hc : comps u (psi s (app (split b' θ).1 W') z) =
      app (split b' θ).1 W' :: (comps u (app (split b' θ).1 W') ++ comps u s) := by simp [comps, hsu]
  have hcX' : comps u (psi s b' c') = b' :: (comps u b' ++ comps u s) ++ comps u c' := by
    simp [comps, hsu]
  rw [hc] at hg
  simp only [List.mem_cons, List.mem_append] at hg
  rcases hg with rfl | hg | hg
  · exact ⟨D, by rw [hcD]; simp, hD1⟩
  · rw [comps_app] at hg
    apply hX'dom
    rcases List.mem_append.mp hg with hg | hg
    · have : g ∈ comps u b' := by rw [← hbpl', comps_app]; exact List.mem_append_left _ hg
      rw [hcX']; simp [this]
    · by_cases hlo' : (split b' θ).2 = z
      · rw [if_pos hlo'] at hW'; subst hW'; rw [hcX']; simp [hg]
      · rw [if_neg hlo'] at hW'; subst hW'; exact hg
  · exact ⟨g, by rw [hcD]; simp [hg], le_refl _⟩

theorem omega_lhd_same {s b' c' b c : T} (hX' : isOT (psi s b' c') = true)
    (hX : isOT (psi s b c) = true) (hE : ¬ psi s b' c' < E0) (h : LhdE (psi s b' c') (psi s b c)) :
    LhdE (omega (psi s b' c')) (omega (psi s b c)) := by
  rcases h with h | h
  · rw [h]; exact Or.inl rfl
  · exact Or.inr (omega_lhd_same_lhd hX' hX hE h)

/-- **`ω^` preserves `⊴`** when both sides are below `ψ_0(Ω_1)`, or `X′` is not and both have the same
leading subscript. Without `hs` it fails (`omega_lhd_counterexample`: `Ω_1·2 ◁ Ω_2`). -/
theorem omega_lhd {X' X : T} (hX' : isOT X' = true) (hX : isOT X = true)
    (h : LhdE X' X) (hE : X < E0 ∨ ¬ X' < E0)
    (hs : X < E0 ∨ ∃ s b' c' b c, X' = psi s b' c' ∧ X = psi s b c) :
    LhdE (omega X') (omega X) := by
  by_cases hXE : X < E0
  · exact omega_lhd_small h (lt_of_le_of_lt h.le hXE) hXE
  · have hX'E := hE.resolve_left hXE
    obtain ⟨s, b', c', b, c, rfl, rfl⟩ := hs.resolve_left hXE
    exact omega_lhd_same hX' hX hX'E h

/-! ## 反例: 先頭の添字が上がると成り立たない -/

/-- `Ω_1 + Ω_1`. -/
def cxX' : T := psi one z (psi one z z)
/-- `Ω_2`. -/
def cxX : T := psi (psi z z one) z z

theorem cx_lhd : Lhd z cxX' cxX := by
  refine ⟨by decide, fun u c _ _ g hg => ⟨z, by simp [Gc], ?_⟩⟩
  have : g = z := by
    simp only [cxX', one, comps] at hg
    split_ifs at hg <;> simp_all
  subst this; exact le_refl _

/-- **`ω^` does not preserve `◁` when the leading subscript grows**:
`Ω_1·2 ◁ Ω_2` but `ω^(Ω_1·2) = ψ_1(Ω_1)` is not `⊴ ω^(Ω_2) = Ω_2`. -/
theorem omega_lhd_counterexample :
    isOT cxX' = true ∧ isOT cxX = true ∧ LhdE cxX' cxX ∧ ¬ cxX' < E0 ∧
      ¬ LhdE (omega cxX') (omega cxX) := by
  refine ⟨by decide, by decide, Or.inr cx_lhd, by decide, ?_⟩
  have h1 : omega cxX' = psi one (psi one z z) z := by decide
  have h2 : omega cxX = cxX := by decide
  rw [h1, h2]
  rintro (h | h)
  · exact absurd h (by decide)
  · obtain ⟨y, hy, hle⟩ := h.2 z cxX h.1 (le_refl _) (psi one z z) (by decide)
    revert hle; revert hy; revert y; decide

end Ytosk
