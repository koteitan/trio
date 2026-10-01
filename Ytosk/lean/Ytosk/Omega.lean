/-
**ω 冪 `omega` は標準形を保つ（`isOT_omega`）。**

- x < ψ_0(Ω_1) なら ω^x = ψ_0(x)。標準形の y < ψ_0(Ω_1) では y < ψ_0(y) なので、x の成分は x より小さい。
- それ以外では x = ψ_s(b) + c、p = b の Ω_{s+1} 以上の部分として、ω^x = ψ_s(p + x)（b に低い部分があるとき）か
  ψ_s(b + c)。b の低い部分は ψ_s(b) より小さいので、成分は引数より小さい。
-/
import Ytosk.SF

namespace Ytosk

open T

/-- `ψ_0(Ω_1)`. -/
def E0 : T := psi z (Om one) z

/-! ## 切り分け `split` -/

theorem split_app (t : T) : ∀ b : T, app (split b t).1 (split b t).2 = b
  | z => rfl
  | psi a b' c => by
    simp only [split]
    split
    · rfl
    · simp [split_app t c]

theorem split_fst_ge (t : T) : ∀ b : T, ∀ q ∈ summands (split b t).1, ¬ q < t
  | z => by simp [split, summands]
  | psi a b' c => by
    simp only [split]
    split
    · simp [summands]
    · rename_i h
      intro q hq
      simp only [summands, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h
      · exact split_fst_ge t c q hq

theorem split_snd_head (t : T) : ∀ b : T, (split b t).2 = z ∨ head (split b t).2 < t
  | z => Or.inl rfl
  | psi a b' c => by
    simp only [split]
    split
    · rename_i h; exact Or.inr (by simpa [head] using h)
    · exact split_snd_head t c

/-! ## 連結の標準形 -/

theorem isOT_app_of : ∀ {p x : T}, isOT p = true → isOT x = true →
    (∀ q ∈ summands p, head x ≤ q) → isOT (app p x) = true
  | z, x, _, hx, _ => hx
  | psi a b c, x, hp, hx, hq => by
    rw [app_psi, isOT_psi_iff]
    obtain ⟨h1, h2, h3, h4, h5⟩ := isOT_psi_iff.mp hp
    refine ⟨h1, h2, isOT_app_of h3 hx (fun q hq' => hq q (by simp [summands, hq'])), ?_, h5⟩
    by_cases hc : c = z
    · subst hc; simpa using hq (psi a b z) (by simp [summands])
    · rw [head_app_of_ne x hc]; exact h4

theorem comps_eq_nil_of_lev {u : T} : ∀ {t : T}, (∀ q ∈ summands t, lev q < u) → comps u t = []
  | z, _ => rfl
  | psi s b c, h => by
    have h1 : s < u := by simpa using h (psi s b z) (by simp [summands])
    have h2 : comps u c = [] := comps_eq_nil_of_lev (fun q hq => h q (by simp [summands, hq]))
    have : lt s u = true := h1
    simp [comps, this, h2]

/-- The summands of a standard term are at or below its head. -/
theorem summands_le_head : ∀ {t : T}, isOT t = true → ∀ q ∈ summands t, q ≤ head t
  | z, _ => by simp [summands]
  | psi a b c, h => by
    intro q hq
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact le_refl _
    · have h4 := (isOT_psi_iff.mp h).2.2.2.1
      by_cases hc : c = z
      · subst hc; simp [summands] at hq
      · exact le_trans (summands_le_head (isOT_rest h) q hq) h4

theorem comps_self_nil {s : T} (hs : isOT s = true) : comps s s = [] := by
  apply comps_eq_nil_of_lev
  intro q hq
  have h1 : q ≤ head s := summands_le_head hs q hq
  have hne : s ≠ z := by rintro rfl; simp [summands] at hq
  obtain ⟨a, b, rfl⟩ := mem_summands hq
  have h2 : lev (psi a b z) ≤ lev (head s) := lev_le_of_le h1
  have h3 : lev (head s) < s := by
    cases s with
    | z => exact absurd rfl hne
    | psi => simpa [head] using lev_lt_of_ne_z (by simp : psi _ _ _ ≠ z)
  exact lt_of_le_of_lt h2 h3

/-- In a standard `ψ_s(b) + c`, the level-`s` components of `c` are at most `b`. -/
theorem comps_tail_le {s b : T} : ∀ {c : T}, isOT c = true → head c ≤ psi s b z →
    ∀ g ∈ comps s c, g ≤ b
  | z, _, _ => by simp [comps]
  | psi s' w c', hc, hh => by
    intro g hg
    simp only [comps, List.mem_append] at hg
    have hrest : head c' ≤ psi s b z := by
      by_cases hc' : c' = z
      · subst hc'; exact z_le _
      · exact le_trans (isOT_psi_iff.mp hc).2.2.2.1 (by simpa [head] using hh)
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      · rename_i hns
        have hle : psi s' w z ≤ psi s b z := by simpa [head] using hh
        have hss : s' = s ∧ w ≤ b := by
          rcases (le_iff _ _).mp hle with h | h
          · rw [psi_lt_psi_z_iff] at h
            rcases h with h | ⟨rfl, h⟩
            · exact absurd h (by simpa [lt_iff_lt] using hns)
            · exact ⟨rfl, le_of_lt h⟩
          · simp only [psi.injEq, and_true] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, le_refl _⟩
        obtain ⟨rfl, hwb⟩ := hss
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact hwb
        · exact le_of_lt (lt_of_lt_of_le (comps_lt (isOT_head hc) g hg) hwb)
        · rw [comps_self_nil (isOT_sub hc)] at hg; simp at hg
    · exact comps_tail_le (isOT_rest hc) hrest g hg

/-! ## x < ψ_0(Ω_1) の場合 -/

theorem below_E0 {s w c : T} (h : psi s w c < E0) : s = z ∧ w < Om one := by
  rw [E0, psi_lt_psi_z_iff] at h
  rcases h with h | ⟨rfl, h⟩
  · exact absurd h (T.not_lt_z _)
  · exact ⟨rfl, h⟩

/-- The argument of a standard level-0 summand below `Ω_1` is below `ψ_0(Ω_1)`. -/
theorem arg_lt_E0 {w c : T} (hot : isOT (psi z w c) = true) (hw : w < Om one) : w < E0 := by
  rcases lt_or_ge w E0 with h | h
  · exact h
  · exfalso
    cases w with
    | z => exact absurd h (not_le_of_gt (T.z_lt_psi _ _ _))
    | psi s' w' c' =>
      have hs' : s' = z := by
        have : s' < one := by
          rw [Om, T.psi_lt_psi] at hw
          rcases hw with hw | ⟨_, hw⟩ | ⟨_, _, hw⟩
          · exact hw
          · exact absurd hw (T.not_lt_z _)
          · exact absurd hw (T.not_lt_z _)
        exact lt_one_iff.mp this
      subst hs'
      have hw' : Om one ≤ w' := by
        rcases le_or_gt (Om one) w' with h1 | h1
        · exact h1
        · exfalso
          apply not_lt_of_ge h
          rw [E0, T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h1⟩)
      have hnz : lt z z = false := rfl
      have := comps_lt hot w' (by simp [comps, hnz])
      exact absurd (lt_trans this (lt_of_lt_of_le hw hw')) (lt_irrefl _)

theorem lt_psi0_self : ∀ {y : T}, isOT y = true → y < E0 → y < psi z y z
  | z, _, _ => T.z_lt_psi _ _ _
  | psi s w c, hot, h => by
    obtain ⟨rfl, hw⟩ := below_E0 h
    have hwE := arg_lt_E0 hot hw
    have ih := lt_psi0_self (isOT_arg hot) hwE
    rw [psi_lt_psi_z_iff]
    refine Or.inr ⟨rfl, lt_of_lt_of_le ih ?_⟩
    rw [le_iff, T.psi_lt_psi]
    cases c with
    | z => exact Or.inr rfl
    | psi => exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩))

theorem comps_z_lt_of_lt_E0 : ∀ {x : T}, isOT x = true → x < E0 → ∀ g ∈ comps z x, g < x
  | z, _, _ => by simp [comps]
  | psi s w c, hot, h => by
    obtain ⟨rfl, hw⟩ := below_E0 h
    have hwE := arg_lt_E0 hot hw
    have hle : psi z w z ≤ psi z w c := by
      rw [le_iff, T.psi_lt_psi]
      cases c with
      | z => exact Or.inr rfl
      | psi => exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩))
    have hwx : w < psi z w c := lt_of_lt_of_le (lt_psi0_self (isOT_arg hot) hwE) hle
    intro g hg
    have hnz : lt z z = false := rfl
    simp only [comps, hnz, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact hwx
    · exact lt_trans (comps_lt hot g hg) hwx
    · simp at hg
    · have hcx : c < psi z w c := rest_lt hot
      exact lt_trans (comps_z_lt_of_lt_E0 (isOT_rest hot) (lt_trans hcx h) g hg) hcx

/-! ## ω 冪の標準形 -/

theorem app_lt_app_left : ∀ (p : T) {y y' : T}, y < y' → app p y < app p y'
  | z, _, _, h => h
  | psi a b c, y, y', h => by
    simp only [app_psi]; rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, app_lt_app_left c h⟩)

theorem lt_app_of {x y : T} (hy : y ≠ z) : x < app x y := by
  cases x with
  | z =>
    cases y with
    | z => exact absurd rfl hy
    | psi => exact T.z_lt_psi _ _ _
  | psi => exact lt_app_left (by simp) hy

theorem le_app_self (x y : T) : x ≤ app x y := by
  by_cases hy : y = z
  · subst hy; rw [app_z_right]
  · exact le_of_lt (lt_app_of hy)

/-- `ω^x` is standard. -/
theorem isOT_omega {x : T} (hx : isOT x = true) : isOT (omega x) = true := by
  unfold omega
  split
  · rename_i hlt
    rw [isOT_psi_iff]
    exact ⟨rfl, hx, rfl, z_le _, comps_z_lt_of_lt_E0 hx hlt⟩
  · cases x with
    | z => exact isOT_one
    | psi s b c =>
      simp only
      have hs := isOT_sub hx
      have hb := isOT_arg hx
      have hc := isOT_rest hx
      have hcomp := comps_lt hx
      have hhc : head c ≤ psi s b z := (isOT_psi_iff.mp hx).2.2.2.1
      have hOm : psi s b z < Om (succ s) := by
        rw [Om, psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s)
      rw [add_one_eq_succ hs]
      have hbpl : app (split b (psi (succ s) z z)).1 (split b (psi (succ s) z z)).2 = b := split_app _ b
      have hpge := split_fst_ge (psi (succ s) z z) b
      have hlo1 := split_snd_head (psi (succ s) z z) b
      generalize (split b (psi (succ s) z z)) = pr at hbpl hpge hlo1 ⊢
      obtain ⟨p, lo⟩ := pr
      simp only at hbpl hpge hlo1 ⊢
      have hpot : isOT p = true := by rw [← hbpl] at hb; exact isOT_app_left hb
      have hge : ∀ q ∈ summands p, psi s b z ≤ q := fun q hq =>
        le_of_lt (lt_of_lt_of_le hOm (le_of_not_gt (hpge q hq)))
      have hcp : ∀ g ∈ comps s p, g < b := fun g hg =>
        hcomp g (by rw [← hbpl, comps_app]; exact List.mem_append_left _ hg)
      have hss : lt s s = false := Bool.eq_false_iff.mpr (lt_irrefl' s)
      have hcx : ∀ g ∈ comps s (psi s b c), g ≤ b := by
        intro g hg
        simp only [comps, hss, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
        rcases hg with (rfl | hg | hg) | hg
        · exact le_refl _
        · exact le_of_lt (hcomp g hg)
        · rw [comps_self_nil hs] at hg; simp at hg
        · exact comps_tail_le hc hhc g hg
      by_cases hlo : lo = z
      · subst hlo
        simp only [app_z_right] at hbpl
        subst hbpl
        have hsub : sub (psi s p c) (psi s p z) = c := by
          simp only [sub]; rw [if_neg (show ¬ lt (psi s p z) (psi s p z) = true from lt_irrefl' _)]; cases c <;> rfl
        rw [hsub]
        have happ : isOT (app p c) = true := isOT_app_of hpot hc (fun q hq => le_trans hhc (hge q hq))
        rw [add_eq_app happ, isOT_psi_iff]
        refine ⟨hs, happ, rfl, z_le _, ?_⟩
        intro g hg
        rw [comps_app] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact lt_of_lt_of_le (hcomp g hg) (le_app_self _ _)
        · have hcz : c ≠ z := by rintro rfl; simp [comps] at hg
          exact lt_of_le_of_lt (comps_tail_le hc hhc g hg) (lt_app_of hcz)
      · have hpb : psi s p z < psi s b z := by
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, by rw [← hbpl]; exact lt_app_of hlo⟩
        have hsub : sub (psi s b c) (psi s p z) = psi s b c := by
          simp only [sub]; exact if_pos hpb
        rw [hsub]
        have happ : isOT (app p (psi s b c)) = true := isOT_app_of hpot hx hge
        rw [add_eq_app happ, isOT_psi_iff]
        have hlolt : lo < psi s b z := by
          rcases hlo1 with h | h
          · exact absurd h hlo
          cases lo with
          | z => exact absurd rfl hlo
          | psi s' w c'' =>
            have hs' : s' ≤ s := by
              have : s' < succ s := by
                have h' : psi s' w z < psi (succ s) z z := h
                rw [psi_lt_psi_z_iff] at h'
                rcases h' with h' | ⟨_, h'⟩
                · exact h'
                · exact absurd h' (T.not_lt_z _)
              exact lt_succ_iff.mp this
            rw [T.psi_lt_psi]
            rcases (le_iff _ _).mp hs' with h2 | h2
            · exact Or.inl h2
            · refine Or.inr (Or.inl ⟨h2, hcomp w ?_⟩)
              rw [← hbpl, comps_app]; apply List.mem_append_right
              rw [h2]; simp [comps, hss]
        have hbY : b < app p (psi s b c) :=
          calc b = app p lo := hbpl.symm
            _ < app p (psi s b c) := app_lt_app_left p (lt_of_lt_of_le hlolt (head_le_self (psi s b c)))
        refine ⟨hs, happ, rfl, z_le _, ?_⟩
        intro g hg
        rw [comps_app] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact lt_trans (hcp g hg) hbY
        · exact lt_of_le_of_lt (hcx g hg) hbY

end Ytosk
