/-
**始点の条件を定理にする（2 行・t = 1・q ≠ r）。**

S1: 落とした行列での r の値の引数 σ_x は b[0] = fs(b, 0) 以下（b = M での r の値の引数）。
q から r まで「落とした値の引数 ≤ fs(元の引数, 0)」を帰納法で示す（`frame_fs_le` と step の単調性）。
`drop_path` の σ_x ◁ b と合わせて、`seedOK_of_lhd` で始点 c1 = o_{M.take x}(r) は良い（`seed_of_drop`）。
-/
import Ytosk.TwoRowU

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- An all-high argument of `Ω_{μ+1}` cofinality (`μ < s`) has a nonzero `[0]`. -/
theorem fs_z_ne_z {y μ s : T} (hy : y ≠ z) (hcy : cof y = .big μ) (hμs : μ < s)
    (hhigh : loP s y = z) : fs y z ≠ z := by
  cases y with
  | z => exact absurd rfl hy
  | psi a b c =>
    cases c with
    | psi c1 d e => simp [fs]
    | z =>
      have hh : ¬ psi a b z < psi (succ s) z z := by
        intro hlt
        apply (show loP s (psi a b z) ≠ z from ?_) hhigh
        unfold loP; simp [split, show lt (psi a b z) (psi (succ s) z z) = true from hlt]
      unfold fs
      by_cases hb : b = z
      · subst hb
        rw [if_pos rfl]
        by_cases ha : a = z
        · subst ha; simp [cof] at hcy
        · rw [if_neg ha]
          by_cases hs : isSucc a = true
          · exfalso
            have hc' : cof (psi a z z) = .big (init a) := by simp [cof, ha, hs]
            rw [hc'] at hcy
            injection hcy with hμ
            have ha' : a = succ μ := by rw [← hμ]; exact (init_app_one hs).symm
            apply hh
            rw [ha', psi_lt_om_succ]
            exact lt_of_le_of_lt (succ_le_of_lt hμs) (lt_succ_self s)
          · rw [if_neg hs]; simp
      · rw [if_neg hb]
        by_cases hs : isSucc b = true
        · exfalso
          have : cof (psi a b z) = .omega := by simp [cof, hb, hs]
          rw [this] at hcy; cases hcy
        · rw [if_neg hs]
          split
          · split <;> simp
          · simp

theorem last_psi_form : ∀ {y : T}, y ≠ z → ∃ st u, last y = psi st u z
  | z, h => absurd rfl h
  | psi a b z, _ => ⟨a, b, rfl⟩
  | psi a b (psi c d e), _ => by
    show ∃ st u, last (psi c d e) = psi st u z
    exact last_psi_form (by simp)

/-- `[0]` of an all-high argument stays all high (the last summand keeps its subscript or vanishes),
when a last summand `ψ_st(0)` has a successor or zero subscript. -/
theorem loP_fs_z {y μ s : T} (hy : y ≠ z) (hcy : cof y = .big μ) (hhigh : loP s y = z)
    (hlast : ∀ st, last y = psi st z z → isSucc st = true ∨ st = z) : loP s (fs y z) = z := by
  obtain ⟨st, u, ht⟩ := last_psi_form hy
  have hdec : app (init y) (psi st u z) = y := by rw [← ht]; exact init_app_last y
  set P := init y with hPdef
  have htz : psi st u z ≠ z := by simp
  have hct : cof (psi st u z) = .big μ := by rw [← cof_app P htz, hdec]; exact hcy
  have hsP : (split P (psi (succ s) z z)).2 = z ∧ ¬ psi st u z < psi (succ s) z z := by
    by_contra hcon
    apply (show loP s y ≠ z from ?_) hhigh
    rw [← hdec]; unfold loP
    rw [split_app_single, if_neg (fun h => hcon ⟨h.1, h.2⟩)]
    intro h0; have := (app_eq_z h0).2; simp at this
  have hfs : fs y z = app P (fs (psi st u z) z) := by rw [← hdec]; exact fs_app P htz z
  rw [hfs]
  by_cases hu : u = z
  · subst hu
    rcases hlast st ht with hs | hs
    · have hsz : st ≠ z := by intro h; subst h; simp [isSucc, last, one] at hs
      have h0 : fs (psi st z z) z = z := by
        unfold fs; rw [if_pos rfl, if_neg hsz, if_pos hs]
      rw [h0, app_z_right]; exact hsP.1
    · subst hs; simp [cof] at hct
  · by_cases hus : isSucc u = true
    · exfalso
      have : cof (psi st u z) = .omega := by simp [cof, hu, hus]
      rw [this] at hct; cases hct
    · cases hcu : cof u with
      | big μ' =>
        by_cases hl : lt μ' st = true
        · have hpass := fs_psi_pass hu hcu hl z
          rw [hpass]
          unfold loP
          rw [split_app_single, if_pos ⟨hsP.1, fun h => hsP.2 (psi_lt_om_succ.mpr (psi_lt_om_succ.mp h))⟩]
        · exfalso
          have : cof (psi st u z) = .omega := by simp [cof, hu, hus, hcu, hl]
          rw [this] at hct; cases hct
      | zero => exfalso; have : cof (psi st u z) = .zero := by simp [cof, hu, hus, hcu]
                rw [this] at hct; cases hct
      | succ => exfalso; have : cof (psi st u z) = .succ := by simp [cof, hu, hus, hcu]
                rw [this] at hct; cases hct
      | omega => exfalso; have : cof (psi st u z) = .omega := by simp [cof, hu, hus, hcu]
                 rw [this] at hct; cases hct

/-- **The step against `[0]`**: one step on `y[0]` is at most `[0]` of the step on `y`. -/
theorem frame_fs_le {a B s y μ : T}
    (hc : isOT (psi s y z) = true) (hy : y ≠ z) (hcy : cof y = .big μ) (hμs : lt μ s = true)
    (happ : isOT (app B (psi s y z)) = true)
    (hHi : B ≠ z → lt B y = true → lt (psi a z z) (psi s y z) = true → hiP s y = B ∧ loP s y ≠ z)
    (hFC : B = z → lt z y = true → lt (psi a z z) (psi s y z) = true → a = s →
      hiP s y = z ∧ loP s y ≠ z)
    (hlast : ∀ st, last y = psi st z z → isSucc st = true ∨ st = z) :
    step a B s (fs y z) z ≤ fs (step a B s y z) z := by
  have hpsi : fs (psi s y z) z = psi s (fs y z) z := fs_psi_pass hy hcy hμs z
  have hV : Valid (psi s y z) z := by
    refine ⟨rfl, ?_⟩
    have : cof (psi s y z) = .big μ := by
      have h1 : isSucc y = false := not_succ_of_cof_big hcy
      simp [cof, hy, h1, hcy, hμs]
    rw [this]; exact T.z_lt_psi _ _ _
  obtain ⟨hfot, hflt⟩ := fs_ot_lt hc hV
  rw [hpsi] at hfot hflt
  have hylt : fs y z < y := by
    rw [psi_lt_psi_z_iff] at hflt
    rcases hflt with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  by_cases hB : B = z
  · subst hB
    rw [step_first hc, step_first hfot]
    by_cases htr : lt z y = true ∧ lt (psi a z z) (psi s y z) = true
    · rw [if_pos htr]
      by_cases hlo : loP s y = z
      · -- absorbed
        have has : a < s := by
          have h2 : psi a z z < psi s y z := htr.2
          rw [psi_lt_psi_z_iff] at h2
          rcases h2 with h | ⟨h, _⟩
          · exact h
          · exact absurd hlo (hFC rfl htr.1 htr.2 h).2
        have hyhi : hiP s y = y := by
          have := hiP_loP s y; rw [hlo, app_z_right] at this; exact this
        rw [if_pos hlo, app_z_right, hyhi]
        have hfz : fs y z ≠ z := fs_z_ne_z hy hcy hμs hlo
        have htr' : lt z (fs y z) = true ∧ lt (psi a z z) (psi s (fs y z) z) = true :=
          ⟨lt_of_le_of_ne (z_le _) (Ne.symm hfz), (psi_lt_psi_z_iff.mpr (Or.inl has) : psi a z z < psi s (fs y z) z)⟩
        rw [if_pos htr']
        have hlo' : loP s (fs y z) = z := loP_fs_z hy hcy hlo hlast
        have hyhi' : hiP s (fs y z) = fs y z := by
          have := hiP_loP s (fs y z); rw [hlo', app_z_right] at this; exact this
        rw [if_pos hlo', app_z_right, hyhi']
      · -- a nonempty low part: the high part is kept
        rw [if_neg hlo]
        have hyB := hiP_loP s y
        set C := hiP s y with hCdef
        set L := loP s y with hLdef
        have hcL : cof L = .big μ := by rw [← cof_app C hlo, hyB]; exact hcy
        have hVL : ValidLt L z := by unfold ValidLt; rw [hcL]; exact T.z_lt_psi _ _ _
        have hfsL := fs_lt hVL
        have hfy : fs y z = app C (fs L z) := by rw [← hyB]; exact fs_app C hlo z
        have hChi : ∀ q ∈ summands C, ¬ q < psi (succ s) z z := fun q hq => split_fst_ge _ y q hq
        have hLlo : fs L z = z ∨ head (fs L z) < psi (succ s) z z := by
          by_cases h0 : fs L z = z
          · exact Or.inl h0
          · right
            rcases split_snd_head (psi (succ s) z z) y with h | h
            · exact absurd h hlo
            · exact lt_of_le_of_lt (head_le_of_lt hfsL) h
        have hsp : split (fs y z) (psi (succ s) z z) = (C, fs L z) := by rw [hfy]; exact split_app_of hChi hLlo
        have hhi' : hiP s (fs y z) = C := by unfold hiP; rw [hsp]
        have hlo'' : loP s (fs y z) = fs L z := by unfold loP; rw [hsp]
        have hRHS : fs (app C (psi s y z)) z = app C (psi s (fs y z) z) := by
          rw [fs_app C (by simp) z, hpsi]
        rw [hRHS]
        by_cases htr' : lt z (fs y z) = true ∧ lt (psi a z z) (psi s (fs y z) z) = true
        · rw [if_pos htr', hhi', hlo'']
          by_cases h0 : fs L z = z
          · rw [if_pos h0, app_z_right]; exact le_app_self _ _
          · rw [if_neg h0]
        · rw [if_neg htr']
          have hz := notrig_first htr htr'
          rw [hfy] at hz
          have hC0 := (app_eq_z hz).1
          rw [hC0, app_z]
    · -- no rewriting
      rw [if_neg htr, hpsi]
      have htr' : ¬ (lt z (fs y z) = true ∧ lt (psi a z z) (psi s (fs y z) z) = true) := by
        intro h; exact htr (trig_mono hylt h.1 h.2)
      rw [if_neg htr']
  · -- a nonzero state: both append
    have hY := step_append (a := a) hc happ (hHi hB)
    have happ' : isOT (app B (psi s (fs y z) z)) = true := by
      apply isOT_app_of (isOT_app_left happ) hfot
      intro q hq
      have h1 := summand_ge_of_app happ hq
      simp only [head] at h1 ⊢
      exact le_trans (le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hylt⟩))) h1
    have hY' : step a B s (fs y z) z = app B (psi s (fs y z) z) := by
      apply step_append hfot happ'
      intro h1 h2
      obtain ⟨t1, t2⟩ := trig_mono hylt h1 h2
      obtain ⟨hhi, hlo⟩ := hHi hB t1 t2
      exact prehi_of_lt hhi hlo h1 hylt
    rw [hY, hY', fs_app B (by simp) z, hpsi]

end Ytosk
