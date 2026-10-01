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

/-! ## 落とした行列の枠の式と、q から r までの帰納法 -/

/-- The frame in the dropped matrix over a kept path child. -/
theorem drop_frameN {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M)
    {p c : Nat} (hc : par M 0 c = some p) (hcA : Anc0 M c (M.length - 1)) (hcx : c < M.length - 1) :
    o2r (M.take (M.length - 1)) p =
      psi (vr M p) (spArg (vr M p) (bst M p c) (o2r (M.take (M.length - 1)) c)) z := by
  have hx : M.length - 1 + 1 = M.length := by omega
  set x := M.length - 1 with hxdef
  set N := M.take x with hNdef
  have hpc := par_lt M 0 c p hc
  have hle := children_le_of_anc_last hcA hx hc
  have hcmem : c ∈ children M p := mem_children_iff.mpr ⟨by omega, hc⟩
  have hsplit := split_last_max _ c (children_sorted M p) hcmem hle
  have hoff : ∀ d ∈ (children M p).filter (fun d => decide (d < c)), o2r N d = o2r M d := by
    intro d hd
    rw [List.mem_filter] at hd
    have hdc : d < c := by simpa using hd.2
    have hdp := mem_children_iff.mp hd.1
    exact o2r_take_off hx d (by omega) (not_anc_of_earlier hdp.2 hc hdc hcA.le)
  have hall : ∀ d ∈ children M p, d < x := fun d hd => lt_of_le_of_lt (hle d hd) hcx
  have hchNM : children N p = children M p := by
    rw [children_take M x p]
    exact List.filter_eq_self.mpr (fun d hd => by simpa using hall d hd)
  have hchN : children N p = (children N p).filter (fun d => decide (d < c)) ++ [c] := by
    rw [hchNM]; exact hsplit
  have hvalsN : (children N p).map (o2r N) =
      ((children M p).filter (fun d => decide (d < c))).map (o2r M) ++ [o2r N c] := by
    rw [hchN, List.map_append, hchNM]
    simp only [List.map_cons, List.map_nil]
    congr 1
    exact List.map_congr_left hoff
  obtain ⟨hcot, hcN_lt⟩ := drop_lt hM hG hH hFC hcA hcx
  have hdM := hG.dec p
  rw [hsplit, List.map_append] at hdM
  have hsingN : ∀ t ∈ (children N p).map (o2r N), Single t := by
    intro t ht
    rw [hvalsN] at ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i
    · rw [List.mem_singleton] at ht; subst ht
      refine ⟨hcot, ?_⟩
      obtain ⟨y, y', _, hy', _⟩ := drop_path hM hG hH hFC c hcA hcx
      exact ⟨_, _, hy'⟩
  have hdecN : ((children N p).map (o2r N)).Pairwise (fun a b => b ≤ a) := by
    rw [hvalsN, List.pairwise_append]
    have hdM' := List.pairwise_append.mp hdM
    refine ⟨hdM'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt hcN_lt) (hdM'.2.2 a ha _ (by simp))
  have hfrN := o2r_frame' (F1_take hG.f1 x) hchN hsingN hdecN
  rw [bst_take hx hc hcx, vr_take M p (by omega)] at hfrN
  exact hfrN

/-- The node over the last column in the dropped matrix. -/
theorem drop_frameQ {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) {q : Nat}
    (hq : par M 0 (M.length - 1) = some q) :
    o2r (M.take (M.length - 1)) q = psi (vr M q) (bst M q (M.length - 1)) z := by
  have hx : M.length - 1 + 1 = M.length := by omega
  set x := M.length - 1 with hxdef
  set N := M.take x with hNdef
  have hqx := par_lt M 0 x q hq
  have hvp : vr N q = vr M q := vr_take M q hqx
  have hchN : children N q = (children M q).filter (fun d => decide (d < x)) := children_take M x q
  have hle := children_le_of_anc_last (Anc0.refl x) hx hq
  have hoff : ∀ d ∈ (children M q).filter (fun d => decide (d < x)), o2r N d = o2r M d := by
    intro d hd
    rw [List.mem_filter] at hd
    have hdx : d < x := by simpa using hd.2
    have hdp := mem_children_iff.mp hd.1
    exact o2r_take_off hx d hdx (not_anc_of_earlier hdp.2 hq hdx (le_refl _))
  have hvN : (children N q).map (o2r N) =
      ((children M q).filter (fun d => decide (d < x))).map (o2r M) := by
    rw [hchN]; exact List.map_congr_left hoff
  have hdecC : (((children M q).filter (fun d => decide (d < x))).map (o2r M)).Pairwise
      (fun a b => b ≤ a) := List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) (hG.dec q)
  have hSC := sumN_dec _ (fun t ht => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i) hdecC
  rw [o2r_spArg (by rw [hvp]; exact isOT_vr hG.f1 q) (by rw [hvN]; exact hSC.1), hvN, hvp]; rfl

theorem last_step {a B s y : T} (hc : isOT (psi s y z) = true) (hy : y ≠ z)
    (happ : isOT (app B (psi s y z)) = true)
    (hHi : B ≠ z → lt B y = true → lt (psi a z z) (psi s y z) = true → hiP s y = B ∧ loP s y ≠ z) :
    ∀ st, last (step a B s y z) = psi st z z → last y = psi st z z := by
  intro st hst
  by_cases hB : B = z
  · subst hB
    rw [step_first hc] at hst
    split_ifs at hst with htr hlo
    · have hyhi : hiP s y = y := by
        have := hiP_loP s y; rw [hlo, app_z_right] at this; exact this
      rw [app_z_right, hyhi] at hst; exact hst
    · rw [last_app _ (by simp), show last (psi s y z) = psi s y z from rfl] at hst
      exact absurd (psi.inj hst).2.1 hy
    · rw [show last (psi s y z) = psi s y z from rfl] at hst
      exact absurd (psi.inj hst).2.1 hy
  · rw [step_append hc happ (hHi hB), last_app _ (by simp),
      show last (psi s y z) = psi s y z from rfl] at hst
    exact absurd (psi.inj hst).2.1 hy

/-- **S1 along the path**: from `q` up to `r`, the dropped argument is at most `[0]` of the argument. -/
theorem drop_le_fs {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M)
    {r : Nat} (hr1 : par M 1 (M.length - 1) = some r) (hb1 : 0 < entry M 1 (M.length - 1)) :
    ∀ p, Anc0 M p (M.length - 1) → r ≤ p → p < M.length - 1 →
      ∃ y y', o2r M p = psi (vr M p) y z ∧ o2r (M.take (M.length - 1)) p = psi (vr M p) y' z ∧
        y' ≤ fs y z ∧ (∀ st, last y = psi st z z → isSucc st = true ∨ st = z) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  set x := M.length - 1 with hxdef
  set N := M.take x with hNdef
  obtain ⟨b, hrv, hb, hcb, hbelow, _⟩ := twoRow_shape hG hx hr1 hb1
  have hvx : vr M x = succ (vr M r) := by
    obtain ⟨m0, hm0, he⟩ := hG.f1 x hb1
    rw [hr1] at hm0; cases hm0
    rw [vr_eq_nT hG.f1, vr_eq_nT hG.f1, ← he, nT_succ]
  have key : ∀ m p, x - p ≤ m → Anc0 M p x → r ≤ p → p < x →
      ∃ y y', o2r M p = psi (vr M p) y z ∧ o2r N p = psi (vr M p) y' z ∧
        y' ≤ fs y z ∧ (∀ st, last y = psi st z z → isSucc st = true ∨ st = z) := by
    intro m
    induction m with
    | zero => intro p h1 _ _ h3; omega
    | succ m ih =>
      intro p hm hpA hrp hpx
      obtain ⟨c, hc, hcA⟩ := anc0_child hpA (by omega)
      have hpc := par_lt M 0 c p hc
      have hcx := hcA.le
      have hfr := o2r_frame hG hx hcA hc
      rcases Nat.eq_or_lt_of_le hcx with hcx' | hcx'
      · -- `p = q`
        rw [hcx'] at hfr hc
        have hleaf := o2r_leaf hx (isOT_vr hG.f1 x)
        rw [hleaf, spArg_single] at hfr
        have hnotrig : ¬ (lt (bst M p x) z = true ∧
            lt (psi (vr M p) z z) (psi (vr M x) z z) = true) := by simp [lt]
        unfold step at hfr
        rw [if_neg hnotrig] at hfr
        have hge := bst_summands_ge hG hx (Anc0.refl x) hc
        rw [hleaf] at hge
        rw [add_eq_app_of_ge ⟨_, _, rfl⟩ _ hge] at hfr
        have hfs0 : fs (app (bst M p x) (psi (vr M x) z z)) z = bst M p x := by
          rw [fs_app _ (by simp) z, hvx]
          have hss : isSucc (succ (vr M r)) = true := isSucc_succ _
          have hsz : succ (vr M r) ≠ z := by
            intro h; rw [h] at hss; simp [isSucc, last, one] at hss
          have : fs (psi (succ (vr M r)) z z) z = z := by
            unfold fs; rw [if_pos rfl, if_neg hsz, if_pos hss]
          rw [this, app_z_right]
        refine ⟨_, _, hfr, drop_frameQ hM hG hc, by rw [hfs0], ?_⟩
        intro st hst
        rw [last_app _ (by simp), show last (psi (vr M x) z z) = psi (vr M x) z z from rfl] at hst
        obtain ⟨rfl, _, _⟩ := psi.inj hst
        left; rw [hvx]; exact isSucc_succ _
      · -- above another path node
        obtain ⟨yc, yc', hoc, hoc', hlec, hlastc⟩ := ih c (by omega) hcA (by omega) hcx'
        obtain ⟨yd, yd', hod, hod', hotd', hld, _⟩ := drop_path hM hG hH hFC c hcA hcx'
        rw [hoc] at hod; rw [hoc'] at hod'
        obtain ⟨_, rfl, _⟩ := psi.inj hod
        obtain ⟨_, rfl, _⟩ := psi.inj hod'
        have hcot : isOT (psi (vr M c) yc z) = true := by rw [← hoc]; exact hG.ot c
        have hyc : yc ≠ z := by intro h; rw [h] at hld; exact T.not_lt_z _ hld.1
        have hcofc := hbelow c hcA (by omega)
        rw [hoc] at hcofc
        obtain ⟨hcy, hμs⟩ := cof_psi_inv hyc hcofc
        rw [hoc, spArg_single] at hfr
        have hfrN := drop_frameN hM hG hH hFC hc hcA hcx'
        rw [hoc', spArg_single] at hfrN
        have hpl : c < M.length := by omega
        have happ := happ_frame hG hx hH hcA hc hoc
        have hHic := fun hB t1 t2 => hH p c (vr M c) yc hpl hc hoc hB t1 t2
        have hFCc := fun hB t1 t2 hav => hFC p c (vr M c) yc hpl hc hoc hB t1 t2 hav
        -- `[0]` of the child is standard
        have hpsi : fs (psi (vr M c) yc z) z = psi (vr M c) (fs yc z) z := fs_psi_pass hyc hcy hμs z
        have hV : Valid (psi (vr M c) yc z) z := by
          refine ⟨rfl, ?_⟩
          rw [hcofc]; exact T.z_lt_psi _ _ _
        have hfot := (fs_ot_lt hcot hV).1
        rw [hpsi] at hfot
        have hmono : step (vr M p) (bst M p c) (vr M c) yc' z ≤
            step (vr M p) (bst M p c) (vr M c) (fs yc z) z := by
          rcases (le_iff _ _).mp hlec with h | h
          · left
            have := frame_same (a := vr M p) (b := bst M p c) (Ru := z) (Rw := z) hotd' hfot h (z_le _)
            simpa [app_z_right] using this
          · right; rw [h]
        have hfle := frame_fs_le hcot hyc hcy hμs happ hHic hFCc hlastc
        refine ⟨_, _, hfr, hfrN, le_trans hmono hfle, ?_⟩
        intro st hst
        exact hlastc st (last_step hcot hyc happ hHic st hst)
  exact fun p hp hrp hpx => key _ p (Nat.le_refl _) hp hrp hpx

/-- **The seed is good**: `c1 = o_{M.take x}(r)` satisfies the seed condition (two rows, `t = 1`). -/
theorem seed_of_drop {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M)
    {r : Nat} (hr1 : par M 1 (M.length - 1) = some r) (hb1 : 0 < entry M 1 (M.length - 1)) :
    ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (M.take (M.length - 1)) r) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  obtain ⟨b, hrv, hb, hcb, _, _⟩ := twoRow_shape hG hx hr1 hb1
  have hrx := par_lt M 1 _ r hr1
  have hrA : Anc0 M r (M.length - 1) := anc0_of_par M 1 r _ hr1
  intro a' ha' hot
  have harg : argOf (o2r M r) = b := by rw [hrv]; rfl
  rw [harg] at hot ⊢
  obtain ⟨y, y', hy, hy', hle, _⟩ := drop_le_fs hM hG hH hFC hr1 hb1 r hrA (le_refl r) hrx
  obtain ⟨yd, yd', hyd, hyd', hot', hl, _⟩ := drop_path hM hG hH hFC r hrA hrx
  rw [hrv] at hy hyd
  obtain ⟨_, rfl, _⟩ := psi.inj hy
  obtain ⟨_, rfl, _⟩ := psi.inj hyd
  rw [hy'] at hyd'
  obtain ⟨_, rfl, _⟩ := psi.inj hyd'
  rw [hy']
  exact seedOK_of_lhd hot hcb ha' hot' hle hl

end Ytosk
