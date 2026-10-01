/-
**3 行・t = 1・q ≠ r: r の値についての仮定（hF1・hcb・hbr）。**

- P_1(j) = m・行 1 ≠ 0 なら v(m) < v(j)（`v_par1_lt`、順位の帰納法）。
- r と j の間の祖先の行 1 がすべて r より大きければ、P_1 の鎖は r を通り v(r) < v(j)（`v_chain_lt`）。
- D の列 i ∈ (r, x] はこの条件を満たす（`hiR_dep`）。これで hF1（`hF1_t1`）。
- r より後ろの D の呼び出しの値は共終数 Ω_{μ+1}（`t1_cof`。v の枠は VLocal から）。r の数える子から
  o の枠を通して、o(r) = ψ_{v(r)}(b_r) の引数 b_r の共終数が Ω_{μ+1}、b_r ≠ 0（`hcb_t1`）。
まとめ: hcb・hbr・hF1 を外した `t1_main_drop` が `t1_main_val`。新しい不変条件は要らない。
-/
import Ytosk.V3MainT1D

namespace Ytosk

open T

/-! ## v は P_1 の鎖で増える -/

theorem isOT_last : ∀ {t : T}, isOT t = true → isOT (last t) = true
  | z, h => h
  | psi _ _ z, h => h
  | psi _ _ (psi c d e), h => by
    show isOT (last (psi c d e)) = true
    exact isOT_last (isOT_rest h)

theorem omega_single (x : T) : ∃ s y, omega x = psi s y z := by
  unfold omega
  split
  · exact ⟨_, _, rfl⟩
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- Adding a single standard summand to a standard term makes it strictly larger (after `sf`). -/
theorem lt_sf_add_single {a X : T} (ha : isOT a = true) (hX : isOT X = true) (hs : ∃ s y, X = psi s y z) :
    a < sf (add a X) := by
  rw [sf_ot (isOT_add ha hX)]
  obtain ⟨s, y, rfl⟩ := hs
  exact lt_add_principal s y a

/-- **`v` grows along `P_1`.** -/
theorem v_par1_lt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) : ∀ n i m, rk false i ≤ n → i < M.length → entry M 1 i ≠ 0 →
      par M 1 i = some m → ρ.v m < ρ.v i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i m hn hi h1 hp
  have hmi := par_lt M 1 i m hp
  have hvm := hG.ot_v m (by omega)
  rw [(hC i hi).2]
  unfold vRhs
  rw [if_neg h1, hp]
  show ρ.v m < (if entry M 2 i = 0 then _ else _)
  split
  · rename_i h2
    cases hu : upg M i with
    | none => exact lt_sf_add_single hvm rfl ⟨z, z, rfl⟩
    | some k =>
      simp only
      obtain ⟨m', hm1, hm2, hcol, _⟩ := upg_spec hu
      rw [hp] at hm1
      cases hm1
      have hk := upg_lt_len hu
      have hkl : k < M.length := by have := upg_le hu; omega
      have he1 : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact h1
      have hrk := ((hR i hi).2.2 h1).2.1 h2 k hu
      have hvk := ih (rk false k) (by omega) k m (Nat.le_refl _) hkl he1 hm2
      have hkz : ρ.v k ≠ z := by
        intro h; rw [h] at hvk; exact T.not_lt_z _ hvk
      obtain ⟨s, y, hl⟩ := last_psi_form hkz
      exact lt_sf_add_single hvm (isOT_last (hG.ot_v k hkl)) ⟨s, y, hl⟩
  · exact lt_sf_add_single hvm
      (isOT_omega (isOT_sumN _ (by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · obtain ⟨c, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i c)))
      (omega_single _)

/-- `P_1` is at or below a proper ancestor with a smaller row 1. -/
theorem par1_near {M : Mat} {a j : Nat} (hA : Anc0 M a j) (hne : a ≠ j)
    (he : entry M 1 a < entry M 1 j) : ∃ m, par M 1 j = some m ∧ a ≤ m ∧ Anc0 M a m := by
  obtain ⟨S, hS, hSp⟩ := ancL_through hA hne
  rw [par1_find, hS, List.find?_append]
  cases hf : S.find? (fun q => decide (entry M 1 q < entry M 1 j)) with
  | some t =>
    obtain ⟨h1, _, h3, _⟩ := hSp t (List.mem_of_find?_eq_some hf)
    exact ⟨t, by simp, h1.le, h3⟩
  | none =>
    refine ⟨a, ?_, Nat.le_refl _, Anc0.refl a⟩
    simp [he]

/-- Every column strictly between `r` and `j` on the path, and `j`, has a larger row 1 than `r`. -/
def HiR (M : Mat) (r j : Nat) : Prop :=
  ∀ s, Anc0 M r s → Anc0 M s j → s ≠ r → entry M 1 r < entry M 1 s

/-- **`v(r) < v(j)`** below `r` along columns with a larger row 1. -/
theorem v_chain_lt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) {r : Nat} : ∀ j, r < j → j < M.length → Anc0 M r j → HiR M r j → ρ.v r < ρ.v j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hrj hjl hA hH
  have he := hH j hA (Anc0.refl j) (by omega)
  obtain ⟨m, hm, hrm, hAm⟩ := par1_near hA (by omega) he
  have hmj := par_lt M 1 j m hm
  have hlt := v_par1_lt hC hG hR _ j m (Nat.le_refl _) hjl (by omega) hm
  rcases Nat.eq_or_lt_of_le hrm with rfl | hrm'
  · exact hlt
  · have hAmj := anc0_of_par M 1 m j hm
    exact lt_trans' (ih m hmj hrm' (by omega) hAm
      (fun s h1 h2 h3 => hH s h1 (h2.trans hAmj) h3)) hlt

/-! ## D の列は HiR、hF1 -/

section
variable {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 x = some r)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB h1

omit hx hR0 hZ2 hSD hZ1 hUAT hUAB in
theorem hiR_x : HiR M r x := by
  have hA := anc0_of_par M 1 r x h1
  have hrx : r ≠ x := by have := par_lt M 1 x r h1; omega
  intro s hrs hsx hsr
  by_cases hs : s = x
  · subst hs; exact par1_entry_lt h1
  · exact hpath_of_par1 h1 hA hrx s hrs hsx hsr hs

/-- **The columns of `D` after `r` keep row 1 above `r` on the way up to `r`.** -/
theorem hiR_dep {b : Bool} {i : Nat} (hD : DepX M x b i) : r < i → HiR M r i := by
  have hA := anc0_of_par M 1 r x h1
  have hrx' := par_lt M 1 x r h1
  induction hD with
  | leaf => intro _; exact hiR_x h1
  | @ochild i c hc _ _ _ ih =>
    intro hri
    have hic := (mem_children hc).1
    have hH := ih (by omega)
    intro s hs1 hs2 hs3
    exact hH s hs1 (hs2.trans (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl i))) hs3
  | ov _ ih => exact ih
  | @vpar i m _ hp hdm _ =>
    intro hri
    by_cases hix : i = x
    · subst hix; exact hiR_x h1
    · exfalso
      have hmi := par_lt M 1 i m hp
      have hil : i < M.length := anc0_lt_len (anc0_of_par M 1 m i hp) (by omega)
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i
        (by omega) hp
  | @vupg i k _ _ hu hdk ih =>
    intro hri
    have hix : i < x := by have := upg_succ_lt hu; omega
    obtain ⟨m, hm1, _, hcol, hcase⟩ := upg_spec hu
    rcases hcase with rfl | ⟨hAk, hki⟩
    · have hH := ih (by omega)
      have he1 : entry M 1 (i + 1) = entry M 1 i := e1_of_col hcol
      have he0 : entry M 0 (i + 1) = entry M 0 m + 1 := e0_of_col hcol
      have hmi := par_lt M 1 i m hm1
      have hAmi := anc0_of_par M 1 m i hm1
      obtain ⟨h, hph⟩ := par0_some_of (M := M) (show m < i + 1 by omega) (by omega)
      have hhi1 := par_lt M 0 (i + 1) h hph
      have hAhi : Anc0 M h i := anc_between (Anc0.step hph (Anc0.refl h)) i (by omega) (by omega)
      have hhm : h = m := anc0_eq_of_e0 hAhi hAmi (by have := hR0 (i + 1) h hph; omega)
      subst hhm
      have hAm : Anc0 M h (i + 1) := Anc0.step hph (Anc0.refl h)
      have hAr1 : Anc0 M r (i + 1) := anc_between hA (i + 1) (by omega) (by omega)
      have hr1 := hH (i + 1) hAr1 (Anc0.refl _) (by omega)
      intro s hrs hsi hsr
      rcases anc0_total hsi hAmi with hsm | hms
      · exact hH s hrs (hsm.trans hAm) hsr
      · by_cases hsm' : s = h
        · subst hsm'; exact hH s hrs hAm hsr
        · have := par1_between hm1 s hsi (lt_of_le_of_ne hms.le (Ne.symm hsm'))
          omega
    · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
        ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl (by omega))
        (by omega) hu hAk hki).elim
  | @vbump i j k _ _ hj _ hk _ ih =>
    intro hri
    have hij := (mem_children hj).1
    have hjk := (mem_children hk).1
    have hH := ih (by omega)
    intro s hs1 hs2 hs3
    exact hH s hs1 (hs2.trans (Anc0.step (mem_children_iff.mp hk).2
      (Anc0.step (mem_children_iff.mp hj).2 (Anc0.refl i)))) hs3

/-- **`hF1`**: on the `o` calls of `D` after `r`, `v(r) < v(i)`. -/
theorem hF1_t1 {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) :
    ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt (ρ.v r) (ρ.v i) = true := by
  intro i hri hix hD _
  have hA := anc0_of_par M 1 r x h1
  exact v_chain_lt hC hG hR i hri (by omega) (anc_between hA i (by omega) (by omega))
    (hiR_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hD hri)

end

/-! ## r より後ろの D の値は共終数 Ω_{μ+1}、hcb・hbr -/

/-- `ω^G` keeps a passing cofinality. -/
theorem cof_omega_pass {μ G : T} (hot : isOT G = true) (hc : cof G = .big μ)
    (hpass : ∀ s b c, G = psi s b c → cof G = .big μ → lt μ s = true) :
    cof (omega G) = .big μ := by
  by_cases hE : G < E0
  · exact absurd hE (not_lt_E0_of_cof_big hot hc)
  · cases G with
    | z => simp [cof] at hc
    | psi s b c =>
      rw [omega_big' hot hE]
      have hps : lt μ s = true := hpass s b c rfl hc
      by_cases hlo : loOf s b = z
      · rw [if_pos hlo]
        by_cases hcz : c = z
        · subst hcz
          have hb : hiOf s b = b := by
            have := split_app (psi (succ s) z z) b
            unfold hiOf; unfold loOf at hlo; rw [hlo, app_z_right] at this; exact this
          rw [app_z_right, hb]; exact hc
        · have hcs : cof (psi s b c) = cof c := by
            cases c with
            | z => exact absurd rfl hcz
            | psi => rfl
          exact cof_psi_pass (by intro he; exact hcz (app_eq_z he).2)
            (by rw [cof_app _ hcz, ← hcs]; exact hc) hps
      · rw [if_neg hlo]
        exact cof_psi_pass (by intro he; have := (app_eq_z he).2; simp at this)
          (by rw [cof_app _ (by simp)]; exact hc) hps

theorem cof_big_ne_z {μ t : T} (h : cof t = .big μ) : t ≠ z := by
  intro he; subst he; simp [cof] at h

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ ζ : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hC : Cons M ρ) (hG : Good3 M ρ)
  (hox : ρ.o x = psi (succ μ) z z)
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS hV

/-- **After `r`, the values on `D` have cofinality `Ω_{μ+1}`.** -/
theorem t1_cof : ∀ b i, DepX M x b i → r < i → (i < x ∨ (i = x ∧ b = true)) →
    cof (valB ρ b i) = .big μ := by
  intro b i hD
  induction hD with
  | leaf =>
    intro _ _
    show cof (ρ.o x) = _
    rw [hox]; exact cof_omega_succ μ
  | @ochild i c hc hcb' hcu hdc ih =>
    intro hri hix
    have hcM := (mem_children hc).2
    have hic := (mem_children hc).1
    have hi : i < x := by
      rcases hix with h | ⟨h, _⟩
      · exact h
      · omega
    have hcpos : c < x ∨ (c = x ∧ true = true) := by
      rcases Nat.lt_or_ge c x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩
    have ihc := ih (by omega) hcpos
    simp only [valB, cond_true] at ihc
    rcases hOS i hi (DepX.ochild hc hcb' hcu hdc) with ⟨_, hnc⟩ | ⟨hv, L, c', R, hch, hcb2, hcu2, hR, hLnd⟩
    · exact absurd (hnc c hc) (by
        rintro (h | h)
        · exact hcb' h
        · exact hcu h)
    · have hcc : c = c' := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h ⟨hcb', hcu⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c h with h' | h'
            · exact absurd h' hcb'
            · exact absurd h' hcu
      subst hcc
      have hiM : i < M.length := by omega
      obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
      have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
      have hframe := o_frame hC hG hiM hch hcb2 hcu2 hR hcM
      rw [hcv, spArg_single] at hframe
      rw [hcv] at ihc
      have hstep := cof_step (a := ρ.v i) (b := preState M ρ i L) hcot ihc
      show cof (ρ.o i) = _
      rw [hframe]
      exact cof_psi_pass (cof_big_ne_z hstep) hstep (hF1 i hri hi (DepX.ochild hc hcb' hcu hdc) hv)
  | @ov i hv ih =>
    intro hri hix
    rcases hix with hi | ⟨rfl, _⟩
    · have ihv := ih hri (Or.inl hi)
      simp only [valB, cond_false] at ihv
      rcases hOS i hi (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hv', _⟩
      · have hoi := o_nocnt hC hG (by omega) hnc
        show cof (ρ.o i) = _
        rw [hoi]
        have hvz := cof_big_ne_z ihv
        have hvs := not_succ_of_cof_big ihv
        unfold cof
        rw [if_pos rfl, if_neg hvz, if_neg (by rw [hvs]; simp), ihv]
      · exact absurd hv hv'
    · show cof (ρ.o _) = _
      rw [hox]; exact cof_omega_succ μ
  | @vpar i m' h1 hp hdm _ =>
    intro _ hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    exact absurd hdm ((hV i hi (DepX.vpar h1 hp hdm)).2.1 m' hp)
  | @vupg i k h1 h2 hu hdk ih =>
    intro hri hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, _, hcase⟩ := hV i hi (DepX.vupg h1 h2 hu hdk)
    rcases hcase with ⟨k', _, hu', hk, hVs, _, _⟩ | ⟨_, _, _, _, h2', _⟩
    · have hkk : k = k' := by rw [hu] at hu'; exact Option.some.inj hu'
      subst hkk
      have hrk : r < k := by
        obtain ⟨_, _, _, _, hc⟩ := upg_spec hu
        rcases hc with h | ⟨hA, hki⟩
        · omega
        · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
            ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl hk) hk hu hA hki).elim
      have ihk := ih hrk (Or.inl hk)
      simp only [valB, cond_false] at ihk
      obtain ⟨B, hvi⟩ := upg_valL hC (by omega) h1 h2 hu hVs (vOpt_ot hG (by omega))
      show cof (ρ.v i) = _
      rw [hvi, cof_app B (single_ne_z hVs), cof_last_g, ihk]
    · exact absurd h2 h2'
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hri hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    have hiM : i < M.length := by omega
    obtain ⟨_, _, hcase⟩ := hV i hi (DepX.vbump h1 h2 hj hjb hk hdk)
    rcases hcase with ⟨_, h2', _⟩ | ⟨L, K, j', k', _, hch, hjb', hchj, hKnd, hLnd, _, hsK, hpK, hsL,
        hpp, _, hgt, _, _, hAbs, hpassG, hpassP⟩
    · exact absurd h2' h2
    · have hjj : j = j' := by
        rw [hch] at hj
        rcases List.mem_append.mp hj with h | h
        · exact absurd hdk (hLnd j h k hk).2
        · exact List.mem_singleton.mp h
      subst hjj
      have hkk : k = k' := by
        rw [hchj] at hk
        rcases List.mem_append.mp hk with h | h
        · exact absurd hdk (hKnd k h)
        · exact List.mem_singleton.mp h
      subst hkk
      have hkM := (mem_children hk).2
      have hjk := (mem_children hk).1
      have hij := (mem_children hj).1
      have hkpos : k < x ∨ (k = x ∧ true = true) := by
        rcases Nat.lt_or_ge k x with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, rfl⟩
      have ihk := ih (by omega) hkpos
      simp only [valB, cond_true] at ihk
      have hvi := v_bump_valueG hC hiM h1 h2 hch hjb hchj hsK hpK hsL hpp hgt (vOpt_ot hG (by omega))
      set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
      set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
      have hGot : isOT G = true := (sumN_dec _ hsK hpK).1
      have hkS : Single (ρ.o k) := hsK _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hG : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hsK hpK
      have hsP : ∀ t ∈ P ++ [omega G], Single t := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · simp only [hPdef, nzs, List.mem_filter] at ht
          rcases hsL t ht.1 with h | h
          · exact absurd h (by simpa using ht.2)
          · exact h
        · rw [List.mem_singleton] at ht; subst ht; exact single_omega hGot
      have hpot : isOT (app (sumN P) (omega G)) = true := by
        rw [← sumN_snoc_dec hsP hpp]; exact (sumN_dec _ hsP hpp).1
      have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
      show cof (ρ.v i) = _
      obtain ⟨B, hvi2⟩ : ∃ B, ρ.v i = app B (omega (app (sumN P) (omega G))) := by
        obtain ⟨_, s0, y0, hW0⟩ := single_omega hpot
        obtain ⟨B, X, _, _, hadd⟩ := add_prefix s0 y0 (vOpt ρ (par M 1 i))
        exact ⟨B, by rw [hvi, hW0, hadd]⟩
      rw [hvi2, cof_app B (single_ne_z (single_omega hpot))]
      have hcG : cof G = .big μ := by rw [hG, cof_app _ (single_ne_z hkS)]; exact ihk
      have hcω := cof_omega_pass hGot hcG hpassG
      exact cof_omega_pass hpot (by rw [cof_app _ hωGz]; exact hcω) hpassP


/-- **`hcb`, `hbr`**: the argument of `o(r)` has cofinality `Ω_{μ+1}` and is nonzero. -/
theorem hcb_t1 (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hqr : par M 0 x ≠ some r)
    (hR12 : R12 M) (hBE : BumpE2 M) {vr br : T} (hro : ρ.o r = psi vr br z) :
    cof br = .big μ ∧ br ≠ z := by
  have hAr := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  have hpath := hpath_of_par1 h1 hAr (by omega)
  have hDr : DepX M x true r := dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hAr
  have hnv : ¬ DepX M x false r := fun h =>
    v_r_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hAr (by omega) hqr hpath (depX_chgX h)
  have hcof := t1_cof hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS hV
  rcases hOS r hrx hDr with ⟨hv, _⟩ | ⟨_, L, c, R, hch, hcb2, hcu2, hR, hLnd⟩
  · exact absurd hv hnv
  · have hc : c ∈ children M r := by rw [hch]; simp
    -- the child through which `o(r)` is in `D` is `c`
    have hcD : DepX M x true c := by
      cases hDr with
      | leaf => omega
      | @ochild _ c0 hc0 hcb0 hcu0 hdc0 =>
        have : c0 = c := by
          rw [hch] at hc0
          rcases List.mem_append.mp hc0 with h | h
          · exact absurd hdc0 (hLnd c0 h ⟨hcb0, hcu0⟩)
          · rcases List.mem_cons.mp h with h | h
            · exact h
            · rcases hR c0 h with h' | h'
              · exact absurd h' hcb0
              · exact absurd h' hcu0
        rw [← this]; exact hdc0
      | ov h => exact absurd h hnv
    have hcM := (mem_children hc).2
    have hrc := (mem_children hc).1
    obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
    have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
    have hframe := o_frame hC hG (by omega) hch hcb2 hcu2 hR hcM
    rw [hcv, spArg_single] at hframe
    have hcc := hcof true c hcD hrc (by
      rcases Nat.lt_or_ge c x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩)
    simp only [valB, cond_true] at hcc
    rw [hcv] at hcc
    have hstep := cof_step (a := ρ.v r) (b := preState M ρ r L) hcot hcc
    rw [hro] at hframe
    obtain ⟨_, hb, _⟩ := T.psi.inj hframe
    rw [hb]
    exact ⟨hstep, cof_big_ne_z hstep⟩

end

/-! ## まとめ: hcb・hbr・hF1 を外した t1_main_drop -/

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**, without the hypotheses `hcb`, `hbr`, `hF1`. -/
theorem t1_main_val {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true)
    (hLo : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2 (gamS μ br ((drop1 M (r + L) rkM).o r) m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) (psi (succ s) z z)).2 = z))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1 Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  have hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true := by
    intro i h2 h3 h4 h5
    rw [hμr, ← hvr]
    exact hF1_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hRM i h2 h3 h4 h5
  have hox : ρ.o (r + L) = psi (succ μ) z z := by
    rw [o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2, hvr, hμr]
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  obtain ⟨hcb, hbr⟩ := hcb_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS (hV 0) h1 hx2 hqr
    hR12 hBE hro
  exact t1_main_drop hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA hne hcb hμr hbr hro hF1 hV hW hLo hsM hpM hG1 Pn hP1 hPs

end Ytosk
