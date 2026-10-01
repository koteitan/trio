/-
**3 行・t = 1・q ≠ r: r の値についての仮定（hF1・hcb・hbr）。**

- P_1(j) = m・行 1 ≠ 0 なら v(m) < v(j)（`v_par1_lt`、順位の帰納法）。
- r と j の間の祖先の行 1 がすべて r より大きければ、P_1 の鎖は r を通り v(r) < v(j)（`v_chain_lt`）。
- D の列 i ∈ (r, x] はこの条件を満たす（`hiR_dep`）。これで hF1（`hF1_t1`）。
- r より後ろの D の呼び出しの値は共終数 Ω_{μ+1}（`t1_cof`）。r の数える子から o の枠を通して
  o(r) = ψ_{v(r)}(b_r) の引数 b_r の共終数が Ω_{v(r)+1}、b_r ≠ 0（`hcb_t1`）。
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

end Ytosk
