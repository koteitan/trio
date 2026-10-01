/-
**3 行・t = 1・q ≠ r（n ≥ 2）: 値の不変条件だけを仮定にした最終形。**

`t1_main_vloc`（VLocal・(W)・(L)・始点の下限・hcb・hbr・hF1 を外した形）から、o(r) が実際に変わること hne を
`V3StrictR` の D の帰納法（ここでは VLocal の代わりに構造の形 `dv_shape` を使う `dep_strict0`・`o_r_strict0`）で外す
（`t1_main_final`）。
-/
import Ytosk.V3VLocT1
import Ytosk.V3StrictR

namespace Ytosk

open T

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- **Every call of `D` drops strictly** in `M.take x` (`t = 1`: `x` has row 2 zero and `v(x) ∉ D`). -/
theorem dep_strict0 {q : Nat} (hx2 : entry M 2 x = 0) (hq : par M 0 x = some q)
    (hnx : ¬ DepX M x false x) :
    ∀ b i, DepX M x b i → i < x → valB ρ' b i < valB ρ b i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  intro b i hD
  induction hD with
  | leaf => intro h; exact absurd h (lt_irrefl _)
  | @ochild i c hc hcb hcu hdc ih =>
    intro hi
    show ρ'.o i < ρ.o i
    rcases hOS_t1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq i hi (DepX.ochild hc hcb hcu hdc) with
      ⟨_, hnc⟩ | ⟨_, L, c0, R, hch, _, _, hR, hLnd⟩
    · exfalso
      rcases hnc c hc with h | h
      · exact hcb h
      · exact hcu h
    · have hcnt : Counted M i c := ⟨hcb, hcu⟩
      have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
        rcases hR d h with h' | h'
        · exact hd.1 h'
        · exact hd.2 h'
      have hcCL : c ∈ CL M i := by
        unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
      obtain ⟨hL, hRo⟩ := sib_order (children_sorted M i) hch
      have hcc0 : c = c0 := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h hcnt)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · exact absurd hcnt (hcR c h)
      subst hcc0
      apply o_strict_frame hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi hcCL
      · intro d hd
        have hdc : d ∈ children M i := (List.mem_filter.mp hd).1
        have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hd).2
        rw [hch] at hdc
        rcases List.mem_append.mp hdc with h | h
        · exact le_of_lt (hL d h)
        · rcases List.mem_cons.mp h with h | h
          · rw [h]
          · exact absurd hdcnt (hcR d h)
      · exact ih
  | @ov i hv ih =>
    intro hi
    show ρ'.o i < ρ.o i
    have hiT : i < (M.take x).length := by omega
    have hiM : i < M.length := by omega
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hv)).1 rfl hi
    have hvlt : ρ'.v i < ρ.v i := ih hi
    rw [o_of_no_counted hC' hiT (hdrop i hi).2.2 hT.2.1, o_cl_eq hC hG hiM]
    exact psi_lt_psi_z_iff.mpr (Or.inl hvlt)
  | @vpar i m h1 hp hdm _ =>
    intro hi
    exfalso
    have hm := par_lt M 1 i m hp
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i hi hp
  | @vupg i k h1 h2 hu hdk ih =>
    intro hi
    show ρ'.v i < ρ.v i
    have hiM : i < M.length := by omega
    have hiT : i < (M.take x).length := by omega
    have hkl := upg_lt hiM hu
    have hkx : k < x := by
      rcases Nat.lt_or_ge k x with h | h
      · exact h
      · exfalso
        have : k = x := by omega
        subst this; exact hnx hdk
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl hkx
    obtain ⟨m, hm1, _, _, hcase⟩ := upg_spec hu
    have hik : k = i + 1 := by
      rcases hcase with h | ⟨hA, hki⟩
      · exact h
      · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT hkx hu hA hki).elim
    have hi1 : i + 1 < x := by omega
    have hmi := par_lt M 1 i m hm1
    have huT : upg (M.take x) i = some k := by rw [upg_take M hi1]; exact hu
    have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
      rw [hm1]; exact hG.ot_v m (by omega)
    have ek : ρ.v i = ρ.v k :=
      v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
    have ek' : ρ'.v i = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hi]; exact h1)
      (by rw [entry_take M 2 hi]; exact h2) huT
      (by rw [par_take M 1 i hi, hm1]; exact (hdrop m (by omega)).2.2)
      (fun _ _ _ k' hk' => (hdrop k' (by have := (mem_children hk').2; omega)).1.2.1)
    rw [ek, ek']
    exact ih hkx
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hi
    show ρ'.v i < ρ.v i
    obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vbump h1 h2 hj hjb hk hdk)
    rcases hcase with ⟨h2', _⟩ | ⟨_, L, K, j', k', hch, _, hchj, _, hKnd, hLnd⟩
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
      exact v_strict_bump hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi h1 h2 hch hjb hchj
        (fun d hd e he => (hLnd d hd e he).1) ih


end

/-- **`o(r)` drops strictly** (`t = 1`, `q ≠ r`), from the drop lemma's conclusion. -/
theorem o_r_strict0 {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M)
    (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hqr : par M 0 x ≠ some r)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i) :
    ρ'.o r < ρ.o r := by
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  have hr : r < x := par_lt M 1 x r h1
  have hrx : r ≠ x := by omega
  have hpath := hpath_of_par1 h1 hA hrx
  obtain ⟨q, hq⟩ := par0_of_anc hA hrx
  have hnx : ¬ DepX M x false x := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact v_r_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hA hrx hqr hpath (depX_chgX hdm)
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  exact dep_strict0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hx2 hq hnx true r
    (dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hA) hr

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**: only value invariants of `M` remain as hypotheses. -/
theorem t1_main_final {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hTP : TP1 M ρ) (hTPLo : TPLo M ρ) (hAD : AbsD M ρ) (hAU : AbsU M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS)
    hUA
  have hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r :=
    ne_of_lt (o_r_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE h1 hx2 hqr hC hG hC1 hRk1 hdrop)
  exact t1_main_vloc hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hTP hTPLo hAD hAU hArgT hKD hTD hAbs hWS hVSt hUA hne hμr hro hsM hpM hG1

end Ytosk
