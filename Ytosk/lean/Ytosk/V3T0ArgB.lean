import Ytosk.V3T0DepS
import Ytosk.V3T0Sh3

namespace Ytosk.T0ArgB
open T

/-- Natural indices are standard as well as in range. -/
theorem valid_nat {a b : T} (hb : b ≠ z) (k : Nat) : Valid (psi a b z) (natT k) := by
  refine ⟨isOT_natT k, ?_⟩
  have hv := validLt_natT (a := a) hb k
  unfold ValidLt at hv
  cases hc : cof (psi a b z) with
  | zero => simp only [hc] at hv
  | succ =>
    have h := (cof_props (psi a b z)).2 hc
    simp only [isSucc, last, beq_iff_eq, one, psi.injEq] at h
    exact False.elim (hb h.2.1)
  | omega => exact ⟨k,rfl⟩
  | big μ => simpa only [hc] using hv

/-- The finite middle-copy node is a standard FS term of the old parent. -/
theorem copies_ot {a B v Y0 : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q) :
    isOT (psi a (spArg a B (mulT (psi v Y0 z) m)) z) = true := by
  have hArg : spArg a B (psi v (app Y0 one) z) ≠ z := by
    intro h
    have := lt_spArg a (b := B) hX (by simp)
    rw [h] at this
    exact T.not_lt_z _ this
  have hfs : ∃ k, psi a (spArg a B (mulT (psi v Y0 z) m)) z =
      fs (psi a (spArg a B (psi v (app Y0 one) z)) z) (natT k) := by
    by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
    · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
      · exact ⟨m-1,(t0_frame_swallow hm hX hO htr hbad.1 hbad.2).symm⟩
      · exact ⟨m,(t0_frame_trig hm hOld hX hO htr hbad).symm⟩
    · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
        have h1 := isOT_arg hOld
        rw [spArg_single] at h1
        unfold step at h1
        rw [if_neg htr, add_eq_app_of_ge ⟨_,_,rfl⟩ _ hBX] at h1
        exact h1
      exact ⟨m,(t0_frame_notrig m hXapp htr hBX).symm⟩
  obtain ⟨k,hk⟩ := hfs
  rw [hk]
  exact isOT_fs hOld (valid_nat hArg k)

/-- The exact weak seed conclusion needed at the parent g. Argument Lhd is
not asserted: it is false on some generated tuples satisfying these premises. -/
theorem weak_seed {a B v Y0 w' : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hW : WkVA w' v) (hWC : WCS a w') (hc' : isOT (psi w' z z) = true)
    (hva : v ≤ a) :
    let X := spArg a B (psi v (app Y0 one) z)
    let X' := spArg a (spArg a B (mulT (psi v Y0 z) m)) (psi w' z z)
    isOT (psi a X' z) = true ∧ Lhd z (psi a X' z) (psi a X z) ∧
      (split X' (psi (succ a) z z)).1 = (split X (psi (succ a) z z)).1 ∧
      (split X' (psi (succ a) z z)).2 ≠ z := by
  dsimp only
  set B' := spArg a B (mulT (psi v Y0 z) m) with hB'
  have hwa : w' < a := lt_of_lt_of_le hW.1 hva
  have hOX : psi v Y0 z < psi v (app Y0 one) z :=
    psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl,lt_app_one Y0⟩)
  have hB'O : ∀ q ∈ summands B', psi v Y0 z ≤ q :=
    spArg_summands_ge ⟨v,Y0,rfl⟩ _ B (isOT_mulT hO ⟨_,_,rfl⟩ m)
      (fun q hq => by rw [summands_mulT ⟨_,_,rfl⟩ m q hq])
      (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
  have hleafO : psi w' z z < psi v Y0 z := psi_lt_psi_z_iff.mpr (Or.inl hW.1)
  have hB'leaf : ∀ q ∈ summands B', psi w' z z ≤ q :=
    fun q hq => le_trans (le_of_lt hleafO) (hB'O q hq)
  have hnew : spArg a B' (psi w' z z) = app B' (psi w' z z) := by
    rw [spArg_single,step_leaf]
    exact add_eq_app_of_ge ⟨w',z,rfl⟩ B' hB'leaf
  have hmid := copies_ot hm hOld hX hO hBX
  change isOT (psi a B' z) = true at hmid
  have harg := isOT_app_of (isOT_arg hmid) hc' hB'leaf
  have hot : isOT (psi a (spArg a B' (psi w' z z)) z) = true := by
    rw [hnew,isOT_psi_iff]
    refine ⟨isOT_sub hmid,harg,rfl,z_le _,?_⟩
    intro g hg
    rw [comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact lt_of_lt_of_le (comps_lt hmid g hg) (le_app_self _ _)
    · simp only [comps, if_pos (show lt w' a = true from hwa), List.append_nil, List.not_mem_nil] at hg
  have hlow : (split (spArg a B' (psi w' z z)) (psi (succ a) z z)).2 ≠ z := by
    rw [hnew]
    exact lo_ne_of_low_change (by simp) (by
      change psi w' z z < psi (succ a) z z
      exact psi_lt_psi_z_iff.mpr (Or.inl (lt_trans hwa (lt_succ_self a))))
  have hcls := s1_core_cls hm hX hO hBX ⟨hc',w',z,rfl⟩ (le_of_lt hleafO)
    (by intro s y h hs; simp only [psi.injEq] at h; exact h.2.1.symm)
    (by intro s y h hs hn; exact False.elim (hn (psi_lt_psi_z_iff.mpr
      (Or.inl (lt_of_le_of_lt hva (lt_succ_self a))))))
  change ClsNode a (spArg a B' (psi w' z z)) _ at hcls
  have hhi : (split (spArg a B' (psi w' z z)) (psi (succ a) z z)).1 =
      (split (spArg a B (psi v (app Y0 one) z)) (psi (succ a) z z)).1 := by
    rcases hcls with h | h | h
    · exact h.1
    · exact False.elim (hlow h.1)
    · have hz := split_snd_z_of_ge (split_fst_ge (psi (succ a) z z)
          (spArg a B (psi v (app Y0 one) z)))
      rw [← h] at hz
      exact False.elim (hlow hz)
  exact ⟨hot,s1_core_weak hm hOld hX hO hBX hW hWC hc',hhi,hlow⟩

#print axioms weak_seed
end Ytosk.T0ArgB
