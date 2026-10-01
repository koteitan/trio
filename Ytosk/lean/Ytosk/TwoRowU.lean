/-
**(I1) 最後の列を落としても不変条件が保たれる（2 行）。**

`drop_path` から: M.take x の Good2（値の標準形・兄弟の降順・F1）、PreHi、PreFC。
-/
import Ytosk.TwoRowV

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- Outside the matrix the value is `1`. -/
theorem o2r_out {N : Mat} {i : Nat} (hi : N.length ≤ i) : o2r N i = psi z z z := by
  have hch : children N i = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc; have := mem_children hc; omega
  have hv : vr N i = z := by
    unfold vr
    have : entry N 1 i = 0 := by
      unfold entry; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]; rfl
    rw [if_pos this]
  rw [o2r_eq, hch, hv]; rfl

/-- The path value drops (node level). -/
theorem drop_lt {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M)
    {p : Nat} (hpA : Anc0 M p (M.length - 1)) (hpx : p < M.length - 1) :
    isOT (o2r (M.take (M.length - 1)) p) = true ∧ o2r (M.take (M.length - 1)) p < o2r M p := by
  obtain ⟨y, y', hy, hy', hot, hl, _⟩ := drop_path hM hG hH hFC p hpA hpx
  rw [hy, hy']
  exact ⟨hot, by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hl.1⟩⟩

/-- **Good2 survives dropping the last column.** -/
theorem good2_take {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M) :
    Good2 (M.take (M.length - 1)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  set x := M.length - 1 with hxdef
  set N := M.take x with hNdef
  have hlen : N.length = x := by rw [hNdef, List.length_take]; omega
  refine ⟨F1_take hG.f1 x, ?_, ?_⟩
  · intro i
    rcases Nat.lt_or_ge i x with hix | hix
    · by_cases hA : Anc0 M i x
      · exact (drop_lt hM hG hH hFC hA hix).1
      · rw [o2r_take_off hx i hix hA]; exact hG.ot i
    · rw [o2r_out (by omega)]; rfl
  · intro h
    rcases Nat.lt_or_ge h x with hhx | hhx
    · rw [children_take M x h]
      by_cases hA : Anc0 M h x
      · -- `h` on the path: the path child (if kept) drops
        obtain ⟨c, hc, hcA⟩ := anc0_child hA (by omega)
        have hle := children_le_of_anc_last hcA hx hc
        have hcmem : c ∈ children M h := mem_children_iff.mpr ⟨by have := hcA.le; omega, hc⟩
        have hsplit := split_last_max _ c (children_sorted M h) hcmem hle
        have hoff : ∀ d ∈ (children M h).filter (fun d => decide (d < c)), o2r N d = o2r M d := by
          intro d hd
          rw [List.mem_filter] at hd
          have hdc : d < c := by simpa using hd.2
          have hdp := mem_children_iff.mp hd.1
          exact o2r_take_off hx d (by have := hcA.le; omega) (not_anc_of_earlier hdp.2 hc hdc hcA.le)
        have hdM := hG.dec h
        rw [hsplit, List.map_append] at hdM
        have hdM' := List.pairwise_append.mp hdM
        rw [hsplit, List.filter_append, List.map_append]
        have hC : ((children M h).filter (fun d => decide (d < c))).filter (fun d => decide (d < x)) =
            (children M h).filter (fun d => decide (d < c)) := by
          apply List.filter_eq_self.mpr
          intro d hd; rw [List.mem_filter] at hd
          have : d < c := by simpa using hd.2
          simpa using (show d < x by have := hcA.le; omega)
        rw [hC, List.map_congr_left hoff]
        rcases Nat.lt_or_ge c x with hcx | hcx
        · simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, hcx, if_true,
            List.map_cons, List.map_nil]
          rw [List.pairwise_append]
          refine ⟨hdM'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          exact le_trans (le_of_lt (drop_lt hM hG hH hFC hcA hcx).2) (hdM'.2.2 a ha _ (by simp))
        · simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq,
            show ¬ c < x by omega, if_false, List.map_nil, List.append_nil]
          exact hdM'.1
      · -- off the path: the children keep their values
        have hv : ((children M h).filter (fun d => decide (d < x))).map (o2r N) =
            ((children M h).filter (fun d => decide (d < x))).map (o2r M) := by
          apply List.map_congr_left
          intro d hd
          rw [List.mem_filter] at hd
          have hdx : d < x := by simpa using hd.2
          apply o2r_take_off hx d hdx
          intro hdA
          exact hA (anc0_up (mem_children_iff.mp hd.1).2 hdA)
        rw [hv]
        exact List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) (hG.dec h)
    · have : children N h = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc; have := mem_children hc; omega
      rw [this]; exact List.Pairwise.nil

/-! ## PreHi・PreFC・RootsDec -/

theorem prehi_of_lt {s B y y' : T} (hhi : hiP s y = B) (hlo : loP s y ≠ z) (h1 : lt B y' = true)
    (hlt : y' < y) : hiP s y' = B ∧ loP s y' ≠ z := by
  have hyB : y = app B (loP s y) := by have := hiP_loP s y; rw [hhi] at this; exact this.symm
  obtain ⟨c0, hc0, hzc, hcle⟩ := between_app (A := B) (x := z) (y := loP s y) (c := y')
    (by rw [app_z_right]; exact h1) (by rw [← hyB]; exact le_of_lt hlt)
  have hBhi : ∀ q ∈ summands B, ¬ q < psi (succ s) z z := by
    intro q hq; rw [← hhi] at hq; exact split_fst_ge _ y q hq
  have hc0lo : c0 = z ∨ head c0 < psi (succ s) z z := by
    right
    rcases split_snd_head (psi (succ s) z z) y with h | h
    · exact absurd h hlo
    · rcases (le_iff _ _).mp hcle with h' | h'
      · exact lt_of_le_of_lt (head_le_of_lt h') h
      · rw [h']; exact h
  have hsp := split_app_of hBhi hc0lo
  unfold hiP loP
  rw [hc0, hsp]
  exact ⟨rfl, fun h => by subst h; exact T.not_lt_z _ hzc⟩

theorem head_lt_of_hiP_z {s y : T} (hy : y ≠ z) (hhi : hiP s y = z) : head y < psi (succ s) z z := by
  cases y with
  | z => exact absurd rfl hy
  | psi a b c =>
    unfold hiP at hhi
    simp only [split] at hhi
    split at hhi
    · rename_i h; exact h
    · simp at hhi

theorem prefc_of_le {s y y' : T} (hhi : hiP s y = z) (hlo : loP s y ≠ z) (hz : z < y')
    (hle : y' ≤ y) : hiP s y' = z ∧ loP s y' ≠ z := by
  have hy : y ≠ z := by
    intro h; apply hlo; subst h; rfl
  have hhead : head y' < psi (succ s) z z :=
    lt_of_le_of_lt (by rcases (le_iff _ _).mp hle with h | h
                       · exact head_le_of_lt h
                       · rw [h]) (head_lt_of_hiP_z hy hhi)
  have h1 : hiP s y' = z := split_fst_of_head_lt hhead
  refine ⟨h1, ?_⟩
  have := hiP_loP s y'
  rw [h1, app_z] at this
  rw [this]; exact fun h => by subst h; exact T.not_lt_z _ hz

/-- **PreHi survives dropping the last column.** -/
theorem preHi_take {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M) :
    PreHi (M.take (M.length - 1)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hlen : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
  intro h p s y' hpl hp hc hB h1 h2
  rw [hlen] at hpl
  rw [par_take M 0 p hpl] at hp
  rw [bst_take hx hp hpl] at hB h1 ⊢
  rw [vr_take M h (by have := par_lt M 0 p h hp; omega)] at h2
  by_cases hA : Anc0 M p (M.length - 1)
  · obtain ⟨y, y'', hy, hy'', _, hl, _⟩ := drop_path hM hG hH hFC p hA hpl
    rw [hy''] at hc
    obtain ⟨rfl, rfl, _⟩ := psi.inj hc
    obtain ⟨t1, t2⟩ := trig_mono hl.1 h1 h2
    obtain ⟨hhi, hlo⟩ := hH h p (vr M p) y (by omega) hp hy hB t1 t2
    exact prehi_of_lt hhi hlo h1 hl.1
  · rw [o2r_take_off hx p hpl hA] at hc
    exact hH h p s y' (by omega) hp hc hB h1 h2

/-- **PreFC survives dropping the last column.** -/
theorem preFC_take {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M) :
    PreFC (M.take (M.length - 1)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hlen : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
  intro h p s y' hpl hp hc hB h1 h2 hv
  rw [hlen] at hpl
  rw [par_take M 0 p hpl] at hp
  rw [bst_take hx hp hpl] at hB
  have hvh := vr_take M h (show h < M.length - 1 by have := par_lt M 0 p h hp; omega)
  rw [hvh] at h2 hv
  by_cases hA : Anc0 M p (M.length - 1)
  · obtain ⟨y, y'', hy, hy'', _, hl, _⟩ := drop_path hM hG hH hFC p hA hpl
    rw [hy''] at hc
    obtain ⟨rfl, rfl, _⟩ := psi.inj hc
    obtain ⟨t1, t2⟩ := trig_mono hl.1 h1 h2
    obtain ⟨hhi, hlo⟩ := hFC h p (vr M p) y (by omega) hp hy hB t1 t2 hv
    exact prefc_of_le hhi hlo h1 (le_of_lt hl.1)
  · rw [o2r_take_off hx p hpl hA] at hc
    exact hFC h p s y' (by omega) hp hc hB h1 h2 hv

/-- **RootsDec survives dropping the last column.** -/
theorem rootsDec_take {M : Mat} (hM : 2 ≤ M.length) (hG : Good2 M) (hH : PreHi M) (hFC : PreFC M)
    (hRD : RootsDec M) (hz0 : TRIO.z0ok M) (h00 : entry M 0 0 = 0) :
    RootsDec (M.take (M.length - 1)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hlt : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
  unfold RootsDec at hRD ⊢
  by_cases hcol : col M (M.length - 1) = (0, 0, 0)
  · have hsplit := roots_split hx (Anc0.refl _) hcol
    set R := (roots M).filter (fun c => decide (c < M.length - 1)) with hRd
    have hex : entry M 0 (M.length - 1) = 0 := by unfold entry; unfold col at hcol; rw [hcol]; rfl
    have hroots : roots (M.take (M.length - 1)) = R := by
      apply eq_of_sorted_mem _ _ (roots_sorted _) (List.Pairwise.filter _ (roots_sorted M))
      intro c
      rw [mem_roots, List.mem_filter, mem_roots, hlt]
      constructor
      · rintro ⟨hc, hc0⟩
        rw [col_take M hc] at hc0; exact ⟨⟨by omega, hc0⟩, by simpa using hc⟩
      · rintro ⟨⟨_, hc0⟩, hc⟩
        have hc' : c < M.length - 1 := by simpa using hc
        exact ⟨hc', by rw [col_take M hc']; exact hc0⟩
    have hRv : R.map (o2r (M.take (M.length - 1))) = R.map (o2r M) := by
      apply List.map_congr_left
      intro c hc
      rw [hRd, List.mem_filter] at hc
      exact o2r_take_low hex c (by simpa using hc.2)
    rw [hroots, hRv]
    rw [hsplit, List.map_append] at hRD
    exact (List.pairwise_append.mp hRD).1
  · obtain ⟨ρ, hρ, hρn⟩ := top_anc M (M.length - 1)
    have hρ0 := col_zero_of_top hz0 h00 (by have := hρ.le; omega) hρn
    have hρx : ρ < M.length - 1 := by
      rcases Nat.eq_or_lt_of_le hρ.le with h | h
      · rw [h] at hρ0; exact absurd hρ0 hcol
      · exact h
    have hroots : roots (M.take (M.length - 1)) = roots M := by
      apply roots_eq hx (by omega) (fun c hc => col_take M hc) hcol
      intro c h1 h2; rw [hlt] at h2; omega
    have hsplit := roots_split hx hρ hρ0
    set R := (roots M).filter (fun c => decide (c < ρ)) with hRd
    have hRv : R.map (o2r (M.take (M.length - 1))) = R.map (o2r M) := by
      apply List.map_congr_left
      intro c hc
      rw [hRd, List.mem_filter] at hc
      have hcρ : c < ρ := by simpa using hc.2
      apply o2r_take_off hx c (by omega)
      intro hcA
      rcases anc0_total hcA hρ with h' | h'
      · cases h' with
        | refl => omega
        | step hp _ => rw [hp] at hρn; cases hρn
      · have := h'.le; omega
    rw [hroots, hsplit, List.map_append, hRv]
    rw [hsplit, List.map_append] at hRD
    have hRD' := List.pairwise_append.mp hRD
    rw [List.pairwise_append]
    refine ⟨hRD'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt (drop_lt hM hG hH hFC hρ hρx).2) (hRD'.2.2 a ha _ (by simp))

end Ytosk
