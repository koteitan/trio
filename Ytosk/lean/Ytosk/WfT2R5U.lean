/-
**WfT2R5: the root descent of every `M[n]` (`n ≥ 2`, `t = 2`) from `T2BelowXResAtXU` (2026-11-01).**

`t2_root_ofXU`: the proof of `t2BelowXS_ofX` (WfT2X4) with the root engines of WfT2R4 in place of the `below` ones.
-/
import Ytosk.WfT2R4U

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem t2_root_ofXU {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hRes : T2BelowXResAtXU M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) :
    ∀ n, 2 ≤ n → (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      (∀ j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).length → isOT (σ.o j) = true ∧ isOT (σ.v j) = true) →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) = true ∧ root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ < root M ρ := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hrx : r < r + L := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  have hL : M.length - 1 = r + L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hXu_of : upg M (r + L - 1) ≠ some (r + L) → ∀ i, upg M i ≠ some (r + L) := by
    intro hux i hu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    have hi : i < M.length := by
      by_contra h
      exact (upg_e12 hu).1 (entry_out (by omega) 1)
    rcases hcase with h | ⟨_, h⟩
    · exact hux (by rw [show r + L - 1 = i by omega]; exact hu)
    · omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hrU : isUpg M r = false := by
    cases h : isUpg M r with
    | false => rfl
    | true =>
      exfalso
      unfold isUpg at h
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
      have := upg_target_e2 (of_decide_eq_true hk); omega
  have hrcl_of : par M 0 (r + L) = some r → upg M (r + L - 1) ≠ some (r + L) → CL M r ≠ [] := by
    intro hq hux hnil
    have hcnt : Counted M r (r + L) := ⟨hxbr, by rw [isUpg_x_false (hXu_of hux)]; simp⟩
    have hxin : r + L ∈ CL M r := by
      unfold CL; rw [List.mem_filter]
      exact ⟨mem_children_iff.mpr ⟨by omega, hq⟩, by simpa using hcnt⟩
    rw [hnil] at hxin; simp at hxin
  have hexp : ∀ n, expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  -- the valuation of `M.take x`
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV M ρ (drop1 M (r + L) rk) i := by
    have := R.hdrop; rw [hL] at this; exact this
  have hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rk) :=
    good3_take (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := (anc0_par hA (by omega) hq).le
  have hqx : q < r + L := par_lt M 0 _ q hq
  -- `n ≥ 2`
  intro n hn hGP σ hCN hOTx hGN
  obtain ⟨rkN, hRN⟩ : ∃ rkN, Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) rkN := by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
    rw [hexp n] at h'; exact ⟨rk', h'⟩
  have hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n).length → isOT (valB σ b j) = true := by
    intro b j h1 h2'
    cases b
    · exact (hOTx j h1 h2').2
    · exact (hOTx j h1 h2').1
  obtain ⟨hHard, hSeedP, hW, hAbsN, hNB⟩ := hRes hM hS I R hz h2 r L hlen hr n hn hGP σ hCN hOTout
  have hT : (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).take
      (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hUN : UAT (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) := by
    rw [← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hlN := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := entry M 0 (r + L) - entry M 0 r)
    (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  have hcolN : ∀ d, d < r + L →
      col (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) d = col M d :=
    fun d hd => col_gexp_pre hlen (by omega) hd
  have hbN : ∀ c, c < r + L →
      bump (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c = bump M c :=
    fun c hc => by unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]
  have hkx : ∀ i j k, i < r + L → j ∈ children M i → col M j = bump M i → k ∈ children M j → k < r + L := by
    intro i j k hi hj hjb hk
    have hkl := (mem_children hk).2
    by_contra h'
    have hkx' : k = r + L := by omega
    have hpk := (mem_children_iff.mp hk).2
    rw [hkx', hq] at hpk
    have hjq : q = j := Option.some.inj hpk
    subst hjq
    have hpj := (mem_children_iff.mp hj).2
    have hrq' := (anc0_par hA (by omega) hq).le
    by_cases hqr' : q = r
    · rw [hqr'] at hjb; exact hrb i (by rw [← hqr']; exact hpj) hjb
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr' h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      obtain ⟨_, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      rw [show r + (q - r) = q by omega] at Tqb
      rw [hpj] at hpq; cases hpq
      exact Tqb hjb
  by_cases hqr : q = r
  · rw [hqr] at hq
    have hAbs := hAbsN
    by_cases hux : upg M (r + L - 1) = some (r + L)
    · obtain ⟨Sp1, _, Sdv, Sos, Svsh⟩ := sv_shapes hlen hL0 hq hux (rx_of_sv hlen I.z2 I.z1 hr hux) hrb he2r
        I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be
      obtain ⟨hs1, hs2, hs3⟩ := hSeedP r (Or.inl ⟨hq, rfl⟩)
      have hIUt : ∀ c, c < r + L → topped M c = true →
          isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
            isUpg M c := by
        intro c hc htM
        have hcr : c ≠ r := by
          intro hcr'
          rw [hcr'] at htM
          have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
          have hsplit := children_split_x hlen hxr
          unfold topped at htM; rw [hsplit] at htM; simp at htM
          exact hxbr htM
        have hch := children_N2 (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e (by omega) hn hc
        apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
        rw [topped_eq_of hch (fun d hd => hcolN d (by
          have := (mem_children hd).2
          by_contra h'
          have hdx : d = r + L := by omega
          have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcr (Option.some.inj this).symm))
          (hbN c hc)]
        exact htM
      exact t2_sv_rootXU hlen hL0 hq hd0e hn hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) hIUt
        Sp1 Sdv Sos Svsh I.cons I.good I.rank hCN hRN I.fc I.fo I.vs I.td I.kd hAbs hNB (hHard r (Or.inl ⟨hq, rfl⟩)) hOTout
        ⟨hs1, hs2⟩ hs3 hGN
    · obtain ⟨hs1, hs2, hs3⟩ := hSeedP r (Or.inl ⟨hq, rfl⟩)
      have hIU : ∀ c, c < r + L → topped M c = true →
          isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
            isUpg M c := by
        intro c hc htM
        apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
        rw [topped_N2 (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e hn (hXu_of hux) hxbr he2r hc]
        exact htM
      have hxcN : Counted (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
          (entry M 1 (r + L) - entry M 1 r) n) r (r + L) := by
        have hx2 := (entry_xprime (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e (by omega) hn).1
        refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
        · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
        · unfold isUpg at hiu
          obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
          have := upg_target_e2 (of_decide_eq_true hk0); omega
      exact t2_qr_rootXU hlen hL0 hq hd0e hn (hXu_of hux) hxbr hrb he2r hIU I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
        I.be I.r01 I.e00 I.cons I.good I.rank hCN hRN I.fc I.fo I.vs I.td I.kd hAbsN hNB hxcN (hHard r (Or.inl ⟨hq, rfl⟩)) hOTout
        ⟨hs1, hs2⟩ hs3 hGN
  · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
    obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
    obtain ⟨Tp1, TqL, Tdv, Tos, Tvsh⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
      I.uat I.uab I.r12 hpq' Tqb
    have hAbs := hAbsN
    obtain ⟨hs1, hs2, hs3⟩ := hSeedP pq (Or.inr ⟨q, hq, hqr, hpq⟩)
    obtain ⟨hqot, hqdec⟩ := hW q hq hqr
    have hIUt : ∀ c, c < r + L → c ≠ r + (q - r) → topped M c = true →
        isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
          isUpg M c := by
      intro c hc hcq htM
      have hch := children_N2Q (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hA hq' (by omega) hd0e
        (by omega) hn hc
      apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
      rw [topped_eq_of hch (fun d hd => hcolN d (by
        have := (mem_children hd).2
        by_contra h'
        have hdx : d = r + L := by omega
        have := (mem_children_iff.mp hd).2; rw [hdx, hq'] at this; exact hcq (Option.some.inj this).symm))
        (hbN c hc)]
      exact htM
    have hd1e : entry M 1 (r + L) = entry M 1 r + (entry M 1 (r + L) - entry M 1 r) := by omega
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    have hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
      intro i hi; rw [hpq] at hi; cases hi
      have := Tqb; rwa [show r + (q - r) = q by omega] at this
    have hxb : col M (r + L) = bump M q := by
      have := Txb; rwa [show r + (q - r) = q by omega] at this
    obtain ⟨hvqot, _⟩ := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 hqr hxb I.be I.uat hUN
      I.cons I.good hCN hRN
    have hvqot' : isOT (σ.v (r + (q - r))) = true := by rw [show r + (q - r) = q by omega]; exact hvqot
    have hqot' : isOT (σ.o (r + (q - r))) = true := by rw [show r + (q - r) = q by omega]; exact hqot
    have hqdec' : (cvals (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) σ (r + (q - r))).Pairwise (fun a b => b ≤ a) := by
      rw [show r + (q - r) = q by omega]; exact hqdec
    exact t2_qn_rootXU hlen hL0 hA hq' (by omega) hd0e hn Txb I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hpq'
      Tqb Te2pq Tclq Tclpq hIUt Tp1 TqL Tdv Tos Tvsh I.cons I.good I.rank hCN hRN
      I.fc I.fo I.vs I.td I.kd hAbs hNB (hHard pq (Or.inr ⟨q, hq, hqr, hpq⟩)) hOTout hvqot' ⟨hs1, hs2⟩ hs3 hqot' hqdec' hGN

end Ytosk.WfT2X
