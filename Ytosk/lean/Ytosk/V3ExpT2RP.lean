/-
**3 行・t = 2: M[n] の根の値の並び RootP（`rootP_expand_t2`）。**

M[n] の根は M の根（x 以後の行 0 は正）。x の最後の根 Rt より前の根の値は M と同じ（N の依存の閉包で種は
Rt 以後、`depS_ge` と `agree_N`）、Rt の値は M の値以下（`T2BelowXS`）。
-/
import Ytosk.V3ExpT2FO
import Ytosk.V3ExpT2F

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **`RootP` of every `M[n]`** (`t = 2`, `n ≥ 2`). -/
theorem rootP_expand_t2 (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) :
    ∀ n, 2 ≤ n → ∀ σ, Cons (expand M n) σ → RootP (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXAll_of hB M ρ rk hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hz0 := hz
  rw [hL] at hr hz
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqx := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hrq' : r ≤ q := hrq.le
  have hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
    intro i hi
    by_cases hqr : q = r
    · intro h
      rw [hqr] at h
      have := e2_of_col (show col M r = (entry M 0 i + 1, entry M 1 i, 1) from h); omega
    · obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      obtain ⟨_, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      rw [hpq] at hi; cases hi
      rwa [show r + (q - r) = q by omega] at Tqb
  have hBS := t2BelowXS_of hB hM hS I R hz0 h2 hlen hr
  intro n hn σ hCN
  rw [hexp n] at hCN ⊢
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hGN : Good3 N σ := by have := hGall n hm1 σ (by rw [hexp n]; exact hCN); rwa [hexp n] at this
  obtain ⟨rkN, hRN⟩ : ∃ rk, Rk N rk := by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz0 h2 I.rank n hm1
    rw [hexp n] at h'; exact ⟨rk', h'⟩
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  -- row 0 is positive from `x` on
  have hpos : ∀ j, r + L ≤ j → j < N.length → entry N 0 j ≠ 0 := by
    intro j hj1 hj2
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have := e0_NQ_pos (d1 := d1) hlen hL0 hA hq' (by omega) hd0e hn hj1 (by rw [hlN] at hj2; exact hj2)
    exact Nat.pos_iff_ne_zero.mp this
  have hroots : roots N = roots M := by
    apply roots_eq (N := N) (x := r + L) hlen (by omega) (fun c hc => col_gexp_pre hlen hm1 hc) hz
    intro c hc1 hc2 h
    apply hpos c hc1 hc2
    unfold entry; unfold col at h; rw [h]; rfl
  -- the last root above `x`
  obtain ⟨Rt, hRA, hR0e, hRlast⟩ := root_exists hX.e00 (r + L)
  have hR0 : col M Rt = (0, 0, 0) := by
    have h1 : entry M 1 Rt = 0 := hX.r01 Rt hR0e
    exact (col_zero_iff M Rt).mpr ⟨hR0e, h1, hX.r12 Rt h1⟩
  have hRle : ∀ a, Anc0 M a (r + L) → Rt ≤ a := by
    intro a ha
    rcases anc0_total ha hRA with h | h
    · by_cases hae : a = Rt
      · omega
      · have := anc0_e0_lt h hae; omega
    · exact h.le
  have hRtr : Rt ≤ r := hRle r hA
  have hRtq : Rt ≤ q := hRle q (Anc0.step hq (Anc0.refl q))
  -- calls before `Rt` do not depend on the seeds of `N`
  have hnd : ∀ c, c < Rt → ¬ DepS N (SN M r (r + L) q) true c := by
    intro c hc hd
    have hR0N : entry N 0 Rt = 0 := by rw [entry_gexp_pre hlen hm1 0 (by have := hRA.le; omega)]; exact hR0e
    have hRlastN : ∀ j, Rt < j → j ≤ N.length - 1 → entry N 0 j ≠ 0 := by
      intro j h1 h2'
      rcases Nat.lt_or_ge j (r + L) with hj | hj
      · rw [entry_gexp_pre hlen hm1 0 hj]; exact hRlast j h1 (by omega)
      · exact hpos j hj (by omega)
    have hSge : ∀ b i, SN M r (r + L) q b i → Rt ≤ i := by
      rintro b i (⟨_, rfl⟩ | ⟨_, rfl, _⟩ | ⟨_, hqr, hpi⟩ | ⟨_, hix, _⟩)
      · exact hRtq
      · exact hRtq
      · exact hRle i (Anc0.step hq (Anc0.step hpi (Anc0.refl i)))
      · omega
    have := depS_ge (show N.length - 1 + 1 = N.length by omega) hR0N hRlastN hSge hd
    omega
  have hag := agree_N hlen hL0 hA hq hd0e hn he2r h1lt hqb hX.toSInv.uat hUN I.cons hCN hRN
  have hle : σ.o Rt ≤ ρ.o Rt := by
    have hRx : Rt < r + L := by have := hRA.le; have : Rt ≠ r + L := fun h => by rw [h] at hR0; exact hz hR0
                                omega
    refine (hBS n hn (fun τ hτ => by
        have := hGall (n - 1) (by omega) τ (by rw [hexp (n - 1)]; exact hτ)
        rwa [hexp (n - 1)] at this) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) Rt hRx).2.2.2.2.1 ?_
    intro q' hq' hqr' hRq
    rw [hq] at hq'; cases hq'
    -- `q ≠ r` has row 2 equal to `1`, a root has row 2 equal to `0`
    obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr')
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
    obtain ⟨Txb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
    rw [show r + (q - r) = q by omega] at Txb
    have he2q := hX.loc.2.2.1 q (r + L) (mem_children_iff.mpr ⟨by omega, hq⟩) Txb
    rw [← hRq, e2_of_col hR0] at he2q; omega
  have hsplit := roots_split (show r + L + 1 = M.length from hlen) hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hNm : (roots N).map σ.o = pre.map ρ.o ++ [σ.o Rt] := by
    rw [hroots, hsplit, List.map_append, List.map_singleton]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact (hag c (by have := hpre_lt c hc; have := hRA.le; omega)).1 (hnd c (hpre_lt c hc))
  have hMm : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  have hpM : RootP M ρ := I.rootP
  unfold RootP at hpM ⊢
  rw [hMm] at hpM
  rw [hNm]
  rw [List.pairwise_append] at hpM ⊢
  refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb; subst hb
  exact le_trans hle (hpM.2.2 a ha _ (List.mem_singleton_self _))

end Ytosk
