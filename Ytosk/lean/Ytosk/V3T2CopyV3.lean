/-
The t=2 copy boundary theorem never read the old Res3W argument.
This interface removes it explicitly and feeds the PV2 Good3 engine.
-/
import Ytosk.V3T2GoodV3
import Ytosk.V3ExpT2CR

namespace Ytosk.V3Main
open T Classical WfExQ1
set_option linter.unusedVariables false

theorem t2CopyResV3 {M : Mat} {ρM : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρM rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) : T2CopyResE M := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  intro r L hlen hr
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hrx : r < r + L := par_lt M 2 _ r hr
  have hL : 0 < L := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + (entry M 1 (r + L) - entry M 1 r) := by omega
  have hd0 : 0 < entry M 0 (r + L) - entry M 0 r := by omega
  have hd1 : 0 < entry M 1 (r + L) - entry M 1 r := by omega
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqlt := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hqr' : r ≤ q := hrq.le
  -- the structure at `q`
  have hqs : q ≠ r → col M (r + L) = bump M q ∧ ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
    intro hqr
    obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
    obtain ⟨Txb, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
    rw [show r + (q - r) = q by omega] at Txb Tqb
    refine ⟨Txb, fun i hi => ?_⟩
    rw [hpq] at hi; cases hi; exact Tqb
  have hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
    intro i hi
    by_cases hqr : q = r
    · intro h
      rw [hqr] at h
      have := e2_of_col (show col M r = (entry M 0 i + 1, entry M 1 i, 1) from h); omega
    · exact (hqs hqr).2 i hi
  have hxb : q ≠ r → col M (r + L) = bump M q := fun hqr => (hqs hqr).1
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
  have hUM : UAT M := hX.toSInv.uat
  have hUG : ∀ m, UAT (TRIO.gexp M r L d0 d1 m) := fun m => by
    rw [← hexp m]; exact (sInvX_expand hX m).toSInv.uat
  have hXG : ∀ m, SInvX (TRIO.gexp M r L d0 d1 m) := fun m => by rw [← hexp m]; exact sInvX_expand hX m
  have hJG : ∀ m, RowJ (TRIO.gexp M r L d0 d1 m) := fun m => by rw [← hexp m]; exact rowJ_expand hX hJ m
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (TRIO.gexp M r L d0 d1 m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  intro n hn σ ρ hCN hCP hGP
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
  have hm1 : 1 ≤ n - 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- `T2GuardVal`
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    apply t2GuardVal_of (hXG (n - 1)) (hJG (n - 1)) hCP hGP
      (by rw [entry_gexp_pre hlen hm1 2 (by omega)]; exact he2r)
    intro c hc1 hc2
    obtain ⟨a, rfl⟩ : ∃ a, c = r + a := ⟨c - r, by omega⟩
    exact ancP_r hlen hL hA hd0e hn hd0 hd1 hgx (by omega)
  · -- `T2Base`
    exact t2Base_gexp hlen hL hA hd0e hn hd0 hd1 hgx he2r hX.loc.2.2.2 hUM (hUG n) (hUG (n - 1)) I.cons
      hCN hRN hCP hRP
  · -- the copy root
    obtain ⟨hot, hlt⟩ := vx_N hlen hL hA hq hd0e hn hd1e he2r h1lt hqb hr1 hxb hX.loc.2.2.1 hJ hX.r0p
      hUM (hUG n) I.cons I.good hCN hRN
    refine ⟨hot, lt_of_le_of_lt ?_ hlt⟩
    by_cases hn1 : n - 1 = 1
    · rw [hn1] at hCP hRP
      exact vr_take_le hlen hL hA hd0e he2r hUM (hUG 1) I.cons I.good I.rank hCP hRP
    · exact le_of_eq (vr_N hlen hL hA hq hd0e (by omega) hd1e he2r h1lt hqb hr1 hUM (hUG (n - 1))
        I.cons hCP hRP)


/-- Good3 on every t=2 expansion; only the below-boundary obligation remains. -/
theorem good3_t2_of_belowV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hBX : T2BelowXE M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → Good3 (expand M n) σ := by
  have I := coreW C.S C.I
  have hl : 2 ≤ M.length := by
    obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr
    omega
  exact good3_expand_t2V3 C.std C.ne I (C.drop hl) hz h2 hBX
    (t2CopyResV3 C.std C.ne I hz h2)

end Ytosk.V3Main
