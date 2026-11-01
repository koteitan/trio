/-
The t=2 Good3 engine with the repaired drop conclusion.
Only PO and PV2 are read; no Res3W, old PV, or Inv3V2 is assumed.
The below-boundary and copy-boundary obligations are left explicit.
-/
import Ytosk.V3EngineV3
import Ytosk.V3ExpT2W

namespace Ytosk.V3Main
open T WfExQ1

/-- The canonical prefix context, using PV2 rather than the old PV. -/
theorem t2_drop_ctxV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) {x : Nat} (hx : x + 1 = M.length) :
    Cons (M.take x) (drop1 M x rk) ∧ Rk (M.take x) rk ∧
    Good3 (M.take x) (drop1 M x rk) ∧
      ∀ i, i < x → PO ρ (drop1 M x rk) i ∧ PV2 M ρ (drop1 M x rk) i := by
  have hdrop : ∀ i, i < x → PO ρ (drop1 M x rk) i ∧ PV2 M ρ (drop1 M x rk) i := by
    have h := D.1
    rwa [show M.length - 1 = x by omega] at h
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = x by omega] at hcnt
  have hR := rk_take (show x ≤ M.length by omega) I.rank hcnt
  have hC := cons_of_rk hR
  exact ⟨hC, hR, good3_take2 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab
    I.cons I.good hC hR hdrop, hdrop⟩

theorem good3_expand_t2V3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hBX : T2BelowXE M) (hCR : T2CopyResE M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → Good3 (expand M n) σ := by
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
  rw [hL] at hr
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hexp : ∀ n, expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  obtain ⟨hSD, _, _, _⟩ := hX.loc
  -- the base `M[1] = M.take x`
  have hB1 : ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) 1) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) 1) σ := by
    intro σ hσ
    rw [gexp_one_gen hlen] at hσ ⊢
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    rw [show M.length - 1 = r + L by omega] at hcnt
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
    have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i := by
      have := D.1; rwa [show M.length - 1 = r + L by omega] at this
    have hG := good3_take2 (x := r + L) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good (cons_of_rk hRk1) hRk1
      hdrop
    exact good3_congr hG (agree_of_cons (cons_of_rk hRk1) hσ hRk1)
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact good3_gexp_t2 hlen hL0 hA hd0e (by omega) (by omega) hgx he2r hX.r0p hSD
    (fun m hm => by obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm; rw [hexp m] at h'; exact ⟨rk', h'⟩)
    (fun m _ => by rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1)
    hB1 (hCR r L hlen hr) (hBX r L hlen hr) n hn σ hσ


end Ytosk.V3Main
