/-
**3 行・t = 2: Std な行列の展開 M[n] の順位（hExp の Rk の欄）。**

最後の列の型が t = 2 で、M が構造の不変条件 SInvX ∧ RowJ を満たし順位を持つなら、すべての n ≥ 1 で
expand M n に順位がある（`rk_expand_t2`）。rk_gexp_t2_final の仮定を SInvX・RowJ と P_2 の性質から出す。
-/
import Ytosk.V3ExpT2H
import Ytosk.V3InvT2
import Ytosk.V3IndV

namespace Ytosk

open T

/-- **The ranking of `M[n]` for a last column of type `t = 2`.** -/
theorem rk_expand_t2 {M : Mat} (hX : SInvX M) (hJ : RowJ M) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) :
    ∀ n, 1 ≤ n → ∃ rk, Rk (expand M n) rk := by
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
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqlt := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hqr : r ≤ q := hrq.le
  -- `q` is not the bump child of its parent
  have hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
    intro i hi
    by_cases hqr' : q = r
    · subst hqr'
      intro h
      have := e2_of_col (show col M q = (entry M 0 i + 1, entry M 1 i, 1) from h); omega
    · have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hi' : par M 0 (r + (q - r)) = some i := by rw [show r + (q - r) = q by omega]; exact hi
      have := (t2_qn_struct hX hJ hlen hr hq' (by omega) hi').2.1
      rwa [show r + (q - r) = q by omega] at this
  intro n hn
  obtain ⟨hSD, hZ1, _, hBL⟩ := hX.loc
  have hUM : UAT M := hX.toSInv.uat
  obtain ⟨rk, hrk⟩ := rk_gexp_t2_final (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hA hq hd0e
    (by omega) (by omega) hgx he2r h1lt hqb
    hX.r0p hX.z2 hSD hZ1 hUM hBL
    (fun m _ => by rw [← hexp m]; exact (sInvX_expand hX m).toSInv.uat)
    (fun m _ => by rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1) hRM n hn
  exact ⟨rk, by rw [hexp n]; exact hrk⟩

/-- **The remaining work of `hExp` for `t = 2`**: given the evaluation (`Cons`) and a ranking of
`M[n]`, the value fields of `Inv3V` and `Res3A`. -/
def T2ExpRes : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
    col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 → ∀ n, 2 ≤ n →
    ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN →
      Inv3V (expand M n) σ rkN ∧ Res3A (expand M n) σ rkN

/-- **`hExp` for `t = 2`** from its remaining work: the ranking of `M[n]` is `rk_expand_t2` and the
evaluation is the iteration of the equations along it (`cons_of_rk`). -/
theorem hExp_t2 (hRes : T2ExpRes) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  intro M ρ rk hM hS _ I R hz h2 n hn
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  exact ⟨_, rkN, hRes M ρ rk hM hS I R hz h2 n hn _ rkN (cons_of_rk hRN) hRN⟩

end Ytosk
