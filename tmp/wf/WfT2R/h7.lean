/-
**WfT2R7: the `t = 2` descent without the false field `Res3T2.absN` (2026-11-01, t = 2 Bad2 route).**

`Res3T2.absN` (V3T2Top) is `AbsWN M M[n]`, false on the standard 36-column Bad2 matrix (WfSrcC3Cex・WfAbsWCex), so
`R2V2` (and `r2V2_of`, which reads it from `T2BelowXResV2`) cannot come from `T2BelowXResV2X`.
- `Res3T2X`: `Res3T2` without `absN`; `R2V2X`; `r2V2X_of` (copy of `hR2_t2` on `T2BelowXResAtX`).
- `T2Drop2X`: the root drop of every `M[n]` (`n ≥ 2`), proved from `T2BelowXResV2X` (`t2Drop2X_of`, by
  `WfT2X.t2_root_ofX`). It replaces `absN` in `t2_dropsCX` (copy of `t2_dropsC`).
- `hT2_V2XR`, `desc3_V2OXR`, `badOutT2B_ofXR`: copies with `R2V2X` and `T2Drop2X`. At the bad C shape (`T2CBad`) they
  still use `T2CBadOut` (whose `Res3T2` keeps `absN`; a top-level residual not touched here).
-/
import Ytosk.WfT2R6
import Ytosk.V3MainV2
import Ytosk.V3TopT2B

namespace Ytosk

open T Classical

/-- **`Res3T2` without `absN`.** -/
structure Res3T2X (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  qn : ∀ r L qp pq, r + L + 1 = M.length → par M 2 (r + L) = some r →
    par M 0 (r + L) = some (r + qp) → 0 < qp → par M 0 (r + qp) = some pq → T2QN M ρ rk r L qp pq
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    T2R M ρ rk r L

theorem Res3T2.toX {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : Res3T2 M ρ rk) : Res3T2X M ρ rk :=
  ⟨h.qn, h.qr⟩

def R2V2X : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    Res3T2X M ρ rk

/-- **The root drop of `M[n]`, `n ≥ 2`, `t = 2`** (the part of `Res3T2.absN` that the descent reads). -/
def T2Drop2X : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      isOT (root (expand M n) σ) = true ∧ root (expand M n) σ < root M ρ

theorem t2Drop2X_of (hB : WfT2X.T2BelowXResV2X) : T2Drop2X := by
  intro M ρ rk C hz h2 n hn σ rkN hCN hRN hGN
  have hM := C.std
  have hS := C.ne
  have IW : Inv3W M ρ rk := Inv3W.ofV2 C.S C.I
  have RW : Res3W M ρ rk := C.toW
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS IW RW hz h2 (WfT2X.t2BelowXE_ofX (hB M ρ rk C) hM hS IW RW hz h2)
    (t2CopyResAll_holds M ρ rk hM hS IW RW hz h2)
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  rw [hL] at hr
  have hexp : ∀ m, expand M m = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have key := WfT2X.t2_root_ofX (hB M ρ rk C) hM hS IW RW hz h2 hlen hr n hn
    (fun m hm1 _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm1 τ hτ) σ
    (by rw [← hexp n]; exact hCN)
    (fun j _ hj => by rw [← hexp n] at hj; exact ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
    (by rw [← hexp n]; exact hGN)
  rw [hexp n]; exact key

end Ytosk

