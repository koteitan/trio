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


namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`hR2` for `t = 2`** from `T2BelowXRes` and the two seed1 residuals. -/
theorem r2X_t2XR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hSV : T2Seed1SV) (hQC : T2Seed1C) :
    Std M → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2X M ρ rk := by
  intro hM I R hz h2
  have hS : M ≠ SRO := ne_SRO_of_rk I.rank
  have RA : Res3W M ρ rk := R
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hGall := good3_expand_t2 hM hS I RA hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I RA hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I RA hz h2)
  -- the seeds for `n ≥ 2`
  have hbig : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      ∀ n σ, 2 ≤ n →
        Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        (∀ p, T2Seed M r L p → SeedL ρ σ p) ∧
        WfAbsW.AbsWNx M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
          (r + L) ρ σ := by
    intro r L hlen hr n σ hn hCN
    have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ _ hr; omega
    have hexp : expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n := by
      have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
      rw [h2, show M.length - 1 = r + L by omega] at h
      simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
        Nat.add_sub_cancel_left] at h
      exact h
    have hGN := hGall n (by omega) σ (by rw [hexp]; exact hCN)
    rw [hexp] at hGN
    have hOT : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length → isOT (valB σ b j) = true := by
      intro b j _ hj
      cases b
      · exact hGN.ot_v j hj
      · exact hGN.ot_o j hj
    have hGP : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ := by
      intro m hm1 _ τ hτ
      have hexp1 : expand M m = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
          (entry M 1 (r + L) - entry M 1 r) m := by
        have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
        rw [h2, show M.length - 1 = r + L by omega] at h
        simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
          Nat.add_sub_cancel_left] at h
        exact h
      have := hGall m hm1 τ (by rw [hexp1]; exact hτ)
      rwa [hexp1] at this
    have hBR := hB hM hS I RA hz h2 r L hlen hr n hn hGP σ hCN hOT
    exact ⟨fun p hp => (hBR.2.1 p hp).1, hBR.2.2.2.1⟩
  -- the drop to `M.take x`
  have hdropOf : ∀ r L, r + L + 1 = M.length →
      ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV M ρ (drop1 M (r + L) rk) i := by
    intro r L hlen
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
    have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
    have := R.hdrop; rw [show M.length - 1 = r + L by omega] at this; exact this
  have hctx : ∀ r L, r + L + 1 = M.length →
      Cons (M.take (r + L)) (drop1 M (r + L) rk) ∧ Rk (M.take (r + L)) rk := by
    intro r L hlen
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
    exact ⟨cons_of_rk hRk1, hRk1⟩
  -- `q = r`, `x − 1` does not upgrade to `x`: `x` is a counted child of `r`
  have hqr1 : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      upg M (r + L - 1) ≠ some (r + L) → (drop1 M (r + L) rk).o r ≠ ρ.o r := by
    intro r L hlen hr hq hux
    have hrx : r < r + L := par_lt M 0 _ _ hq
    obtain ⟨_, h1lt⟩ := par2_facts I.z2 (by omega) hr
    have hxbr : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    have hXu : ∀ i, upg M i ≠ some (r + L) := by
      intro i hu
      obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
      have hi : i < M.length := by
        by_contra h
        exact (upg_e12 hu).1 (entry_out (by omega) 1)
      rcases hcase with h | ⟨_, h⟩
      · exact hux (by rw [show r + L - 1 = i by omega]; exact hu)
      · omega
    have hcnt : Counted M r (r + L) := ⟨hxbr, by rw [isUpg_x_false hXu]; simp⟩
    have hxin : r + L ∈ CL M r := by
      unfold CL; rw [List.mem_filter]
      exact ⟨mem_children_iff.mpr ⟨by omega, hq⟩, by simpa using hcnt⟩
    obtain ⟨hC1, hRk1⟩ := hctx r L hlen
    exact ne_of_lt (o_strict_cl_x hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1
      (hdropOf r L hlen) hrx hxin)
  refine ⟨fun r L qp pq hlen hr hq hqp hpq => ⟨?_, ?_⟩, fun r L hlen hr hq => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- `q ≠ r`: seed1 at `pq`
    have hqx : r + qp < r + L := par_lt M 0 _ _ hq
    by_cases hcl : r + qp ∈ CL M pq
    · obtain ⟨Txb, _, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq hqp hpq
      have he2q := hX.loc.2.2.1 (r + qp) (r + L) (mem_children_iff.mpr ⟨by omega, hq⟩) Txb
      have h2q : entry M 2 (r + qp) ≠ 0 := by omega
      have h1q : entry M 1 (r + qp) ≠ 0 := fun h => h2q (I.r12 _ h)
      obtain ⟨hC1, hRk1⟩ := hctx r L hlen
      exact ne_of_lt (o_strict_qn hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1
        (hdropOf r L hlen) hq hpq Txb h1q h2q Tclq hcl)
    · exact hQC M ρ rk hM I R hz h2 r L (r + qp) pq hlen hr hq (by omega) hpq hcl
  · exact fun n σ hn hCN => (hbig r L hlen hr n σ hn hCN).1 pq (Or.inr ⟨r + qp, hq, by omega, hpq⟩)
  · exact fun hux => ⟨hSV M ρ rk hM I R hz h2 r L hlen hr hq hux,
      fun n σ hn hCN => (hbig r L hlen hr n σ hn hCN).1 r (Or.inl ⟨hq, rfl⟩)⟩
  · exact fun hux => ⟨hqr1 r L hlen hr hq (by rw [hux]; simp)⟩
  · exact fun k hux hk => ⟨fun _ => hqr1 r L hlen hr hq (by rw [hux]; intro h; cases h; omega)⟩
  · exact fun _ n σ hn hCN => (hbig r L hlen hr n σ hn hCN).1 r (Or.inl ⟨hq, rfl⟩)

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Step 1 for `t = 2`**: from the invariants, the remaining hypotheses (`Res3`, `Res3T2`) and a
valuation of each `M[n]` (`n ≥ 2`), every expansion drops the root value. -/
theorem t2_dropsCX {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3C M ρ rk) (R : Res3D M ρ rk) (R2 : Res3T2X M ρ rk)
    (hD2 : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      isOT (root (expand M n) σ) = true ∧ root (expand M n) σ < root M ρ)
    (hX : SInvX M) (hJ : RowJ M)
    (hCh : ∀ j k, j ≤ k → k < M.length → root (M.take j) (drop1 M j rk) ≤ root (M.take k) (drop1 M k rk))
    (hPv : ∀ j, j < M.length → Cons (M.take j) (drop1 M j rk) ∧ Rk (M.take j) rk ∧
      isOT (root (M.take j) (drop1 M j rk)) = true)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hNval : ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
      ∃ σ rkN, Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧ Good3 (expand M n) σ) :
    ∀ n, DropsAt M ρ n := by
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
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
  have hdr : DropRes M (r + L) ρ (drop1 M (r + L) rk) := by
    have := R.drop; rw [hL] at this; exact this
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rk) :=
    good3_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
  have hdrop := drop_all (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws)
    hdr.ua
  have hseed1 : UpgAbsX M (r + L) ρ → ∀ p, p < r + L → CL M p ≠ [] → (drop1 M (r + L) rk).o p ≠ ρ.o p →
      Lhd z ((drop1 M (r + L) rk).o p) (ρ.o p) :=
    fun hua p hp hcl hne => lhd_of_po I.cons I.good (by omega) hcl
      (PO.zero_of_strong (by omega) hua I.cons I.good (by omega) (hdrop p hp).1 (hdrop p hp).2) hne
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := (anc0_par hA (by omega) hq).le
  have hqx : q < r + L := par_lt M 0 _ q hq
  -- `n ≤ 1`: the drop to `M.take x`
  have hlast : isOT (root (M.take (r + L)) (drop1 M (r + L) rk)) = true ∧
      root (M.take (r + L)) (drop1 M (r + L) rk) < root M ρ := by
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hua' : UpgAbsX M (r + L) ρ ∨ T2UABad M (r + L) :=
        (T2UpgAbs.strong_or_old_target hlen I.cons I.good (T2UpgAbs.e2_ne_of_par2 (by omega) hr) hdr.ua).imp_right
          (fun ⟨k, hk, hkx, hNB⟩ => ⟨⟨r, hq, hr⟩, ⟨k, hk, hkx⟩, hNB⟩)
      have hAbs := absWN_of_absC hdr.ab hC1 hq hrb
      cases hux : upg M (r + L - 1) with
      | none =>
        have T' := T.nn hux
        have hua := hua'.resolve_right (fun hb => by
          obtain ⟨_, ⟨k, hk, _⟩, _⟩ := hb; rw [hux] at hk; cases hk)
        obtain ⟨hdv, hos, hvsh⟩ := qr_shapes hlen hL0 hq (hXu_of (by rw [hux]; simp)) hxbr hrb
          I.r0p I.z2 I.sd I.z1 I.uat I.uab
        exact t2_qr_take hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (hrcl_of hq (by rw [hux]; simp)) hrU hux
          hdv hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
          (hseed1 hua r (by omega) (hrcl_of hq (by rw [hux]; simp)) T'.seed1)
      | some k =>
        have hkl := upg_lt (by omega) hux
        by_cases hkx : k = r + L
        · rw [hkx] at hux
          have T' := T.sv hux
          have hua := hua'.resolve_right (fun hb => by
            obtain ⟨_, ⟨k', hk', hk'x⟩, _⟩ := hb; rw [hux] at hk'; cases hk'; omega)
          obtain ⟨Sp1, _, Sdv, Sos, Svsh⟩ := sv_shapes hlen hL0 hq hux (rx_of_sv hlen I.z2 I.z1 hr hux) hrb he2r
            I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be
          exact t2_sv_take hlen hL0 hq hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) hrU
            Sp1 Sdv Sos Svsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
            (hseed1 hua r (by omega) (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) T'.seed1)
        · have hk : k < r + L := by omega
          have T' := T.up k hux hk
          obtain ⟨hp1, hdv, hos, hvsh⟩ :
              (∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
              (∀ c, c < r + L → c ≠ r → DepS M (SV r (r + L - 1)) false c → CL M c = []) ∧
              OSh M (SV r (r + L - 1)) (r + L) ∧ VSh M (SV r (r + L - 1)) (r + L) := by
            by_cases hrx : r = r + L - 1
            · exact qu_shapes hlen hL0 hq hrx (hXu_of (by rw [hux]; intro h; cases h; omega)) hxbr hrb he2r
                I.r0p I.z2 I.sd I.z1 I.uat I.uab
            · obtain ⟨h1, _, h3, h4, h5⟩ := sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat
                I.uab I.r12 I.be
              exact ⟨h1, fun c hc _ hd => h3 c hc hd, h4, h5⟩
          by_cases hbad : T2UABad M (r + L)
          · -- the strong absorption may fail: the seed moves to the parent of `x − 1`
            obtain ⟨_, _, hbp⟩ := hbad
            have hux' : upg M (r + L - 1) = some k := hux
            have he1j : entry M 1 (r + L - 1) ≠ 0 := (upg_e12 hux').1
            have he0j : entry M 0 (r + L - 1) ≠ 0 := fun h => he1j (I.r01 _ h)
            have hj0 : 0 < r + L - 1 := by
              rcases Nat.eq_zero_or_pos (r + L - 1) with h | h
              · rw [h] at he0j; exact absurd I.e00 he0j
              · exact h
            obtain ⟨pr, hpr⟩ := par0_some_of (M := M) hj0 (by rw [I.e00]; omega)
            exact t2_qu_take_bad hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb
              (hrcl_of hq (by rw [hux]; intro h; cases h; omega)) hrU hux hk
              (I.uat _ k hux (by omega)) hp1 hdv
              (fun hrx => (sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be).2.1)
              hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
              (fun h => lhd_of_po I.cons I.good (by omega) (hrcl_of hq (by rw [hux]; intro h'; cases h'; omega))
                (PO.zero_of_ne (by omega) I.cons I.good (by omega) (hdrop r (by omega)).1 (hdrop r (by omega)).2 hdr.ws.2.2)
                (T'.seed1 h))
              hpr (fun g hg => hbp pr g (by rw [show r + L - 1 = r + L - 1 from rfl]; exact hpr) hg)
              (fun hrx => by
                have hcnt : Counted M r (r + L) :=
                  ⟨hxbr, by rw [isUpg_x_false (hXu_of (by rw [hux]; intro h; cases h; omega))]; simp⟩
                unfold CL; rw [List.mem_filter]
                exact ⟨mem_children_iff.mpr ⟨by omega, hq⟩, by simpa using hcnt⟩)
              I.r0p I.sd I.z1 I.uab hdrop hdr.ws.2.2
          have hua := hua'.resolve_right hbad
          exact t2_qu_take hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (hrcl_of hq (by rw [hux]; intro h; cases h; omega)) hrU hux hk
            (I.uat _ k hux (by omega)) hp1 hdv
            (fun hrx => (sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be).2.1)
            hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
            hua hAbs
            (fun h => hseed1 hua r (by omega) (hrcl_of hq (by rw [hux]; intro h'; cases h'; omega)) (T'.seed1 h))
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      obtain ⟨Tp1, TqL, Tdv, Tos, Tvsh⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
        I.uat I.uab I.r12 hpq' Tqb
      have hAbs := absWN_of_absC hdr.ab hC1 hq' (fun i h => by rw [hpq'] at h; cases h; exact Tqb)
      have hs1 := T2UpgAbs.strong_seed_of_drop hlen I.cons I.good
        (by have := par_lt M 0 _ _ hpq; omega) (by have := par_lt M 0 _ _ hpq; omega) Tclpq
        (hdrop pq (by have := par_lt M 0 _ _ hpq; omega)) T.seed1 hdr.ws.2.2
      cases hux : upg M (r + L - 1) with
      | none =>
        exact t2_qn_take hlen hL0 hA hq' (by omega) Txb I.be I.z2 I.uat I.r12 I.r01 I.e00 hpq' Tqb Te2pq
          Tclq Tclpq hux Tp1 TqL Tdv Tos Tvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
          hAbs hs1
      | some k =>
        obtain ⟨Up1, Up1a, Uqsh, Udv, Uos, Uvsh⟩ := qnu_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd
          I.z1 I.uat I.uab I.r12 hpq' Tqb hux
        exact T2UpgAbs.qnu_take_of_drop hlen hL0 hA hq' (by omega) Txb I.be
          I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.r01 I.e00
          hpq' Tqb Te2pq Tclq Tclpq hux Up1 Up1a Uqsh Udv Uos Uvsh
          I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hdr.ua hdr.ws.2.2 hdrop hAbs hs1
  -- `n ≥ 2`
  have hbig : ∀ n, 2 ≤ n → ∀ σ rkN,
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) σ) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ <
        root M ρ := by
    intro n hn σ rkN hCN hRN hGN
    have h := hD2 n hn σ rkN (by rw [hexp n]; exact hCN) (by rw [hexp n]; exact hRN) (by rw [hexp n]; exact hGN)
    rw [hexp n] at h; exact h
  intro n
  rcases n with _ | _ | n
  · by_cases hBp : ∃ j, j + 1 < M.length ∧ Bad2 (M.take (j + 1))
    · apply dropsAt_of (by rw [hexp 0, gexp_zero_gen])
      obtain ⟨hc, hrk, hot⟩ := hPv r (by omega)
      exact ⟨_, _, hc, hrk, hot, lt_of_le_of_lt (hCh r (r + L) (by omega) (by omega)) hlast.2⟩
    apply dropsAt_of (by rw [hexp 0, gexp_zero_gen])
    exact drop_n0_gen hlen hL0 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
      (fun j _ hj => R.chain j (by omega) (fun hb => hBp ⟨j, by omega, hb⟩)) hlast.2
  · apply dropsAt_of (by rw [hexp 1, gexp_one_gen hlen])
    exact ⟨_, _, hC1, hRk1, hlast⟩
  · have hne := gexp_ne_SRO (n := n + 2) hlen hL0 hA hd0e
      (show entry M 1 (r + L) = entry M 1 r + (entry M 1 (r + L) - entry M 1 r) by omega) he2r h1lt
      (by omega)
    have hnil : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n + 2)
        ≠ [] := by
      intro h
      have hl := TRIO.gexp_length (M := M) (j0 := r) (Lb := L)
        (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r) (n := n + 2) hlen
      rw [h] at hl
      have : L ≤ (n + 2) * L := Nat.le_mul_of_pos_left L (by omega)
      simp at hl; omega
    obtain ⟨σ, rkN, hCN, hRN, hGN⟩ := hNval (n + 2) (by omega) (by rw [hexp]; exact hne)
      (by rw [hexp]; exact hnil)
    rw [hexp] at hCN hRN hGN
    apply dropsAt_of (hexp (n + 2))
    exact ⟨σ, rkN, hCN, hRN, hbig (n + 2) (by omega) σ rkN hCN hRN hGN⟩

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem hT2_V2XR (h2 : ExpT2V2) (hR2 : R2V2X) (hD2 : T2Drop2X) (hCB : T2CBadOut) (hTB : TakeBadV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk) (R : Res3D M ρ rk) :
    col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n := by
  intro hz hs
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  by_cases hb : T2CBad M
  · apply t2_dropsC (Inv3V2.toC C.S C.I) R (hCB M ρ rk C.toStepCtxB hb hz hs).2 hX hJ (root_chain_pre hTB C) (prefix_facts_pre C) hz hs
    intro n hn _ _
    obtain ⟨ρN, rkN, IN⟩ := (hCB M ρ rk C.toStepCtxB hb hz hs).1 n hn
    exact ⟨ρN, rkN, IN.cons, IN.rank, IN.good⟩
  · apply t2_dropsCX (Inv3V2.toC C.S C.I) R (hR2 M ρ rk ⟨C.toStepCtxB, hb⟩ hz hs)
      (hD2 M ρ rk ⟨C.toStepCtxB, hb⟩ hz hs) hX hJ (root_chain_pre hTB C) (prefix_facts_pre C) hz hs
    intro n hn _ _
    obtain ⟨ρN, rkN, IN⟩ := h2 M ρ rk ⟨C.toStepCtxB, hb⟩ hz hs n hn
    exact ⟨ρN, rkN, IN.cons, IN.rank, IN.good⟩

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Desc3 from the residuals**, with `t = 0` and `t = 1` in the conclusion forms `ExpT0OutV2`・`ExpT1OutV2`
(2026-10-17: no strong absorption `HAbSV2`; the `t = 0` descent comes from t0's engine). -/
theorem desc3_V2OXR (hU : HDropU) (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (h0 : ExpT0OutV2) (h1 : ExpT1OutV2) (h2 : ExpT2V2) (hR2 : R2V2X) (hD2 : T2Drop2X) (hCB : T2CBadOut) : Desc3 := by
  intro M n hM hS hE
  obtain ⟨ρ, rk, I⟩ := hInvV2_all hU hD hT hTB hBO h0 h1 h2 hCB M hM hS hE
  by_cases hB : Bad2 M
  · have hl2 : 2 ≤ M.length := by
      obtain ⟨⟨k, hu⟩, _⟩ := hB
      have := upg_succ_lt hu; omega
    have hpre := pre_V2 hD hT hTB hM hS I
    obtain ⟨IT, hlast⟩ := hTB M ρ rk hM hS hl2 hB I
    rcases n with _ | _ | n
    · obtain ⟨j, hj, he⟩ := expand_zero_take hE
      obtain ⟨hc, hrk, _⟩ := prefix_facts_of_pre hpre j hj
      refine ⟨root M ρ, root (M.take j) (drop1 M j rk), ⟨ρ, rk, I.cons, I.rank, rfl⟩, ?_, root_ot I.good,
        lt_of_le_of_lt (root_chain_of_pre hTB hM hpre j (M.length - 1) (by omega) (by omega)) hlast⟩
      rw [he]; exact ⟨_, rk, hc, hrk, rfl⟩
    · refine ⟨root M ρ, _, ⟨ρ, rk, I.cons, I.rank, rfl⟩, ?_, root_ot I.good, hlast⟩
      rw [expand_one]; exact ⟨_, rk, IT.cons, IT.rank, rfl⟩
    · obtain ⟨t', hv, _, hlt⟩ := (hBO M ρ rk hM hS hE hB I (n + 2) (by omega)).2
      exact ⟨root M ρ, t', ⟨ρ, rk, I.cons, I.rank, rfl⟩, hv, root_ot I.good, hlt⟩
  have C := ctx_V2 hU hD hT hTB hM hS hE hB I
  have R := res3D_of_V2 C
  obtain ⟨t', hv, _, hlt⟩ := desc_stepV2 hE (Inv3V2.toC C.S I) R (root_chain_pre hTB C) (prefix_facts_pre C)
    (hT0_V2 h0 C) (hT1_V2 h1 C) (hT2_V2XR h2 hR2 hD2 hCB hTB C R) n
  exact ⟨root M ρ, t', ⟨ρ, rk, I.cons, I.rank, rfl⟩, hv, root_ot I.good, hlt⟩

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`BadOutT2B` from the `t = 2` engines** (2026-10-25): the context `StepCtxB` holds on `Bad2` too, the engines run
on it (`ExpT2V2`, `R2V2`, and `T2CBadOut` at the bad C shape), and the descent for `n ≥ 2` is `t2_drops_ge2`. -/
theorem badOutT2B_ofXR (hU : HDropU) (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (h2 : ExpT2V2) (hR2 : R2V2X)
    (hD2 : T2Drop2X) (hCB : T2CBadOut) : BadOutT2B := by
  intro M ρ rk hM hS hE hB I h2t n hn
  have CB := ctxB_V2 hU hD hT hTB hM hS hE I
  have hz : col M (M.length - 1) ≠ (0, 0, 0) := bad2_col_ne_zero hB
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  by_cases hb : T2CBad M
  · have key := hCB M ρ rk CB hb hz h2t
    refine ⟨key.1 n hn, ?_⟩
    exact t2_drops_ge2 (Inv3W.ofV2 CB.S CB.I) CB.toW key.2 hX hJ hz h2t (fun m hm _ _ => by
      obtain ⟨ρN, rkN, IN⟩ := key.1 m hm
      exact ⟨ρN, rkN, IN.cons, IN.rank, IN.good⟩) n hn
  · obtain ⟨ρN, rkN, IN⟩ := h2 M ρ rk ⟨CB, hb⟩ hz h2t n hn
    refine ⟨⟨ρN, rkN, IN⟩, root (expand M n) ρN, ⟨ρN, rkN, IN.cons, IN.rank, rfl⟩, ?_⟩
    exact hD2 M ρ rk ⟨CB, hb⟩ hz h2t n hn ρN rkN IN.cons IN.rank IN.good

end Ytosk

namespace Ytosk

/-- **`R2V2X` from `T2BelowXResV2X`** (`r2V2_of` without `absN`). -/
theorem r2V2_ofXR (hB : WfT2X.T2BelowXResV2X) : R2V2X := fun M ρ rk C hz h2 =>
  r2X_t2XR (hB M ρ rk C) t2Seed1SV_holds t2Seed1C_holds C.std (Inv3W.ofV2 C.S C.I) C.toW hz h2

end Ytosk
