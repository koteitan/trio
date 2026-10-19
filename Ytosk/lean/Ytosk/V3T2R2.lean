/-
**3 行・t = 2: hR2（Res3T2）の組み立て。**

- big（n ≥ 2 の種 SeedL）: T2BelowXRes の種の欄（N の Good3 は good3_expand_t2 から）。
- seed1（n ≤ 1、M.take x で種の o が変わる）: V3T2Seed1 の狭義性。
  - q = r で x − 1 が x へ上げない（nn・up）: x は r の数える子（o_strict_cl_x）。
  - q ≠ r で q が pq の数える子: o_strict_qn。
  - 残り（仮定）: sv（x − 1 が x へ上げる）と、q ≠ r で q が pq で数えられない場合（q は q − 1 の上げの的）。
    どちらも上げの的の v の変化が祖先の鎖を通って種に届く。
-/
import Ytosk.V3T2Seed1
import Ytosk.V3ExpT2BA
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **Residual of seed1**: `x − 1` upgrades to `x` (`q = r`). -/
def T2Seed1SV : Prop :=
  ∀ M ρ rk, Std M → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    par M 0 (r + L) = some r → upg M (r + L - 1) = some (r + L) → (drop1 M (r + L) rk).o r ≠ ρ.o r

/-- **Residual of seed1**: `q ≠ r` is not a counted child of `pq`. -/
def T2Seed1C : Prop :=
  ∀ M ρ rk, Std M → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L q pq, r + L + 1 = M.length → par M 2 (r + L) = some r →
    par M 0 (r + L) = some q → q ≠ r → par M 0 q = some pq → q ∉ CL M pq →
    (drop1 M (r + L) rk).o pq ≠ ρ.o pq

/-- **The strong absorption at `x − 1` for `t = 2`, outside the shape `T2UABad`** (2026-10-12, drop-fix:
`DropRes.ua` is now the weak `UpgAbsXW`. 2026-10-17: the strong form alone is false on T2Ext (175 matrices on the
11 sets, 89 of std_b), all of the shape `T2UABad`; with the exception the 11 sets and std_b have no counterexample). -/
def T2UpgAbsW : Prop :=
  ∀ M ρ rk, Std M → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → UpgAbsX M (M.length - 1) ρ ∨ T2UABad M (M.length - 1)

/-- **`hR2` for `t = 2`** from `T2BelowXRes` and the two seed1 residuals. -/
theorem hR2_t2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hSV : T2Seed1SV) (hQC : T2Seed1C) :
    Std M → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk := by
  intro hM I R hz h2
  have hS : M ≠ SRO := ne_SRO_of_rk I.rank
  have RA : Res3W M ρ rk := R
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hGall := good3_expand_t2 hM hS I RA hz h2 (t2BelowXE_of hB hM hS I RA hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I RA hz h2)
  -- the seeds for `n ≥ 2`
  have hbig : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      ∀ n σ, 2 ≤ n →
        Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        (∀ p, T2Seed M r L p → SeedL ρ σ p) ∧
        AbsWN M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
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
    exact ⟨fun p hp => (hBR.2.1 p hp).1, hBR.2.2.2⟩
  -- the drop to `M.take x`
  have hdropOf : ∀ r L, r + L + 1 = M.length →
      ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV M ρ (drop1 M (r + L) rk) i := by
    intro r L hlen
    have hdr : DropRes M (r + L) ρ (drop1 M (r + L) rk) := by
      have := R.drop; rw [show M.length - 1 = r + L by omega] at this; exact this
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
    have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
    have hdrop := drop_all (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
      I.fc I.fo hdr.argT
      (bump_drop (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws)
      hdr.ua
    exact fun i hi => ⟨(hdrop i hi).1, (hdrop i hi).2⟩
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
  refine ⟨fun r L hlen hr n σ hn hCN _ => (hbig r L hlen hr n σ hn hCN).2,
    fun r L qp pq hlen hr hq hqp hpq => ⟨?_, ?_⟩, fun r L hlen hr hq => ⟨?_, ?_, ?_, ?_⟩⟩
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
