/-
**3 行・t = 2: 残り T2BelowRV2（種での RClaimU・REr と AbsWN）を、M と M.take x だけの残りに減らす（2026-10-17、t2）。**

- 種の RClaimU・REr（T2SeedRR）: 4 つの場合ごとに V3T2SeedRRC。qr は既にある残り T2SeedQRRes（dom の欄）だけから。
  qn・sv・C は閉じた条件（T2SeedQNCl・T2SeedSVCl・T2SeedCCl、まとめて `T2SeedClV2`）。
- AbsWN: 落とし側は BumpAbsC から、展開側は bumpW の単調性（`T2BumpMonoV2`）。V3T2AbW。Bad2 では落とし側が偽なので、
  AbsWN M M[n] を残り `T2AbsNBad` にした（2026-10-25）。
-/
import Ytosk.V3T2SeedRRC
import Ytosk.V3T2AbW

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Residual (t2): the closedness of the seed argument in `M[n]`** (qn・sv・C; `M` and `M.take x` only). -/
def T2SeedClV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNCl M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVCl M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCCl M ρ r L q)

/-- **Residual (t2): the bump term grows from `M.take x` to `M[n]`** before `x`. -/
def T2BumpMonoV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → T2BumpMono M r L

/-- **Residual (t2, `Bad2`): the weak absorption `AbsWN M M[n]` before `x`** (2026-10-25). Outside `Bad2` it comes from
the drop side `AbsWN M (M.take x)` and the bump monotonicity (`t2_absWN`); on `Bad2` the drop side is false
(graftBb2St: 3 standard matrices) but `AbsWN M M[n]` holds (b2grow1・b2grow2・graftBb2St, `n = 2, 3`: no exception). -/
def T2AbsNBad : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      AbsWN M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
        (r + L) ρ σ

/-- **`T2BelowRV2` from the seed residuals, the closedness and the bump monotonicity** (and `T2AbsNBad` on `Bad2`). -/
theorem t2BelowRV2_of (hP : T2SeedPResV2) (hCl : T2SeedClV2) (hBM : T2BumpMonoV2) (hAB : T2AbsNBad) :
    T2BelowRV2 := by
  intro M ρ rk C hz h2 r L hlen hr n hn hG σ hCN _ hor hoq hdec
  have IW := Inv3W.ofV2 C.S C.I
  have RW : Res3W M ρ rk := C.toW
  have hPR := hP M ρ rk C hz h2
  obtain ⟨hQN, hSV, hCC⟩ := hCl M ρ rk C hz h2 r L hlen hr
  refine ⟨fun p hp => ?_, ?_⟩
  swap
  · by_cases hB2 : Bad2 M
    · exact hAB M ρ rk C hB2 hz h2 r L hlen hr n hn σ hCN
    · exact t2_absWN C.std C.ne IW RW hB2 hlen hr (hBM M ρ rk C hz h2 r L hlen hr) hn hCN
  have hpr : p = r := by
    rcases hp with ⟨_, h⟩ | ⟨q, hq, hqr, hpq⟩
    · exact h
    · rw [par0_q_t2 C.std C.ne IW hlen hr hq hqr] at hpq; cases hpq; rfl
  rw [hpr]
  rcases t2_seed_cases hlen hr with hc | hc | hc | hc
  · obtain ⟨hq, hXu⟩ := hc
    obtain ⟨_, h1lt⟩ := par2_facts IW.z2 (by omega) hr
    have hxb : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
    exact seedRR_qr C.std C.ne IW RW hz h2 hlen hr hq hXu hCLM (hPR.qr r L hlen hr hq hXu Lc hCLM)
      n hn hG σ hCN hor
  · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
    exact seedRR_qn C.std C.ne IW RW hz h2 hlen hr hq hqr hCLM (hPR.qn r L q hlen hr hq hqr Lc hCLM)
      (hQN q Lc hq hqr hCLM) n hn hG σ hCN (hoq q hq hqr) hdec hor
  · obtain ⟨hq, hux⟩ := hc
    exact seedRR_sv C.std C.ne IW RW hz h2 hlen hr hq hux (hPR.sv r L hlen hr hq hux) (hSV ⟨hq, hux⟩)
      n hn hG σ hCN hdec hor
  · obtain ⟨q, hq, hqr, hncl⟩ := hc
    exact seedRR_C C.std C.ne IW RW hz h2 hlen hr hq hqr hncl (hPR.C r L q hlen hr hq hqr hncl).1
      (hCC q hq hqr hncl) n hn hG σ hCN (hoq q hq hqr) hdec hor

end Ytosk
