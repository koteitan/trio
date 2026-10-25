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

/-- **Residual (t2, `Bad2`): the weak absorption of `M[n]` at the columns where that of `M.take x` fails**
(2026-10-25/26). Outside `Bad2`, `AbsWN M M[n]` comes from the drop side `AbsWN M (M.take x)` and the bump monotonicity
(`t2_absWN`); on `Bad2` the drop side is false at some columns (graftBb2St: 3 standard matrices, the qr shape with
`x` a child of `x − 1`), where the premise of `M[n]` is empty (the bump term of `M[n]` stays large). At the other
columns the drop side and `T2BumpMono` give it (`t2_absWN_bad`). -/
def T2AbsNBad : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ¬ (∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → ¬ s < bumpW (M.take (r + L)) τ i →
          s < bumpW M ρ i → Lhd z s (bumpW M ρ i)) →
      ∀ n, 2 ≤ n → ∀ σ,
        Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
          ¬ s < bumpW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ i →
          s < bumpW M ρ i → Lhd z s (bumpW M ρ i)

/-- **`AbsWN M M[n]` on `Bad2`**: the drop side where it holds (with `T2BumpMono`), `T2AbsNBad` where it fails. -/
theorem t2_absWN_bad (hAB : T2AbsNBad) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk)
    (hB2 : Bad2 M) (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hm : T2BumpMono M r L) {n : Nat} (hn : 2 ≤ n)
    {σ : Valn}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) :
    AbsWN M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
      (r + L) ρ σ := by
  have I := C.I
  have hcnt := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  intro i hi h1 h2' s hs hs2 hnN hlt
  by_cases hT : ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)) i →
      s < bumpW M ρ i → Lhd z s (bumpW M ρ i)
  · exact hT s hs hs2 (fun h => hnN (lt_of_lt_of_le h (hm _ hC0 n hn σ hCN i hi h1 h2'))) hlt
  · exact hAB M ρ rk C hB2 hz h2 r L hlen hr _ hC0 i hi h1 h2' hT n hn σ hCN s hs hs2 hnN hlt

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
    · exact t2_absWN_bad hAB C hB2 hz h2 hlen hr (hBM M ρ rk C hz h2 r L hlen hr) hn hCN
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
