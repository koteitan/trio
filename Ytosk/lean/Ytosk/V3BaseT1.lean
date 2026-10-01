/-
**3 行・t = 1・q ≠ r: 基底 M[1] = M.take x の評価と始点。**

M.take x の順位は M の順位から（`rk_take`、数える子が増えないこと）、評価は `cons_of_rk`。始点 seed = o_{M.take x}(r) の
条件 SeedOK は「seed ◁ o_M(r)」と「v の r の値が同じ」から（`seedOK_of_lhd_top`）。これらを `t1_main` に渡す（`t1_main2`）。
残る基底の仮定は落とす補題が与える: 数える子が増えない、v(r) 不変、seed の標準形、seed ◁ o(r)、写しが読む v の一致。
-/
import Ytosk.V3SeedTop
import Ytosk.V3Struct2

namespace Ytosk

open T

/-- The subscript of an `o` value is the normalized `v` value. -/
theorem o_psi_sub {M : Mat} {ρ : Valn} (hC : Cons M ρ) {i : Nat} (hi : i < M.length) :
    ∃ y, ρ.o i = psi (sf (ρ.v i)) y z := by
  rw [(hC i hi).1]
  unfold oRhs
  show ∃ y, add (sp (sf (ρ.v i)) z (sf _)) (sf z) = psi (sf (ρ.v i)) y z
  rw [sp_eq_spArg]; exact ⟨_, rfl⟩

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`, with the base from `M.take x`.** -/
theorem t1_main2 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    {μ br vr : T}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hoxv : ρ.o (r + L) = psi (succ μ) z z)
    (hro : ρ.o r = psi vr br z) (hrD : DepX M (r + L) true r)
    (hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    -- the base: the evaluation of `M.take x`
    (hcnt : ∀ i c, i < r + L → c ∈ children (M.take (r + L)) i → Counted (M.take (r + L)) i c →
      Counted M i c)
    (hv1 : (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).v r = vr)
    (hs1ot : isOT ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) = true)
    (hs1lhd : Lhd z ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) (ρ.o r))
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) →
      ρ.v g = (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).v g)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) m) μ i)
    (hS2 : ∀ i k, i ≤ r → DepX M (r + L) false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
    (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
      DepX M (r + L) true k → k ≤ r)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L')
        (fsD y (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) m)) = true)
    (hLo : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2
          (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) m))
          (psi (succ s) z z)).2 = z))
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM))) (hPs : ExpStepT1 Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  set M1 := M.take (r + L) with hM1
  set ρ1 := rhsIt M1 (rkBound M1 rkM) with hρ1
  have hR1 : Rk M1 rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons M1 ρ1 := cons_of_rk hR1
  have hg1 : TRIO.gexp M r L d0 0 1 = M1 := gexp_one_eq hlen
  have hrM1 : r < M1.length := by rw [hM1, List.length_take]; omega
  -- the seed
  obtain ⟨σ, hs1⟩ := o_psi_sub hC1 hrM1
  have hvot : isOT vr = true := isOT_sub hrot
  rw [hv1, sf_ot hvot, ← hμr] at hs1
  -- the seed condition
  have hro' : ρ.o r = psi μ br z := by rw [hro, hμr]
  have hlhd : Lhd z (psi μ σ z) (psi μ br z) := by rw [← hs1, ← hro']; exact hs1lhd
  have hσb : σ < br := by
    have := hlhd.1; rw [psi_lt_psi_z_iff] at this
    rcases this with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  have hsot : isOT (psi μ σ z) = true := by rw [← hs1]; exact hs1ot
  have hrot' : isOT (psi μ br z) = true := by rw [hμr]; exact hrot
  have hμ' : ¬ lt μ μ = true := lt_irrefl' μ
  have hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ (ρ1.o r) := by
    intro a' ha' hot'
    rw [hs1]
    exact seedOK_of_lhd_top hot' hcb (by rw [hμr]; exact ha') hsot hσb hlhd
  intro n hn
  obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, _, _, hot, hlt⟩ :=
    t1_main hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hqr hC hG hRM hrot hcb hμr hbr
      hS ⟨σ, hs1⟩ hoxv hro hrD hF1 hOS hV hS2 hS3 hW hLo hRA hR0 hRlast hRd hsM hpM
      (ρ1 := ρ1) (rk1 := rkM) (by rw [hg1]; exact hC1) (by rw [hg1]; exact hR1) rfl
      (fun g hg a ha h => hPv1 g hg a ha h) (by rw [hg1]; exact hG1) Pn (by rw [hg1]; exact hP1) hPs n hn
  exact ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩

end

end Ytosk
