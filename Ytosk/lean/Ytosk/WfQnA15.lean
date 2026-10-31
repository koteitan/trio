/-
**WfQnA15 (2026-11-01): the seed part of `WfQnA8.ResT1B` from the bad-leaf facts.**
`ResT1Bv` = `ResT1B` without the seeds.  `resT1B_of`: for `B n = BadSet M x ρ r (gamS μ b_r seed (n − 2))`,
the seeds (`◁` at the bad leaves) follow from `WfQnA3.seed_bad_t1` with the residuals `hVlt` (`V < A`), `hnest`
(no nested bad call), `hRwin` (window absorption) and `hna` (`BumpNA`, by `WfQnA14.bump_naB` from `hnest`).
-/
import Ytosk.WfQnA14

namespace Ytosk.WfQnA15
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad

/-- `ResT1B` without the seeds. -/
def ResT1Bv (M : Mat) (r L d0 : Nat) (ρ : Valn) (μ br seed : T) (B : Nat → Nat → Prop) : Prop :=
  ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP → ρP.o r = gamS μ br seed (n - 2) →
    Cons (TRIO.gexp M r L d0 0 n) σ →
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M (B n) true i) →
      σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed (n - 2))).o i) →
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M (B n) false i) →
      σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed (n - 2))).v i) →
    (∀ i (Lc : List Nat) c, i < r + L → DepXB M (B n) true i → CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] →
      σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))) ∧
    (∀ i (Lc : List Nat) c s y y', i < r + L → DepXB M (B n) true i →
      CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] → ρ.o c = psi s y z →
      σ.o c = psi s y' z → lt (ρ.v i) s = true →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
      ∀ g ∈ comps (ρ.v i) y', g ≤ H s y') ∧
    (∀ i, i < r + L → DepXB M (B n) false i → ¬ B n i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z →
        ¬ q < bumpW (TRIO.gexp M r L d0 0 n) σ i → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) {q : Nat} (hq : par M 0 (r + L) = some q)
include hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq

theorem resT1B_of {ρ : Valn} {μ br vr seed : T} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hro : ρ.o r = psi μ br z) (hcb : cof br = .big μ) (hSd : SeedOK μ br μ seed)
    (hox : ρ.o (r + L) = psi (succ μ) z z)
    (hVlt : ∀ m i, BadSet M (r + L) ρ r (gamS μ br seed m) i → vOpt ρ (par M 1 i) < ρ.o r)
    (hnest : ∀ m i, BadSet M (r + L) ρ r (gamS μ br seed m) i → ∀ j ∈ children M i, col M j = bump M i →
      ∀ k ∈ children M j, ¬ DepXB M (BadSet M (r + L) ρ r (gamS μ br seed m)) true k)
    (hRwin : ∀ m i, BadSet M (r + L) ρ r (gamS μ br seed m) i → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < fsD (ρ.o r) (gamS μ br seed m) → q < ρ.o r → Lhd z q (ρ.o r))
    (hna : ∀ m i, BadSet M (r + L) ρ r (gamS μ br seed m) i → WfQnL6.BumpNA M (r + L) ρ (gamS μ br seed m) i)
    (hRest : ResT1Bv M r L d0 ρ μ br seed (fun n => BadSet M (r + L) ρ r (gamS μ br seed (n - 2)))) :
    WfQnA8.ResT1B M r L d0 ρ μ br seed (fun n => BadSet M (r + L) ρ r (gamS μ br seed (n - 2))) := by
  intro n hn ρP σ hCP hGP hPr hCN hE1o hE1v
  obtain ⟨hVSN, hHard, hAbsW⟩ := hRest n hn ρP σ hCP hGP hPr hCN hE1o hE1v
  refine ⟨?_, hVSN, hHard, hAbsW⟩
  intro i hBi hi
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hxN' : r + L < (TRIO.gexp M r L d0 0 n).length := by
    rw [hlN]; have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simp at this; omega
  have hxN : (shiftV ρP L).o (r + L) = fsD (ρ.o (r + L)) (gamS μ br seed (n - 2)) := by
    show ρP.o (r + L - L) = _
    rw [show r + L - L = r by omega, hox, fsD_leaf (isSucc_succ μ) (succ_ne_z μ)]; exact hPr
  obtain ⟨_, hdi, _, h1i, h2i, hWi, _⟩ := id hBi
  have hpd := (dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hdi).2.1
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m' => exact hG.ot_v m' (by have := par_lt M 1 i m' hp; omega)
  have hAot : isOT (ρ.o r) = true := hG.ot_o r (by have := par_lt M 1 (r + L) r h1; omega)
  exact WfQnA3.seed_bad_t1 (x := r + L) hlen hxN' hC hCN
    (WfQnA2.sameAt_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 i hi) hxN hi h1i h2i hpd
    (hna _ i hBi) hWi hro hAot hcb hSd hVot (by rw [← hro]; exact hVlt _ i hBi) (fun j h => h.2.1) hE1o hE1v
    (hnest _ i hBi) (hRwin _ i hBi)

end

end Ytosk.WfQnA15
