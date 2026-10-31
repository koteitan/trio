/-
**WfQnA5 (2026-11-01): root decrease of the q ≠ r engine with the bad leaves as seeds.**
`t1_rootX2` = `WfQnA4.t1_rootX` with `hSeedB` discharged by `WfQnA3.seed_bad_t1` for `B = BadSet M x ρ r ζ`.
Residuals at the bad leaves: `hna` (`BumpNA`), `hVlt` (`V < A`), `hnest` (no nested bad call), `hRwin` (window
absorption `A[ζ] ≤ q < A ⇒ q ◁ A`).
-/
import Ytosk.WfQnA4

namespace Ytosk.WfQnA5
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad Ytosk.WfQnA4

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0)
  (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
  (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
  {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
  (hndN : ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 (r + L) = some r) (hqr : par M 0 (r + L) ≠ some r)
include hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN hR0 hZ2 hSD hZ1 hUAT hUAB h1 hqr

/-- **Root decrease with the bad leaves as seeds** (`hSeedB` from `WfQnA3.seed_bad_t1`). -/
theorem t1_rootX2 (hz2 : entry M 2 r ≤ 1) {ρ ρP σ : Valn} {rkN : Bool → Nat → Nat} {μ br vr seed : T} {m : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed m)).v g = ρP.v g)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN)
    (hrot : isOT (psi vr br z) = true) (hro_eq : ρ.o r = psi vr br z) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o (r + L)))
    (hxN : (shiftV ρP L).o (r + L) = fsD (ρ.o (r + L)) (gamS μ br seed m))
    (hO : ∀ i, i < r + L → DepX M (r + L) true i → ¬ DepXB M B true i →
      OLocal M (r + L) ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ i, i < r + L → DepX M (r + L) false i → ¬ DepXB M B false i →
      VLocal M (r + L) ρ (gamS μ br seed m) μ i)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0c : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsR : Single (fsD (ρ.o Rt) (gamS μ br seed m))) (hlt : fsD (ρ.o Rt) (gamS μ br seed m) < ρ.o Rt)
    -- the engine
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hOTD : ∀ b j, j < r + L → DepX M (r + L) b j → isOT (fsD (valB ρ b j) (gamS μ br seed m)) = true)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 0 n).length → isOT (valB σ b j) = true)
    -- the bad leaves
    (hBdef : B = BadSet M (r + L) ρ r (gamS μ br seed m))
    (hna : ∀ i, B i → WfQnL6.BumpNA M (r + L) ρ (gamS μ br seed m) i)
    (hVlt : ∀ i, B i → vOpt ρ (par M 1 i) < ρ.o r)
    (hnest : ∀ i, B i → ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, ¬ DepXB M B true k)
    (hRwin : ∀ i, B i → ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < fsD (ρ.o r) (gamS μ br seed m) →
      q < ρ.o r → Lhd z q (ρ.o r))
    (hVSN : ∀ i (Lc : List Nat) c, i < r + L → DepXB M B true i → CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] →
      σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hHard : ∀ i (Lc : List Nat) c s y y', i < r + L → DepXB M B true i →
      CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] → ρ.o c = psi s y z →
      σ.o c = psi s y' z → lt (ρ.v i) s = true →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
      ∀ g ∈ comps (ρ.v i) y', g ≤ H s y')
    (hAbsW : ∀ i, i < r + L → DepXB M B false i → ¬ B i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z →
        ¬ q < bumpW (TRIO.gexp M r L d0 0 n) σ i → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    isOT (root (TRIO.gexp M r L d0 0 n) σ) = true ∧ root (TRIO.gexp M r L d0 0 n) σ < root M ρ := by
  have hE := WfQnH5.t1_E1B hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN hz2 hC hG hCP hagree hCN hRN
    hrot hcb hμr hbr hS hHx hxN hO hV
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hxN' : r + L < (TRIO.gexp M r L d0 0 n).length := by
    rw [hlN]; have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simp at this; omega
  have hro' : ρ.o r = psi μ br z := by rw [hro_eq, hμr]
  have hSd : SeedOK μ br μ seed := by
    have := hS vr (lt_irrefl' vr) hrot; rwa [← hμr] at this
  have hSeedB : ∀ i, B i → i < r + L → Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true := by
    intro i hBi hi
    have hBi' := hBi
    rw [hBdef] at hBi'
    obtain ⟨_, hdi, _, h1i, h2i, hWi, _⟩ := hBi'
    have hpd := (dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hdi).2.1
    have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
      cases hp : par M 1 i with
      | none => rfl
      | some m' => exact hG.ot_v m' (by have := par_lt M 1 i m' hp; omega)
    have hAot : isOT (ρ.o r) = true := hG.ot_o r (by have := par_lt M 1 (r + L) r h1; omega)
    exact WfQnA3.seed_bad_t1 (x := r + L) hlen hxN' hC hCN
      (WfQnA2.sameAt_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 i hi) hxN hi h1i h2i hpd (hna i hBi)
      hWi hro' hAot hcb hSd hVot (by rw [← hro']; exact hVlt i hBi) hB hE.1 hE.2 (hnest i hBi) (hRwin i hBi)
  exact t1_rootX hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN hR0 hZ2 hSD hZ1 hUAT hUAB h1 hqr hz2
    hC hG hCP hagree hCN hRN hrot hcb hμr hbr hS hHx hxN hO hV hRA hR0c hRlast hRd hsM hpM hsR hlt hF hFO hVS
    hTD hKD hOTD hOTout hSeedB hVSN hHard hAbsW

end

end Ytosk.WfQnA5
