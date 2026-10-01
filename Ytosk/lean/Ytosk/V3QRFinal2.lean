/-
**3 行・t = 1・q = r（n ≥ 2）: o(r) の形を内部で出した形。**

b = qrB（r の x より前の子の状態）とおくと、`qr_o_r` から o(r) = ψ_μ(b + Ω_{μ+1})、b の加数は Ω_{μ+1} 以上。
`qr_final` の仮定 hro・hb・hpre を外す（`qr_final2`）。
-/
import Ytosk.V3QRFinal

namespace Ytosk

open T

/-- The state of the children of `r` before `x`. -/
noncomputable def qrB (M : Mat) (ρ : Valn) (r x : Nat) : T :=
  preState M ρ r ((children M r).filter (fun d => decide (d < x)))

/-- **`t = 1`, `q = r`, all `n ≥ 2`**, with `b = qrB`. -/
theorem qr_final2 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
    (hTP : TP1W M ρ) (hTPL : TPLoW M ρ) (hAU' : AbsUW M ρ) (hAD' : AbsDW M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s,
      ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      preState M ρ i L' ≤ qrB M ρ r (r + L))
    (hS : ∀ a', ¬ lt (ρ.v r) a' = true →
      isOT (psi a' (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      SeedOK a' (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) (ρ.v r)
        ((drop1 M (r + L) rkM).o r))
    (hsp0 : spArg (ρ.v r) (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r) =
      app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r))
    (hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbq : b = qrB M ρ r (r + L) := hbe
  subst hbq
  exact qr_final hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD
    hAD hTP hTPL hAU' hAD' hsM hpM hro hb rfl hYB hS hsp0 hLs

end Ytosk
