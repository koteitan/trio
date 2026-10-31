/-
**WfQnA4 (2026-11-01): root decrease of the q ≠ r engine with (E3) from the `◁` engine.**
`t1_rootX` = `WfQnH5.t1_rootB` where the (E3) hypothesis `hE3` at the root is discharged by
`WfQnA3.engine_t1B` (through `WfQnH8.e3_root`).  The seeds are the bad leaves; `hSeedB` is discharged by
`WfQnA3.seed_bad_t1` in `t1_rootX2`.  Named residuals (measured, tmp/wf/WfQnA/meas.py): `hVSN`, `hHard`, `hAbsW`
(closure only), `hOTout` (`N` from `x` on), and at the bad leaves `hVlt`, `hnest`, `hRwin`, `hna`.
-/
import Ytosk.WfQnA3

namespace Ytosk.WfQnA4
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad

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

/-- **Root decrease, (E3) from the engine.** -/
theorem t1_rootX (hz2 : entry M 2 r ≤ 1) {ρ ρP σ : Valn} {rkN : Bool → Nat → Nat} {μ br vr seed : T} {m : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed m)).v g = ρP.v g)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN)
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
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
    (hSeedB : ∀ i, B i → i < r + L → Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true)
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
  have hEng := WfQnA3.engine_t1B hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq hB hC hG hCN hRM
    hF hFO hVS hTD hKD hE.1 hE.2 hOTD hOTout hSeedB hVSN hHard hAbsW
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hxNl : r + L ≤ (TRIO.gexp M r L d0 0 n).length := by rw [hlN]; omega
  apply WfQnH5.t1_rootB hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN hz2 hC hG hCP hagree hCN hRN
    hrot hcb hμr hbr hS hHx hxN hO hV hRA hR0c hRlast hRd hsM hpM hsR hlt
  intro hb
  have hRx : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRA.le with h | h
    · exfalso
      rw [h] at hb
      exact WfQnA2.notXB hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hB hb
    · exact h
  exact WfQnH8.e3_root hCN hRx hxNl (fun b i hD hi => hEng b i (WfQnH8.depS_iff.mp hD) hi) hb

end

end Ytosk.WfQnA4
