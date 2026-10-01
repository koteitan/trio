/-
**3 行・t = 1・q ≠ r: n についての帰納法。**

M[1] = M.take x の評価（r の値が始点 seed）から、すべての n ≥ 2 で M[n] に評価があり、
r の値は鎖の項 gamS μ b_r seed (n − 1)、D の外の v は M と同じ、値は標準形で M の値より小さい（`t1_chain`）。
-/
import Ytosk.V3ValT1

namespace Ytosk

open T

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2`** (`t = 1`, `q ≠ r`). -/
theorem t1_chain (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    {μ br vr seed : T}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o (r + L)))
    (hox : ∀ ζ, fsD (ρ.o (r + L)) ζ = ζ)
    (hro : ρ.o r = psi vr br z) (hrD : DepX M (r + L) true r)
    (hO : ∀ m i, i < r + L → DepX M (r + L) true i →
      OLocal M (r + L) ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ (gamS μ br seed m) μ i)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsR : ∀ m, Single (fsD (ρ.o Rt) (gamS μ br seed m)))
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  -- one level: from `P = M[n-1]` to `M[n]`
  have step : ∀ n, 2 ≤ n → ∀ ρP rkP, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP → ρP.o r = gamS μ br seed (n - 2) →
      (∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ρ.v g = ρP.v g) →
      ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
        ρN.o r = gamS μ br seed (n - 1) ∧
        (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
        isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
        root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
    intro n hn ρP rkP hCP hRP hPr hPv
    set ζ := gamS μ br seed (n - 2) with hζ
    have hPr' : ρP.o r = fsD (ρ.o (r + L)) ζ := by rw [hox]; exact hPr
    -- the valuation and ranking built in `val_N_t1`
    have hHt := t1_path (ρN := shiftV ρP L) hC hG hx hrot hcb hμr hbr hS hHx
      (by show ρP.o (r + L - L) = _; rw [show r + L - L = r by omega]; exact hPr')
      (hO (n - 2)) (hV (n - 2))
    have hF : ∀ i, i < r + L →
        (DepX M (r + L) true i →
          oRhs M (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)) i = fsD (ρ.o i) ζ) ∧
        (DepX M (r + L) false i →
          vRhs M (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)) i = fsD (ρ.v i) ζ) := by
      intro i hi
      exact ⟨fun hd => (hHt true i hd (Or.inl hi)).2 hi, fun hd => (hHt false i hd (Or.inl hi)).2 hi⟩
    have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
        (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)).v g = ρP.v g := by
      intro g hg a ha hr
      rw [glueZ_v_lt ρ _ _ (by omega) (hnd n hn g hg a ha hr)]
      exact hPv g hg a ha hr
    have hCN := cons_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hCP
      hagree hF
    have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hnd n hn)
      hRM hRP
    refine ⟨_, _, hCN, hRN, ?_, ?_, ?_⟩
    · -- the value at `r`
      show (glue M (r + L) ρ (shiftV ρP L) ζ).o r = _
      rw [glue_o_dep ρ _ ζ (by omega) hrD, hro, fsD_here hbr hcb, ← hμr]
      rw [show n - 1 = (n - 2) + 1 by omega]; rfl
    · intro g hg hd
      exact glueZ_v_lt ρ _ _ hg hd
    · -- the root
      have hRx : Rt < r + L := by
        rcases Nat.eq_or_lt_of_le hRA.le with h | h
        · exfalso
          have h1 : entry M 0 (r + L) ≠ 0 := by
            have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
          have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
          rw [h] at hR0e; exact h1 hR0e
        · exact h
      have hRt := hHt true Rt hRd (Or.inl hRx)
      have hRot : isOT (ρ.o Rt) = true := hG.ot_o Rt (by omega)
      have hlt := (hok_of_holeT hrot hcb (by rw [hμr]; exact lt_irrefl' _) hS hRot hRt.1 (n - 2)).2
      exact root_N_t1 hlen hL hA hd0e hn (ρN := shiftV ρP L) (Z := fun _ => ζ)
        hRA hR0 hRlast hRd hsM hpM (hsR (n - 2)) hlt
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact step 2 (le_refl _) ρ1 rk1 hC1 hR1 hr1 (fun g hg a ha hr => hPv1 g hg a (by omega) hr)
  | succ n hn ih =>
    obtain ⟨ρP, rkP, hCP, hRP, hPr, hPd, _⟩ := ih
    apply step (n + 1) (by omega) ρP rkP (by simpa using hCP) (by simpa using hRP)
      (by rw [show n + 1 - 2 = n - 1 by omega]; exact hPr)
    intro g hg a ha hr
    exact (hPd g (by omega) (hnd (n + 1) (by omega) g hg a ha hr)).symm

end

end Ytosk
