/-
**3 行・t = 1・q = r: n についての帰納法（局所の等式を仮定に置いた形）。**

q ≠ r の `t1_chain` と同じ組み立て（`cons_N_t1`・`rk_N_t1`・`root_N_t1` はそのまま使える）。違いは D の列の添字が
列ごとに違う（引き上げで鎖の先へずれる）ことで、各 n で「列ごとの添字 Zf で局所の等式が成り立ち、Zf r が
鎖の項」という仮定 `hLoc` に置く（`qr_chain`）。r の値は fsD(ψ_μ(br), Zf r) = ψ_μ(br[Zf r]) で鎖の次の項。
-/
import Ytosk.V3QRBump

namespace Ytosk

open T

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2`** (`t = 1`, `q = r`), given the local equations with per-column indices. -/
theorem qr_chain (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hC : Cons M ρ) (hRM : Rk M rkM)
    {μ br seed : T} (hbr : br ≠ z) (hcb : cof br = .big μ)
    (hro : ρ.o r = psi μ br z) (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the local equations at each level, with per-column indices
    (hLoc : ∀ n, 2 ≤ n → ∀ ρP : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r = gamS μ br seed (n - 2) → ∃ Zf : Nat → T, Zf r = gamS μ br seed (n - 2) ∧
        (∀ i, i < r + L →
          (DepX M (r + L) true i →
            oRhs M (glueZ M (r + L) ρ (shiftV ρP L) Zf) i = fsD (ρ.o i) (Zf i)) ∧
          (DepX M (r + L) false i →
            vRhs M (glueZ M (r + L) ρ (shiftV ρP L) Zf) i = fsD (ρ.v i) (Zf i))) ∧
        Single (fsD (ρ.o Rt) (Zf Rt)) ∧ fsD (ρ.o Rt) (Zf Rt) < ρ.o Rt)
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
    obtain ⟨Zf, hZr, hF, hsR, hlt⟩ := hLoc n hn ρP hCP hPr
    have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
        (glueZ M (r + L) ρ (shiftV ρP L) Zf).v g = ρP.v g := by
      intro g hg a ha hr
      rw [glueZ_v_lt ρ _ _ (by omega) (hnd n hn g hg a ha hr)]
      exact hPv g hg a ha hr
    have hCN := cons_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hCP
      hagree hF
    have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hnd n hn)
      hRM hRP
    refine ⟨_, _, hCN, hRN, ?_, ?_, ?_⟩
    · rw [glueZ_o_dep ρ _ Zf (by omega) hrD, hro, fsD_here hbr hcb, hZr]
      rw [show n - 1 = (n - 2) + 1 by omega]; rfl
    · intro g hg hd
      exact glueZ_v_lt ρ _ _ hg hd
    · exact root_N_t1 hlen hL hA hd0e hn (ρN := shiftV ρP L) (Z := Zf)
        hRA hR0 hRlast hRd hsM hpM hsR hlt
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
