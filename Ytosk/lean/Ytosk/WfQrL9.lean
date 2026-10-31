/-
**WfQrL9 (2026-11-01): `qr_chainT`, the chain of the q = r engine from facts about the true values.**

Same induction as `qr_chainQ` (WfQrL7), with the `D` values taken from the true valuation `σ` of `M[n]`
(`cons_of_rk` with `rk_N_t1`); the local equations come from `true_glue` (WfQrL8).  What is left at each level
(`hLocT`) is about the values of `σ` on `D` only: `σ.o r` is the next chain term, `σ.o Rt < o(Rt)`, standard
form, `σ.o c ≤ o(c)`, `σ.o c ≠ 0` — the content of "`σ` is a `DQ` of `ρ` on `D`" (WfQrE1) plus standard form.
-/
import Ytosk.WfQrL8

namespace Ytosk.WfQrL9
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL7 Ytosk.WfQrL8

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2` from facts about the true values** (`t = 1`, `q = r`): `hLocT` asks, for a solution `σ` of
`M[n]`, only the next chain term at `r`, the root drop, standard form, `σ.o c ≤ o(c)`, `σ.o c ≠ 0` on `D`. -/
theorem qr_chainT (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (γ : Nat → T) (hgam : ∀ m, γ m ≤ ρ.o (r + L) ∧ γ m ≠ z)
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (Ex : Nat → Valn → (Nat → T) → (Nat → T) → Prop)
    -- facts about the true values at each level
    (hLocT : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r = γ (n - 2) → Cons (TRIO.gexp M r L d0 0 n) σ →
        σ.o r = γ (n - 1) ∧ Single (σ.o Rt) ∧ σ.o Rt < ρ.o Rt ∧
        (∀ i, i < r + L → DepX M (r + L) true i → isOT (σ.o i) = true) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → isOT (σ.v i) = true) ∧
        (∀ c, c < r + L → DepX M (r + L) true c → σ.o c ≤ ρ.o c ∧ σ.o c ≠ z) ∧
        Ex n ρP σ.o σ.v)
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r = γ 0)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepQ Pn Ex M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = γ (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have step : ∀ n, 2 ≤ n → ∀ ρP rkP, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP → ρP.o r = γ (n - 2) →
      (∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ρ.v g = ρP.v g) →
      ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
        Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = γ (n - 1) ∧
        (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
        isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
        root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
    intro n hn ρP rkP hCP hRP hGP hPP hPr hPv
    have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hnd n hn)
      hRM hRP
    have hCσ := cons_of_rk hRN
    set σ := rhsIt (TRIO.gexp M r L d0 0 n) (rkBound (TRIO.gexp M r L d0 0 n)
      (rkN M (r + L) L rkM rkP (rkBound M rkM) (rkBound M rkM + rkBound (TRIO.gexp M r L d0 0 (n - 1)) rkP)))
    obtain ⟨hZr, hsR, hlt, hoto, hotv, hle, hEx⟩ := hLocT n hn ρP σ hCP hPr hCσ
    set oq := σ.o
    set vq := σ.v
    have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
        (glueQ M (r + L) ρ (shiftV ρP L) oq vq).v g = ρP.v g := by
      intro g hg a ha hr
      rw [glueQ_v_lt (by omega) (hnd n hn g hg a ha hr)]
      exact hPv g hg a ha hr
    have hCN := (true_glue hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hCP hCσ hRN
      hagree).1
    have hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z := by rw [hPr]; exact hgam (n - 2)
    have hGN := good3_N_t1Q hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hG hGP hOS
      hoto hotv hle hlex
    refine ⟨_, _, hCN, hRN, hGN, hPs n hn ρP oq vq hCP hGP hPP hCN hGN hEx, ?_, ?_, ?_⟩
    · rw [glueQ_o_dep (by omega) hrD]; exact hZr
    · intro g hg hd
      exact glueQ_v_lt hg hd
    · exact root_N_t1Q hlen hL hA hd0e hn (ρN := shiftV ρP L) (vq := vq)
        hRA hR0 hRlast hRd hsM hpM hsR hlt
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact step 2 (le_refl _) ρ1 rk1 hC1 hR1 hG1 hP1 hr1 (fun g hg a ha hr => hPv1 g hg a (by omega) hr)
  | succ n hn ih =>
    obtain ⟨ρP, rkP, hCP, hRP, hGP, hPP, hPr, hPd, _⟩ := ih
    apply step (n + 1) (by omega) ρP rkP (by simpa using hCP) (by simpa using hRP) (by simpa using hGP)
      (by simpa using hPP)
      (by rw [show n + 1 - 2 = n - 1 by omega]; exact hPr)
    intro g hg a ha hr
    exact (hPd g (by omega) (hnd (n + 1) (by omega) g hg a ha hr)).symm

end

end Ytosk.WfQrL9
