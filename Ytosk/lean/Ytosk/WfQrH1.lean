/-
**WfQrH1 (2026-11-01): the q = r chain without a given chain `γ`, and `hX` from the shape of `o(x)`.**
`qr_chainF` is `qr_chainE` (WfQrL18) with the chain term `σ.o r = γ(n-1)` replaced by the bound it was used for:
the carried invariant is `ρP.o r < o(x) ∧ ρP.o r ≠ 0`.  It is re-established at each level from the engine
(`σ.o r < o(r)`, `r ∈ D`) and the `M`-side fact `o(r) ≤ o(x)`.  The step `hX` of the engine (the value at `x`)
is no longer a hypothesis: `σ.o x = ρP.o r` (the copy) and `o(x) = Ω_{a+1}` (an `M`-side fact) give
`DQ.base` with `η = ρP.o r` (`fsD(Ω_{a+1}, η) = η`).
-/
import Ytosk.WfQrL18

namespace Ytosk.WfQrH1
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL7 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10
  Ytosk.WfQrL16 Ytosk.WfQrL18

/-- **`hX` from the shape of `o(x)`**: `o(x) = Ω_{a+1}` and the new value below it. -/
theorem hX_of_omsucc {a e : T} (he : e < psi (succ a) z z) : ∃ η, DQ η false (psi (succ a) z z) e := by
  refine ⟨e, ?_⟩
  have h := DQ.base (η := e) (l := psi (succ a) z z) (by rw [WfQrL11.fsD_om_succ]; exact he)
  rwa [WfQrL11.fsD_om_succ] at h

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2` without a chain `γ`** (`t = 1`, `q = r`).  New `M`-side facts: `o(x) = Ω_{a+1}` (`hOx`),
`o(r) ≤ o(x)` (`hrx`); base: `ρ1.o r < o(x)`, `ρ1.o r ≠ 0`.  `hLocE` lost its chain term and `hX`. -/
theorem qr_chainF (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    {ax : T} (hOx : ρ.o (r + L) = psi (succ ax) z z) (hrx : ρ.o r ≤ ρ.o (r + L))
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (Ex : Nat → Valn → (Nat → T) → (Nat → T) → Prop)
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocE : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        Single (σ.o Rt) ∧
        (∀ i, i < r + L → DepX M (r + L) true i → isOT (σ.o i) = true) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → isOT (σ.v i) = true) ∧
        (∀ c, c < r + L → DepX M (r + L) true c → σ.o c ≠ z) ∧
        Ex n ρP σ.o σ.v ∧
        (∀ c, c ≤ r + L → DepX M (r + L) true c → Single (σ.o c) ∧ isOT (σ.o c) = true) ∧
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          (∃ η, DQ η false (ρ.o c) (σ.o c)) →
          ∃ η', DQ η' false (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L') (ρ.o c)) z)
            (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L') (σ.o c)) z)) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k)))))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r < ρ.o (r + L)) (hr1z : ρ1.o r ≠ z)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepQ Pn Ex M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have step : ∀ n, 2 ≤ n → ∀ ρP rkP, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP → ρP.o r < ρ.o (r + L) → ρP.o r ≠ z →
      (∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ρ.v g = ρP.v g) →
      ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
        Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
        ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
        (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
        isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
        root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
    intro n hn ρP rkP hCP hRP hGP hPP hPr hPrz hPv
    have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hnd n hn)
      hRM hRP
    have hCσ := cons_of_rk hRN
    set σ := rhsIt (TRIO.gexp M r L d0 0 n) (rkBound (TRIO.gexp M r L d0 0 n)
      (rkN M (r + L) L rkM rkP (rkBound M rkM) (rkBound M rkM + rkBound (TRIO.gexp M r L d0 0 (n - 1)) rkP)))
    obtain ⟨hsR, hoto, hotv, hnz, hEx, hSo, hOF, hUpgL, hBW2⟩ := hLocE n hn ρP σ hCP hPr hPrz hCσ
    set oq := σ.o
    set vq := σ.v
    have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
        (glueQ M (r + L) ρ (shiftV ρP L) oq vq).v g = ρP.v g := by
      intro g hg a ha hr
      rw [glueQ_v_lt (by omega) (hnd n hn g hg a ha hr)]
      exact hPv g hg a ha hr
    obtain ⟨hag, hCN, hF⟩ := true_glue_eq hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hCP
      hCσ hRN hagree
    have hlN := len_N (d0 := d0) hlen hn
    have hpos : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
    have hxN : (shiftV ρP L).o (r + L) = σ.o (r + L) := by
      rw [(hag (r + L) (by omega)).1, glueQ_o_ge (le_refl _)]
    have hxv : σ.o (r + L) = ρP.o r := by
      rw [← hxN]; simp [shiftV]
    have hX : ∃ η, DQ η false (ρ.o (r + L)) (σ.o (r + L)) := by
      rw [hOx, hxv]; rw [hOx] at hPr; exact hX_of_omsucc hPr
    have hE := qr_engineDQ2 (x := r + L) (ρN := shiftV ρP L) (σ := σ) hC hG hx hRM hxN
      (fun i hi hd => (hF i hi).1 hd) (fun i hi hd => (hF i hi).2 hd) hX hOSD hVS hSo hotv hOF hPre hUpgL hBW2
    have hRx : Rt < r + L := by
      rcases Nat.eq_or_lt_of_le hRA.le with h | h
      · exfalso
        have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
        have h1 : entry M 0 (r + L) ≠ 0 := by
          have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
        rw [h] at hR0e; exact h1 hR0e
      · exact h
    have hlt : σ.o Rt < ρ.o Rt := engine_o_lt hRx hRd hE
    have hrlt : σ.o r < ρ.o r := engine_o_lt (by omega) hrD hE
    have hle : ∀ c, c < r + L → DepX M (r + L) true c → σ.o c ≤ ρ.o c ∧ σ.o c ≠ z :=
      fun c hc hd => ⟨le_of_lt (engine_o_lt hc hd hE), hnz c hc hd⟩
    have hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z := ⟨le_of_lt hPr, hPrz⟩
    have hGN := good3_N_t1Q hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hG hGP hOS
      hoto hotv hle hlex
    have hro : (glueQ M (r + L) ρ (shiftV ρP L) oq vq).o r = σ.o r := glueQ_o_dep (by omega) hrD
    refine ⟨_, _, hCN, hRN, hGN, hPs n hn ρP oq vq hCP hGP hPP hCN hGN hEx, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hro]; exact hrlt
    · rw [hro]; exact lt_of_lt_of_le hrlt hrx
    · rw [hro]; exact hnz r (by omega) hrD
    · intro g hg hd
      exact glueQ_v_lt hg hd
    · exact root_N_t1Q hlen hL hA hd0e hn (ρN := shiftV ρP L) (vq := vq)
        hRA hR0 hRlast hRd hsM hpM hsR hlt
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact step 2 (le_refl _) ρ1 rk1 hC1 hR1 hG1 hP1 hr1 hr1z (fun g hg a ha hr => hPv1 g hg a (by omega) hr)
  | succ n hn ih =>
    obtain ⟨ρP, rkP, hCP, hRP, hGP, hPP, _, hPr, hPrz, hPd, _⟩ := ih
    apply step (n + 1) (by omega) ρP rkP (by simpa using hCP) (by simpa using hRP) (by simpa using hGP)
      (by simpa using hPP) (by simpa using hPr) (by simpa using hPrz)
    intro g hg a ha hr
    exact (hPd g (by omega) (hnd (n + 1) (by omega) g hg a ha hr)).symm

end

end Ytosk.WfQrH1
