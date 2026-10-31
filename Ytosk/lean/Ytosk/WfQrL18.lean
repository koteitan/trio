/-
**WfQrL18 (2026-11-01): `qr_chainE`, the q = r chain with the bounds from the DQ engine.**
At each level the true valuation `σ` of `M[n]` (cons_of_rk) is the glue of its own `D` values (`true_glue_eq`);
the engine `qr_engineDQ2` (WfQrL16) gives `σ.o c < o(c)` on `D` from the frame steps; `qr_chainT`'s remaining facts
(chain term at `r`, `Single σ.o Rt`, standard form, `≠ 0`) and the engine's frame steps are the hypotheses `hLocE`.
-/
import Ytosk.WfQrL17

namespace Ytosk.WfQrL18
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL7 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10
  Ytosk.WfQrL16

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- `true_glue` with the agreement `σ = τ` exported. -/
theorem true_glue_eq (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP σ : Valn} {rkN : Bool → Nat → Nat} (hC : Cons M ρ) (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v).v g = ρP.v g) :
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length →
      σ.o i = (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v).o i ∧ σ.v i = (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v).v i) ∧
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v) ∧
    ∀ i, i < r + L →
      (DepX M (r + L) true i → oRhs M (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v) i = σ.o i) ∧
      (DepX M (r + L) false i → vRhs M (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v) i = σ.v i) := by
  have hlN := len_N (d0 := d0) hlen hn
  set τ := glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v with hτ
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hoff := cons_glueQ_off (ρ := ρ) (ρN := shiftV ρP L) (oq := σ.o) (vq := σ.v)
    (N := TRIO.gexp M r L d0 0 n) (by omega) hC hSA (fun i hi _ m _ hm => reads_lt_x hlen hx2 hi hm)
  have hcopy : ∀ i, r + L ≤ i → i < (TRIO.gexp M r L d0 0 n).length →
      τ.o i = oRhs (TRIO.gexp M r L d0 0 n) τ i ∧ τ.v i = vRhs (TRIO.gexp M r L d0 0 n) τ i := by
    intro i h hi
    rw [hτ, glueQ_eq_glueZ M (r + L) ρ (shiftV ρP L) σ.o σ.v (fun _ => z)] at hagree ⊢
    have := cons_copy hlen hL hA hd0e hn hpath hz2 hCP hagree (i - (r + L)) (by omega)
    rw [show r + L + (i - (r + L)) = i by omega] at this
    exact this
  let S : Bool → Nat → Prop := fun b i => i < r + L ∧ DepX M (r + L) b i
  have hS : ∀ b i, i < (TRIO.gexp M r L d0 0 n).length → S b i → valB σ b i = valB τ b i := by
    intro b i _ ⟨hi, hd⟩
    cases b with
    | true => simp only [valB, cond_true]; rw [hτ, glueQ_o_dep hi hd]
    | false => simp only [valB, cond_false]; rw [hτ, glueQ_v_dep hi hd]
  have hτo : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ S true i →
      τ.o i = oRhs (TRIO.gexp M r L d0 0 n) τ i := by
    intro i hi hn'
    rcases Nat.lt_or_ge i (r + L) with h | h
    · exact (hoff i h).1 (fun hd => hn' ⟨h, hd⟩)
    · exact (hcopy i h hi).1
  have hτv : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ S false i →
      τ.v i = vRhs (TRIO.gexp M r L d0 0 n) τ i := by
    intro i hi hn'
    rcases Nat.lt_or_ge i (r + L) with h | h
    · exact (hoff i h).2 (fun hd => hn' ⟨h, hd⟩)
    · exact (hcopy i h hi).2
  have hag : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → σ.o i = τ.o i ∧ σ.v i = τ.v i := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have := agree_of_eqs S hCN hRN hS hτo hτv (rkN true i + 1) true i (Nat.lt_succ_self _) hi
      simpa [valB] using this
    · have := agree_of_eqs S hCN hRN hS hτo hτv (rkN false i + 1) false i (Nat.lt_succ_self _) hi
      simpa [valB] using this
  have hCτ := cons_of_agree hCN hag
  refine ⟨hag, hCτ, fun i hi => ⟨fun hd => ?_, fun hd => ?_⟩⟩
  · rw [← oRhs_same (hSA i hi), ← (hCτ i (by omega)).1, hτ, glueQ_o_dep hi hd]
  · rw [← vRhs_same (hSA i hi), ← (hCτ i (by omega)).2, hτ, glueQ_v_dep hi hd]

end

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2`, the bounds from the DQ engine** (`t = 1`, `q = r`): `hLocE` asks, for the true valuation `σ`
of `M[n]`, the chain term at `r`, `Single σ.o Rt`, standard form, `σ.o c ≠ 0`, and the frame steps of
`qr_engineDQ2`; the drop `σ.o c < o(c)` (hence `≤` and the root drop) is proved by the engine. -/
theorem qr_chainE (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    -- facts about the true values at each level, and the frame steps
    (hLocE : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r = γ (n - 2) → Cons (TRIO.gexp M r L d0 0 n) σ →
        σ.o r = γ (n - 1) ∧ Single (σ.o Rt) ∧
        (∀ i, i < r + L → DepX M (r + L) true i → isOT (σ.o i) = true) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → isOT (σ.v i) = true) ∧
        (∀ c, c < r + L → DepX M (r + L) true c → σ.o c ≠ z) ∧
        Ex n ρP σ.o σ.v ∧
        (∃ η, DQ η false (ρ.o (r + L)) (σ.o (r + L))) ∧
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
    obtain ⟨hZr, hsR, hoto, hotv, hnz, hEx, hX, hSo, hOF, hUpgL, hBW2⟩ := hLocE n hn ρP σ hCP hPr hCσ
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
    have hle : ∀ c, c < r + L → DepX M (r + L) true c → σ.o c ≤ ρ.o c ∧ σ.o c ≠ z :=
      fun c hc hd => ⟨le_of_lt (engine_o_lt hc hd hE), hnz c hc hd⟩
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

end Ytosk.WfQrL18
