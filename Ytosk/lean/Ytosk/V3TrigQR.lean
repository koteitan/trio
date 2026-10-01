/-
**3 行・t = 1・q = r: TrigOm の hLeaf（古い値が Ω_{t+1} の子）を外す。**

- x より前の D の値は対角点を持つ（`qr_holeD`）。Ω_{t+1} は対角点の位置にならないので、そのような子はない。
- x の枠 (r, L, x) の頭は b_r。新しい値 gamS k の引数が Ω_{ν+1} の形なら b_r = 0:
  k ≥ 1 では引数は b_r ++ γ（γ ≠ 0）で、b_r ≠ 0 なら 1 項にならない。k = 0（種）では SeedOK から添字は μ、
  Ω_{ν+1} < b_r ++ seed、一方 引き金から b_r < Ω_{ν+1} で、b_r ++ seed < Ω_{ν+1} となって矛盾。
-/
import Ytosk.V3TrigN
import Ytosk.V3QRLocV

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `Ω_{t+1}` is never at a diagonal position. -/
theorem not_diag_om {a b μ t : T} (hb : b ≠ z) (h : DiagAt a b μ (psi (succ t) z z)) : False := by
  generalize hT : psi (succ t) z z = U at h
  cases h with
  | here hb' _ _ => exact hb' (T.psi.inj hT).2.1.symm
  | rest _ => exact absurd (T.psi.inj hT).2.2 (by simp)
  | arg hb' _ _ => exact hb' (T.psi.inj hT).2.1.symm
  | sub _ hs _ =>
    have := (T.psi.inj hT).1
    rw [← this, isSucc_succ] at hs; cases hs

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) (h1 : par M 1 x = some r) (hq : par M 0 x = some r)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
  (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hox : ρ.o x = psi (succ μ) z z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS

/-- **hLeaf for `q = r`.** -/
theorem qr_hLeaf (hμ : ρ.v r = μ) {seed : T} (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
    (hseedz : seed ≠ z)
    (hpre : preState M ρ r ((children M r).filter (fun d => decide (d < x))) = b)
    {σ' : Valn} (hxk : ∃ k, σ'.o x = gamS μ (app b (psi (succ μ) z z)) seed k) :
    ∀ i Lc c R, i < x → children M i = Lc ++ c :: R → Counted M i c → c ≤ x →
      DepX M x true c → ∀ t, ρ.o c = psi (succ t) z z → ∀ s ν,
      σ'.o c = psi s (psi (succ ν) z z) z →
      lt (preState M ρ i Lc) (psi (succ ν) z z) = true →
      lt (psi (ρ.v i) z z) (psi s (psi (succ ν) z z) z) = true → preState M ρ i Lc = z := by
  intro i Lc c R hi hch _ hcx hd t hto s ν hnew ht1 ht2
  rcases Nat.lt_or_ge c x with hc | hc
  · exfalso
    obtain ⟨_, a', _, hD⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS
      true c hd hc
    simp only [valB, cond_true] at hD
    rw [hto] at hD
    exact not_diag_om (fun h => absurd (app_eq_z h).2 (by simp)) hD
  · have hcx' : c = x := by omega
    subst hcx'
    have hcm : c ∈ children M i := by rw [hch]; simp
    have hir : i = r := Option.some.inj ((mem_children_iff.mp hcm).2.symm.trans hq)
    subst hir
    -- the head is `b`
    have hR : R = [] := by
      rcases R with _ | ⟨d, R'⟩
      · rfl
      · exfalso
        have hdm : d ∈ children M i := by rw [hch]; simp
        have hsort := children_sorted M i
        rw [hch] at hsort
        have hcd := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1 d (by simp)
        have := (mem_children hdm).2; omega
    subst hR
    have hLc : (children M i).filter (fun d => decide (d < c)) = Lc := by
      rw [hch, List.filter_append]
      have h1' : Lc.filter (fun d => decide (d < c)) = Lc := by
        rw [List.filter_eq_self]
        intro d hd
        have hsort := children_sorted M i
        rw [hch] at hsort
        simpa using (List.pairwise_append.mp hsort).2.2 d hd c (by simp)
      rw [h1']; simp
    rw [hLc] at hpre
    rw [hpre] at ht1 ⊢
    rw [hμ] at ht2
    obtain ⟨k, hk⟩ := hxk
    rw [hnew] at hk
    by_contra hbz
    obtain ⟨p, q, c', rfl⟩ : ∃ p q c', b = psi p q c' := by
      cases b with
      | z => exact absurd rfl hbz
      | psi p q c' => exact ⟨p, q, c', rfl⟩
    cases k with
    | succ k =>
      rw [gamS_succ_q] at hk
      unfold qnext at hk
      have h2 := (T.psi.inj hk).2.1
      have h3 : app c' (gamS μ (app (psi p q c') (psi (succ μ) z z)) seed k) = z := by
        simp only [app] at h2; exact (T.psi.inj h2).2.2.symm
      exact gamS_ne_z_q hseedz k (app_eq_z h3).2
    | zero =>
      have hs : s = μ := by
        have hlo : psi s (psi (succ ν) z z) z < psi (succ μ) z z := by
          have := hSr.lt_om; rw [show seed = psi s (psi (succ ν) z z) z from hk.symm] at this; exact this
        have hle : s ≤ μ := by
          rcases psi_lt_psi_z_iff.mp hlo with h | ⟨_, h⟩
          · exact lt_succ_iff.mp h
          · exact absurd h (not_lt_z _)
        rcases psi_lt_psi_z_iff.mp (show psi μ z z < psi s (psi (succ ν) z z) z from ht2) with h | ⟨h, _⟩
        · exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)
        · exact h.symm
      subst hs
      have hnx : seed < gamS s (app (psi p q c') (psi (succ s) z z)) seed 1 := hSr.lt_next
      rw [gamS_succ_q] at hnx
      unfold qnext at hnx
      rw [show seed = psi s (psi (succ ν) z z) z from hk.symm] at hnx
      have h4 : psi (succ ν) z z < app (psi p q c') (psi s (psi (succ ν) z z) z) := by
        rcases psi_lt_psi_z_iff.mp hnx with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl _)
        · exact h
      have hp : p < succ ν := by
        rcases psi_lt_psi_z_iff.mp (show psi p q c' < psi (succ ν) z z from ht1) with h | ⟨_, h⟩
        · exact h
        · exact absurd h (not_lt_z _)
      have h5 : app (psi p q c') (psi s (psi (succ ν) z z) z) < psi (succ ν) z z := by
        show psi p q (app c' _) < _
        exact psi_lt_psi_z_iff.mpr (Or.inl hp)
      exact absurd (lt_trans h4 h5) (lt_irrefl _)

end

end Ytosk
