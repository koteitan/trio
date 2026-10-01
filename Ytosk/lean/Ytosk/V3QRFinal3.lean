/-
**3 行・t = 1・q = r（n ≥ 2）: 始点の条件を落とす補題から出した形。**

落とす補題（`drop_all`、仮定は t1 の `t1_main_final` と同じ）から:
- seed = o_{M[1]}(r) < A（D の狭義の降下 `dep_strict0`）、seed ◁ A（PO の 2 つ目の場合は A = Ω_w の形なので起きない）。
- spArg(μ, b, seed) = b + seed（`spArg_seed`）。
- SeedOK: seed の添字が μ なら `seedOK_of_lhd_top`、μ より小さいなら成分の条件 hcs から `seedOK_of_c2`。
- 始点の (L)(ii): seed ≥ ψ_μ(1) なら TPLoW から。そうでない場合（b = 0、r = x − 1 のときだけ）は仮定 hLs0。
残る仮定（q = r に固有）: hYB、hcs（添字が μ より小さい始点の成分は始点より小さい）、hLs0。
-/
import Ytosk.V3QRSeed
import Ytosk.V3MainT1F

namespace Ytosk

open T

/-- **`t = 1`, `q = r`, all `n ≥ 2`**, with the seed conditions from the drop lemma. -/
theorem qr_final3 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    -- the drop lemma (as for `t1_main_final`)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM)) (hUA : UpgAbsX M (r + L) ρ)
    -- value invariants
    (hAD : AbsD M ρ) (hTP : TP1W M ρ) (hTPL : TPLoW M ρ) (hAU' : AbsUW M ρ) (hAD' : AbsDW M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- `q = r`
    (hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s,
      ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      preState M ρ i L' ≤ qrB M ρ r (r + L))
    (hcs : lt (sf ((drop1 M (r + L) rkM).v r)) (ρ.v r) = true →
      ∀ u g, g ∈ comps u ((drop1 M (r + L) rkM).o r) → g < (drop1 M (r + L) rkM).o r)
    (hLs0 : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z → ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hr : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  set μ := ρ.v r with hμ
  set b := qrB M ρ r (r + L) with hbdef
  set seed := (drop1 M (r + L) rkM).o r with hseed
  -- `o(r) = A`
  obtain ⟨b0, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbb : b0 = b := hbe
  rw [hbb] at hro hb
  have hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hxv : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact hdep.2.1 hdm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  -- the drop lemma
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS)
    hUA
  have hlt : seed < ρ.o r := dep_strict0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hq hxv
    true r hdep.1 hr
  obtain ⟨hPO, hsing⟩ := (hdrop r hr).1
  have hlhd : Lhd z seed (ρ.o r) := by
    rcases hPO with hl | ⟨_, w, hw⟩
    · rcases hl with he | hl
      · exact absurd (he ▸ hlt) (lt_irrefl' _)
      · exact hl
    · rw [hro] at hw
      exact absurd (T.psi.inj hw).2.1 (fun he => absurd (app_eq_z he).2 (by simp))
  -- the form of the seed
  obtain ⟨σ1, hs1⟩ := o_psi_sub hC1 hrT
  set s1 := sf ((drop1 M (r + L) rkM).v r) with hs1def
  have hs1' : seed = psi s1 σ1 z := hs1
  have hsot : isOT (psi s1 σ1 z) = true := by rw [← hs1]; exact hsing.1
  have hlt' : psi s1 σ1 z < psi μ (app b (psi (succ μ) z z)) z := by rw [← hs1, ← hro]; exact hlt
  have hseedz : seed ≠ z := by rw [hs1']; simp
  -- `spArg(μ, b, seed) = b + seed`
  have hsp0 : spArg μ b seed = app b seed := by rw [hs1']; exact spArg_seed hb hsot hlt'
  -- `SeedOK`
  have hbot : isOT b = true := isOT_app_left (isOT_arg hrot)
  have hS : ∀ a', ¬ lt μ a' = true → isOT (psi a' (app b (psi (succ μ) z z)) z) = true →
      SeedOK a' (app b (psi (succ μ) z z)) μ seed := by
    intro a' ha' hot'
    rw [hs1']
    have hsub := hlt'
    rw [psi_lt_psi_z_iff] at hsub
    rcases hsub with hsμ | ⟨hsμ, hσb⟩
    · -- the subscript is below `μ`
      apply seedOK_of_c2 hot' cof_br ha' hsot
      · exact lt_trans hlt' (by rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ))
      · rw [psi_lt_psi_z_iff]; exact Or.inl hsμ
      · intro u _ g hg
        left
        have hg' := hcs hsμ u g (by rw [hs1']; exact hg)
        rw [hs1'] at hg'
        rw [fs_br]
        refine lt_of_lt_of_le hg' ?_
        by_cases hbz : b = z
        · rw [hbz]; exact le_refl _
        · apply le_of_lt
          apply lt_app_right _ hbz
          apply isOT_app_of hbot hsot
          intro q hq
          exact le_of_lt (lt_of_lt_of_le (lt_trans hlt'
            (by rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ))) (le_of_not_gt (hb q hq)))
    · -- the subscript is `μ`
      rw [hsμ] at hsot ⊢
      have hl' : Lhd z (psi μ σ1 z) (psi μ (app b (psi (succ μ) z z)) z) := by
        rw [← hro]; rw [hs1', hsμ] at hlhd; exact hlhd
      exact seedOK_of_lhd_top hot' cof_br ha' hsot hσb hl'
  -- the (L)(ii) at the seed
  have hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
      (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z := by
    intro c hc hdc hd0 s y hcv hyb hl
    by_cases h1s : psi μ one z ≤ seed
    · by_cases hyz : y = z
      · subst hyz; simp [fsD, split]
      have hox : ρ.o (r + L) = psi (succ μ) z z :=
        o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
      have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
      obtain ⟨_, a', _, hDc⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro
        hox hOS true c hdc hc
      simp only [valB, cond_true] at hDc
      rw [hcv] at hDc
      have hDy : DiagAt a' _ μ y := DiagAt.arg_inv hDc hyz (fun h => hyb h.2)
      have hlev : holeLev y = μ := DiagAt.holeLev_eq hDy
      refine lo_keep_Q hDc hyz hyb ?_ h1s hl
      intro hl' a hla hns hOa hca
      have := hTPL c (by omega) s y hcv hl' a hla hns hOa hca
      rw [hlev] at this; exact this
    · have hlt1 : seed < psi μ one z := by
        rcases lt_trichotomy' seed (psi μ one z) with h | h | h
        · exact h
        · exact absurd (le_of_eq h.symm) h1s
        · exact absurd (le_of_lt h) h1s
      exact hLs0 hlt1 c hc hdc hd0 s y hcv hyb hl
  exact qr_final2 hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD
    hAD hTP hTPL hAU' hAD' hsM hpM hYB hS hsp0 hLs

end Ytosk
