/-
**3 行・t = 1・q = r（n ≥ 2）: 始点の条件を落とす補題から出した形。**

落とす補題（`drop_all`、仮定は t1 の `t1_main_final` と同じ）から:
- seed = o_{M[1]}(r) < A（D の狭義の降下 `dep_strict0`）、seed ◁ A（PO の 2 つ目の場合は A = Ω_w の形なので起きない）。
- spArg(μ, b, seed) = b + seed（`spArg_seed`）。
- SeedOK: seed の添字が μ なら `seedOK_of_lhd_top`、μ より小さいなら ◁ と段 a′ の成分の条件 hcs（comps_a の形）から `seedOK_of_lhd_below`。
  （2026-10-02: 以前の hcs「始点の成分はすべて始点より小さい」は標準形で偽。弱めた。）
- 始点の (L)(ii): 仮定 hLs0（V3QRFinal4 で TPLoN から）。
- y = b_r の書き換えの枠の (W)（B < b + ζ）: 鎖の 2 項目以降は TP1（t1 の不変条件、η = ψ_μ(1)）から。
残る仮定（q = r に固有、どれも始点が ψ_μ(1) より小さい場合（b = 0）か添字が μ より小さい場合だけ）:
hYBs（始点で B < b + seed）、hcs（始点の成分は始点より小さい）、hLs0（始点での (L)(ii)）、
hADs0（添字 0 ののりしろの枠の吸収を始点で）。
-/
import Ytosk.V3QRSeed
import Ytosk.V3SeedLhd
import Ytosk.V3MainT1F
import Ytosk.V3DropPres
import Ytosk.V3TrigSeed
import Ytosk.V3QRWeak

namespace Ytosk

open T

/-- The `upg` field of `AbsSR` in the shape of the `q = r` engine (`L = 1`, `x − 1 = r`). -/
theorem AbsSR.upgX {M : Mat} {ρ : Valn} (h : AbsSR M ρ) {r L : Nat} (hlen : r + L + 1 = M.length)
    (h1 : par M 1 (r + L) = some r) (hq : par M 0 (r + L) = some r) : L = 1 → UpgAbsX M (r + L) ρ := by
  intro hL1 i k W hi hu hv hW
  have e : M.length - 1 = r + L := by omega
  exact h.upg r (by rw [e]; exact h1) (by rw [e]; exact hq) (by omega) i k W (by omega) hu hv hW

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
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM)) (hUA : UpgAbsXW M (r + L) ρ)
    -- value invariants
    (hTP : TP1WC M ρ) (hTPL : TPLoW M ρ) (hAU' : AbsUWL M ρ) (hAD' : AbsDW M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- `q = r`
    (hTP1 : TP1C M ρ)
    (hYBs : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
        (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 → ∀ s,
      ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r)) = true)
    (hcs : lt (sf ((drop1 M (r + L) rkM).v r)) (ρ.v r) = true →
      ∀ a', ¬ lt (ρ.v r) a' = true →
      isOT (psi a' (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      ∀ g ∈ comps a' ((drop1 M (r + L) rkM).o r),
        g < app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r))
    (hADs0 : ∀ i, i < r + L →
      DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ((drop1 M (r + L) rkM).o r))
    (hAUs0 : ∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) i = 0 →
      OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) →
        q < fsD (last (ρ.v k)) ((drop1 M (r + L) rkM).o r))
    (hLs0 : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1 Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
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
  -- the seed: `◁ o(r)`, or (only at `r = x − 1`, which lost its upgrade) `Ω_{w′}` with `SmallSelf w′`
  have hold : (LhdE seed (ρ.o r) ∨ (WkOA seed (ρ.o r) ∧ ∃ w, ρ.o r = psi w z z)) → Lhd z seed (ρ.o r) := by
    intro h
    rcases h with hl | ⟨_, w, hw⟩
    · rcases hl with he | hl
      · exact absurd (he ▸ hlt) (lt_irrefl' _)
      · exact hl
    · rw [hro] at hw
      exact absurd (T.psi.inj hw).2.1 (fun he => absurd (app_eq_z he).2 (by simp))
  have hseedC : Lhd z seed (ρ.o r) ∨ ∃ w', seed = psi w' z z ∧ w' < μ ∧ SmallSelf w' := by
    rcases hPO with hl | ⟨hW, hw | hnl⟩
    · exact Or.inl (hold (Or.inl hl))
    · exact Or.inl (hold (Or.inr ⟨hW, hw⟩))
    rcases (hdrop r hr).2.1 with hl | ⟨hWV, _, hn | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩⟩
    · exact absurd hl hnl
    · exact Or.inl (hold (Or.inr ⟨hW, _, o_of_no_counted hC hrM (hG.ot_v r hrM) hn⟩))
    rcases hUA r k W (by omega) hu hvk hWz with h | ⟨_, hSm, _, _⟩
    · exact absurd h hbad
    have h12 := upg_e12 hu
    have h2r : entry M 2 r = 0 := by have := hZ2 r; omega
    have hvr := v_last_take (x := r + L) (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1
      (r := r) (by omega) h12.1 h2r
    have hVot : isOT (add (vOpt ρ (par M 1 r)) one) = true := isOT_add (vOpt_ot hG hrM) isOT_one
    rw [sf_ot hVot] at hvr
    obtain ⟨w', w, X, hs, _, _⟩ := hW
    obtain ⟨σ0, hs0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hs0
    simp only [psi.injEq] at hs0
    have hw' : w' = (drop1 M (r + L) rkM).v r := by rw [hs0.1, sf_ot (hdrop r hr).2.2]
    rw [hw'] at hs
    refine Or.inr ⟨_, hs, hWV.1, ?_⟩
    rw [hvr]; exact hSm
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
    rcases hseedC with hlhd | ⟨w', hw', hwμ, hsm⟩
    · rw [hs1']
      have hsub := hlt'
      rw [psi_lt_psi_z_iff] at hsub
      rcases hsub with hsμ | ⟨hsμ, hσb⟩
      · -- the subscript is below `μ`
        apply seedOK_of_lhd_below ha' hsot hsμ
        · rw [← hro, ← hs1']; exact hlhd
        · have h := hcs hsμ a' ha' hot'
          rw [hs1'] at h; exact h
      · -- the subscript is `μ`
        rw [hsμ] at hsot ⊢
        have hl' : Lhd z (psi μ σ1 z) (psi μ (app b (psi (succ μ) z z)) z) := by
          rw [← hro]; rw [hs1', hsμ] at hlhd; exact hlhd
        exact seedOK_of_lhd_top hot' cof_br ha' hsot hσb hl'
    · -- the weak seed `Ω_{w′}`
      have hs1w : s1 = w' := by
        have h := hs1'.symm.trans hw'
        simp only [psi.injEq] at h; exact h.1
      have hsμ : lt s1 (ρ.v r) = true := by rw [hs1w]; exact hwμ
      have hca := hcs hsμ a' ha' hot'
      rw [hw'] at hca ⊢
      have hsotw : isOT (psi w' z z) = true := by rw [← hw']; exact hsing.1
      exact seedOK_of_small_below hb hsotw hwμ hsm hca
  -- the (L)(ii) at the seed
  have hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
      (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z := by
    exact hLs0
  -- The seed bound is used only when the child's lift count is zero.
  have hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c → ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
      lt (preState M ρ i L') (app b (psi (succ μ) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
      ∀ m', lt (preState M ρ i L') (app b (gamS μ (app b (psi (succ μ) z z)) seed
        (m' + dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c))) = true := by
    intro i L' c R hi hd hch hcnt hdc s hcv htr1 htr2 m'
    have h0 := hTP1 i L' c R hch hcnt s _ hcv htr1 htr2 (ohole_of_cof_big cof_br)
    rw [holeLev_cof cof_br, fsD_eq_fs cof_br, fs_br] at h0
    set d := dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c
    by_cases h1s : psi μ one z ≤ gamS μ (app b (psi (succ μ) z z)) seed (m' + d)
    · refine lt_of_lt_of_le (show preState M ρ i L' < app b (psi μ one z) from h0) ?_
      rcases (le_iff _ _).mp h1s with h | h
      · exact le_of_lt (app_lt_app_left b h)
      · rw [h]
    · have hz : m' + d = 0 := by
        by_contra hn
        obtain ⟨k, hk⟩ : ∃ k, m' + d = k + 1 := ⟨m' + d - 1, by omega⟩
        rw [hk] at h1s
        exact h1s (gamS_ge_psi1 hseedz k)
      have hd0 : d = 0 := by omega
      rw [hz]
      have hlt1 : seed < psi μ one z := by
        rcases lt_trichotomy' seed (psi μ one z) with h | h | h
        · exact h
        · exact (h1s (by rw [hz]; change psi μ one z ≤ seed; rw [h])).elim
        · exact (h1s (by rw [hz]; exact le_of_lt h)).elim
      exact hYBs hlt1 i L' c R hi hd hch hcnt hdc hd0 s hcv htr1 htr2
  exact qr_final2 hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD
    hTP hTPL hAU' hAD' hsM hpM hYB hS hsp0 hADs0 hAUs0 hLs
    (good3_take (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop) Pn hP1 hPs

end Ytosk
