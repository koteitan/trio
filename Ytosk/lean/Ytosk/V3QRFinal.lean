/-
**3 行・t = 1・q = r（n ≥ 2）: 組み立て。**

`qr_main`（列ごとの添字での帰納法）に、構造の補題（t1 と共通: `hOS_t1`・`dv_shape`・`hS3_t1`・`hxnb_t1`・
`hiu_t1`・`hiux_t1`・`hnd_t1`・`root_t1`・`dep_anc_x`）、局所条件（`qr_oloc`・`qr_vloc`）、M[1] の評価
（`drop1`、`base_v_read`）を入れる（`qr_final`）。
残る仮定:
- 値の不変条件: BumpKidsDec・BumpTermDec・AbsD（t1 と共通）、TP1W・TPLoW・AbsUW・AbsDW（η = 1 版）。
- y = b_r の書き換えの枠で B < b + ζ（鎖のすべての項、hYB）。
- 始点 seed = o_{M[1]}(r) の条件: SeedOK（hS）、spArg(μ, b, seed) = b + seed（hsp0）、引き上げのない列の
  (L)(ii)（hLs）。
-/
import Ytosk.V3QRLocV

namespace Ytosk

open T

/-- **`t = 1`, `q = r`, all `n ≥ 2`.** -/
theorem qr_final {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
    (hTP : TP1W M ρ) (hTPL : TPLoW M ρ) (hAU' : AbsUW M ρ) (hAD' : AbsDW M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- `A = o(r) = ψ_μ(b + Ω_{μ+1})`
    {b : T} (hro : ρ.o r = psi (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) z)
    (hb : AllGeT (psi (succ (ρ.v r)) z z) b)
    (hpre : preState M ρ r ((children M r).filter (fun d => decide (d < r + L))) = b)
    -- the frames with the child `ψ_s(b_r)`
    (hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s, ρ.o c = psi s (app b (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app b (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app b (psi (succ (ρ.v r)) z z)) z) = true →
      ∀ m', lt (preState M ρ i L')
        (app b (gamS (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) ((drop1 M (r + L) rkM).o r) m')) = true)
    -- the seed `o_{M[1]}(r)`
    (hS : ∀ a', ¬ lt (ρ.v r) a' = true →
      isOT (psi a' (app b (psi (succ (ρ.v r)) z z)) z) = true →
      SeedOK a' (app b (psi (succ (ρ.v r)) z z)) (ρ.v r) ((drop1 M (r + L) rkM).o r))
    (hsp0 : spArg (ρ.v r) b ((drop1 M (r + L) rkM).o r) = app b ((drop1 M (r + L) rkM).o r))
    (hADs0 : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z → ∀ i, i < r + L →
      DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ (ρ.v r) b) (lbQ M ρ (ρ.v r) b) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ((drop1 M (r + L) rkM).o r))
    (hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) b) (lbQ M ρ (ρ.v r) b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hpath := hpath_of_par1 h1 hA (by omega)
  set μ := ρ.v r with hμ
  set seed := (drop1 M (r + L) rkM).o r with hseed
  have hox : ρ.o (r + L) = psi (succ μ) z z :=
    o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  have hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hv => dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  have hS3 := hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1
  have hBk : ∀ i j k, i < r + L → DepX M (r + L) false i → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → DepX M (r + L) true k → k < r + L := by
    intro i j k hi hv hj hjb hk hdk
    have hir : i ≤ r := by
      by_contra h
      exact hdep.2.2 false i (by omega) hi hv
    have := hS3 i j k hir hj hjb hk hdk
    omega
  have hxv : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact hdep.2.1 hdm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  -- the base `M[1] = M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hseedS : ∃ a X, seed = psi a X z := by
    obtain ⟨σ, hσ⟩ := o_psi_sub hC1 hrT
    exact ⟨_, σ, hσ⟩
  -- the lifts
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  obtain ⟨hxcb, hxcu⟩ := qr_x_counted hx h1 hx2 hq
  have hdr : dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) r = 0 := by
    rw [dOf_ochild hx hxv hOS hVS hxr hxcb hxcu DepX.leaf, dOf_x hx hxv hOS hVS]
    unfold loQ
    rw [if_neg]
    rintro ⟨h, _⟩
    rw [hox] at h
    exact absurd (T.psi.inj h).2.1.symm (fun he => absurd (app_eq_z he).2 (by simp))
  -- the root
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 (r + L)
  have hRd := dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hRA
  have hRx : Rt < r + L := by
    rcases Nat.lt_or_ge Rt (r + L) with h | h
    · exact h
    · exfalso
      have : Rt = r + L := by have := hRA.le; omega
      rw [this] at hRt0
      have h2 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hRt0
      have he : entry M 1 (r + L) = 0 := by
        unfold entry; unfold col at h2; simpa using h2
      have := par1_entry_lt h1; omega
  have hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hRt : ∀ m, Single (fsD (ρ.o Rt) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ
        (app b (psi (succ μ) z z)) seed m Rt)) ∧
      fsD (ρ.o Rt) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m Rt)
        < ρ.o Rt := by
    intro m
    obtain ⟨hHR, _⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS
      true Rt hRd hRx
    simp only [valB, cond_true] at hHR
    have hRM' : Rt < M.length := by omega
    have hok := hok_of_holeT hrot cof_br (lt_irrefl' μ) hS (hG.ot_o Rt hRM') hHR
      (m + dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) Rt)
    have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
    have hgS : ∀ k, ∃ a X, gamS μ (app b (psi (succ μ) z z)) seed k = psi a X z := by
      intro k; cases k with
      | zero => exact hseedS
      | succ k => exact ⟨μ, _, rfl⟩
    refine ⟨?_, hok.2⟩
    exact single_fsD (o_psi_form hC hRM') (holeT_not_succ hHR)
      (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHR)) (hgS _) hok.1
  intro n hn
  obtain ⟨ρN, rkN, hCN, hRN, _, _, hot, hlt⟩ :=
    qr_main hlen hL hA hd0e hpath hx2 (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1) (hZ2 r)
      (fun n hn => hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
      (fun n hn => hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
      (hnd_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2) hC hG hRM
      (fun h => absurd (app_eq_z h).2 (by simp)) cof_br hro hdep.1 (fun ζ => by
        rw [hox]; exact fsD_leaf (isSucc_succ μ) (succ_ne_z μ))
      hRA hRt0 hRlast hRd hsM hpM hxv hOS hVS hdr
      (fun m => qr_oloc hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro rfl hb hpre hox
        hOS hVS hBk hxv hS hseedS hsp0 hTP hTPL hYB hLs m)
      (fun m => qr_vloc hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS hb hVS
        hBk hxv hseedS hTPL hLs hS hAU' hAD' hADs0 m)
      hRt (ρ1 := drop1 M (r + L) rkM) (rk1 := rkM) (by rw [gexp_one_eq hlen]; exact hC1)
      (by rw [gexp_one_eq hlen]; exact hRk1) rfl
      (fun g hg a ha h => by
        rw [gexp_one_eq hlen] at h
        exact base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg ha h)
      n hn
  exact ⟨ρN, rkN, hCN, hRN, hot, hlt⟩

end Ytosk
