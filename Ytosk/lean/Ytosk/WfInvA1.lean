/-
**WfInvA1 (2026-10-31): AbsDN at the seed of the last-column frame (`AbsDN0`).**

`AbsDN` (V3QRFinal4, all columns, index 1) is false on a standard 38-column matrix (WfReM4.not_absDN, i = 31).
The only live consumer of `AbsDN` is `qr_final4_seedG` (`hADs0`, through `qr_final4SG`・`qr_final4S`,
`Inv3V2.adn` in `badOutT1`・`expT1Out_V2`); it uses `AbsDN` only in the frame of the last column
(`t = 1`, `q = r`), at a `v` call `i` of `D` with `dOf i = 0`, at the seed `o_{M.take x}(r)`.
`AbsDN0` is exactly that use. Every other live use is transport (`TakeFrameV2.adn`, `base_adn`).

- `AbsDN0`, `absDN0_of_absDN` (`AbsDN0` is weaker).
- `qr_final4_seedG0`・`qr_final4SG0`・`qr_final4S0`: the engines with `AbsDN0` in place of `AbsDN`
  (copies; only the `hADs0` step differs).
-/
import Ytosk.V3Inv2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`AbsDN` at the seed in the last-column frame** (`t = 1`, `q = r`, `o(r) = ψ_μ(b + Ω_{μ+1})`): at a `v` call
`i` of `D` with no lift (`dOf i = 0`), rows 1, 2 nonzero, the bump term `W` an ω-hole that is not its own node,
the summands of `v(P_1 i)` below `W` stay below `W[o_{M.take x}(r)]`. -/
def AbsDN0 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
    one ≤ (drop1 M (M.length - 1) rk).o r →
    ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
    OHole (bumpW M ρ i) → cof (bumpW M ρ i) = .omega → NotNode (bumpW M ρ i) →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
      q < fsD (bumpW M ρ i) ((drop1 M (M.length - 1) rk).o r)

/-- `AbsDN` gives `AbsDN0` (`fsD` is monotone in the index). -/
theorem absDN0_of_absDN {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : AbsDN M ρ) : AbsDN0 M ρ rk := by
  intro r μ b _ _ _ _ hs i hi _ h1 h2 _ hO hc hN q hq hlt
  exact lt_of_lt_of_le (h i (by omega) h1 h2 hO hc hN q hq hlt) (fsD_mono_eta hO hs)

theorem qr_final4_seedG0 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    -- the conclusion of the drop lemma and the seed condition
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV M ρ (drop1 M (r + L) rkM) i)
    (hseedC : Lhd z ((drop1 M (r + L) rkM).o r) (ρ.o r) ∨
      ∃ w', (drop1 M (r + L) rkM).o r = psi w' z z ∧ w' < ρ.v r ∧ SmallSelf w')
    -- value invariants
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hYBs : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
        (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s, ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r)) = true) (hTPN : TPLoN M ρ) (hADN0 : AbsDN0 M ρ rkM)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the seed
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1 Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  set μ := ρ.v r with hμ
  set b := qrB M ρ r (r + L) with hbdef
  set seed := (drop1 M (r + L) rkM).o r with hseed
  obtain ⟨b0, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbb : b0 = b := hbe
  rw [hbb] at hro hb
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  have hVS' : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hv => dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
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
  have hox : ρ.o (r + L) = psi (succ μ) z z :=
    o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  -- the base
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hseedz : seed ≠ z := by
    obtain ⟨σ1, hs1⟩ := o_psi_sub hC1 hrT
    show (drop1 M (r + L) rkM).o r ≠ z
    rw [hs1]; simp
  have h1s : one ≤ seed := one_le_of_ne_z hseedz
  -- the DiagAt and the `A`-freeness of lift-free columns
  have hdiag : ∀ bb c, c < r + L → DepX M (r + L) bb c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      DiagAt μ (app b (psi (succ μ) z z)) μ (valB ρ bb c) ∧
      (bb = true → (∀ s y, ρ.o c = psi s y z → ∀ a, last y = psi a z z →
          a ≠ psi μ (app b (psi (succ μ) z z)) z)) ∧
      (bb = false → last (ρ.v c) ≠ psi μ (app b (psi (succ μ) z z)) z) := by
    intro bb c hc hdc hd0
    obtain ⟨d, hd⟩ := depL_of_depX (lo := loQ M ρ μ b) (lb := lbQ M ρ μ b) hdc
    have hdd : d = 0 := by
      cases bb with
      | true => rw [← dOf_o hx hxv hOS hVS' (by omega) hd]; exact hd0
      | false => rw [← dOf_v hx hxv hOS hVS' (by omega) hd]; exact hd0
    have hNA := qr_lastNA hx hC hG hKD hTD hq hro hOS hVS' hBk hb hd hc hdd
    refine ⟨qr_diag0 hx hC hG hKD hTD hq hro hOS hVS' hBk hd hc hdd, fun h => (hNA.1 h).1, hNA.2⟩
  -- hLs0
  have hLs0 : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
      (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z := by
    intro c hc hdc hd0 s y hcv hyb hl
    by_cases hyz : y = z
    · subst hyz; simp [fsD, split]
    obtain ⟨hD, hNA, _⟩ := hdiag true c hc hdc hd0
    simp only [valB, cond_true] at hD
    rw [hcv] at hD
    refine lo_keep_Q hD hyz hyb ?_ (le_refl _) hl
    intro hl' a hla hns hOa hca
    have hDy : DiagAt μ _ μ y := DiagAt.arg_inv hD hyz (fun h => hyb h.2)
    have hDl := hDy.last_g
    rw [hla] at hDl
    have hDa : DiagAt μ (app b (psi (succ μ) z z)) μ a := by
      generalize hBB : app b (psi (succ μ) z z) = BB at hDl ⊢
      cases hDl with
      | here hb' _ _ => exact absurd rfl hb'
      | arg hb' _ _ => exact absurd rfl hb'
      | sub _ _ h => exact h
    have hxl : M.length - 1 = r + L := by omega
    have hTPN' := hTPN (drop1 M (r + L) rkM) rkM (by rw [hxl]; exact hC1) (by rw [hxl]; exact hRk1)
    exact hTPN' r μ b (by rw [hxl]; exact h1) (by rw [hxl]; exact hq) (by rw [hxl]; exact hx2) hro c
      (by rw [hxl]; exact hc) (by rw [hxl]; exact hdc) (by rw [hxl]; exact hd0) s y hcv hyb hl' a hla hns hOa hca
      (notNode_of_diag hDa (hNA rfl s y hcv a hla))
  have hq0 : par M 0 (r + L) = some r := hq
  -- hADs0
  have hADs0 : ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) seed := by
    intro i hi hv h2 hd0 q hq hlt
    have hiM : i < M.length := by omega
    obtain ⟨h1', _, hcase⟩ := hVS' i hi hv
    rcases hcase with ⟨h2', _⟩ | ⟨_, L', K, j, k, hch, hjb, hchj, hdk, _, _⟩
    · exact absurd h2' h2
    have hj : j ∈ children M i := by rw [hch]; simp
    have hkj : k ∈ children M j := by rw [hchj]; simp
    have hkx : k < r + L := hBk i j k hi hv hj hjb hkj hdk
    have hdb := dOf_bump hx hxv hOS hVS' (lo := loQ M ρ μ b) (lb := lbQ M ρ μ b) hi h1' h2 hj hjb hkj hdk
    have hdk0 : dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) k = 0 := by omega
    obtain ⟨hDk, _, _⟩ := hdiag true k hkx hdk hdk0
    simp only [valB, cond_true] at hDk
    obtain ⟨_, _, hNAi⟩ := hdiag false i hi hv hd0
    have hNA := hNAi rfl
    have hBD : BumpData M ρ μ i L' K j k := bump_data hC hG hKD hTD h1' h2 hch hjb hchj
    set P := nzs (L'.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hDG : DiagAt μ (app b (psi (succ μ) z z)) μ G := by
      rw [hGe]; exact DiagAt.append _ (single_ne_z hkS) hDk
    have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
    have hDW : DiagAt μ (app b (psi (succ μ) z z)) μ (bumpW M ρ i) := by
      rw [hBD.W]
      exact diag_omega hBD.potW (DiagAt.append _ hωGz (diag_omega hGot hDG))
    -- `W` is the last summand of `v(i)`
    have hvi := v_bump_valueG hC hiM h1' h2 hch hjb hchj hBD.sK hBD.pK hBD.sL hBD.pp hBD.gt
      (vOpt_ot hG (by omega))
    have hsW := single_omega hBD.potW
    have hWz : omega (app (sumN P) (omega G)) ≠ z := single_ne_z hsW
    obtain ⟨_, s0, y0, hW0⟩ := hsW
    obtain ⟨B, X, _, _, hadd⟩ := add_prefix s0 y0 (vOpt ρ (par M 1 i))
    have hlast : last (ρ.v i) = bumpW M ρ i := by
      rw [hvi, hW0, hadd, last_app B (by simp), hBD.W, hW0]; rfl
    have hWne : bumpW M ρ i ≠ psi μ (app b (psi (succ μ) z z)) z := by rw [← hlast]; exact hNA
    have h := hADN0
    unfold AbsDN0 at h
    rw [show M.length - 1 = r + L by omega] at h
    exact h r μ b h1 hq0 hx2 hro h1s i hi hv h1' h2 hd0 (ohole_of_diag hDW) (DiagAt.cof_omega hDW)
      (notNode_of_diag hDW hWne) q hq hlt
  have hAUL : AbsUWL M ρ := hAU'
  have hAUs0 : ∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
      OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) seed :=
    fun i k hi hv hu hd hO hc qq hqq hlt => by
      have h := hAU0
      unfold AbsUW0 at h
      rw [show M.length - 1 = r + L by omega] at h
      exact h r μ b h1 hq hx2 hro i k hi hv hu hd hO hc qq hqq hlt
  exact qr_final3G hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM
    hKD hTD hdrop hseedC hTP hTPL hAUL hAD' hsM hpM hTP1 hYBs hADs0 hAUs0 hLs0 Pn hP1 hPs

theorem qr_final4SG0 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    -- the conclusion of the drop lemma and the seed condition
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV M ρ (drop1 M (r + L) rkM) i)
    (hseedC : Lhd z ((drop1 M (r + L) rkM).o r) (ρ.o r) ∨
      ∃ w', (drop1 M (r + L) rkM).o r = psi w' z z ∧ w' < ρ.v r ∧ SmallSelf w')
    -- value invariants
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hTS : TrigS0 M ρ rkM) (hTPN : TPLoN M ρ) (hADN0 : AbsDN0 M ρ rkM)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the seed
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1 Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hlast : M.length - 1 = r + L := by omega
  have hro : ρ.o r = psi (ρ.v r)
      (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z := by
    obtain ⟨b0, hro, hbe, _⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
    have hbb : b0 = qrB M ρ r (r + L) := hbe
    rw [hbb] at hro
    exact hro
  have hYBs : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
        (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s, ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r)) = true := by
    have h := hTS r (ρ.v r) (qrB M ρ r (r + L))
      (by simpa only [hlast] using h1) (by simpa only [hlast] using hq)
      (by simpa only [hlast] using hx2) hro
    simpa only [hlast] using h
  exact qr_final4_seedG0 hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00
    h1 hx2 hq hC hG hRM hKD hTD hdrop hseedC
    hTP hTPL hAU' hAU0 hAD' hTP1 hYBs hTPN hADN0 hsM hpM Pn hP1 hPs

theorem qr_final4S0 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
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
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hTS : TrigS0 M ρ rkM) (hTPN : TPLoN M ρ) (hADN0 : AbsDN0 M ρ rkM)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the seed
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1 Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  obtain ⟨hdrop, hseedC⟩ := qr_dropSeed hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq hC hG hRM hVS hF hFO hArgT
    hKD hTD hAbs hWS hVSt hUA
  exact qr_final4SG0 hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD hdrop hseedC hTP hTPL hAU' hAU0 hAD' hTP1 hTS hTPN hADN0 hsM hpM Pn hP1 hPs


/-- **`Inv3V2` with `AbsDN0` in place of the false `AbsDN`.** -/
structure Inv3V2A (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  ph : PH3cG M ρ
  fc3 : FC3 M ρ
  vra : VSmallRAll M ρ
  ads : AbsDS M ρ rk
  aus : AbsUS M ρ rk
  tp1 : TP1C M ρ
  tplos : TPLoS M ρ rk
  tp1w : TP1WC M ρ
  tplow : TPLoWs M ρ rk
  auwl : AbsUWL M ρ
  auw0 : AbsUW0 M ρ rk
  adw : AbsDWs M ρ rk
  trigs : TrigS0 M ρ rk
  tplon : TPLoN M ρ
  adn0 : AbsDN0 M ρ rk
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- `Inv3V2` gives `Inv3V2A`. -/
theorem Inv3V2.toA {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3V2 M ρ rk) : Inv3V2A M ρ rk :=
  ⟨I.cons, I.good, I.rank, I.vs, I.fc, I.fo, I.kd, I.td, I.ph, I.fc3, I.vra, I.ads, I.aus, I.tp1, I.tplos,
    I.tp1w, I.tplow, I.auwl, I.auw0, I.adw, I.trigs, I.tplon, absDN0_of_absDN I.adn, I.rootS, I.rootP⟩

theorem Inv3V2A.tplowAt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (I : Inv3V2A M ρ rk)
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) :
    TPLoWAt M ρ (fun _ => (drop1 M (r + L) rk).o r) := by
  have h := I.tplow.const (r := r) (by rw [show M.length - 1 = r + L by omega]; exact h1)
  rwa [show M.length - 1 = r + L by omega] at h

theorem Inv3V2A.adwAt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (I : Inv3V2A M ρ rk)
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) :
    AbsDWAt M ρ (fun _ => (drop1 M (r + L) rk).o r) := by
  have h := I.adw.const (r := r) (by rw [show M.length - 1 = r + L by omega]; exact h1)
  rwa [show M.length - 1 = r + L by omega] at h

/-- **The `t = 1`, `q = r` engine with `Inv3V2A`** (as `qr_final_inv3V2`; the field `adn0` is the only change). -/
theorem qr_final_inv3V2A {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2A M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) (hNB : ¬ Bad2 M)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2A (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hPs : ExpStepT1 (fun N σ => ∃ rkN, Inv3V2A N σ rkN) M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2A (TRIO.gexp M r L d0 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  intro n hn
  obtain ⟨ρN, _, _, _, _, ⟨rkN, IN⟩, hot, hlt⟩ :=
    qr_final4S0 hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hq I.cons I.good I.rank I.vs I.fc I.fo R.argT I.kd I.td R.ab R.ws R.vst R.ua
      I.tp1w (I.tplowAt hlen h1) I.auwl I.auw0 (I.adwAt hlen h1) I.tp1 I.trigs I.tplon I.adn0 I.rootS I.rootP
      (fun N σ => ∃ rkN, Inv3V2A N σ rkN) ⟨rk, I1⟩ hPs n hn
  exact ⟨ρN, rkN, IN, hot, hlt⟩

end Ytosk
