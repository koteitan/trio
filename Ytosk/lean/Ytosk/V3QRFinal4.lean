/-
**3 行・t = 1・q = r（n ≥ 2）: 始点が小さい場合の仮定を値の不変条件から。**

値の不変条件（大域）:
- **TrigOm**: 子の値が ψ_s(Ω_{ν+1}) で書き換えが起きる枠では、前の状態 B は 0。
- **TPLoN**: TPLo の η = 1 版（最後の項 Ω_a の a が自分自身の対角化の点でないとき）。
- **AbsDN**: AbsD の η = 1 版（のりしろの項 W が自分自身の対角化の点でないとき）。
`qr_final3` の仮定のうち:
- hYBs: 始点 < ψ_μ(1) なら r + 1 = x（`qr_seed_big`）で b = 0、b_r = Ω_{μ+1}。TrigOm で B = 0。
- hLs0: 引き上げのない列は A の対角化の点の下（`qr_diag0`）で、a ≠ A（`qr_lastNA`）。よって a は自分自身の
  点でなく、TPLoN と 1 ≤ seed から。
- hADs0: 同じく W ≠ A（`qr_lastNA` の v の最後の項）で W は自分自身の点でなく、AbsDN と 1 ≤ seed から。
残る q = r に固有の仮定は hcs（添字が μ より小さい始点の成分は始点より小さい）だけ。
-/
import Ytosk.V3QRSmall

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `t` is not itself a diagonal node `ψ_a(b)` with `cof b = Ω_{μ+1}`. -/
def NotNode (t : T) : Prop := ∀ a b, t = psi a b z → ∀ μ, cof b ≠ .big μ

/-- **Value invariant TrigOm.** -/
def TrigOm (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → ∀ s ν, ρ.o c = psi s (psi (succ ν) z z) z →
    lt (preState M ρ i L) (psi (succ ν) z z) = true →
    lt (psi (ρ.v i) z z) (psi s (psi (succ ν) z z) z) = true → preState M ρ i L = z

/-- **Value invariant TPLoN** (`η = 1`, the subscript is not its own node). -/
def TPLoN (M : Mat) (ρ : Valn) : Prop :=
  ∀ c, c < M.length → ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega → NotNode a →
    ¬ psi (fsD a one) z z < psi (succ s) z z

/-- **Value invariant AbsDN** (`η = 1`, the bump term is not its own node). -/
def AbsDN (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
    cof (bumpW M ρ i) = .omega → NotNode (bumpW M ρ i) →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) one

/-- Under the diagonal point of `A`, a term other than `A` is not itself a node. -/
theorem notNode_of_diag {μ br t : T} (hD : DiagAt μ br μ t) (hne : t ≠ psi μ br z) : NotNode t := by
  intro a b ht μ' hcb
  subst ht
  cases hD with
  | here _ _ _ => exact hne rfl
  | arg _ _ hDb => rw [DiagAt.cof_omega hDb] at hcb; cases hcb
  | sub _ _ _ => simp [cof] at hcb

/-- **`t = 1`, `q = r`, all `n ≥ 2`**, with only `hcs` left among the seed conditions. -/
theorem qr_final4 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
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
    (hTP1 : TP1 M ρ) (hTO : TrigOm M ρ) (hTPN : TPLoN M ρ) (hADN : AbsDN M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the seed
    (hcs : lt (sf ((drop1 M (r + L) rkM).v r)) (ρ.v r) = true →
      ∀ u g, g ∈ comps u ((drop1 M (r + L) rkM).o r) → g < (drop1 M (r + L) rkM).o r) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
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
  -- a small seed means `r + 1 = x`, so `b = 0`
  have hsmall : seed < psi μ one z → r + 1 = r + L := by
    intro hlt1
    by_contra hne
    have := qr_seed_big hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hC1 hRk1 (by omega)
    exact absurd (lt_of_lt_of_le hlt1 this) (lt_irrefl' _)
  have hb0 : r + 1 = r + L → b = z := by
    intro hrL
    rw [hbdef]
    unfold qrB
    have : (children M r).filter (fun d => decide (d < r + L)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      have := (mem_children hc).1
      simp; omega
    rw [this]; rfl
  -- hYBs
  have hYBs : seed < psi μ one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
      lt (preState M ρ i L') (app b (psi (succ μ) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
      lt (preState M ρ i L') (app b seed) = true := by
    intro hlt1 i L' c R _ _ hch _ s hcv htr1 htr2
    have hbz := hb0 (hsmall hlt1)
    rw [hbz] at hcv htr1 htr2 ⊢
    have h0 := hTO i L' c R hch s μ hcv htr1 htr2
    rw [h0]
    show z < app z seed
    cases hs : seed with
    | z => exact absurd hs hseedz
    | psi a c d => exact T.z_lt_psi a c d
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
  have hLs0 : seed < psi μ one z → ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
      (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z := by
    intro _ c hc hdc hd0 s y hcv hyb hl
    by_cases hyz : y = z
    · subst hyz; simp [fsD, split]
    obtain ⟨hD, hNA, _⟩ := hdiag true c hc hdc hd0
    simp only [valB, cond_true] at hD
    rw [hcv] at hD
    refine lo_keep_Q hD hyz hyb ?_ h1s hl
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
    exact hTPN c (by omega) s y hcv hl' a hla hns hOa hca
      (notNode_of_diag hDa (hNA rfl s y hcv a hla))
  -- hADs0
  have hADs0 : seed < psi μ one z → ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) seed := by
    intro _ i hi hv h2 hd0 q hq hlt
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
    have h0 := hADN i hiM h1' h2 (ohole_of_diag hDW) (DiagAt.cof_omega hDW)
      (notNode_of_diag hDW hWne) q hq hlt
    exact lt_of_lt_of_le h0 (fsD_mono_eta (ohole_of_diag hDW) h1s)
  exact qr_final3 hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hVS hF hFO
    hArgT hKD hTD hAbs hWS hVSt hUA hAD hTP hTPL hAU' hAD' hsM hpM hTP1 hYBs hcs hADs0 hLs0

end Ytosk
