/-
**WfSdH2: `qr_oloc` and `qr_vloc` without `SeedOK` at every diagonal point (2026-11-01).**

Copies of `V3QRLocOA.qr_oloc` and `V3QRLocV.qr_vloc` with the section hypothesis
`hS : ∀ a′ ≤ μ, SeedOK a′ b_r μ seed` (false at `a′ = 0` for a weak seed) replaced by `hSr : SeedOK μ b_r μ seed` and
`hok0 : HokQ μ b_r μ seed` (the descent of `fsD` asked at index `0` only on terms whose diagonal points are all `μ`).
The index-0 condition is supplied at each use:
- a `D` column value at lift count `0`: `qr_only_mu_col` (`qr_diag0` and `DiagAt.unique`);
- the last summand of `v(i + 1)` (upgrade frame): `DiagAt.last_g` of `qr_diag_col`, then `diag_only_mu`;
- the bump frame `G = Σ K + o(k)` and `P + ω^G`: `μ` is a diagonal point of both (`DiagAt.append`, `diag_omega`), and
  `omega_fsD_hole_QW` asks the descent only on subterms whose diagonal points are those of `G` / `P + ω^G`.
-/
import Ytosk.WfSdH1

namespace Ytosk

open T

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b seed : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) (h1 : par M 1 x = some r) (hq : par M 0 x = some r)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z) (hvr : ρ.v r = μ)
  (hb : AllGeT (psi (succ μ) z z) b)
  (hpre : preState M ρ r ((children M r).filter (fun d => decide (d < x))) = b)
  (hox : ρ.o x = psi (succ μ) z z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hxv : ¬ DepX M x false x)
  (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
  (hok0 : HokQ μ (app b (psi (succ μ) z z)) μ seed)
  (hseedS : ∃ a X, seed = psi a X z)
  (hsp0 : spArg μ b seed = app b seed)
  (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => seed))
  (hYB : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → Counted M i c →
    DepX M x true c →
    ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
    lt (preState M ρ i L) (app b (psi (succ μ) z z)) = true →
    lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
    ∀ m', lt (preState M ρ i L) (app b (gamS μ (app b (psi (succ μ) z z)) seed (m' + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c))) = true)
  (hLs : ∀ c, c < x → DepX M x true c → dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
    ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
    (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hvr hb hpre hox hOS hVS hBk hxv
  hSr hok0 hseedS hsp0 hTP hTPL hYB hLs

/-- **`qr_oloc` with `SeedOK μ` and `HokQ` in place of `SeedOK` at every diagonal point.** -/
theorem qr_olocW (m : Nat) : ∀ i, i < x → DepX M x true i →
    OLocZ M x ρ (zfQ M x (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m) i := by
  set br := app b (psi (succ μ) z z) with hbrdef
  set lo := loQ M ρ μ b with hlodef
  set lb := lbQ M ρ μ b with hlbdef
  have hbr : br ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  have hrx : r < x := par_lt M 1 x r h1
  have hrM : r < M.length := by omega
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  have hrot : isOT (psi μ br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hμ : ¬ lt μ μ = true := lt_irrefl' μ
  have hro' : ρ.o r = psi μ br z := hro
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hHx : HoleT μ br μ (ρ.o x) := Or.inl (by rw [hox]; exact cof_omega_succ μ)
  have hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true :=
    fun i h2 h3 h4 _ => absurd h4 (hdep.2.2 true i h2 h3)
  have hHole := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hA hro'
    cof_br rfl hbr hHx hF1 hOS (hS2_t1 hR0 hA (by omega)) (hS3_t1 h1 hA (by omega) hx hR0 hZ2 hSD hZ1)
  have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
  have hgS : ∀ k, ∃ a X, gamS μ br seed k = psi a X z := by
    intro k; cases k with
    | zero => exact hseedS
    | succ k => exact ⟨μ, _, rfl⟩
  have hdx : dOf M x lo lb x = 0 := dOf_x hx hxv hOS hVS
  intro i hi hd
  have hiM : i < M.length := by omega
  rcases hOS i hi hd with ⟨hv, hnc⟩ | ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd⟩
  · -- only the subscript changes
    have hHv := (hHole false i hv (Or.inl hi)).1
    simp only [valB, cond_false] at hHv
    exact Or.inl ⟨hv, hnc, (hok0 _ (m + dOf M x lo lb i) (hG.ot_v i hiM) hHv
      (fun h0 => qr_only_mu_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hv hi (by rw [hlodef, hlbdef] at h0; omega))).1, holeT_ne_z hHv, holeT_not_succ hHv⟩
  right
  have hcmem : c ∈ children M i := by rw [hch]; exact List.mem_append_right _ List.mem_cons_self
  have hdc : DepX M x true c := by
    cases hd with
    | leaf => omega
    | @ochild _ c' hc' hb' hu' hd' =>
      have : c' = c := by
        rw [hch] at hc'
        rcases List.mem_append.mp hc' with h | h
        · exact absurd hd' (hLnd c' h ⟨hb', hu'⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c' h with h' | h'
            · exact absurd h' hb'
            · exact absurd h' hu'
      rw [← this]; exact hd'
    | ov hv' => exact absurd hv' hv
  have hcm := mem_children hcmem
  have hcM := hcm.2
  have hfl := filter_lt_split (children_sorted M i) hch
  have hdO : dOf M x lo lb i = dOf M x lo lb c + lo i c := dOf_ochild hx hxv hOS hVS hcmem hcb hcu hdc
  refine ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd, hdc, ?_⟩
  unfold zfQ
  rcases Nat.lt_or_ge c x with hcx | hcx
  · -- `c < x`: `c ≤ r` and a diagonal point below
    have hcr : c ≤ r := by
      by_contra h
      exact hdep.2.2 true c (by omega) hcx hdc
    obtain ⟨hHc, hDLc, _⟩ := hHole true c hdc (Or.inl hcx)
    simp only [valB, cond_true] at hHc hDLc
    obtain ⟨a', ha', hDc⟩ := hDLc hcr
    set k := m + dOf M x lo lb c with hk
    have hokc := hok0 (ρ.o c) k (hG.ot_o c hcM) hHc
      (fun h0 => qr_only_mu_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hdc hcx (by rw [hlodef, hlbdef] at hk; omega))
    have hsing : Single (fsD (ρ.o c) (gamS μ br seed k)) :=
      single_fsD (o_psi_form hC hcM) (holeT_not_succ hHc)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHc)) (hgS k) hokc.1
    refine ⟨hsing, le_of_lt hokc.2, ?_⟩
    have hζz : gamS μ br seed k ≠ z := gamS_ne_z_q hseedz k
    by_cases hlo1 : lo i c = 1
    · -- the lift
      have hl := hlo1
      rw [hlodef] at hl
      unfold loQ at hl
      split at hl
      · rename_i hcond
        obtain ⟨hcA, htr1, htr2⟩ := hcond
        rw [hfl] at htr1
        rw [hdO, hlo1, show m + (dOf M x lo lb c + 1) = k + 1 by omega, gamS_succ_q]
        exact qr_frame_lift hC hG hiM hch hcb hcu hR hcM hb hcA
          (by rw [← gamS_succ_q]; exact gamS_ot hrot cof_br hμ hSr (k + 1))
          ⟨htr1, htr2⟩ (gamS_lt_om hrot cof_br hμ hSr k) hζz
          (hYB i L c R hi hd hch ⟨hcb, hcu⟩ hdc μ hcA htr1 htr2 m)
      · exact absurd hl (by omega)
    · -- no lift
      have hlo0 : lo i c = 0 := by
        have : lo i c ≤ 1 := by rw [hlodef]; unfold loQ; split <;> omega
        omega
      rw [hdO, hlo0, Nat.add_zero]
      apply qr_frame_nolift hC hG hiM hch hcb hcu hR hcM hDc ha' hokc
      · -- (W)
        intro s y hcv htr1 htr2
        by_cases hyb : y = br
        · subst hyb
          rw [fsD_eq_fs cof_br, fs_br]
          exact hYB i L c R hi hd hch ⟨hcb, hcu⟩ hdc s hcv htr1 htr2 m
        · have hyz : y ≠ z := by intro h; subst h; simp [lt] at htr1
          have hDy : DiagAt a' br μ y := DiagAt.arg_inv (by rw [← hcv]; exact hDc) hyz
            (fun h => hyb h.2)
          have h1' := hTP i L c R hch ⟨hcb, hcu⟩ s y hcv htr1 htr2 (DiagAt.cof_omega hDy) (ohole_of_diag hDy)
          exact persist_of_tp1 (ohole_of_diag hDy) (one_le_of_ne_z hζz) h1'
      · -- (L)
        intro s y hcv htr1 htr2
        have hyz : y ≠ z := by intro h; subst h; simp [lt] at htr1
        have hHcy : HoleT μ br μ (psi s y z) := by rw [← hcv]; exact hHc
        refine ⟨fun hl => lo_ne_z_of_holeT hζz (holeT_arg hyz hHcy cof_br) hl, fun hl0 => ?_⟩
        have hDc' : DiagAt a' br μ (psi s y z) := by rw [← hcv]; exact hDc
        by_cases hyb : y = br
        · subst hyb
          -- the child is `ψ_s(b_r)` with `s < μ`: at least one lift, so the index is `ψ_μ(…)`
          have hsμ : s ≠ μ := by
            intro hs; subst hs
            have : lo i c = 1 := by
              rw [hlodef]; unfold loQ; rw [hfl, if_pos ⟨hcv, htr1, htr2⟩]
            omega
          have hsle : ¬ lt μ s = true := diag_here_inv hDc'
          have hslt : lt s μ = true := by
            rcases lt_trichotomy' s μ with h | h | h
            · exact h
            · exact absurd h hsμ
            · exact absurd h hsle
          have hdpos : dOf M x lo lb c ≠ 0 := qr_d_pos hx hC hG hKD hTD hq hro hOS hVS hBk hxv hcx hdc hcv hsμ
          obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [hk', gamS_succ_q]
          exact lo_keep_br hb hslt rfl
        · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · -- the seed
            have hm0 : m = 0 := by omega
            have hdc0 : dOf M x lo lb c = 0 := by omega
            rw [hk0]
            exact hLs c hcx hdc hdc0 s y hcv hyb hl0
          · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            rw [hk']
            refine lo_keep_Q hDc' hyz hyb ?_ (le_refl (gamS μ (app b (psi (succ μ) z z)) seed (k' + 1))) hl0
            intro hl a hla hns hOa hca
            have hT := hTPL
            unfold TPLoWAt at hT
            rw [show M.length - 1 = x by omega] at hT
            have hkd : dOf M x lo lb c ≤ k' + 1 := by omega
            rw [hlodef, hlbdef] at hkd
            exact hT r μ b h1 hq hx2 hro (one_le_of_ne_z hseedz) c hcx hdc s y hcv hyb hl a hla hns hOa hca
              (k' + 1) (max_le (by omega) hkd)
  · -- `c = x`: `i = r`, the frame at `r`
    have hcx' : c = x := by omega
    subst hcx'
    have hir : i = r := by
      have := (mem_children_iff.mp hcmem).2; rw [hq] at this; exact (Option.some.inj this).symm
    subst hir
    have hlox : lo i c = 0 := by
      rw [hlodef]; unfold loQ
      rw [if_neg]
      rintro ⟨h, _⟩
      rw [hox] at h
      exact hbr (T.psi.inj h).2.1.symm
    have hfx : ∀ k, fsD (ρ.o c) (gamS μ br seed k) = gamS μ br seed k := by
      intro k; rw [hox]; exact fsD_leaf (isSucc_succ μ) (succ_ne_z μ)
    rw [hdx, Nat.add_zero, hfx]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨a, X, he⟩ := hgS m
      exact ⟨gamS_ot hrot cof_br hμ hSr m, a, X, he⟩
    · rw [hox]; exact le_of_lt (gamS_lt_om hrot cof_br hμ hSr m)
    · rw [hdO, hdx, hlox, Nat.add_zero, hro, hvr]
      rw [← hfl, hpre]
      have hsp : spArg μ b (gamS μ br seed m) = app b (gamS μ br seed m) := by
        cases m with
        | zero => exact hsp0
        | succ k =>
          rw [gamS_succ_q]
          exact spArg_qnext hb (gamS_ne_z_q hseedz k) (gamS_lt_om hrot cof_br hμ hSr k)
            (by rw [← gamS_succ_q]; exact gamS_ot hrot cof_br hμ hSr (k + 1))
      rw [hsp, fsD_A]; rfl

end

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b seed : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) (h1 : par M 1 x = some r) (hq : par M 0 x = some r)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hox : ρ.o x = psi (succ μ) z z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS

variable (hb : AllGeT (psi (succ μ) z z) b)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hxv : ¬ DepX M x false x)
  (hseedS : ∃ a X, seed = psi a X z)
  (hTPL : TPLoWAt M ρ (fun _ => seed))
  (hLs : ∀ c, c < x → DepX M x true c → dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
    ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
    (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z)
include hb hVS hBk hxv hseedS hTPL hLs

variable (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
  (hok0 : HokQ μ (app b (psi (succ μ) z z)) μ seed)
  (hAU' : AbsUWL M ρ)
  (hAUs0 : ∀ i k, i < x → DepX M x false i → upg M i = some k → dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
    OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) seed)
  (hAD' : AbsDWAt M ρ (fun _ => seed))
  (hADs0 : ∀ i, i < x → DepX M x false i → entry M 2 i ≠ 0 →
    dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) seed)
include hSr hok0 hAU' hAUs0 hAD' hADs0

/-- **`qr_vloc` with `SeedOK μ` and `HokQ` in place of `SeedOK` at every diagonal point**; the index-0 condition
at each use: the column's own value (`qr_only_mu_col`), its last summand (`DiagAt.last_g`), and inside
`omega_fsD_hole_QW` the diagonal points of the subterms of `G` and of the bump term. -/
theorem qr_vlocW (m : Nat) : ∀ i, i < x → DepX M x false i →
    VLocZ M x ρ (zfQ M x (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m) i := by
  have hqx0 : par M 0 x = some r := hq
  set br := app b (psi (succ μ) z z) with hbrdef
  set lo := loQ M ρ μ b with hlodef
  set lb := lbQ M ρ μ b with hlbdef
  have hrx : r < x := par_lt M 1 x r h1
  have hrM : r < M.length := by omega
  have hrot : isOT (psi μ br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hμ : ¬ lt μ μ = true := lt_irrefl' μ
  have hSμ := hSr
  have hHD := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS
  have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
  have hgS : ∀ k, ∃ a X, gamS μ br seed k = psi a X z := by
    intro k; cases k with
    | zero => exact hseedS
    | succ k => exact ⟨μ, _, rfl⟩
  have hgot : ∀ k, isOT (gamS μ br seed k) = true := gamS_ot hrot cof_br hμ hSμ
  have hglt : ∀ k, gamS μ br seed k < psi (succ μ) z z := gamS_lt_om hrot cof_br hμ hSμ
  have hgz : ∀ k, gamS μ br seed k ≠ z := gamS_ne_z_q hseedz
  intro i hi hv
  have hiM : i < M.length := by omega
  obtain ⟨h1', hpd, hcase⟩ := hVS i hi hv
  refine ⟨h1', hpd, ?_⟩
  rcases hcase with ⟨h2, hu, hk, hdk⟩ | ⟨h2, L, K, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
  · -- the upgrade frame
    left
    obtain ⟨hHk, a', _, hDk⟩ := hHD false (i + 1) hdk hk
    simp only [valB, cond_false] at hHk hDk
    have hkM : i + 1 < M.length := by omega
    have hVs : Single (last (ρ.v (i + 1))) :=
      ⟨isOT_last (hG.ot_v _ hkM), last_psi_form (holeT_ne_z hHk)⟩
    have hHl := holeT_last_g hHk
    have hDl := hDk.last_g
    have hokl := hok0 _ (m + dOf M x lo lb (i + 1)) hVs.1 hHl (fun h0 => by
      have hDμ := qr_diag_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hdk hk (by rw [hlodef, hlbdef] at h0; omega)
      simp only [valB, cond_false] at hDμ
      exact diag_only_mu (DiagAt.last_g hDμ))
    refine ⟨i + 1, h2, hu, hk, hdk, ?_, hVs, ?_, le_of_lt hokl.2, ?_⟩
    · unfold zfQ; rw [dOf_upg hx hxv hOS hVS hi h1' h2 hu (by omega) hdk]
    · exact single_fsD hVs.2 (holeT_not_succ hHl)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHl)) (hgS _) hokl.1
    · intro q hq hlt
      have hOl := ohole_of_diag hDl
      have hdu : dOf M x lo lb i = dOf M x lo lb (i + 1) :=
        dOf_upg hx hxv hOS hVS hi h1' h2 hu (by omega) hdk
      unfold zfQ
      by_cases hk0 : m + dOf M x lo lb (i + 1) = 0
      · rw [hk0]
        exact hAUs0 i (i + 1) hi hv hu (by omega) hOl (DiagAt.cof_omega hDl) q hq hlt
      · have hxl : M.length - 1 = x := by omega
        have hT := hAU'
        unfold AbsUWL at hT
        rw [hxl] at hT
        have h0 := hT r μ b h1 hqx0 hx2 hro i (i + 1) hi hv hu hOl (DiagAt.cof_omega hDl) q hq hlt
        exact lt_of_lt_of_le h0 (fsD_mono_eta hOl
          (gamS_lb (one_le_of_ne_z hseedz) (max 1 (dOf M x lo lb i)) (m + dOf M x lo lb (i + 1))
            (le_max_left _ _) (max_le (by omega) (by omega))))
  · -- the bump frame
    right
    have hj : j ∈ children M i := by rw [hch]; simp
    have hkj : k ∈ children M j := by rw [hchj]; simp
    have hkx : k < x := hBk i j k hi hv hj hjb hkj hdk
    have hkM : k < M.length := by omega
    obtain ⟨hHk, a', ha', hDk⟩ := hHD true k hdk hkx
    simp only [valB, cond_true] at hHk hDk
    have hBD : BumpData M ρ μ i L K j k := bump_data hC hG hKD hTD h1' h2 hch hjb hchj
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    set kk := m + dOf M x lo lb k with hkk
    set ζ := gamS μ br seed kk with hζdef
    have hζz : ζ ≠ z := hgz kk
    have hDμk : kk = 0 → DiagAt μ br μ (ρ.o k) := fun h0 => by
      have hDμ := qr_diag_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hdk hkx (by rw [hlodef, hlbdef] at hkk; omega)
      simp only [valB, cond_true] at hDμ
      exact hDμ
    have hokζ : ∀ Y, (kk = 0 → DiagAt μ br μ Y) → ∀ t, isOT t = true → HoleT μ br μ t →
        (∀ a'', DiagAt a'' br μ t → DiagAt a'' br μ Y) → isOT (fsD t ζ) = true ∧ fsD t ζ < t :=
      fun Y hY t hot hH hsub => hok0 t kk hot hH (fun h0 a'' hD => diag_only_mu (hY h0) a'' (hsub a'' hD))
    obtain ⟨hfkot, hfklt⟩ := hokζ _ hDμk _ (hG.ot_o k hkM) hHk (fun _ h => h)
    have hfkS : Single (fsD (ρ.o k) ζ) :=
      single_fsD (o_psi_form hC hkM) (holeT_not_succ hHk)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHk)) (hgS kk) hfkot
    have hfkz : fsD (ρ.o k) ζ ≠ z := single_ne_z hfkS
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hDG : DiagAt a' br μ G := by rw [hGe]; exact DiagAt.append _ (single_ne_z hkS) hDk
    have hHG : HoleT μ br μ G := Or.inr ⟨a', ha', hDG⟩
    have hDωG := diag_omega hGot hDG
    have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
    have hDY2 : DiagAt a' br μ (app (sumN P) (omega G)) := DiagAt.append _ hωGz hDωG
    have hHY2 : HoleT μ br μ (app (sumN P) (omega G)) := Or.inr ⟨a', ha', hDY2⟩
    have hDμG : kk = 0 → DiagAt μ br μ G := fun h0 => by
      rw [hGe]; exact DiagAt.append _ (single_ne_z hkS) (hDμk h0)
    have hDμY2 : kk = 0 → DiagAt μ br μ (app (sumN P) (omega G)) := fun h0 =>
      DiagAt.append _ hωGz (diag_omega hGot (hDμG h0))
    have hDW := diag_omega hBD.potW hDY2
    set G' := sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]) with hG'def
    have hsK' : ∀ t ∈ K.map ρ.o ++ [fsD (ρ.o k) ζ], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.sK t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht]; exact hfkS
    have hpK' : (K.map ρ.o ++ [fsD (ρ.o k) ζ]).Pairwise (fun a b => b ≤ a) := by
      have hpK := hBD.pK
      rw [List.pairwise_append] at hpK ⊢
      refine ⟨hpK.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans (le_of_lt hfklt) (hpK.2.2 a ha _ (List.mem_singleton_self _))
    have hG'ot : isOT G' = true := (sumN_dec _ hsK' hpK').1
    have hG'e : G' = app (sumN (K.map ρ.o)) (fsD (ρ.o k) ζ) := sumN_snoc_dec hsK' hpK'
    have hG'z : G' ≠ z := by rw [hG'e]; intro he; exact hfkz (app_eq_z he).2
    have hG'lt : G' < G := by rw [hG'e, hGe]; exact app_lt_app_left _ hfklt
    have hωle : omega G' ≤ omega G := le_of_lt (omega_lt_omega hG'ot hGot hG'lt)
    have hfG : fsD G ζ = G' := by rw [hGe, hG'e]; exact fsD_app _ (single_ne_z hkS) ζ
    -- the index of `i`
    have hdb : dOf M x lo lb i = dOf M x lo lb k + lb i j k :=
      dOf_bump hx hxv hOS hVS hi h1' h2 hj hjb hkj hdk
    have hfl : (children M i).filter (fun d => decide (d < j)) = L :=
      filter_lt_split (children_sorted M i) (show children M i = L ++ j :: [] from hch)
    -- the `ω` exchange
    have hωp : fsD (omega (app (sumN P) (omega G))) (zfQ M x lo lb μ br seed m i) =
        omega (app (sumN P) (omega G')) := by
      unfold zfQ
      rw [hdb, ← Nat.add_assoc]
      show fsD _ (gamS μ br seed (kk + lb i j k)) = _
      by_cases hlift : children M j = [k] ∧ ρ.o k = psi μ br z
      · have hK0 : K = [] := by
          have h3 : K ++ [k] = [k] := hchj.symm.trans hlift.1
          have hl := congrArg List.length h3
          simp at hl
          exact hl
        rw [hK0] at hGe hG'e
        have hGA : G = psi μ br z := by rw [hGe, ← hlift.2]; rfl
        have hG'A : G' = fsD (psi μ br z) ζ := by rw [hG'e, hlift.2]; rfl
        rw [hGA, hG'A]
        by_cases hP : sumN P = z
        · have h2' : lb i j k = 2 := by
            rw [hlbdef]; unfold lbQ; rw [if_pos hlift, hfl, if_pos hP]
          rw [h2', hP]
          show fsD (omega (omega (psi μ br z))) (gamS μ br seed (kk + 1 + 1)) =
            omega (omega (fsD (psi μ br z) ζ))
          rw [gamS_succ_q, gamS_succ_q]
          exact omega_lift2 hb hrot hζz (hglt kk) (by rw [← gamS_succ_q]; exact hgot _)
            (by rw [← gamS_succ_q, ← gamS_succ_q]; exact hgot _) (by rw [← gamS_succ_q]; exact hglt _)
        · have h1'' : lb i j k = 1 := by
            rw [hlbdef]; unfold lbQ; rw [if_pos hlift, hfl, if_neg hP]
          rw [h1'', gamS_succ_q]
          have hPA : isOT (app (sumN P) (psi μ br z)) = true := by
            have := hBD.potW
            rw [← hPdef, ← hGdef, hGA, omega_A hb hrot] at this
            exact this
          have hn2 : qnext μ b (qnext μ b ζ) < psi μ br z :=
            qnext_lt_A (by rw [← gamS_succ_q]; exact hglt _)
          apply omega_lift1 hb hP hrot hPA
            (fun h => A_not_lt_E0 hb (lt_trans (lt_app_right hPA hP) h)) hζz (hglt kk)
            (by rw [← gamS_succ_q]; exact hgot _)
          apply isOT_app_of (isOT_app_left hPA) (by rw [← gamS_succ_q, ← gamS_succ_q]; exact hgot _)
          intro q hq
          exact le_trans (le_of_lt hn2) (summands_ge_of_app hPA q hq)
      · have h0 : lb i j k = 0 := by
          rw [hlbdef]; unfold lbQ; rw [if_neg hlift]
        rw [h0, Nat.add_zero]
        have hLG : ∀ s b', G = psi s b' z → b' ≠ z → (split b' (psi (succ s) z z)).2 = z →
            (split (fsD b' ζ) (psi (succ s) z z)).2 = z := by
          intro s b' hGs hb' hl
          have hK0 : sumN (K.map ρ.o) = z := by
            by_contra hK
            exact app_single_ne hK (single_ne_z hkS) (by rw [← hGe]; exact hGs)
          have hok' : ρ.o k = psi s b' z := by rw [← hGs, hGe, hK0]; rfl
          have hnA : ¬ (s = μ ∧ b' = br) := by
            rintro ⟨hs, hbb⟩
            apply hlift
            refine ⟨?_, by rw [hok', hs, hbb]⟩
            have hKn : K = [] := by
              by_contra hKne
              exact sumN_ne_z_of_single (fun t ht => hBD.sK t (List.mem_append_left _ ht))
                (List.pairwise_append.mp hBD.pK).1 (by simpa using hKne) hK0
            rw [hchj, hKn]; rfl
          exact qr_lkeep hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS hb hVS
            hBk hxv hseedS hTPL hLs m hkx hdk hok' hb' hnA hl
        have hLY2 : ∀ s b', app (sumN P) (omega G) = psi s b' z → b' ≠ z →
            (split b' (psi (succ s) z z)).2 = z → (split (fsD b' ζ) (psi (succ s) z z)).2 = z := by
          intro s b' hY hb' hl
          have hP0 : sumN P = z := by
            by_contra hP; exact app_single_ne hP hωGz hY
          rw [hP0] at hY
          have hY' : omega G = psi s b' z := hY
          have hfix := omega_single_nolo hGot (DiagAt.ne_z hDG) hY' hl
          exact hLG s b' (by rw [← hfix]; exact hY') hb' hl
        have hωGfs : fsD (omega G) ζ = omega G' := by
          rw [omega_fsD_hole_QW hGot hHG hDG cof_br hζz (hokζ G hDμG) hLG, hfG]
        rw [omega_fsD_hole_QW hBD.potW hHY2 hDY2 cof_br hζz (hokζ _ hDμY2) hLY2, fsD_app _ hωGz ζ, hωGfs]
    refine ⟨L, K, j, k, h2, hch, hjb, hchj, hdk, hKnd, hLnd, hfkS, le_of_lt hfklt, hBD.sK, hBD.pK,
      hBD.sL, hBD.pp, ?_, hBD.gt, ?_, hωp, ?_⟩
    · have hpp := hBD.pp
      rw [List.pairwise_append] at hpp ⊢
      refine ⟨hpp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans hωle (hpp.2.2 a ha _ (List.mem_singleton_self _))
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.gt t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht, ← omega_z]
        exact omega_lt_omega rfl hG'ot (lt_of_le_of_ne (z_le _) (Ne.symm hG'z))
    · intro q hq hlt
      show q < omega (app (sumN P) (omega G'))
      rw [← hωp]
      have hOW : OHole (bumpW M ρ i) := by rw [hBD.W]; exact ohole_of_diag hDW
      have hcW : cof (bumpW M ρ i) = .omega := by rw [hBD.W]; exact DiagAt.cof_omega hDW
      unfold zfQ
      by_cases hk0 : m + dOf M x lo lb i = 0
      · rw [hk0]
        have h2' := hADs0 i hi hv h2 (by omega) q hq (by rw [hBD.W]; exact hlt)
        rw [hBD.W] at h2'
        exact h2'
      · have hxl : M.length - 1 = x := by omega
        have hT := hAD'
        unfold AbsDWAt at hT
        rw [hxl] at hT
        have hkd : dOf M x lo lb i ≤ m + dOf M x lo lb i := by omega
        have hk1 : 1 ≤ m + dOf M x lo lb i := by omega
        rw [hlodef, hlbdef] at hkd
        have h0 := hT r μ b h1 hqx0 hx2 hro (one_le_of_ne_z hseedz) i hi hv h1' h2 hOW hcW q hq
          (by rw [hBD.W]; exact hlt) (m + dOf M x lo lb i) (max_le hk1 hkd)
        rw [hBD.W] at h0
        exact h0

end

end Ytosk
