/-
**3 行・t = 1・q = r: o の局所条件 `OLocZ` をすべての D の呼び出しで（`qr_oloc`）。**

列ごとの添字 Zf_m(i) = gamS(m + d_i)。o の呼び出し i（D、i < x）について:
- 添字だけ変わる枠: 穴（`t1_hole0`）と鎖の fsD の降下（`hok_of_holeT`）。
- 子 c = x（i = r）: r の枠（`qr_frame_r`、鎖の 2 項目以降は `spArg_qnext`、始点は仮定 hsp0）。
- 子 c < x（c ≤ r、対角化の点の下）: 引き上げ（`qr_frame_lift`、B ≤ b から (W)）か、引き上げなし
  （`qr_frame_nolift`: (W) は TP1W か B ≤ b、(L)(ii) は y ≠ b_r なら TPLoW（添字 ≥ 1）か始点の仮定 hLs、
  y = b_r なら引き上げの数 ≥ 1（`qr_d_pos`）で ζ = ψ_μ(…)）。
残る仮定: TP1W・TPLoW（大域の値の不変条件）、y = b_r の書き換えの枠で B < b + ζ（鎖のすべての項、hYB）、始点の (L)(ii)（hLs）、
r の枠の始点の条件 spArg(μ, b, seed) = b + seed（hsp0）。
-/
import Ytosk.V3QRKeep

namespace Ytosk

open T

/-- A diagonal point at `ψ_s(b_r)` is the node itself: `s ≤ μ`. -/
theorem diag_here_inv {a' μ b s : T}
    (h : DiagAt a' (app b (psi (succ μ) z z)) μ (psi s (app b (psi (succ μ) z z)) z)) :
    ¬ lt μ s = true := by
  generalize hB : app b (psi (succ μ) z z) = B at h
  cases h with
  | here _ _ h => exact h
  | arg _ _ hD => rw [← hB] at hD; exact absurd hD not_diag_br
  | sub _ _ _ => exact absurd (app_eq_z hB).2 (by simp)

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b seed : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) (h1 : par M 1 x = some r) (hq : par M 0 x = some r)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
  (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z) (hvr : ρ.v r = μ)
  (hb : AllGeT (psi (succ μ) z z) b)
  (hpre : preState M ρ r ((children M r).filter (fun d => decide (d < x))) = b)
  (hox : ρ.o x = psi (succ μ) z z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hxv : ¬ DepX M x false x)
  (hS : ∀ a', ¬ lt μ a' = true → isOT (psi a' (app b (psi (succ μ) z z)) z) = true →
    SeedOK a' (app b (psi (succ μ) z z)) μ seed)
  (hseedS : ∃ a X, seed = psi a X z)
  (hsp0 : spArg μ b seed = app b seed)
  (hTP : TP1W M ρ) (hTPL : TPLoW M ρ)
  (hYB : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
    ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
    lt (preState M ρ i L) (app b (psi (succ μ) z z)) = true →
    lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
    ∀ m', lt (preState M ρ i L) (app b (gamS μ (app b (psi (succ μ) z z)) seed m')) = true)
  (hLs : ∀ c, c < x → DepX M x true c → dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
    ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
    (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hvr hb hpre hox hOS hVS hBk hxv
  hS hseedS hsp0 hTP hTPL hYB hLs

/-- **`OLocZ` on all `o` calls of `D`** (`t = 1`, `q = r`). -/
theorem qr_oloc (m : Nat) : ∀ i, i < x → DepX M x true i →
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
  have hHole := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hrx hA hro'
    cof_br rfl hbr hHx hF1 hOS (hS2_t1 hR0 hA (by omega)) (hS3_t1 h1 hA (by omega) hx hR0 hZ2 hSD hZ1)
  have hok : ∀ t k, isOT t = true → HoleT μ br μ t →
      isOT (fsD t (gamS μ br seed k)) = true ∧ fsD t (gamS μ br seed k) < t :=
    fun t k hot hH => hok_of_holeT hrot cof_br hμ hS hot hH k
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
    exact Or.inl ⟨hv, hnc, (hok _ _ (hG.ot_v i hiM) hHv).1, holeT_ne_z hHv, holeT_not_succ hHv⟩
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
    have hokc := hok (ρ.o c) k (hG.ot_o c hcM) hHc
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
          (by rw [← gamS_succ_q]; exact gamS_ot hrot cof_br hμ (hS μ hμ hrot) (k + 1))
          ⟨htr1, htr2⟩ (gamS_lt_om hrot cof_br hμ (hS μ hμ hrot) k) hζz
          (hYB i L c R hi hd hch hdc μ hcA htr1 htr2 k)
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
          exact hYB i L c R hi hd hch hdc s hcv htr1 htr2 k
        · have hyz : y ≠ z := by intro h; subst h; simp [lt] at htr1
          have hDy : DiagAt a' br μ y := DiagAt.arg_inv (by rw [← hcv]; exact hDc) hyz
            (fun h => hyb h.2)
          have h1' := hTP i L c R hch s y hcv htr1 htr2 (DiagAt.cof_omega hDy) (ohole_of_diag hDy)
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
            have hDy : DiagAt a' br μ y := DiagAt.arg_inv hDc' hyz (fun h => hyb h.2)
            have hlev : holeLev y = μ := DiagAt.holeLev_eq hDy
            rw [hk']
            refine lo_keep_Q hDc' hyz hyb ?_ (gamS_ge_psi1 hseedz k') hl0
            intro hl a hla hns hOa hca
            have := hTPL c hcM s y hcv hl a hla hns hOa hca
            rw [hlev] at this; exact this
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
      exact ⟨gamS_ot hrot cof_br hμ (hS μ hμ hrot) m, a, X, he⟩
    · rw [hox]; exact le_of_lt (gamS_lt_om hrot cof_br hμ (hS μ hμ hrot) m)
    · rw [hdO, hdx, hlox, Nat.add_zero, hro, hvr]
      rw [← hfl, hpre]
      have hsp : spArg μ b (gamS μ br seed m) = app b (gamS μ br seed m) := by
        cases m with
        | zero => exact hsp0
        | succ k =>
          rw [gamS_succ_q]
          exact spArg_qnext hb (gamS_ne_z_q hseedz k) (gamS_lt_om hrot cof_br hμ (hS μ hμ hrot) k)
            (by rw [← gamS_succ_q]; exact gamS_ot hrot cof_br hμ (hS μ hμ hrot) (k + 1))
      rw [hsp, fsD_A]; rfl

end

end Ytosk
