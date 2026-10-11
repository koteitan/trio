/-
**比べる道に沿った移し替え（fsD_transfer の道の版）。**

u と fsD(X, ξ) の比較は、fsD の再帰に沿って X の穴の位置まで降り、そこで u の 1 本の部分項と ξ の比較になる。
groupA の fsD_transfer は条件を u のすべての部分項（部分項で閉じた集合 S）に課すが、使うのはこの 1 本の道だけ。
groupA の Al X s u（X の穴に並ぶ s の部分項、V3AlignT）と fsD_transfer_al を使う。
t = 1 の TPLo の種の条件は ext1x・expP で偽になる（s0 の深い部分項が帯に入る）が、道の条件は成り立つ。
-/
import Ytosk.V3ExpT1N
import Ytosk.V3AlignT

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`tplo_fsD_gen` along the path.** -/
theorem tplo_fsD_path {s a0 ζ θ η0 : T} (hOa0 : OHole a0) (hζ : ζ ≠ z) (hζs : isSucc ζ = false)
    (hM : s < fsD a0 η0) (hN : s < fsD a0 ζ)
    (hpath : ∀ u, Al a0 s u → u < ζ → u < η0 → u < fsD ζ θ) :
    s < fsD (fsD a0 ζ) θ := by
  rw [fsD_comp hOa0 hζ hζs θ]
  exact fsD_transfer_al hOa0 s hpath hN hM


/-- **Residual (TPLo, the path form)**: the subterm of `s₀` aligned with the hole of the old last subscript `a₀`
satisfies the seed condition (`SeedRes` asks it of every subterm, false on ext1x・expP). -/
def TPLoPathRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    GoodIdx (Z c) → TPLoPatN s0 y0 (Z c) → ∀ a0, last y0 = psi a0 z z →
    ∀ u, Al a0 s0 u → u < Z c → u < etaOm (holeLev y0) → u < fsD (Z c) (etaOm (holeLev (Z c)))

theorem tplo_new_path {s0 y0 ζ θ : T} (hO : OHole y0) (hζz : ζ ≠ z) (hζs : isSucc ζ = false)
    (hζ1 : ∃ μ X, ζ = psi μ X z ∧ X ≠ z) (hle : fsD y0 ζ ≤ y0) (hM : TPLoAt s0 y0)
    (hS : ∀ a0, last y0 = psi a0 z z → ∀ u, Al a0 s0 u → u < ζ → u < etaOm (holeLev y0) → u < fsD ζ θ) :
    (split (fsD y0 ζ) (psi (succ s0) z z)).2 = z → ∀ a, last (fsD y0 ζ) = psi a z z →
      ¬ psi (fsD a θ) z z < psi (succ s0) z z := by
  intro hsplit a hl
  have hAll := allGe_of_split_snd hsplit
  obtain ⟨a0, hl0e, _, has0, hOa0, ha, hdec⟩ := last_fsD_om hO hζz hζ1 hl
  have hAll0 := allGe_back hdec hl0e hle hAll
  have hM' := tpl_iff.mp (hM (split_snd_of_allGe hAll0) a0 hl0e has0 hOa0)
  have hN : s0 < a := by
    rw [hdec] at hAll
    exact tpl_iff.mp ((allGe_app.mp hAll).2 _ (by simp [summands]))
  rw [ha] at hN ⊢
  exact tpl_iff.mpr (tplo_fsD_path hOa0 hζz hζs hM' hN (hS a0 hl0e))

theorem tploAt_new_path {s0 y0 ζ : T} (hO : OHole y0) (hζz : ζ ≠ z) (hζs : isSucc ζ = false)
    (hζ1 : ∃ μ X, ζ = psi μ X z ∧ X ≠ z) (hle : fsD y0 ζ ≤ y0) (hM : TPLoAt s0 y0)
    (hS : ∀ a0, last y0 = psi a0 z z →
      ∀ u, Al a0 s0 u → u < ζ → u < etaOm (holeLev y0) → u < fsD ζ (etaOm (holeLev ζ))) :
    TPLoAt s0 (fsD y0 ζ) := by
  intro hsplit a hl _ _
  rw [holeLev_fsD hO hζz hζs]
  exact tplo_new_path hO hζz hζs hζ1 hle hM hS hsplit a hl

theorem expStep_tploP {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : DegRes TPLoAt M r L d0 ρ ∧ TPLoPathRes M r L d0 ρ) :
    ExpStepT1 TPLo M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  intro n hn ρP Z hCP _ hTPP hCN _ _ _ hle _ hH
  have hDeg := hRes.1 n hn ρP Z hH hCN
  have hSd := hRes.2 n hn ρP Z hH hCP hCN
  obtain ⟨μ', br', vr', seed, k0, hHD, _, _, _, _, _⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro c hc s y hσc hsplit a hl has hOa
  rcases Nat.lt_or_ge c (r + L) with hc' | hc'
  · have hcM : c < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons hcM
    by_cases hd : DepX M (r + L) true c
    · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0] at hσc
      by_cases hy0 : y0 = z
      · exfalso
        subst hy0
        by_cases hs0 : isSucc s0 = true
        · -- a `D` leaf with old value `Ω_{t+1}` below `x`: impossible
          rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
          · have hHv := hHD.hole false c hvc hc'
            simp only [valB, cond_false] at hHv
            have hoc := o_nocnt I.cons I.good hcM hnc
            rw [h0] at hoc
            have hs : s0 = ρ.v c := (T.psi.inj hoc).1
            have := holeT_not_succ hHv
            rw [← hs, hs0] at this; cases this
          · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
              c' ∈ children M c)).2
            have hfr := o_frame I.cons I.good hcM hch' hcb' hcu' hR' hc'M
            obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
            rw [hc3, spArg_single, h0] at hfr
            exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
        · by_cases hs0z : s0 = z
          · subst hs0z; unfold fsD at hσc; simp at hσc
          · rw [fsD_sub hs0z (by simpa using hs0)] at hσc
            rw [← (T.psi.inj hσc).2.1] at hl
            simp [last] at hl
      · have hHc := hHD.hole true c hd hc'
        simp only [valB, cond_true] at hHc
        rw [h0] at hHc
        have hy0s := not_succ_arg_of_holeT hy0 hHc
        have hHy := holeT_arg hy0 hHc hHD.cb
        have hOy0 := ohole_of_holeT hHy
        rw [fsD_psi hy0 hy0s] at hσc
        obtain ⟨hss, hyy, _⟩ := T.psi.inj hσc
        subst hss hyy
        have hlec : psi s0 (fsD y0 (Z c)) z ≤ psi s0 y0 z := by
          have := (hle c hc' hd).1
          rw [h0, fsD_psi hy0 hy0s] at this; exact this
        have hyy0 : fsD y0 (Z c) ≤ y0 := by
          rcases (le_iff _ _).mp hlec with h' | h'
          · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
            · exact absurd h'' (lt_irrefl' _)
            · exact le_of_lt h''
          · rw [(T.psi.inj h').2.1]
        by_cases hgood : GoodIdx (Z c)
        · obtain ⟨hζs, μ, X, hζe, hX⟩ := hgood
          have hζz : Z c ≠ z := by rw [hζe]; simp
          exact tploAt_new_path hOy0 hζz hζs ⟨μ, X, hζe, hX⟩ hyy0 (tploAt_of I.tplo hcM h0)
            (hSd c hc' hd s0 y0 h0 hy0 ⟨hζs, μ, X, hζe, hX⟩ ⟨hsplit, a, hl, has, hOa⟩) hsplit a hl has hOa
        · exact hDeg c hc' hd s0 y0 h0 hy0 hgood hsplit a hl has hOa
    · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd] at hσc
      exact I.tplo c hcM s y hσc hsplit a hl has hOa
  · -- a copy column
    obtain ⟨b, rfl⟩ : ∃ b, c = r + L + b := ⟨c - (r + L), by omega⟩
    have hσo : σ.o (r + L + b) = ρP.o (r + b) := by
      rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (r + L + b - L) = ρP.o (r + b); congr 1; omega
    rw [hσo] at hσc
    exact hTPP (r + b) (by rw [hlP]; rw [hlN] at hc; omega) s y hσc hsplit a hl has hOa

/-! ## TP1C along the chain -/

/-- `inv3V_N_t1Bd` with the TPLo residual in the path form. -/
theorem inv3V_N_t1Pa {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hResL : DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoPathRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResD : AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResU : AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResDN : AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hPR : PassRootRes M r L ρ)
    (hFr : ∀ n σ rkN, 2 ≤ n → Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN →
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpKidsDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpTermDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      AbsD (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLo (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLoW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧
      AbsDW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧ TPLoN (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN,
      Inv3V (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  intro n hn
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; have := par_lt M 1 _ r hr; omega
    · exact h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hdr := R.drop
  have hsd := R.seed
  rw [show M.length - 1 = r + L by omega] at hdr hsd
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V1 := valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI hdr
  have hx0 : entry M 0 (r + L) ≠ 0 := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  have hRP1 := rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 hx0 I.cons I.rank hVI hdr
    I.rootP
  have hRT' := hRT
  simp only [RestT] at hRT'
  rw [show M.length - 1 = r + L by omega] at hRT'
  obtain ⟨ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hRT'
  have hcntG := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1' : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcntG
  have hC1' : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1'
  have hAg := agr_base hlen hL0 hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 I.cons I.good I.rank
  have hP1 : (fun N σ => PT1C M r ρ N σ) (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, tp1, tp1w, tplo, ⟨hAg, ad⟩, ⟨hAg, auw⟩, ⟨hAg, adn⟩,
      ⟨vrle_base I R hlen hr, V1.vs⟩⟩
  have hPs : ExpStepT1 (fun N σ => PT1C M r ρ N σ) M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1' I hlen hL0 hd0e hr hx2)
            (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2)
              (expStep_and (expStep_tp1C I hlen hL0 hd0e hr hx2)
                (expStep_and (expStep_tp1WC I hlen hL0 hd0e hr hx2)
                  (expStep_and (expStep_tploP I hlen hL0 hd0e hr hx2 hResL)
                    (expStep_and (expStep_absD I hlen hL0 hd0e hr hx2 hResD)
                      (expStep_and (expStep_absUW I hlen hL0 hd0e hr hx2 hResU)
                        (expStep_and (expStep_absDN I hlen hL0 hd0e hr hx2 hResDN)
                          (expStep_vsmallF2 I hlen hL0 hd0e hr hx2 hPR)))))))))))
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) (fun N σ => PT1C M q ρ N σ)
        hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1C hCN hRN hGN hPN (hFr n ρN rkN hn hRN hCN hGN hPN.2.2.1.1 hPN.2.2.1.2
      hPN.2.2.2.2.2.2.2.2.1.2 hPN.2.2.2.2.2.2.2.1),
      hot, hlt⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g (fun N σ => PT1C M r ρ N σ)
        hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1C hCN hRN hGN hPN (hFr n ρN rkN hn hRN hCN hGN hPN.2.2.1.1 hPN.2.2.1.2
      hPN.2.2.2.2.2.2.2.2.1.2 hPN.2.2.2.2.2.2.2.1),
      hot, hlt⟩

/-- **The `t = 1` part of `hExp` with the TPLo residual in the path form** (`TPLoPathRes`: only the subterm of `s₀`
aligned with the hole of `a₀`; the full `SeedRes` is false on ext1x・expP). -/
theorem hExp_t1OP
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → TPLoW N σ ∧ AbsDW N σ ∧ TPLoN N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoPathRes M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      PassRootRes M r L ρ) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn _ _
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  rw [h1t] at hr
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hexpA := fun n' => expand_eq_gexp_t1 M n' hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hexpA hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp hexpA
  have hlen : r + L + 1 = M.length := by omega
  have hRN := hResN M ρ rk hM hS I R r L hlen hr hx2
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1Pa I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      hRN.1 hRN.2.1 hRN.2.2.1 hRN.2.2.2.1 hRN.2.2.2.2
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        exact hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V⟩

end Ytosk
