/-
**3 行・t = 0: 影の枠（TP1C・TP1WC・TrigOmC の残り）を「t の中の cut」に狭める。**

D の枠で状態 B ≠ 0 が新しい引数 y′ の先頭部分でなく、新しい枠が書き換える場合（T0RWResCR の D の部分）:
- 古い枠も書き換えるので M の PH3c が使える。RE（T0DF）で y = P + t、y′ = P + T′。
- eq・pre は B が y′ の先頭部分になり前提に反する。
- cut で lo(y) ≠ 0、または切り口が P の中: B は y′ の真の先頭部分 A より小さく、fsD は右端だけを変えるので
  P(a, B, s, A + T″) が成り立つ（`hPgt`、各欄で ptp1_gt・ptp1w_gt・ptrig_gt）。
- 残りは切り口が最後の加数 t の中（B = P + κ）で lo(y) = 0 の場合だけ（`T0ShCutRes`、CutResG と同じ場面）。
g の枠の残り `T0ShGRes` はそのまま。
-/
import Ytosk.V3T0TopR
import Ytosk.SPFSD
import Ytosk.V3TP1Cut

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem ptp1_gt {a B s A T' : T} (hBA : B < A) (hT : T' ≠ z) : PTP1 a B s (app A T') := by
  intro _
  rw [fsD_app A hT]
  exact lt_of_lt_of_le hBA (le_app_self _ _)

theorem ptp1w_gt {a B s A T' : T} (hBA : B < A) (hT : T' ≠ z) : PTP1W a B s (app A T') := by
  intro _ _
  rw [fsD_app A hT]
  exact lt_of_lt_of_le hBA (le_app_self _ _)

theorem ptrig_gt {a B s A T' : T} (hBA : B < A) (hT : T' ≠ z) : PTrig a B s (app A T') := by
  intro ν h
  exfalso
  cases A with
  | z => exact T.not_lt_z _ hBA
  | psi a1 b1 c1 =>
    simp only [app_psi, psi.injEq] at h
    exact hT (app_eq_z h.2.2).2

/-- **Residual: the shadow `D` frames with the cut in the last summand** (`lo(y) = 0`, `B = P + κ`). -/
def T0ShCutRes (P : T → T → T → T → Prop) : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    ∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
      ∀ s y P0 a' x T', ρ.o c = psi s y z → σ.o c = psi s (app P0 T') z → y = app P0 (psi a' x z) → T' ≠ z →
        (split y (psi (succ s) z z)).2 = z →
        ∀ κ ∈ cutsNS s (psi a' x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P0 κ →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) (app P0 T') = true →
        lt (psi (ρ.v i) z z) (psi s (app P0 T') z) = true →
        P (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s (app P0 T')

/-- **Residual: the shadow frames of `g`** (the `g` part of `T0RWResCR`). -/
def T0ShGRes (P : T → T → T → T → Prop) : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    ∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rk).o r) → QPS P (ρ.v g) (Lc.map ρ.o) cv

theorem t0RWResAt_of2 (P : T → T → T → T → Prop)
    (hPA : ∀ a B s y y', isOT (psi s y z) = true → (∀ q ∈ summands B, psi s y z ≤ q) → y' < y →
      ClsA s y' y → lt B y' = true → P a B s y')
    (hPpre : ∀ a B s y', lt B y' = true → (B = z ∨ ∃ R, y' = app B R) → P a B s y')
    (hPgt : ∀ a B s A T', B < A → T' ≠ z → P a B s (app A T'))
    (hShD : T0ShCutRes P) (hShG : T0ShGRes P) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hPH : PH3c M ρ) (hDF : T0DF M ρ) : T0RWResAt P M ρ rk := by
  intro r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN
  have hG0 := hShG M ρ rk r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN
  refine ⟨?_, fun g hg hc Lc hcl cv hcv => qp_of_qps hPpre (hG0 g hg hc Lc hcl cv hcv)⟩
  intro i hi hng Lc c Rr hCL hDc s1 y1 hcv ht1 ht2
  have hlN := lenN0 hlen (show 1 ≤ n by omega) (M := M) (L := L)
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcM : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hcr : c < r := by
    by_cases hig : par M 0 r = some i
    · have hle := children_g_le hlen hL hp hig hcM
      rcases Nat.lt_or_ge c r with h | h
      · exact h
      · exfalso; have : c = r := by omega
        rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
    · exact children_lt_r hlen hL hp hi hig hcM
  have hcMl : c < M.length := by omega
  have hiM : i < M.length := by omega
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by
    rw [hlN]; have := Nat.le_mul_of_pos_left L (show 0 < n by omega); omega
  set a := ρ.v i
  set B := spArg a z (sumN (Lc.map ρ.o)) with hBdef
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hiM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_cons] at hsM hpM
  have hpL := List.pairwise_append.mp hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) hpL.1
  have hBc : ∀ q ∈ summands B, ρ.o c ≤ q := by
    obtain ⟨s0, y0, hs0⟩ := (single_o I.cons I.good hcMl).2
    rw [hs0]
    apply spArg_summands_ge ⟨s0, y0, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq
      have := hpL.2.2 q hq (ρ.o c) (by simp)
      rwa [hs0] at this
    · simp [summands]
  obtain ⟨_, hlD, _, hchg, hREc⟩ := (hDF r L hlen hL hp he1 n hn σ hCN c hcr).1 hDc
  by_cases hvc : σ.v c = ρ.v c
  · obtain ⟨X, X', hX, hX', hlX⟩ := df_same I.cons I.good hCN hcMl hcN (hGN.ot_v c hcN) hvc hlD
    rw [hcv] at hX'
    simp only [psi.injEq] at hX'
    obtain ⟨rfl, rfl, -⟩ := hX'
    by_cases hA : ClsA (ρ.v c) y1 X
    · have hcX : isOT (psi (ρ.v c) X z) = true := by rw [← hX]; exact I.good.ot_o c hcMl
      exact hPA a B (ρ.v c) X y1 hcX (fun q hq => by rw [← hX]; exact hBc q hq) hlX hA ht1
    · apply qp_of_qps hPpre _ (ρ.v c) y1 hcv ht1 ht2
      intro s2 y2 hcv2 hlt2 htr2 hB2 hpre2
      rw [hcv] at hcv2; simp only [psi.injEq] at hcv2
      obtain ⟨rfl, rfl, -⟩ := hcv2
      have hlt' : psi (ρ.v c) y1 z < psi (ρ.v c) X z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hlX⟩)
      have htrO : lt B X = true ∧ lt (psi a z z) (psi (ρ.v c) X z) = true :=
        ⟨lt_trans (show B < y1 from hlt2) hlX, lt_trans (show psi a z z < psi (ρ.v c) y1 z from htr2) hlt'⟩
      have hK := hPH i hiM Lc c Rr hCL (ρ.v c) X hX hB2 htrO
      obtain ⟨P0, a', x, T', hXe, hye, hT⟩ := hREc hvc X y1 hX hcv (ne_of_lt hlX)
      set θ := psi (succ (ρ.v c)) z z with hθ
      have e := split_app θ X
      rcases hK with ⟨heq, hlo⟩ | ⟨hne, (⟨R0, hR0, hhi⟩ | ⟨_, hc⟩)⟩
      · exfalso
        rw [heq, hXe] at e
        obtain ⟨R1, hR1⟩ := prefix_of_app_single e (by rw [← hXe]; exact hlo)
        exact hpre2 ⟨app R1 T', by rw [hye, hR1, app_assoc]; rfl⟩
      · exfalso
        rw [hhi, app_assoc, hXe] at e
        obtain ⟨R1, hR1⟩ := prefix_of_app_single e (fun h => hR0 (app_eq_z h).1)
        exact hpre2 ⟨app R1 T', by rw [hye, hR1, app_assoc]; rfl⟩
      · by_cases hlo : (split X θ).2 = z
        · rw [hlo, app_z_right] at e
          rw [e, hXe] at hc
          rcases cutsNS_split hc with h | ⟨κ, hκ, hBk⟩
          · have hBP : B < P0 := by
              rcases (le_iff _ _).mp (cutsNS_le h) with h' | h'
              · exact h'
              · exfalso; exact hpre2 ⟨T', by rw [hye, ← h']; rfl⟩
            rw [hye]; exact hPgt a B (ρ.v c) P0 T' hBP hT
          · rw [hye]
            exact hShD M ρ rk r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN i hi hng Lc c Rr hCL hDc
              (ρ.v c) X P0 a' x T' hX (by rw [hcv, hye]) hXe hT hlo κ hκ hBk (by rw [← hye]; exact hlt2)
              (by rw [← hye]; exact htr2)
        · rw [hXe] at e
          obtain ⟨R1, hR1⟩ := prefix_of_app_single e (by rw [← hXe]; exact hlo)
          rw [← hXe] at hR1
          have hBhi : B < (split X θ).1 := by
            rcases (le_iff _ _).mp (cutsNS_le hc) with h' | h'
            · exact h'
            · exact absurd h'.symm hne
          rw [hye, hR1, app_assoc]
          exact hPgt a B (ρ.v c) _ (app R1 T') hBhi (fun h => hT (app_eq_z h).2)
  · have h0 := hchg hvc
    rw [hcv] at h0
    simp only [psi.injEq] at h0
    rw [h0.2.1] at ht1
    exact absurd ht1 (T.not_lt_z _)


/-- **`hExp` for `t = 0`, the shadow frames narrowed** to the cut in the last summand (`T0ShCutRes`) and the
frames of `g` (`T0ShGRes`). -/
theorem hExp_t0_topS
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hCut : T0CutResG) (hRest : T0RestV)
    (hD1 : T0ShCutRes PTP1) (hD1W : T0ShCutRes PTP1W) (hDT : T0ShCutRes PTrig)
    (hG1 : T0ShGRes PTP1) (hG1W : T0ShGRes PTP1W) (hGT : T0ShGRes PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hVR hz hs0 n hn2
  have hIV := t0IVRes_holds
  have f : ∀ F, T0Field F → T0FieldG F := fun _ h M ρ rk r L n σ rkN hctx _ => h M ρ rk r L n σ rkN hctx
  have g : ∀ F, T0FieldG F → T0Field F := fun F h M ρ rk r L n σ rkN hctx =>
    h M ρ rk r L n σ rkN hctx (hNG M ρ rk hctx.1 hctx.2.1 hctx.2.2.1 hctx.2.2.2.1)
  have hFF := t0_frameFields hFrm (t0_absD hRest.phi) (f _ (t0_tplo hRest.tploR))
  have H2 : T0RestNV := ⟨g _ (t0_absD hRest.phi), g _ (t0_absU hRest.phi), g _ (f _ (t0_tplo hRest.tploR)),
    g _ (f _ (t0_absUW hRest.auwR)), g _ hFF.2.2, g _ (f _ (t0_absDN hRest.adnR)), g _ hFF.1, g _ hFF.2.1⟩
  have hDF := t0DF_of hPH hCut hIV hM hS I R hVR
  apply hExp_t0A hDF (t0_vsmallF_at (t0VSD_at hDF.toH) hIV) H2
    (t0RWResAt_of2 PTP1 (fun _ _ _ _ _ hc hBc hl hA ht => ptp1_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptp1_prefix hlt hpre) (fun _ _ _ _ _ h1 h2 => ptp1_gt h1 h2) hD1 hG1
      (hPH M ρ rk hM hS I R) hDF)
    (t0RWResAt_of2 PTP1W (fun _ _ _ _ _ hc hBc hl hA ht => ptp1w_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptp1w_prefix hlt hpre) (fun _ _ _ _ _ h1 h2 => ptp1w_gt h1 h2) hD1W hG1W
      (hPH M ρ rk hM hS I R) hDF)
    (t0RWResAt_of2 PTrig (fun _ _ _ _ _ hc hBc hl hA ht => ptrig_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptrig_prefix hlt hpre) (fun _ _ _ _ _ h1 h2 => ptrig_gt h1 h2) hDT hGT
      (hPH M ρ rk hM hS I R) hDF)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩


/-- `t0_frameFields` without `NoGapP` (with `AbsD`・`TPLo` of `N` given). -/
theorem t0_frameFieldsF (hF : FrmLF) (hAD : T0Field AbsD) (hTP : T0Field TPLo) :
    T0Field TPLoW ∧ T0Field AbsDW ∧ T0Field TPLoN := by
  have key : ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
      TPLoW (TRIO.gexp M r L 0 0 n) σ ∧ AbsDW (TRIO.gexp M r L 0 0 n) σ ∧ TPLoN (TRIO.gexp M r L 0 0 n) σ := by
    intro M ρ rk r L n σ rkN hctx
    obtain ⟨hM, _, I, _, hlen, hL, hp, he1, _, _, hCN, hRN, hGN, _, _, hKD, hTD⟩ := id hctx
    have FV : FrameV (TRIO.gexp M r L 0 0 n) σ :=
      ⟨sInv_std (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk hRN), hCN, hGN, hKD, hTD,
        hAD M ρ rk r L n σ rkN hctx, hTP M ρ rk r L n σ rkN hctx⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      hF _ σ (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk hRN) FV
    exact ⟨tplow_of_lf FV h1 h2, absDW_of_lf FV h3 h4, tplon_of_lf FV h1 h5 h6⟩
  exact ⟨fun M ρ rk r L n σ rkN hctx => (key M ρ rk r L n σ rkN hctx).1,
    fun M ρ rk r L n σ rkN hctx => (key M ρ rk r L n σ rkN hctx).2.1,
    fun M ρ rk r L n σ rkN hctx => (key M ρ rk r L n σ rkN hctx).2.2⟩

/-- **`hExp` for `t = 0` without `NoGapP`**: `AbsD`・`AbsU` of `N` are explicit hypotheses (NoGapP is false on
standard matrices, groupA 2026-10-12). -/
theorem hExp_t0_topA
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hAD : T0Field AbsD) (hAU : T0Field AbsU) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hCut : T0CutResG) (hTPR : T0TPLoRes) (hAUWR : T0AbsUWRes) (hADNR : T0AbsDNRes)
    (hD1 : T0ShCutRes PTP1) (hD1W : T0ShCutRes PTP1W) (hDT : T0ShCutRes PTrig)
    (hG1 : T0ShGRes PTP1) (hG1W : T0ShGRes PTP1W) (hGT : T0ShGRes PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hVR hz hs0 n hn2
  have hIV := t0IVRes_holds
  have hFF := t0_frameFieldsF hFrm hAD (t0_tplo hTPR)
  have H2 : T0RestNV := ⟨hAD, hAU, t0_tplo hTPR, t0_absUW hAUWR, hFF.2.2, t0_absDN hADNR, hFF.1, hFF.2.1⟩
  have hDF := t0DF_of hPH hCut hIV hM hS I R hVR
  apply hExp_t0A hDF (t0_vsmallF_at (t0VSD_at hDF.toH) hIV) H2
    (t0RWResAt_of2 PTP1 (fun _ _ _ _ _ hc hBc hl hA ht => ptp1_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptp1_prefix hlt hpre) (fun _ _ _ _ _ h1 h2 => ptp1_gt h1 h2) hD1 hG1
      (hPH M ρ rk hM hS I R) hDF)
    (t0RWResAt_of2 PTP1W (fun _ _ _ _ _ hc hBc hl hA ht => ptp1w_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptp1w_prefix hlt hpre) (fun _ _ _ _ _ h1 h2 => ptp1w_gt h1 h2) hD1W hG1W
      (hPH M ρ rk hM hS I R) hDF)
    (t0RWResAt_of2 PTrig (fun _ _ _ _ _ hc hBc hl hA ht => ptrig_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptrig_prefix hlt hpre) (fun _ _ _ _ _ h1 h2 => ptrig_gt h1 h2) hDT hGT
      (hPH M ρ rk hM hS I R) hDF)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩


theorem hExp_t0B {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hOTD : T0DFH M ρ)
    (hVSF : ∀ r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → VSmallF (TRIO.gexp M r L 0 0 n) σ) (hRest : T0RestNV)
    (hRW : ∀ N σ, Std N → N ≠ SRO → Cons N σ → GoodOT N σ → TP1C N σ ∧ TP1WC N σ ∧ TrigOmC N σ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0)
    (hT : ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
      ∃ τ rkT, Inv3 (M.take j) τ rkT ∧ Res3A (M.take j) τ rkT)
    (n : Nat) (hn2 : 2 ≤ n) :
    ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shape I hz hs0
  rw [hexp n]
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have hcore := t0_core hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (fun n hn σ hCN => ⟨fun i hi hd => ((hOTD r L hlen hL hp he1 n hn σ hCN i hi).1 hd).1,
      t0_vsmallNewN hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.cons I.good I.rank hn hCN⟩)
    n hn2
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN, hRWN, hpN, _⟩ := hcore
  -- the prefix `M.take x`
  have hTx : ∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT := by
    apply hT (r + L) (by omega)
    · intro h
      have hRk1 : Rk (M.take (r + L)) rk :=
        rk_take (by omega) I.rank (by
          have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
          rwa [show M.length - 1 = r + L by omega] at this)
      rw [h] at hRk1; exact not_val_SRO _ (val_of_rk hRk1)
    · intro h
      have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left (by omega)] at this
      simp only [List.length_nil] at this; omega
  have hctx : T0Ctx M ρ rk r L n σ rkN :=
    ⟨hM, hS, I, R, hlen, hL, hp, he1, hTx, hn2, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN⟩
  have hvs := hVSF r L n σ rkN hctx
  have had := hRest.ad _ _ _ _ _ _ _ _ hctx
  have hau := hRest.au _ _ _ _ _ _ _ _ hctx
  have htplo := hRest.tplo _ _ _ _ _ _ _ _ hctx
  have hauw := hRest.auw _ _ _ _ _ _ _ _ hctx
  have htplon := hRest.tplon _ _ _ _ _ _ _ _ hctx
  have hadn := hRest.adn _ _ _ _ _ _ _ _ hctx
  have htplow := hRest.tplow _ _ _ _ _ _ _ _ hctx
  have hadw := hRest.adw _ _ _ _ _ _ _ _ hctx
  -- the rewriting-frame fields, with the prefix valuation `drop1`
  have hRk1 : Rk (M.take (r + L)) rk :=
    rk_take (by omega) I.rank (by
      have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
      rwa [show M.length - 1 = r + L by omega] at this)
  obtain ⟨τ, rkT, IT, _⟩ := hTx
  have hAg : ∀ i, i < (M.take (r + L)).length →
      τ.o i = (drop1 M (r + L) rk).o i ∧ τ.v i = (drop1 M (r + L) rk).v i :=
    agree_of_cons IT.cons (cons_of_rk hRk1) IT.rank
  obtain ⟨htp1, htp1w, htrig⟩ := hRW _ σ (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk hRN) hCN hGN.toOT
  have V : Inv3V (TRIO.gexp M r L 0 0 n) σ rkN := ⟨hCN, hGN, hRN, hvs, hFCN, hFON, hKDN, hTDN, had, hau, htp1,
    htplo, htp1w, htplow, hauw, hadw, htrig, htplon, hadn, rootS_of_good hCN hGN, hpN⟩
  exact ⟨σ, rkN, V⟩

/-- **`hExp` for `t = 0` with the rewriting-frame fields of `N` from PH3c of `N`** (drop-fix's V3TP1Cut:
`tp1C_of_ph3c`・`tp1WC_of_ph3c`・`trigOmC_of_ph3c`). No shadow residual of `t = 0`. -/
theorem hExp_t0_topB
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hAD : T0Field AbsD) (hAU : T0Field AbsU) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hPHN : ∀ N σ, Std N → N ≠ SRO → Cons N σ → GoodOT N σ →
      PH3c N σ ∧ TP1Leaf N σ ∧ TP1WLeaf N σ ∧ TrigCut N σ)
    (hCut : T0CutResG) (hTPR : T0TPLoRes) (hAUWR : T0AbsUWRes) (hADNR : T0AbsDNRes) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hVR hz hs0 n hn2
  have hIV := t0IVRes_holds
  have hFF := t0_frameFieldsF hFrm hAD (t0_tplo hTPR)
  have H2 : T0RestNV := ⟨hAD, hAU, t0_tplo hTPR, t0_absUW hAUWR, hFF.2.2, t0_absDN hADNR, hFF.1, hFF.2.1⟩
  have hDF := t0DF_of hPH hCut hIV hM hS I R hVR
  apply hExp_t0B hDF.toH (t0_vsmallF_at (t0VSD_at hDF.toH) hIV) H2
    (fun N σ hN hNS hC hO => by
      obtain ⟨h1, h2, h3, h4⟩ := hPHN N σ hN hNS hC hO
      exact ⟨tp1C_of_ph3c hC hO h1 h2, tp1WC_of_ph3c hC hO h1 h3, trigOmC_of_ph3c hC hO h1 h4⟩)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

end Ytosk
