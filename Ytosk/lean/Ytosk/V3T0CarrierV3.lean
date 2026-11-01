/-
The t=0 carried output on Inv3V3, including Bad2, from the repaired PV2 engine.
Residual inputs are explicit: T0AbsW, the seed facts, and T0DF. VSmallF is proved by the PV2 consumers.
The remaining frame fields are supplied separately by V3EngineV3.
-/
import Ytosk.V3T0ConsumersV3

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2

/-- The actual t=0 engine supplies all carried fields; it does not construct or assume any Inv3V2 valuation. -/
theorem t0_carrierV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (I : Inv3V3 M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0)
    (D : DropV3 M ρ rk)
    (I1 : Inv3V3 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hAbW : T0AbsW M r L ρ)
    (hSd : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)
    (hDF : T0DF M ρ) :
    ∀ n, 2 ≤ n → ∃ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ ∧
      Rk (TRIO.gexp M r L 0 0 n) rkN ∧ Good3 (TRIO.gexp M r L 0 0 n) σ ∧
      CarryV3 (TRIO.gexp M r L 0 0 n) σ ∧ RootP (TRIO.gexp M r L 0 0 n) σ ∧
      root (TRIO.gexp M r L 0 0 n) σ < root M ρ := by
  intro n hn2
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := S.r12 _ he1
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i := by
    have h := D.1
    rwa [show M.length - 1 = r + L from by omega] at h
  have hRk1 : Rk (M.take (r + L)) rk := I1.rank
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := I1.cons
  have hVT : ValInv (M.take (r + L)) ρ' := ⟨I1.good, I1.vs, I1.fc, I1.fo, I1.kd, I1.td⟩
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN, _, hpN, hot, hlt⟩ :=
    t0_coreG2 hlen hL S.r0p S.z2 S.sibDec S.z1c S.uat S.uab (sInvXJ_std hM hS).2
      (sInvXJ_std hM hS).1.loc.2.2.2 S.r12 S.bumpE2 S.r01 S.e00 hp he1 I.cons I.good I.rank
      I.vs I.fc I.fo hdrop hVT I.kd I.td hAbW hSd I.rootS I.rootP
      (fun n hn g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn hg hc)
      (fun n hn σ hCN => ⟨fun i hi hd => ((hDF r L hlen hL hp he1 n hn σ hCN i hi).1 hd).1,
        t0_vsmallNewN hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 I.cons I.good I.rank hn hCN⟩)
      n hn2
  have hDC : T0DropF2 M ρ rk := by
    refine ⟨D.1, ?_⟩
    have h := hVT
    rwa [show M.length - 1 = r + L from by omega]
  have hctx : T0CtxC2 M ρ rk r L n σ rkN :=
    ⟨hM, hS, coreC S I, hDC, hlen, hL, hp, he1, trivial, hn2, hCN, hRN, hGN,
      hFON, hFCN, hKDN, hTDN⟩
  have hvs := t0_vsmallF_atC2 (t0VSD_atC2 hDF.toH) t0IVResC_holds r L n σ rkN hctx
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict02 (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop hx2 hp hnx
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp S.r0p S.z2 S.sibDec S.z1c S.uat S.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp S.r0p S.z2 S.sibDec S.z1c S.uat S.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => ⟨(hvC i hiN).1 (fun h => by omega), (hvC i hiN).2 (fun h => by omega)⟩
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2 I.cons I.good
  have hlt0 : ρ'.o r < ρ.o r :=
    hD true r (depLike_r hlen hL hp hx2 (depLike_depX M (r + L))) (by omega)
  have hO'le : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := (hdrop r (by omega)).1.2
    have h := hlt0
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
    intro s' y' hs hne
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    have hv'ot := (hdrop r (by omega)).2.2
    rw [sf_ot hv'ot] at hy0
    have hCv : ChgX M (r + L) false r := by
      by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
    have hT := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hCv).1 rfl (by omega)
    have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
    rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
  have hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d := fun d hd hdd =>
    le_of_lt ((hDF r L hlen hL hp he1 n hn2 σ hCN d hd).1 hdd).2.1.1
  have hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z := by
    intro d hd hne
    have hdv : DepX M (r + L) false d := by
      by_contra hn'; exact hne ((hoffD d hd).2 hn')
    exact ((hDF r L hlen hL hp he1 n hn2 σ hCN d hd).1 (DepX.ov hdv)).2.2.2.1 hne
  have hLastN : ∀ g, par M 0 r = some g → Counted M g r → Counted N g (r + (n - 1) * L) :=
    fun g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn2 hg hc
  have hph : PH3cG N σ := G.ph3c_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT I.ph I1.ph hσB hoffD hσmid hσlast hLastN hC1 I1.good (le_of_lt hlt0) hO'le
    hy' hdl hss
  have hfc3 : FC3 N σ := G.fc3_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT I.fc3 I1.fc3 hσB hoffD hσmid hσlast hLastN hC1 I1.good (le_of_lt hlt0) hO'le
    hy' hdl hss
  have hvra : VSmallRAll N σ := vsmallRAll_N_t02 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT hC1 hRk1 I1.good hdrop hσB hoffD hσmid hσlast hLastN hO'le hy' hdl hss I.vra
  exact ⟨σ, rkN, hCN, hRN, hGN, ⟨hvs, hFCN, hFON, hKDN, hTDN, hph, hfc3, hvra⟩, hpN, hlt⟩

/-- A local t=0 input, at the actual parent and copy length of a StepCtx3 matrix. -/
def T0AtV3 (P : Mat → Valn → Nat → Nat → Prop) : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 → P M ρ r L

/-- The local D comparisons are produced by the PV2 t=0 induction.
The two structural side conditions are the repaired shape lemma and the
already unconditional T0IVResC_holds; they are not extra residuals. -/
theorem t0DF_of_seed_inputs
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsW M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtx3 M ρ rk) : T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have IC := coreC C.S C.I
  have D := C.drop (show 2 ≤ M.length from by omega)
  have I1 := C.pre (r + L) (by omega) (by omega)
  have hVT : ValInv (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨I1.good, I1.vs, I1.fc, I1.fo, I1.kd, I1.td⟩
  have hDC : T0DropF2 M ρ rk := by
    refine ⟨D.1, ?_⟩
    rwa [show M.length - 1 = r + L from by omega]
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i := by
    have h := D.1
    rwa [show M.length - 1 = r + L from by omega] at h
  have h := t0_otdG2 hlen hL C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat C.S.uab
    (sInvXJ_std C.std C.ne).2 (sInvXJ_std C.std C.ne).1.loc.2.2.2
    C.S.r12 C.S.bumpE2 C.S.r01 C.S.e00 hp he1 C.I.cons C.I.good C.I.rank
    C.I.vs C.I.fc C.I.fo hdrop hVT C.I.kd C.I.td
    (hAbs M ρ rk C r L hlen hL hp he1) (hSeeds M ρ rk C r L hlen hL hp he1) C.I.rootS C.I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uab C.S.r12 hn hg hc)
    (C.I.vra.toLast.toP (r + L) r) C.I.ph
    (t0_shape3C2 C.std C.ne IC hDC hlen hL hp he1)
    (t0IVResC_holds M ρ rk r L C.std C.ne IC hlen hL hp he1) n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩

/-- The t=0 carrier output reduced to two separate remaining needs:
weak absorption and seeds. Local D comparisons and VSmallF are proved above.
No other carried field or old frame invariant is an assumption here. -/
theorem expCore0_of_seeds
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsW M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)) : ExpCoreV3 0 := by
  intro M ρ rk C hz hs n hn
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shapeS C.S hz hs
  have hl : 2 ≤ M.length := by omega
  have I1 := C.pre (r + L) (by omega) (by omega)
  obtain ⟨σ, rkN, hCN, hRN, hGN, K, hP, hlt⟩ :=
    t0_carrierV3 C.std C.ne C.S C.I hlen hL hp he1 (C.drop hl) I1
      (hAbs M ρ rk C r L hlen hL hp he1) (hSeeds M ρ rk C r L hlen hL hp he1)
      (t0DF_of_seed_inputs hAbs hSeeds C) n hn
  rw [hexp n]
  exact ⟨σ, rkN, hCN, hRN, hGN, K, hP, hlt⟩

end Ytosk.V3Main
