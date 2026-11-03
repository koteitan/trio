/- t=0 carrier route using upgrade-aware absorption without an assumed target GoodOT. -/
import Ytosk.V3T0CarrierV3
import Ytosk.V3T0CoreAbsU
import Ytosk.V3T0ConsumerAbsU
import Ytosk.V3T0OTDAbsU0

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfT2X

theorem t0_vsmallF_atC2U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hD : ∀ n σ rkN, T0CtxC2 M ρ rk r L n σ rkN →
      ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
        ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hIV : T0IVResC) :
    ∀ n σ rkN, T0CtxC2 M ρ rk r L n σ rkN → VSmallF (TRIO.gexp M r L 0 0 n) σ := by
  intro n σ rkN hctx
  obtain ⟨hM, hS, I, D, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDV := D.vt
  have hDP := D.po
  rw [show M.length - 1 = r + L by omega] at hDV hDP
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' := hDV
  have hdrop : ∀ k, k < r + L → PO ρ ρ' k ∧ PV2 M ρ ρ' k := hDP
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
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
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good
  have hFO := qvs_of_vsmallF I.cons I.good I.vs
  have hFOT := qvs_of_vsmallF hC1 hVT.g hVT.vs
  apply vsmallF_of_qvs hCN hGN
  apply frameQ_N_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
    (ρ' := ρ') hFO hFOT hσB hoffD
  · -- the frame of `g` with `r` counted
    intro g hg hgc
    have hgr : g < r := par_lt M 0 r g hg
    have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := by
      apply (hoffD g hgr).2
      intro hdv
      exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
        (by omega) hdv hrg hgc
    apply g_frames_t0J hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
      hg hgc (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast
      (counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hgc)
      (fun Lc c R hCL => hFO g (by omega) Lc c R hCL)
    intro Lc j cv hCL hcv s y hsy g' hg'
    -- the state grows with the middle copies
    have hgM : g < M.length := by omega
    obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hgM
    rw [hCL] at hsM hpM
    simp only [List.map_append, List.map_singleton] at hsM hpM
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hsO : Single (omid M r L ρ) :=
      ⟨isOT_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN,
        by rw [hom]; exact ⟨_, _, rfl⟩⟩
    have hmono : spArg (ρ.v g) z (sumN (Lc.map ρ.o)) ≤
        spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      have hs : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), Single t := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hsM t (List.mem_append_left _ ht)
        · rw [(List.mem_replicate.mp ht).2]; exact hsO
      have hpw : (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := by
        have hp1 := List.pairwise_append.mp hpM
        refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
        intro a ha b hb
        rw [(List.mem_replicate.mp hb).2]
        exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
      rw [sumN_append_dec hs hpw, spArg_app]
      apply le_spArg
      exact isOT_sumN _ (fun t ht => (hs t (List.mem_append_right _ ht)).1)
    have hold : ∀ g'' ∈ comps (ρ.v g) (ρ.v r), g'' ≤ psi (ρ.v r) z z ∨
        g'' ≤ spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      intro g'' hg''
      rcases I.vs g hgM Lc r [] hCL g'' hg'' with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans h hmono)
    rcases hcv with rfl | ⟨rfl, hj0⟩
    · rw [hom] at hsy; simp only [psi.injEq] at hsy
      rw [← hsy.1] at hg' ⊢
      exact hold g' hg'
    · have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
      obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
      rw [hsy] at hy0; simp only [psi.injEq] at hy0
      have hv'ot := hVT.g.ot_v r hrT
      rw [sf_ot hv'ot] at hy0
      rw [hy0.1] at hg' ⊢
      by_cases hv : ρ'.v r = ρ.v r
      · rw [hv] at hg' ⊢; exact hold g' hg'
      -- the drop at `r`: `x` is a counted child of `r`, so `v′(r) ◁ v(r)`
      obtain ⟨hPO, hPV⟩ := hdrop r (by omega)
      -- the weak case: the components of `v′(r)` at the level `v(g)` are countable (those dominated by
      -- `v(g)` at its own level do not exist)
      rcases hPV.1 with hvE | ⟨hWk, hWC, _⟩
      swap
      · left
        rcases (hWC.wcs2 hWk.2.1 hg) (ρ.v g) (fun h => lt_irrefl' _ (show ρ.v g < ρ.v g from h)) g' hg' with
          h1 | ⟨d, hd, _⟩
        · exact h1
        · rw [comps_self_nil (I.good.ot_v g hgM)] at hd; simp at hd
      have hlv : Lhd z (ρ'.v r) (ρ.v r) := by
        rcases hvE with h | h
        · exact absurd h hv
        · exact h
      -- a changed `v(r)`: `o′(r) = ψ_{v′(r)}(0)`
      have hyz : y = z := by
        have hCv : ChgX M (r + L) false r := by
          by_contra hn'; exact hv ((hoff r (by omega)).2 hn')
        have hT := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hCv).1 rfl (by omega)
        have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
        rw [hsy, hy0.1] at ho; simp only [psi.injEq] at ho; exact ho.2.1
      obtain ⟨d, hd, hgd⟩ := hlv.2 (ρ.v g) (ρ.v r) hlv.1 (le_refl _) g' hg'
      rcases List.mem_append.mp hd with hd | hd
      swap
      · simp [Gc, comps] at hd
        rw [hd] at hgd
        exact Or.inr (le_trans hgd (z_le _))
      rcases I.vs g hgM Lc r [] hCL d hd with hdo | hdB
      swap
      · exact Or.inr (le_trans hgd (le_trans hdB hmono))
      set Bg := spArg (ρ.v g) z (sumN (Lc.map ρ.o)) with hBg
      by_cases hB0 : Bg = z ∧ j = 0
      · -- no middle copy root counts: the old frame does not rewrite at `r` (`T0IVResC`), and `o′(r) ◁ o(r)`
        obtain ⟨Y0, hY0⟩ : ∃ Y0, ρ.o r = psi (ρ.v r) (app Y0 one) z := ⟨_, hor⟩
        have hnt := hIV M ρ rk r L hM hS I hlen hL hp he1 n hn2 g hg hgc (hj0 hB0.2) Lc hCL _ _ hY0
        have hsMc : ∀ d ∈ CL M g, Single (ρ.o d) := fun d hd => single_o I.cons I.good
          (mem_children (cl_mem_children hd)).2
        have hformM := o_last_form I.cons hgM (I.good.ot_v g hgM) hCL hsMc
          (by have := (cl_vals I.cons I.good hgM).2; exact this) hY0
        have hot := I.good.ot_o g hgM
        rw [hformM] at hot
        unfold step at hot
        rw [if_neg (by rw [← hBg, hB0.1]; rw [← hBg, hB0.1] at hnt; exact hnt)] at hot
        rw [← hBg, hB0.1] at hot
        have hot2 : isOT (psi (ρ.v g) (psi (ρ.v r) (app Y0 one) z) z) := hot
        rw [← hY0] at hot2
        have hl0 : LhdE (ρ'.o r) (ρ.o r) := by
          rcases hPO.1 with h | ⟨_, ⟨w, hw⟩ | hnl⟩
          · exact h
          · rw [hY0] at hw; simp only [psi.injEq] at hw
            exact absurd hw.2.1 (fun h => by cases Y0 <;> simp [app, one] at h)
          · exact absurd (Or.inr hlv) hnl
        have hot' := ot_parent_lhd hot2 (single_o hC1 hVT.g hrT).1 hl0
        rw [hsy, hy0.1, hyz] at hot'
        by_cases hsa : ρ'.v r < ρ.v g
        · rw [comps_nil_of_lt hv'ot hsa] at hg'; simp at hg'
        · left
          apply le_of_lt
          apply ((isOT_psi_iff).mp hot').2.2.2.2 g'
          rw [comps_psi_z_of_ge hsa]
          simp [hg']
      · -- the state of `N` is at least `Ω_{v(r)}`
        right
        refine le_trans hgd (le_trans hdo ?_)
        have hs : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), Single t := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hsM t (List.mem_append_left _ ht)
          · rw [(List.mem_replicate.mp ht).2]; exact hsO
        have hpw : (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := by
          have hp1 := List.pairwise_append.mp hpM
          refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
          intro a ha b hb
          rw [(List.mem_replicate.mp hb).2]
          exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
        have hsd := sumN_dec _ hs hpw
        have hge : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), psi (ρ.v r) z z ≤ t := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · have := (List.pairwise_append.mp hpM).2.2 t ht (ρ.o r) (by simp)
            refine le_trans ?_ this
            rw [hor]; exact psi_le_psi_arg (z_le _)
          · rw [(List.mem_replicate.mp ht).2, hom]; exact psi_le_psi_arg (z_le _)
        have hne : Lc.map ρ.o ++ List.replicate j (omid M r L ρ) ≠ [] := by
          intro he
          apply hB0
          rw [List.append_eq_nil_iff, List.map_eq_nil_iff, List.replicate_eq_nil_iff] at he
          refine ⟨?_, he.2⟩
          rw [hBg, he.1]; rfl
        apply le_of_summands_ge
        · apply spArg_ne_z
          right
          intro hz
          have h1 := hsd.2
          rw [hz] at h1
          simp [summands] at h1
          exact hne (by simp [h1.1, h1.2])
        · apply spArg_summands_ge ⟨ρ.v r, z, rfl⟩ _ z hsd.1
          · rw [hsd.2]; exact hge
          · simp [summands]
  · -- the `D` frames before `r`
    intro i hi hng Lc c R hCL hDc s y hsy g' hg'
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
    have hcN : c < N.length := by rw [hlN]; omega
    have he := o_cl_eq hCN hGN hcN
    rw [hsy] at he; simp only [psi.injEq] at he
    rw [he.1] at hg' ⊢
    by_cases hv : σ.v c = ρ.v c
    · rw [hv] at hg' ⊢
      exact I.vs i (by omega) Lc c R hCL g' hg'
    · exact hD n σ rkN hctx i Lc c R hi hcr hCL hv g' hg'


theorem t0_carrierV3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (I : Inv3V3 M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0)
    (D : DropV3 M ρ rk)
    (I1 : Inv3V3 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hAbW : T0AbsWU M r L ρ)
    (hSd : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)
    (hDF : T0DFU0 M ρ r L) :
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
    t0_coreG2U hlen hL S.r0p S.z2 S.sibDec S.z1c S.uat S.uab (sInvXJ_std hM hS).2
      (sInvXJ_std hM hS).1.loc.2.2.2 S.r12 S.bumpE2 S.r01 S.e00 hp he1 I.cons I.good I.rank
      I.vs I.fc I.fo hdrop hVT I.kd I.td hAbW hSd I.rootS I.rootP
      (fun n hn g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn hg hc)
      (fun n hn σ hCN => ⟨fun i hi hd => (((hDF n hn σ hCN i hi).1 hd).1).2,
        t0_vsmallNewN hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 I.cons I.good I.rank hn hCN⟩)
      n hn2
  have hDC : T0DropF2 M ρ rk := by
    refine ⟨D.1, ?_⟩
    have h := hVT
    rwa [show M.length - 1 = r + L from by omega]
  have hctx : T0CtxC2 M ρ rk r L n σ rkN :=
    ⟨hM, hS, coreC S I, hDC, hlen, hL, hp, he1, trivial, hn2, hCN, hRN, hGN,
      hFON, hFCN, hKDN, hTDN⟩
  have hvs := t0_vsmallF_atC2U (t0VSD_atC2U hDF.toDFU) t0IVResC_holds n σ rkN hctx
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
    le_of_lt (PX.lt (((hDF n hn2 σ hCN d hd).1 hdd).1))
  have hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z := by
    intro d hd hne
    have hdv : DepX M (r + L) false d := by
      by_contra hn'; exact hne ((hoffD d hd).2 hn')
    exact ((hDF n hn2 σ hCN d hd).1 (DepX.ov hdv)).2.2.1 hne
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

/-- Produce the no-GoodOT t=0 D output from the upgrade-aware local residuals. -/
theorem t0DF_of_seed_inputsU
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtx3 M ρ rk) :
    ∀ r L, r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r →
      entry M 1 (r + L) = 0 → T0DFU0 M ρ r L := by
  intro r L hlen hL hp he1
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
  exact t0_otdG2U0 hlen hL C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat C.S.uab
    (sInvXJ_std C.std C.ne).2 (sInvXJ_std C.std C.ne).1.loc.2.2.2
    C.S.r12 C.S.bumpE2 C.S.r01 C.S.e00 hp he1 C.I.cons C.I.good C.I.rank
    C.I.vs C.I.fc C.I.fo hdrop hVT C.I.kd C.I.td
    (hAbs M ρ rk C r L hlen hL hp he1) (hSeeds M ρ rk C r L hlen hL hp he1) C.I.rootS C.I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uab C.S.r12 hn hg hc)
    (C.I.vra.toLast.toP (r + L) r) C.I.ph
    (t0_shape3C2 C.std C.ne IC hDC hlen hL hp he1)
    (t0IVResC_holds M ρ rk r L C.std C.ne IC hlen hL hp he1)

/-- The t=0 engine entry using upgrade-aware absorption and seeds. -/
theorem expCore0_of_seedsU
    (hAbs : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)) : ExpCoreV3 0 := by
  intro M ρ rk C hz hs n hn
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shapeS C.S hz hs
  have hl : 2 ≤ M.length := by omega
  have I1 := C.pre (r + L) (by omega) (by omega)
  obtain ⟨σ, rkN, hCN, hRN, hGN, K, hP, hlt⟩ :=
    t0_carrierV3U C.std C.ne C.S C.I hlen hL hp he1 (C.drop hl) I1
      (hAbs M ρ rk C r L hlen hL hp he1) (hSeeds M ρ rk C r L hlen hL hp he1)
      (t0DF_of_seed_inputsU hAbs hSeeds C r L hlen hL hp he1) n hn
  rw [hexp n]
  exact ⟨σ, rkN, hCN, hRN, hGN, K, hP, hlt⟩

end Ytosk.V3Main
