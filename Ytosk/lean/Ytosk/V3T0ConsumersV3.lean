/-
PV2 versions of the remaining t=0 invariant consumers from V3T0C.
Only the drop conclusion is weakened. In the VSmallF weak branch the new bound
is already g <= psi(w') rather than g < Omega(1); that is exactly the goal.
The old structural/value core Inv3C contains none of the refuted V2 fields.
-/
import Ytosk.V3EngineV3

namespace Ytosk.V3Main
open T
set_option linter.unusedSectionVars false

structure T0DropF2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  po : ∀ k, k < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) k ∧ PV2 M ρ (drop1 M (M.length - 1) rk) k
  vt : ValInv (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)

def T0CtxC2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat) (σ : Valn)
    (rkN : Bool → Nat → Nat) : Prop :=
  Std M ∧ M ≠ SRO ∧ Inv3C M ρ rk ∧ T0DropF2 M ρ rk ∧ r + L + 1 = M.length ∧ 0 < L ∧
    par M 0 (r + L) = some r ∧ entry M 1 (r + L) = 0 ∧ True ∧
    2 ≤ n ∧ Cons (TRIO.gexp M r L 0 0 n) σ ∧ Rk (TRIO.gexp M r L 0 0 n) rkN ∧
    Good3 (TRIO.gexp M r L 0 0 n) σ ∧ FrameOT (TRIO.gexp M r L 0 0 n) σ ∧
    FrameClosed (TRIO.gexp M r L 0 0 n) σ ∧
    BumpKidsDec (TRIO.gexp M r L 0 0 n) σ ∧ BumpTermDec (TRIO.gexp M r L 0 0 n) σ

theorem t0_shape3C2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3C M ρ rk) (D : T0DropF2 M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) :
    ∀ g, par M 0 r = some g → ∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z := by
  intro g hg s' y' hs hne hhi
  obtain ⟨hSX, hJ⟩ := sInvXJ_std hM hS
  have hBL : BumpLeaf M := hSX.loc.2.2.2
  have hx : r + L + 1 = M.length := hlen
  have hVT0 := D.vt
  rw [show M.length - 1 = r + L by omega] at hVT0
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hVT : ValInv (M.take (r + L)) ρ' := hVT0
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hgr : g < r := par_lt M 0 r g hg
  have hrM : r < M.length := by omega
  have hs' : s' = ρ'.v r := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hVT.g.ot_v r hrT)]
  have hCv : ChgX M (r + L) false r := by
    by_contra hn'; apply hne; rw [hs']; exact (hoff r (by omega)).2 hn'
  rw [lt_theta_iff] at hhi ⊢
  have hAgr : Anc0 M g r := Anc0.step hg (Anc0.refl g)
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  by_cases hP : par M 1 r = some g
  · -- `s′ = v′(r) > v′(g) = v(g)`
    have hng : ¬ ChgX M (r + L) false g := fun h =>
      (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab h).1 rfl (by omega) |>.2.2 r (by omega) hP
    have hvg : ρ'.v g = ρ.v g := (hoff g (by omega)).2 hng
    have h1r : entry (M.take (r + L)) 1 r ≠ 0 := by
      rw [entry_take M 1 (by omega)]; have := par1_entry_lt hP; omega
    have hPT : par (M.take (r + L)) 1 r = some g := by rw [par_take M 1 r (by omega)]; exact hP
    have hlt := v_par1_lt hC1 hVT.g hRk1 (rk false r) r g (le_refl _) hrT h1r hPT
    rw [hs', ← hvg]
    exact not_le.mpr hlt
  · exfalso
    apply hhi
    rcases chgX_false_cases hCv rfl with ⟨hrx, hup⟩ | ⟨h1, _, hcb⟩ | ⟨m, hm, hcm⟩ | ⟨k, hu, hck⟩ |
        ⟨j, h1, h2, hj, hjb⟩
    · -- `r = x − 1` lost its upgrade: the target is an ancestor `k`, and `v(r) = v(k) ≤ v(g)`
      have hL1 : L = 1 := by omega
      rw [← hrx] at hup
      obtain ⟨k, hu⟩ := Option.ne_none_iff_exists'.mp hup
      obtain ⟨m, hm1, _, hek, hcase⟩ := t0s_upg_facts hu
      have h12 := upg_e12 hu
      have h20 : entry M 2 r = 0 := by have := I.z2 r; omega
      rcases hcase with hk1 | ⟨hkA, hkr⟩
      · exfalso
        rw [hk1, show r + 1 = r + L by omega, he1] at hek
        exact h12.1 hek.symm
      · have hkg : Anc0 M k g := anc0_par hkA (by omega) hg
        have hsp := (upg_anc_spine I.r0p I.z2 I.uab I.be hJ I.cons I.good I.rank hrM hu hkA hkr g hkg hAgr
          (by omega)).2
        have hv := v_upg_eq I.cons hrM h12.1 h20 hu
          (by rw [hm1]; exact I.good.ot_v m (by have := par_lt M 1 r m hm1; omega))
          (fun j _ _ k' hk' => I.good.ot_o k' (mem_children hk').2)
        rw [hv]; exact hsp
    · -- `x` is not a bump child of `r` (its row 1 is `0`)
      have := e1_of_col hcb
      rw [he1] at this; exact absurd this.symm h1
    · -- `v(P_1 r)` does not change (`TopC`)
      have hmr := par_lt M 1 r m hm
      exact absurd hm ((chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hcm).1 rfl (by omega) |>.2.2 r
        (by omega))
    · -- an upgrade of `r` with a changed target: impossible
      obtain ⟨_, _, _, _, hcase⟩ := t0s_upg_facts hu
      rcases hcase with hk1 | ⟨hkA, hkr⟩
      · subst hk1
        have := leaf_of_upg_next I.r0p hu (r + L) (Anc0.step hp (Anc0.refl r))
        omega
      · exact absurd (no_anc_upg hx I.r0p I.z2 I.sd I.z1 I.uat I.uab
          ((chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hck).1 rfl (by omega)) (by omega) hu hkA hkr)
          (fun h => h)
    · -- a bump child of `r`: then `r` is the bump child of `g`, against `BumpLeaf`
      have hge : entry M 1 r ≤ entry M 1 g := by
        by_contra hlt
        exact hP (par1_of_child hg (by omega))
      have hle := hJ r g h2 hg
      have hr2 : entry M 2 r = 1 := by have := I.z2 r; omega
      have hcolr : col M r = bump M g := by
        rw [col_eq_entries, I.r0p r g hg, hr2]
        unfold bump; congr 2; omega
      have hrc : r ∈ children M g := mem_children_iff.mpr ⟨hrM, hg⟩
      have hje1 : entry M 1 j = entry M 1 r := e1_of_col hjb
      have hje2 : entry M 2 j = 1 := e2_of_col hjb
      have := (hBL g r j hrc hcolr hj (by omega)).1
      omega

theorem t0VSD_atC2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hDF : T0DFH M ρ) :
    ∀ r L n σ rkN, T0CtxC2 M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  intro r L n σ rkN hctx i Lc c R hi hc hCL hv
  obtain ⟨hM, hS, I, _, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hdv : DepX M (r + L) false c := by
    by_contra hd
    apply hv
    rw [(hvD c (by rw [hlN]; omega)).2 (fun h' => hd h'.2), tau_v_lt hc]
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hlv : Lhd z (σ.v c) (ρ.v c) := ((hDF r L hlen hL hp he1 n hn2 σ hCN c hc).2 hdv).2
  have hvcot : isOT (σ.v c) = true := hGN.ot_v c hcN
  have hiM : i < M.length := by omega
  have hcM : c < M.length := by omega
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hclc : CL M c = [] := cl_nil_of_depv' hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2
    I.cons I.good hc hdv
  have hoM : ρ.o c = psi (ρ.v c) z z := o_of_no_counted I.cons hcM (I.good.ot_v c hcM) (no_cnt_of_cl_nil hclc)
  -- `c` is the last counted child of `i`
  have hDi : DepX M (r + L) true i := DepX.ochild hcch hccnt.1 hccnt.2 (DepX.ov hdv)
  have hR : R = [] := by
    rcases hOS_t1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp i (by omega) hDi with
      ⟨_, hall⟩ | ⟨_, Lp, c0, Rch, hch, _, _, hRch, hLnd⟩
    · exfalso
      rcases hall c hcch with h | h
      · exact hccnt.1 h
      · exact hccnt.2 h
    have hcc0 : c = c0 := by
      have hc' := hcch
      rw [hch] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact absurd (DepX.ov hdv) (hLnd c h hccnt)
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exfalso
          rcases hRch c h with h' | h'
          · exact hccnt.1 h'
          · exact hccnt.2 h'
    subst hcc0
    obtain ⟨hLs, _⟩ := sib_order (children_sorted M i) hch
    have hsCL : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ (children_sorted M i)
    rw [hCL] at hsCL
    obtain ⟨_, hcR⟩ := sib_order hsCL rfl
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdch : d ∈ children M i := cl_mem_children hdCL
    have hdcnt : Counted M i d := by unfold CL at hdCL; simpa using (List.mem_filter.mp hdCL).2
    have hcd := hcR d hd
    rw [hch] at hdch
    rcases List.mem_append.mp hdch with h | h
    · have := hLs d h; omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · rcases hRch d h with h' | h'
        · exact hdcnt.1 h'
        · exact hdcnt.2 h'
  subst hR
  -- the old frame of `i`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hiM
  have hsMc : ∀ d ∈ CL M i, Single (ρ.o d) := fun d hd => single_o I.cons I.good
    (mem_children (cl_mem_children hd)).2
  have hformM := o_last_form I.cons hiM (I.good.ot_v i hiM) hCL hsMc hpM hoM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  have hpL := List.pairwise_append.mp hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) hpL.1
  have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), psi (ρ.v c) z z ≤ q := by
    apply spArg_summands_ge ⟨ρ.v c, z, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq
      have := hpL.2.2 q hq (ρ.o c) (by simp)
      rwa [hoM] at this
    · simp [summands]
  have hot := I.good.ot_o i hiM
  rw [hformM] at hot
  exact vs_changed_bound hvcot hlv hBc (I.vs i hiM Lc c [] hCL) hot

theorem t0_vsmallF_atC2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hD : ∀ r L n σ rkN, T0CtxC2 M ρ rk r L n σ rkN →
      ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
        ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hIV : T0IVResC) :
    ∀ r L n σ rkN, T0CtxC2 M ρ rk r L n σ rkN → VSmallF (TRIO.gexp M r L 0 0 n) σ := by
  intro r L n σ rkN hctx
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
    · exact hD r L n σ rkN hctx i Lc c R hi hcr hCL hv g' hg'

end Ytosk.V3Main
