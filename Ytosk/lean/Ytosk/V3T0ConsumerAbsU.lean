/- Port of the t=0 VSmall consumer to the upgrade-aware D output. -/
import Ytosk.V3T0ConsumersV3
import Ytosk.V3T0OTDAbsU
import Ytosk.V3AbsUpgFrame

namespace Ytosk.V3Main

open T Ytosk.WfT2X

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The `t=0` VSmall consumer with the upgrade-shaped allowance from `T0DFU`.
At a bad counted child, its row-1 parent level is discharged by `vs_changed_boundVG`. -/
theorem t0VSD_atC2U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hDF : T0DFU M ρ r L) :
    ∀ n σ rkN, T0CtxC2 M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  intro n σ rkN hctx i Lc c R hi hc hCL hv
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
  have hPX : PX M (fun j => BdXU M (TRIO.gexp M r L 0 0 n) ρ σ r j) ρ σ false c :=
    ((hDF n hn2 σ hCN hGN.toOT c hc).2 hdv)
  have hvcot : isOT (σ.v c) = true := hPX.2
  have hiM : i < M.length := by omega
  have hcM : c < M.length := by omega
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hclc : CL M c = [] := cl_nil_of_depv' hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2
    I.cons I.good hc hdv
  have hoM : ρ.o c = psi (ρ.v c) z z := o_of_no_counted I.cons hcM (I.good.ot_v c hcM) (no_cnt_of_cl_nil hclc)
  -- `c` is the last counted child of `i`.
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
  -- The old frame of `i`.
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
  rcases hPX.1 with hlv | ⟨hbad, hlv⟩
  · exact vs_changed_boundV (I.good.ot_v i hiM) hvcot (Ytosk.WfAbsW.lhd_mono_eta hlv) hBc
      (I.vs i hiM Lc c [] hCL) hot
  · obtain ⟨hclcM, hclcN, hpar | hsm⟩ := bdxu_F i c hbad hcCL
    · have hpc : par M 1 c = some i := hpar
      have hlv' : Lhd (ρ.v i) (σ.v c) (ρ.v c) := by simpa [hpc] using hlv
      exact vs_changed_boundV (I.good.ot_v i hiM) hvcot hlv' hBc (I.vs i hiM Lc c [] hCL) hot
    · have hcN0 : CL (TRIO.gexp M r L 0 0 n) c = [] := hclcN
      have hoN : σ.o c = psi (σ.v c) z z :=
        o_of_no_counted hCN hcN hvcot (no_cnt_of_cl_nil hcN0)
      exact vs_changed_boundVG (I.good.ot_v i hiM) hvcot hlv
        (by
          intro g hg
          have hlt := hsm (ρ.v i) g hg
          rw [hoN] at hlt
          exact hlt)
        hBc (I.vs i hiM Lc c [] hCL) hot

end Ytosk.V3Main
