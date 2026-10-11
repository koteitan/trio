/-
**3 行・t = 0: T0VSResD2（VSmallF の D の残り）を「c は i のただ一つの数える子」に帰着。**

v が変わる数える子 c が i のただ一つの数える子で v′(c) ≥ v(i) なら、N では o_N(c) = Ω_{v′(c)} で
o_N(i) = ψ_{v(i)}(Ω_{v′(c)})。これが標準形なので comps_{v(i)}(Ω_{v′(c)}) の成分は Ω_{v′(c)} より小さく、
comps_{v(i)}(last v′(c)) ⊆ comps_{v(i)}(v′(c)) もそうなる（t1-exp の S = 0 の場合と同じ）。
-/
import Ytosk.V3T0VS2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem comps_last_sub (u : T) (t : T) : ∀ g ∈ comps u (last t), g ∈ comps u t := by
  intro g hg
  rw [← init_app_last t, comps_app]
  exact List.mem_append_right _ hg

/-- **Residual**: a counted child `c` of `i` (both before `r`) whose `v` changes in `N` is the only counted
child of `i`, and `v_N(c) ≥ v(i)`. -/
def T0VSOnly : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      Lc = [] ∧ R = [] ∧ ¬ lt (σ.v c) (ρ.v i) = true

/-- **`T0VSResD2` from `T0VSOnly`** and the standard form of `o_N(i)`. -/
theorem t0VSResD2_of (h : T0VSOnly) : T0VSResD2 := by
  intro M ρ rk r L n σ rkN hctx i Lc c R hi hc hCL hv g hg
  obtain ⟨rfl, rfl, hge⟩ := h M ρ rk r L n σ rkN hctx i Lc c R hi hc hCL hv
  obtain ⟨_, _, I, _, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcM : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  -- the values of `N` before `r`
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 := cons_of_rk hRk1
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun j hj hd => (chg_off (show r + L + 1 = M.length from hlen) I.cons I.good hC1 hRk1 j hj).2 hd) hCN hRN
  have hvi : σ.v i = ρ.v i := by
    rw [(hvD i (by rw [hlN]; omega)).2 (fun h => ?_), tau_v_lt hi]
    exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
      (by omega) h.2 hcM hccnt
  have hdv : DepX M (r + L) false c := by
    by_contra hn'
    apply hv
    rw [(hvD c (by rw [hlN]; omega)).2 (fun h' => hn' h'.2), tau_v_lt hc]
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hvot : isOT (σ.v c) = true := hGN.ot_v c hcN
  have hoc : σ.o c = psi (σ.v c) z z :=
    o_N_noc' hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hc
      (cl_nil_of_depv' hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hc hdv) hvot
  -- the frame of `i` in `N` is `[c]`
  have hb : par M 0 r = some i → col M r = bump M i := by
    intro hig
    by_contra hb
    have hri : r ∈ CL M i := by
      unfold CL
      refine List.mem_filter.mpr ⟨mem_children_iff.mpr ⟨by omega, hig⟩, ?_⟩
      simpa using (show Counted M i r from ⟨hb, by rw [not_topped_r hlen hL hp hx2]; simp⟩)
    rw [hCL] at hri; simp at hri; omega
  have hCLN : CL (TRIO.gexp M r L 0 0 n) i = [c] := by
    rw [cl_N_eq hlen hL hp hn I.r0p I.z2 hx2 hn2 hi hb, hCL]; rfl
  have hoi := o_cl_eq hCN hGN (show i < (TRIO.gexp M r L 0 0 n).length by rw [hlN]; omega)
  rw [hCLN, List.map_singleton, hoc] at hoi
  have hsum : sumN [psi (σ.v c) z z] = psi (σ.v c) z z := by
    show sf (add z (psi (σ.v c) z z)) = _
    exact sf_ot (by simp [isOT, hvot, comps])
  have hsp : spArg (σ.v i) z (psi (σ.v c) z z) = psi (σ.v c) z z := by
    rw [spArg_cons]
    unfold step
    rw [if_neg (fun h => T.not_lt_z _ h.1)]
    rfl
  rw [hsum, hsp] at hoi
  have hot := hGN.ot_o i (by rw [hlN]; omega)
  rw [hoi] at hot
  have hall : ∀ g ∈ comps (σ.v i) (psi (σ.v c) z z), lt g (psi (σ.v c) z z) = true := by
    simp only [isOT, Bool.and_eq_true, List.all_eq_true] at hot
    exact hot.2
  rw [hvi] at hall
  refine Or.inl (le_of_lt (hall g ?_))
  have hgv := comps_last_sub _ _ g hg
  simp [comps, hge, hgv]

end Ytosk
