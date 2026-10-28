/-
**WfScout: the residual `T2SeedClV2B` (hCl) loses its standard-form fields (2026-10-29).**

`T2SeedClV2B` asks, at every `t = 2` step, the `k`-free base facts of the qn, sv and C seeds
(`T2SeedQNBase`・`T2SeedSVBase`・`T2SeedCBase`). Several of their fields follow from the invariant of
`M.take x` alone:

- qn: `ψ_V(X₁)` is standard, because `X₁` is the argument of `o_{M.take x}(r)` and `v_{M.take x}(r) = v_M(r)`
  (`r` is not topped in `M.take x`, `topP_C`, `v_take_of_untopped`).
- sv and C: `X₁` is standard (the same argument), and at the level `u = V` the components of `X₁` are below `X₁`
  (the standard form of `ψ_V(X₁)`); the components of `V` at its own level are none (`comps_self_nil`).
- sv: the summands of `X` (the argument of `o_M(r)`) and of `X₁` are at least `Ω_{V+1}`, since every child
  `d` of `r` up to `x` has the column of `x` (`t_child_col`), so `P₁(d) = r`, row 2 is `1`, and
  `V + 1 < v(d)` (`v_child_gt`).

The new residual `T2SeedClV2R` keeps only the other fields: the shape `X = P + ψ_b(x)`, `X₁ = P + T₁`, `σ P = P`,
the components at the path levels, and (qn) the level-`V` and `Lc = []` fields, (C) the summand bounds and the
components of `s′ = qnS` at the level `V`.
Bridge: `t2SeedClV2B_of_R : T2SeedClV2R → T2SeedClV2B`.
-/
import Ytosk.V3T2SeedSVCl
import Ytosk.V3T2SeedRes
import Ytosk.V3T2SeedRes2
import Ytosk.V3T2SeedQNV
import Ytosk.V3StrictR
import Ytosk.V3Tame
import Ytosk.V3ResV2

namespace Ytosk.WfScout

open T

set_option linter.unusedSectionVars false

/-- **The summands of the argument of `o(i)` are at least `Ω_w`** when every counted child of `i` has `v > w`. -/
theorem arg_summands_ge {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) {i : Nat} {w : T}
    (hch : ∀ d ∈ CL N i, w ≤ σ.v d) :
    ∀ q ∈ summands (spArg (σ.v i) z (sumN ((CL N i).map σ.o))), ¬ q < psi w z z := by
  have hsing : ∀ t ∈ (CL N i).map σ.o, Single t := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact single_o hC hG (mem_children (cl_mem_children hd)).2
  have h := summands_spArg_ge (a := σ.v i) (w := w) _ z (isOT_sumN _ (fun t ht => (hsing t ht).1))
    (by simp [summands]) (by
      intro q hq hlt
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
      have hdT := (mem_children (cl_mem_children hd)).2
      have hlt' := hch d hd
      obtain ⟨y, hy⟩ := o_psi_sub hC hdT
      rw [sf_ot (hG.ot_v d hdT)] at hy
      rw [hy, Om] at hlt
      rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
      · exact lt_irrefl' _ (lt_of_lt_of_le h hlt')
      · exact not_lt_z _ h)
  intro q hq
  exact h q hq

/-- **sv: every child of `r` in `M` has `v > V + 1`.** -/
theorem sv_children_M {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) :
    ∀ d ∈ children M r, succ (ρ.v r) < ρ.v d := by
  obtain ⟨hX, _⟩ := sInvXJ_std hM hS
  have hxM : r + L < M.length := by omega
  obtain ⟨_, he1x⟩ := par2_facts I.z2 hxM hr
  have he2x : entry M 2 (r + L) = 1 := by
    obtain ⟨_, _, _, he2, _, _⟩ := (par2_iff M hxM).mp hr
    have h' : entry M 2 r < entry M 2 (r + L) := he2
    have := I.z2 (r + L); omega
  intro d hd
  have hdM := (mem_children hd).2
  have hpc : par M 0 d = some r := (mem_children_iff.mp hd).2
  have hcol := t_child_col hX hq hxM he2x he1x hd (by omega)
  have hcx := t_col_x hX hq hxM he2x he1x
  have h1 : entry M 1 d = entry M 1 r + 1 := by
    have : entry M 1 d = (col M d).2.1 := rfl; rw [this, hcol, hcx]
  have h2 : entry M 2 d = 1 := by
    have : entry M 2 d = (col M d).2.2 := rfl; rw [this, hcol, hcx]
  have hp1 : par M 1 d = some r := par1_of_child hpc (by omega)
  exact v_child_gt I.cons I.good (by omega) hdM hp1 (by omega) h2

/-- **C: every child of `r` has row 1 above that of `r`**: `q` is the last child of `r` (`x` lies under `q`), the
earlier children have columns at least that of `q` (`sib_le`), and `x = bump(q)` has the row 1 of `q`, which is above
that of `r` (`par2_facts`). -/
theorem c_children_e1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) :
    ∀ d ∈ children M r, entry M 1 r < entry M 1 d := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hxM : r + L < M.length := by omega
  obtain ⟨_, he1x⟩ := par2_facts I.z2 hxM hr
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, -⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have he1q : entry M 1 q = entry M 1 (r + L) := by
    have : entry M 1 (r + L) = (col M (r + L)).2.1 := rfl
    rw [this, Txb]; rfl
  have hqM : q ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hAqx : Anc0 M q (r + L) := anc0_of_par M 0 q (r + L) hq
  intro d hd
  have hpd : par M 0 d = some r := (mem_children_iff.mp hd).2
  have hdM := (mem_children hd).2
  rcases Nat.lt_trichotomy d q with hdq | rfl | hdq
  · obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hd
    have hqin : q ∈ l₂ := by
      have hs := children_sorted M r
      rw [hl] at hqM hs
      rcases List.mem_append.mp hqM with h | h
      · exact absurd h (by
          intro hq1
          have hlt := (List.pairwise_append.mp hs).2.2 q hq1 d (by simp)
          omega)
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
    have hle := sib_le I.sd l₂ l₁ d hl q hqin
    have h0 : entry M 0 q = entry M 0 d := by rw [I.r0p q r hpq, I.r0p d r hpd]
    unfold colLe at hle
    have e0q : (col M q).1 = entry M 0 q := rfl
    have e0d : (col M d).1 = entry M 0 d := rfl
    have e1q : (col M q).2.1 = entry M 1 q := rfl
    have e1d : (col M d).2.1 = entry M 1 d := rfl
    rw [e0q, e0d, e1q, e1d] at hle
    omega
  · omega
  · exfalso
    have hdx : d ≤ r + L := by omega
    have hAqd : Anc0 M q d := anc_between hAqx d (le_of_lt hdq) hdx
    have hAqr := anc0_par hAqd (by omega) hpd
    have := hAqr.le
    omega

/-- **Children above in row 1 have `v` above `v(r) + 1` or equal to it.** -/
theorem children_v_ge {N : Mat} {σ : Valn} {rk' : Bool → Nat → Nat} (hC : Cons N σ) (hG : Good3 N σ)
    (hR : Rk N rk') {r : Nat} (he : ∀ d ∈ children N r, entry N 1 r < entry N 1 d) :
    ∀ d ∈ CL N r, succ (σ.v r) ≤ σ.v d := by
  intro d hd
  have hdc := cl_mem_children hd
  have hpd := (mem_children_iff.mp hdc).2
  have h1 := he d hdc
  have hp1 : par N 1 d = some r := par1_of_child hpd h1
  exact succ_le_of_lt (v_par1_lt hC hG hR _ d r le_rfl (mem_children hdc).2 (by omega) hp1)

/-- **The level-`V` components of the seed argument `X₁` are below `X₁`**, and `X₁` is standard. -/
theorem x1_facts {M : Mat} {ρ : Valn} {r L : Nat} {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    (hG : Good3 (M.take (r + L)) τ) (hrT : r < (M.take (r + L)).length) (hvr : τ.v r = ρ.v r) :
    isOT (t2X1 M r L τ) = true ∧ ∀ g ∈ comps (ρ.v r) (t2X1 M r L τ), g < t2X1 M r L τ := by
  have hot := hG.ot_o r hrT
  rw [o_cl_eq hτ hG hrT] at hot
  have h5 := (isOT_psi_iff.mp hot).2.2.2.2
  refine ⟨isOT_arg hot, ?_⟩
  rw [← hvr]
  exact h5

/-- **Residual (qn base without the standard form of `ψ_V(X₁)`).** -/
def T2SeedQNBaseR (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
      (∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) ∧
      (Lc = [] → t1 ≤ qnS M ρ r L q) ∧
      ∀ u, PathLvAll M ρ r u → ¬ lt (ρ.v r) u = true →
        ∀ g ∈ comps u t1 ++ comps u (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)

/-- **Residual (sv base without the summand bounds, the standard form of `X₁` and the level `V`).** -/
def T2SeedSVBaseR (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ X, ρ.o r = psi (ρ.v r) X z →
    ∃ P b x T1, X = app P (psi b x z) ∧ t2X1 M r L τ = app P T1 ∧ T1 ≠ z ∧
      sh (ρ.v r) (succ (ρ.v r)) P = P ∧
      ∀ u, PathLvA M ρ r u → ¬ lt (ρ.v r) u = true →
        ∀ g ∈ comps u (t2X1 M r L τ) ++ comps u (ρ.v r), g < t2X1 M r L τ

/-- **Residual (C base without the summand bounds of `X` and `X₁`, the standard form of `X₁` and the level-`V`
components of `X₁`).** -/
def T2SeedCBaseR (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ X, ρ.o r = psi (ρ.v r) X z →
    ∃ P b x T1, X = app P (psi b x z) ∧ t2X1 M r L τ = app P T1 ∧ T1 ≠ z ∧
      sh (ρ.v r) (qnS M ρ r L q) P = P ∧
      (∀ g ∈ summands (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)), ¬ g < psi (succ (qnS M ρ r L q)) z z) ∧
      (∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g < t2X1 M r L τ) ∧
      ∀ u, PathLvAll M ρ r u → ¬ lt (ρ.v r) u = true →
        ∀ g ∈ comps u (t2X1 M r L τ) ++ comps u (qnS M ρ r L q), g < t2X1 M r L τ

/-- **Residual (t2): `T2SeedClV2B` without the fields that follow from the invariant of `M.take x`.** -/
def T2SeedClV2R : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNBaseR M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVBaseR M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCBaseR M ρ r L q)

/-- **Bridge: `T2SeedClV2B` from the smaller residual.** -/
theorem t2SeedClV2B_of_R (h : T2SeedClV2R) : T2SeedClV2B := by
  intro M ρ rk C hz h2 r L hlen hr
  obtain ⟨hQN, hSV, hCC⟩ := h M ρ rk C hz h2 r L hlen hr
  have I : Inv3W M ρ rk := Inv3W.ofV2 C.S C.I
  have R : Res3W M ρ rk := C.toW
  have hM := C.std
  have hS := C.ne
  have hrT : r < (M.take (r + L)).length := by
    have := par_lt M 2 _ _ hr; rw [List.length_take]; omega
  have hrM : r < M.length := by omega
  have hG3 : ∀ τ, Cons (M.take (r + L)) τ → Good3 (M.take (r + L)) τ := by
    intro τ hτ
    have hτ' : Cons (M.take (M.length - 1)) τ := by rw [show M.length - 1 = r + L by omega]; exact hτ
    have hG := good3_take_any I R (by omega) hτ'
    rw [show M.length - 1 = r + L by omega] at hG
    exact hG
  refine ⟨fun q Lc hq hqr hCL => ?_, fun hc => ?_, fun q hq hqr hncl => ?_⟩
  · -- qn
    intro τ hτ t1 hsp
    obtain ⟨H1, H2, H3⟩ := hQN q Lc hq hqr hCL τ hτ t1 hsp
    have hG := hG3 τ hτ
    have hvr : τ.v r = ρ.v r :=
      v_take_of_untopped I (by omega) (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hτ
    have hot := hG.ot_o r hrT
    rw [o_cl_eq hτ hG hrT, hsp, hvr] at hot
    exact ⟨hot, H1, H2, H3⟩
  · -- sv
    obtain ⟨hq, hux⟩ := hc
    intro τ hτ X hX
    obtain ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, hcl⟩ := hSV ⟨hq, hux⟩ τ hτ X hX
    obtain ⟨hG, hvr, hch⟩ := sv_children_ctx hM hS I R hlen hr hq hux hτ
    obtain ⟨hX1ot, hX1V⟩ := x1_facts hτ hG hrT hvr
    have hXe' : X = spArg (ρ.v r) z (sumN ((CL M r).map ρ.o)) := by
      have h1 := o_cl_eq I.cons I.good hrM
      rw [hX] at h1
      exact (psi.inj h1).2.1
    have hchM := sv_children_M hM hS I hlen hr hq
    refine ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, ?_, ?_, hX1ot, ?_⟩
    · rw [hXe']
      exact arg_summands_ge I.cons I.good (fun d hd => le_of_lt (hchM d (cl_mem_children hd)))
    · have h := arg_summands_ge hτ hG (w := succ (ρ.v r)) (i := r)
        (fun d hd => le_of_lt (hch d (cl_mem_children hd)))
      intro q hq'
      exact h q hq'
    · intro u hu hlt g hg
      rcases hu with rfl | hu
      · rcases List.mem_append.mp hg with hg | hg
        · exact hX1V g hg
        · rw [comps_self_nil (I.good.ot_v r hrM)] at hg; simp at hg
      · exact hcl u hu hlt g hg
  · -- C
    intro τ hτ X hX
    obtain ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, hs3, hcV, hcl⟩ := hCC q hq hqr hncl τ hτ X hX
    have hG := hG3 τ hτ
    have hvr : τ.v r = ρ.v r :=
      v_take_of_untopped I (by omega) (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hτ
    obtain ⟨hX1ot, hX1V⟩ := x1_facts hτ hG hrT hvr
    have heM := c_children_e1 hM hS I hlen hr hq hqr
    have hXe' : X = spArg (ρ.v r) z (sumN ((CL M r).map ρ.o)) := by
      have h1 := o_cl_eq I.cons I.good hrM
      rw [hX] at h1
      exact (psi.inj h1).2.1
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    rw [show M.length - 1 = r + L by omega] at hcnt
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
    have heT : ∀ d ∈ children (M.take (r + L)) r, entry (M.take (r + L)) 1 r < entry (M.take (r + L)) 1 d := by
      intro d hd
      rw [children_take, List.mem_filter] at hd
      have hdx : d < r + L := by simpa using hd.2
      rw [entry_take M 1 hdx, entry_take M 1 (par_lt M 2 _ _ hr)]
      exact heM d hd.1
    have hs1 : ∀ q ∈ summands X, ¬ q < psi (succ (ρ.v r)) z z := by
      rw [hXe']
      exact arg_summands_ge I.cons I.good (children_v_ge I.cons I.good I.rank heM)
    have hs2 : ∀ q ∈ summands (t2X1 M r L τ), ¬ q < psi (succ (ρ.v r)) z z := by
      have h := arg_summands_ge hτ hG (children_v_ge hτ hG hRk1 heT)
      intro q' hq'
      have h' := h q' hq'
      rwa [hvr] at h'
    refine ⟨P, b, x, T1, hXe, hX1e, hT1, hsP, hs1, hs2, hs3, hX1ot, ?_⟩
    intro u hu hlt g hg
    rcases hu with rfl | hu
    · rcases List.mem_append.mp hg with hg | hg
      · exact hX1V g hg
      · exact hcV g hg
    · exact hcl u hu hlt g hg

end Ytosk.WfScout
