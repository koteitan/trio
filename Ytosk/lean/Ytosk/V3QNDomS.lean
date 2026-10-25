/-
**Bad2 の qn の成分の支配を HUAC から（2026-10-26、lead）。**

Bad2・t = 2・qn で v_T(q) ⋬ v_M(q)（弱い場合）のとき、測った集合ではいつも単純な形になる（b2grow1 319・b2grow2 485 件）:
q の x より前の子は p だけ、p は q の bump 子で子は x − 1 だけ、x − 1 は祖先へ上げる。このとき
- M.take x では x − 1 は上げを失い o′(x − 1) = ψ_{V′+1}(0)（`lost_upg_take`）、M では o(x − 1) = ψ_{v(x−1)}(0)。
- ω^{ψ_a(0)} = ψ_a(0) なので、v_T(q) の最後の項は ω_T = ψ_{V′+1}(0)、s′ = V + ω^S の最後の項は ψ_{v(x−1)}(0)。
- ω_T の成分は 0 か V′ の成分で、HUAC で v(x − 1) の成分に押さえられる（`qnDom_simple`）。
残りは単純な形の外だけの `T2QNDomBad2`。
-/
import Ytosk.V3QNDropV
import Ytosk.V3HUAC

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The components of `ψ_a(0)`, with the level condition. -/
theorem comps_psi_zz' {u a g : T} (h : g ∈ comps u (psi a z z)) : ¬ a < u ∧ (g = z ∨ g ∈ comps u a) := by
  simp only [comps] at h
  split_ifs at h with h'
  · simp at h
  · simp at h
    exact ⟨h', h⟩

theorem mem_comps_psi_zz {u a g : T} (ha : ¬ a < u) (h : g ∈ comps u a) : g ∈ comps u (psi a z z) := by
  have ha' : ¬ lt a u = true := ha
  simp only [comps]
  simp [ha', h]

theorem one_lt_psi_zz {w : T} (hw : w ≠ z) : one < psi w z z := by
  show psi z z z < psi w z z
  rw [T.psi_lt_psi]
  left
  cases w with
  | z => exact absurd rfl hw
  | psi a b c => exact T.z_lt_psi _ _ _

/-- `ω^{1 + ω^{ψ_w(0)}} = ψ_w(0)` for `w ≠ 0`. -/
theorem bumpSum_psi_zz {w : T} (hw : w ≠ z) (hot : isOT (psi w z z) = true) :
    omega (sumN (one :: [omega (sumN [psi w z z])])) = psi w z z := by
  have hS : Single (psi w z z) := ⟨hot, _, _, rfl⟩
  rw [sumN_singleton hS, omega_psi_zz hw hot, sumN_one_cons_gt hS (one_lt_psi_zz hw), sumN_singleton hS,
    omega_psi_zz hw hot]

/-- **The simple shape of the weak qn case from `HUAC`.** -/
theorem qnDom_simple (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {p k : Nat} (hchq : (children M q).filter (fun c => decide (c < r + L)) = [p])
    (hchp : children M p = [r + L - 1]) (hpb : col M p = bump M q) (hk : upg M (r + L - 1) = some k)
    (hkx : k < r + L - 1) {τ : Valn} (hτ : Cons (M.take (r + L)) τ) {ωT : T}
    (hvq : τ.v q = add (ρ.v r) ωT) (hωT : ∃ a b, ωT = psi a b z) :
    ∀ u, Dom (comps u ωT) (comps u (qnS M ρ r L q) ++ [z]) := by
  have S := C.S
  have I := C.I
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hpM : p ∈ children M q := (List.mem_filter.mp (by rw [hchq]; simp : p ∈ (children M q).filter _)).1
  have hpx : p < r + L := by
    have := (List.mem_filter.mp (by rw [hchq]; simp : p ∈ (children M q).filter _)).2; simpa using this
  have hxm1p : r + L - 1 ∈ children M p := by rw [hchp]; simp
  have hpx1 : p < r + L - 1 := (mem_children hxm1p).1
  have hx1 : r + L - 1 + 1 = r + L := by omega
  -- the drop valuation and `τ`
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hag := agree_of_cons hC1 hτ hRk1
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hdrop := C.hdrop
  rw [show M.length - 1 = r + L by omega] at hdrop
  have hG1 := good3_take (show r + L + 1 = M.length by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good
    hC1 hRk1 hdrop
  have hGτ := good3_congr hG1 hag
  obtain ⟨hv', ho'⟩ := lost_upg_take C.std C.ne I (x := r + L) (r := r + L - 1) (by omega) hx1 hk
  set w := add (vOpt ρ (par M 1 (r + L - 1))) one with hw
  have hwot : isOT w = true := isOT_add (vOpt_ot I.good (by omega)) isOT_one
  have hw0 : w ≠ z := by
    intro h
    have := congrArg last h
    rw [hw, show one = psi z z z from rfl, last_add_W ⟨z, z, rfl⟩] at this
    cases this
  have hoτ : τ.o (r + L - 1) = psi w z z := by rw [← (hag _ (by omega)).1, ho']
  -- `ω_T = ψ_w(0)`
  have he2q : entry M 2 q = 1 := S.bumpE2 q p hpM hpb
  have he1q : entry M 1 q ≠ 0 := fun h => by have := S.r12 q h; omega
  have hchT : children (M.take (r + L)) q = [p] := by rw [children_take, hchq]
  have hchTp : children (M.take (r + L)) p = [r + L - 1] := by
    rw [children_take, hchp]; simp; omega
  have hbT : bumpTerm (M.take (r + L)) τ q p = omega (sumN [psi w z z]) := by
    unfold bumpTerm
    rw [col_take M hpx, bump_take M hqx, if_pos hpb, hchTp]
    simp [hoτ]
  have hqT : q < (M.take (r + L)).length := by omega
  have hvqT : τ.v q = add (vOpt τ (par (M.take (r + L)) 1 q)) (psi w z z) := by
    rw [(hτ q hqT).2]; unfold vRhs
    rw [entry_take M 1 hqx, entry_take M 2 hqx, if_neg he1q, if_neg (by omega), hchT]
    simp only [List.map_cons, List.map_nil]
    rw [hbT, bumpSum_psi_zz hw0 (isOT_psi_zz hwot)]
    exact sf_ot (isOT_add (vOpt_ot hGτ hqT) (isOT_psi_zz hwot))
  have hωTe : ωT = psi w z z := by
    obtain ⟨a, b, rfl⟩ := hωT
    have h1 := congrArg last hvq
    rw [hvqT, last_add_W ⟨_, _, rfl⟩, last_add_W ⟨_, _, rfl⟩] at h1
    exact h1.symm
  -- `s′ = V + ψ_{v(x−1)}(0)`
  have hchM : children M (r + L - 1) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    have hcl := mem_children hc
    have hcx : c = r + L := by omega
    have hpc := (mem_children_iff.mp hc).2
    rw [hcx, hq] at hpc
    have := Option.some.inj hpc
    have := (mem_children hpM).1
    omega
  set a := ρ.v (r + L - 1) with ha
  have haot : isOT a = true := I.good.ot_v _ (by omega)
  have ha0 : a ≠ z := v_ne_z_of_e1 I.cons (by omega) (upg_e12 hk).1
  have hoM : ρ.o (r + L - 1) = psi a z z := o_nochild I.cons (by omega) hchM haot
  have hqnS : qnS M ρ r L q = add (ρ.v r) (psi a z z) := by
    unfold qnS; rw [hchq]
    simp only [List.map_cons, List.map_nil]
    unfold bumpTerm
    rw [if_pos hpb, hchp]
    simp only [List.map_cons, List.map_nil]
    rw [hoM, bumpSum_psi_zz ha0 (isOT_psi_zz haot)]
  have hwa : w ≤ a := by rw [← hv']; exact (hdrop (r + L - 1) (by omega)).2.le
  -- the components
  intro u e he
  rw [hωTe] at he
  obtain ⟨hwu, he⟩ := comps_psi_zz' he
  have hz : z ∈ comps u (qnS M ρ r L q) ++ [z] := List.mem_append_right _ (List.mem_singleton_self _)
  rcases he with he | he
  · exact ⟨z, hz, by rw [he]⟩
  rcases dom_add_one (hU M ρ rk C.std C.ne I.cons I.rank I.good (r + L - 1) k hk hkx) u e he with h | ⟨d, hd, hed⟩
  · exact ⟨z, hz, by rw [h]⟩
  refine ⟨d, List.mem_append_left _ ?_, hed⟩
  have hau : ¬ a < u := fun h => hwu (lt_of_le_of_lt hwa h)
  rw [hqnS]
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix (ρ.v r) (psi a z z)
  rw [hP, comps_app]
  exact List.mem_append_right _ (mem_comps_psi_zz hau hd)

/-- **Residual (t2, `Bad2`): `T2QNDomBad` outside the simple shape** (2026-10-26). In the measured weak cases the shape
is always simple (b2grow1 319・b2grow2 485), so this is asserted only where it never occurs on the sets. -/
def T2QNDomBad2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] →
      ¬ (∃ p k, (children M q).filter (fun c => decide (c < r + L)) = [p] ∧ children M p = [r + L - 1] ∧
          col M p = bump M q ∧ upg M (r + L - 1) = some k ∧ k < r + L - 1) →
      ∀ τ, Cons (M.take (r + L)) τ → ¬ LhdE (τ.v q) (ρ.v q) →
        ∀ ωT, τ.v q = add (ρ.v r) ωT → (∃ a b, ωT = psi a b z) →
          ∀ u, Dom (comps u ωT) (comps u (qnS M ρ r L q) ++ [z])

theorem t2QNDomBad_of (hU : HUAC) (h : T2QNDomBad2) : T2QNDomBad := by
  intro M ρ rk C hB hz h2 r L q hlen hr hq hqr Lc hCL τ hτ hE ωT hvq hωT
  by_cases hs : ∃ p k, (children M q).filter (fun c => decide (c < r + L)) = [p] ∧ children M p = [r + L - 1] ∧
      col M p = bump M q ∧ upg M (r + L - 1) = some k ∧ k < r + L - 1
  · obtain ⟨p, k, hchq, hchp, hpb, hk, hkx⟩ := hs
    exact qnDom_simple hU C hlen hq hqr hchq hchp hpb hk hkx hτ hvq hωT
  · exact h M ρ rk C hB hz h2 r L q hlen hr hq hqr Lc hCL hs τ hτ hE ωT hvq hωT

end Ytosk
