/-
**t = 2, sv: `T2SVStrict` holds (2026-11-08).**

The rules of the flow (`flow_top`, V3SVFlowM) with `SV w := v(w) < f(v(w))` and `SA w := arg(w) < σ(arg(w))` in
`T = M.take x`, `σ = σ_{V,V+1}`:
- base: `v_T(x − 1) = V + 1` (`sv_last_v`) and `V + 1 < f(V + 1) = V + 2`;
- `hRU`: an upgraded column has the `v` of its target (`v_upg_eq`);
- `hRC`: the last counted child `j` of `w`: `arg(w) = step v(w) B s y` with `o(j) = ψ_s(y)` (`spArg_snoc`), and
  `step_lt_sh`; if `v(j)` grew then `j` has no counted child, so `y = 0`;
- `hRB`: the bump child `j` of `w` with its last child `k`: `o(k)` grows, so the sum of the children of `j` grows,
  so the bump term `ω^…` grows, so `W(w)` grows (the later children are not bumps), so `v(w) = A + ω^W` grows
  (`shf_lt_of_omega`, `V ≤ A` from `high_v`);
- `hnr`: `r` is not upgraded into its child (the children of `r` have `v > V + 1`).
-/
import Ytosk.V3SVFlowT

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The argument of `w` in `N`. -/
def argT (N : Mat) (τ : Valn) (w : Nat) : T := spArg (τ.v w) z (sumN ((CL N w).map τ.o))

theorem filter_last {p : Nat → Bool} : ∀ {l : List Nat}, l.Pairwise (· < ·) → ∀ {j : Nat}, j ∈ l →
    p j = true → (∀ j' ∈ l, j < j' → p j' = false) → ∃ Lc, l.filter p = Lc ++ [j] := by
  intro l hs j hj hpj hlater
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hj
  refine ⟨l1.filter p, ?_⟩
  have h2 : l2.filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    have hjb : j < b := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b hb
    simp [hlater b (List.mem_append_right _ (List.mem_cons_of_mem _ hb)) hjb]
  rw [List.filter_append, List.filter_cons_of_pos hpj, h2]

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
  {r L : Nat} (hlen : r + L + 1 = M.length) (hq : par M 0 (r + L) = some r)
  (hux : upg M (r + L - 1) = some (r + L)) {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
  (hG : Good3 (M.take (r + L)) τ)
include I hlen hq hux hτ hG

/-- **`v_upg_eq` in `M.take x`.** -/
theorem v_upg_takeX {i j : Nat} (hu : upg M i = some j) (hjx : j < r + L) : τ.v i = τ.v j := by
  have h1 := upg_succ_lt hu
  have hix : i + 1 < r + L := by
    by_contra h
    have hi : i = r + L - 1 := by omega
    rw [hi, hux] at hu; cases hu; omega
  have huN : upg (M.take (r + L)) i = some j := by rw [upg_take M hix]; exact hu
  obtain ⟨he1, he2⟩ := upg_e12 hu
  have he20 : entry M 2 i = 0 := by have := I.z2 i; omega
  have hiT : i < (M.take (r + L)).length := by rw [List.length_take]; omega
  apply v_upg_eq hτ hiT (by rw [entry_take M 1 (by omega)]; exact he1)
    (by rw [entry_take M 2 (by omega)]; exact he20) huN
  · cases hp : par (M.take (r + L)) 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt _ 1 i m hp; omega)
  · intro j' _ _ k' hk'; exact hG.ot_o k' (mem_children hk').2

/-- **The rule `hRC`.** -/
theorem sv_ruleC (hvr : τ.v r = ρ.v r) (hRk : Rk (M.take (r + L)) rk) :
    ∀ w j, w < r + L → (w = r ∨ HighD M r w) → j ∈ children M w → j < r + L →
      Counted (M.take (r + L)) w j →
      (∀ j' ∈ children M w, j < j' → j' < r + L → ¬ Counted (M.take (r + L)) w j') → HighD M r j →
      (FPV M (r + L) (fun d => τ.v d < shf (ρ.v r) (succ (ρ.v r)) (τ.v d)) j ∨
        FPA M (r + L) (fun d => argT (M.take (r + L)) τ d <
          sh (ρ.v r) (succ (ρ.v r)) (argT (M.take (r + L)) τ d)) j) →
      argT (M.take (r + L)) τ w < sh (ρ.v r) (succ (ρ.v r)) (argT (M.take (r + L)) τ w) := by
  intro w j hwx hw hj hjx hcj hlater hjH hjP
  have hrM : r < M.length := by omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hV' : isOT (succ (ρ.v r)) = true := isOT_succ hV
  have hVV : ρ.v r < succ (ρ.v r) := lt_succ_self _
  have hwN : w < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hjN' : j < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hjN : j ∈ children (M.take (r + L)) w := by
    rw [children_take]; exact List.mem_filter.mpr ⟨hj, by simpa using hjx⟩
  obtain ⟨Lc, hCL⟩ : ∃ Lc, CL (M.take (r + L)) w = Lc ++ [j] := by
    unfold CL
    apply filter_last (children_sorted _ w) hjN (by simpa using hcj)
    intro j' hj' hjj'
    rw [children_take] at hj'
    obtain ⟨hj'M, hj'x⟩ := List.mem_filter.mp hj'
    simpa using hlater j' hj'M hjj' (by simpa using hj'x)
  obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hwN
  have hoj : τ.o j = psi (τ.v j) (argT (M.take (r + L)) τ j) z := o_cl_eq hτ hG hjN'
  rw [hCL, List.map_append, List.map_singleton, hoj] at hsing hdec
  have hVj : ρ.v r < τ.v j := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr j hjx hjH).1
  have hLot : ∀ t ∈ Lc.map τ.o, isOT t = true := fun t ht => (hsing t (List.mem_append_left _ ht)).1
  show spArg (τ.v w) z (sumN ((CL (M.take (r + L)) w).map τ.o)) <
    sh (ρ.v r) (succ (ρ.v r)) (spArg (τ.v w) z (sumN ((CL (M.take (r + L)) w).map τ.o)))
  rw [hCL, List.map_append, List.map_singleton, hoj, spArg_snoc hsing hdec]
  apply step_lt_sh hV hV' hVV (isOT_spArg _ _ _ rfl (isOT_sumN _ hLot))
    (by rw [← hoj]; exact hG.ot_o j hjN') hVj
  rcases hjP with ⟨_, hSV, hCLj⟩ | ⟨_, hSA⟩
  · right; refine ⟨hSV, ?_⟩; unfold argT; rw [hCLj]; rfl
  · left; exact hSA

/-- **The rule `hRB`.** -/
theorem sv_ruleB (hvr : τ.v r = ρ.v r) (hRk : Rk (M.take (r + L)) rk) :
    ∀ w j k, w < r + L → HighD M r w → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < r + L → col M j' ≠ bump M w) → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k →
      (FPV M (r + L) (fun d => τ.v d < shf (ρ.v r) (succ (ρ.v r)) (τ.v d)) k ∨
        FPA M (r + L) (fun d => argT (M.take (r + L)) τ d <
          sh (ρ.v r) (succ (ρ.v r)) (argT (M.take (r + L)) τ d)) k) →
      τ.v w < shf (ρ.v r) (succ (ρ.v r)) (τ.v w) := by
  intro w j k hwx hwH hj hjb hlater hk hkmax hkH hkP
  have hrM : r < M.length := by omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hV' : isOT (succ (ρ.v r)) = true := isOT_succ hV
  have hVV : ρ.v r < succ (ρ.v r) := lt_succ_self _
  have hwr : w ≠ r := fun h => hwH.2.1 h.symm
  have hjx : j < r + L := child_lt_x I hlen hq hux hwr hj
  have hwj := (mem_children hj).1
  have hrw := hwH.1.le
  have hjr : j ≠ r := by omega
  have hkx : k < r + L := child_lt_x I hlen hq hux hjr hk
  have hkN : k < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hjN : j < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hwN : w < (M.take (r + L)).length := by rw [List.length_take]; omega
  -- `o(k)` grows
  have hVk : ρ.v r < τ.v k := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr k hkx hkH).1
  have hok : τ.o k < sh (ρ.v r) (succ (ρ.v r)) (τ.o k) := by
    rw [o_cl_eq hτ hG hkN]
    rcases hkP with ⟨_, hSV, _⟩ | ⟨_, hSA⟩
    · exact lt_sh_of_shf hV hV' hVV hVk hSV
    · exact lt_sh_of_arg hV hV' hVV (hG.ot_v k hkN) hVk hSA
  -- the sum of the children of `j` grows
  have hchj : children (M.take (r + L)) j = (children M j).filter (fun d => decide (d < k)) ++ [k] := by
    rw [children_take, List.filter_eq_self.mpr (fun c hc => by simpa using child_lt_x I hlen hq hux hjr hc)]
    exact split_last_max _ k (children_sorted M j) hk hkmax
  have hchot : ∀ u ∈ (children (M.take (r + L)) j).map τ.o, isOT u = true := by
    intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu; exact hG.ot_o d (mem_children hd).2
  have hGlt : sumN ((children (M.take (r + L)) j).map τ.o) <
      sh (ρ.v r) (succ (ρ.v r)) (sumN ((children (M.take (r + L)) j).map τ.o)) := by
    rw [hchj, List.map_append, List.map_singleton]
    apply sumN_snoc_lt_sh hV hV' hVV _ (hG.ot_o k hkN) hok
    intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
    have hdk := (List.mem_filter.mp hd).2
    have : d < k := by simpa using hdk
    exact hG.ot_o d (by omega)
  -- the bump term of `j` grows
  have hbt : bumpTerm (M.take (r + L)) τ w j = omega (sumN ((children (M.take (r + L)) j).map τ.o)) := by
    unfold bumpTerm; rw [if_pos (by rw [col_take M hjx, bump_take M hwx]; exact hjb)]
  -- the later children of `w` are not bumps
  have hjwN : j ∈ children (M.take (r + L)) w := by
    rw [children_take]; exact List.mem_filter.mpr ⟨hj, by simpa using hjx⟩
  obtain ⟨A, Bs, hcw⟩ := List.append_of_mem hjwN
  have hBz : ∀ t ∈ Bs.map (bumpTerm (M.take (r + L)) τ w), t = z := by
    intro t ht
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    have hbw : b ∈ children (M.take (r + L)) w := by
      rw [hcw]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)
    have hjb' : j < b := by
      have hs := children_sorted (M.take (r + L)) w
      rw [hcw] at hs
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b hb
    rw [children_take] at hbw
    obtain ⟨hbM, hbx⟩ := List.mem_filter.mp hbw
    have hbx' : b < r + L := by simpa using hbx
    unfold bumpTerm
    rw [if_neg (by rw [col_take M hbx', bump_take M hwx]; exact hlater b hbM hjb' hbx')]
  have hbtot : ∀ t ∈ one :: A.map (bumpTerm (M.take (r + L)) τ w), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG w b
  have hW : sumN (one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w)) =
      sumN ((one :: A.map (bumpTerm (M.take (r + L)) τ w)) ++ [bumpTerm (M.take (r + L)) τ w j]) := by
    rw [hcw, List.map_append, List.map_cons]
    rw [show one :: (A.map (bumpTerm (M.take (r + L)) τ w) ++ (bumpTerm (M.take (r + L)) τ w j ::
        Bs.map (bumpTerm (M.take (r + L)) τ w))) = ((one :: A.map (bumpTerm (M.take (r + L)) τ w)) ++
        [bumpTerm (M.take (r + L)) τ w j]) ++ Bs.map (bumpTerm (M.take (r + L)) τ w) by simp]
    apply sumN_append_zeros
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hbtot t ht
      · simp at ht; rw [ht]; exact isOT_bumpTerm hG w j
    · exact hBz
  have hWot : isOT (sumN (one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG w b
  have hWlt : sumN (one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w)) <
      sh (ρ.v r) (succ (ρ.v r))
        (sumN (one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w))) := by
    rw [hW]
    apply sumN_snoc_lt_sh hV hV' hVV hbtot (isOT_bumpTerm hG w j)
    rw [hbt]; exact omega_lt_sh hV hV' hVV (isOT_sumN _ hchot) hGlt
  -- the `v` equation of `w`
  obtain ⟨m, hm, hVm, _⟩ := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr w hwx hwH).2
  have he1w : entry M 1 w ≠ 0 := by have := hwH.2.2 w hwH.1 (Anc0.refl w) hwr; omega
  have he2w : entry M 2 w ≠ 0 := by have := I.be w j hj hjb; omega
  have hvw : τ.v w = sf (add (τ.v m)
      (omega (sumN (one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w))))) := by
    rw [(hτ w hwN).2]; unfold vRhs
    rw [entry_take M 1 hwx, entry_take M 2 hwx, if_neg he1w, if_neg he2w, par_take M 1 w hwx, hm]
    rfl
  rw [hvw]
  exact shf_lt_of_omega hV hV' hVV (hG.ot_v m (by have := par_lt M 1 w m hm; omega)) hWot hVm hWlt

/-- **The rule `hnr`**: `r` is not upgraded into its child. -/
theorem sv_ruleNR (hch : ∀ d ∈ children (M.take (r + L)) r, succ (ρ.v r) < τ.v d) (hvr : τ.v r = ρ.v r)
    (hp1x : par M 1 (r + L) = some r) : ∀ j ∈ children M r, upg M r ≠ some j := by
  intro j hj hu
  have hjM := (mem_children hj).2
  have hjx : j < r + L := by
    by_contra h
    have hjx : j = r + L := by omega
    subst hjx
    obtain ⟨m, hm1, hm2, _, _⟩ := upg_spec hu
    rw [hp1x] at hm2; cases hm2
    have := par_lt M 1 r r hm1; omega
  have heq := v_upg_takeX I hlen hq hux hτ hG hu hjx
  have hjN : j ∈ children (M.take (r + L)) r := by
    rw [children_take]; exact List.mem_filter.mpr ⟨hj, by simpa using hjx⟩
  have := hch j hjN
  rw [← heq, hvr] at this
  exact lt_irrefl' _ (lt_trans (lt_succ_self _) this)

end

/-- **`T2SVStrict` holds**: `X₁ < σ_{V,V+1}(X₁)` in the sv case. -/
theorem t2SVStrict_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L)) :
    T2SVStrict M ρ r L := by
  intro τ hτ
  obtain ⟨hG, hvr, hch⟩ := sv_children_ctxV3 hM hS I Ctx hlen hr hq hux hτ
  have hRk : Rk (M.take (r + L)) rk := rk_take_all I.rank I.r0p I.z2 I.sd I.z1 I.uab (r + L) (by omega)
  obtain ⟨hp1, _, he2l⟩ := sv_last_facts I hlen hr hux
  have he2r : entry M 2 r = 0 := (par2_facts I.z2 (by omega) hr).1
  have hp1x : par M 1 (r + L) = some r := by
    obtain ⟨m, hm1, hm2, _, _⟩ := upg_spec hux; rw [hp1] at hm1; cases hm1; exact hm2
  have hrM : r < M.length := by omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r hrM
  exact flow_top I hlen hq he2r hux
    (fun d => τ.v d < shf (ρ.v r) (succ (ρ.v r)) (τ.v d))
    (fun d => argT (M.take (r + L)) τ d < sh (ρ.v r) (succ (ρ.v r)) (argT (M.take (r + L)) τ d))
    (by
      show τ.v (r + L - 1) < shf (ρ.v r) (succ (ρ.v r)) (τ.v (r + L - 1))
      rw [sv_last_v hM hS I Ctx hlen hr hq hux hτ]
      exact succ_lt_shf_succ hV (isOT_succ hV) (lt_succ_self _))
    hp1 he2l
    (fun i j hu hjx _ hSV => by
      show τ.v i < shf (ρ.v r) (succ (ρ.v r)) (τ.v i)
      rw [v_upg_takeX I hlen hq hux hτ hG hu hjx]; exact hSV)
    (sv_ruleC I hlen hq hux hτ hG hvr hRk)
    (sv_ruleB I hlen hq hux hτ hG hvr hRk)
    (sv_ruleNR I hlen hq hux hτ hG hch hvr hp1x)

#print axioms t2SVStrict_holds

end Ytosk.V3Main.SeedPF
