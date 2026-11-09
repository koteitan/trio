/- Value flow rules for a general substitution target V'. -/
import Ytosk.V3FlowG

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
  {x : Nat} (hx : x + 1 = M.length) {τ : Valn} (hτ : Cons (M.take x) τ) (hG : Good3 (M.take x) τ)
include I hx hτ hG

/-- Upgraded columns have equal values under the weak hypothesis at x - 1. -/
theorem v_upg_takeG (hux : ∀ c, upg M (x - 1) = some c → c = x) {i j : Nat} (hu : upg M i = some j) (hjx : j < x) : τ.v i = τ.v j := by
  have h1 := upg_succ_lt hu
  have hix : i + 1 < x := by
    by_contra h
    have hi : i = x - 1 := by omega
    have heq := hux j (by rw [← hi]; exact hu)
    omega
  have huN : upg (M.take x) i = some j := by rw [upg_take M hix]; exact hu
  obtain ⟨he1, he2⟩ := upg_e12 hu
  have he20 : entry M 2 i = 0 := by have := I.z2 i; omega
  have hiT : i < (M.take x).length := by rw [List.length_take]; omega
  apply v_upg_eq hτ hiT (by rw [entry_take M 1 (by omega)]; exact he1)
    (by rw [entry_take M 2 (by omega)]; exact he20) huN
  · cases hp : par (M.take x) 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt _ 1 i m hp; omega)
  · intro j' _ _ k' hk'; exact hG.ot_o k' (mem_children hk').2

/-- The last counted child propagates strict argument growth for general V'. -/
theorem ruleC_G (hRk : Rk (M.take x) rk) {r : Nat} (hrx : r < x) {V V' : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') (hvr : τ.v r = V) :
    ∀ w j, w < x → j ∈ children M w → j < x →
      Counted (M.take x) w j →
      (∀ j' ∈ children M w, j < j' → j' < x → ¬ Counted (M.take x) w j') → HighD M r j →
      (FPV M x (fun d => τ.v d < shf V V' (τ.v d)) j ∨
        FPA M x (fun d => argT (M.take x) τ d <
          sh V V' (argT (M.take x) τ d)) j) →
      argT (M.take x) τ w < sh V V' (argT (M.take x) τ w) := by
  intro w j hwx hj hjx hcj hlater hjH hjP
  have hwN : w < (M.take x).length := by rw [List.length_take]; omega
  have hjN' : j < (M.take x).length := by rw [List.length_take]; omega
  have hjN : j ∈ children (M.take x) w := by
    rw [children_take]; exact List.mem_filter.mpr ⟨hj, by simpa using hjx⟩
  obtain ⟨Lc, hCL⟩ : ∃ Lc, CL (M.take x) w = Lc ++ [j] := by
    unfold CL
    apply filter_last (children_sorted _ w) hjN (by simpa using hcj)
    intro j' hj' hjj'
    rw [children_take] at hj'
    obtain ⟨hj'M, hj'x⟩ := List.mem_filter.mp hj'
    simpa using hlater j' hj'M hjj' (by simpa using hj'x)
  obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hwN
  have hoj : τ.o j = psi (τ.v j) (argT (M.take x) τ j) z := o_cl_eq hτ hG hjN'
  rw [hCL, List.map_append, List.map_singleton, hoj] at hsing hdec
  have hVj : V < τ.v j := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr j hjx hjH).1
  have hLot : ∀ t ∈ Lc.map τ.o, isOT t = true := fun t ht => (hsing t (List.mem_append_left _ ht)).1
  show spArg (τ.v w) z (sumN ((CL (M.take x) w).map τ.o)) <
    sh V V' (spArg (τ.v w) z (sumN ((CL (M.take x) w).map τ.o)))
  rw [hCL, List.map_append, List.map_singleton, hoj, spArg_snoc hsing hdec]
  apply step_lt_sh hV hV' hVV (isOT_spArg _ _ _ rfl (isOT_sumN _ hLot))
    (by rw [← hoj]; exact hG.ot_o j hjN') hVj
  rcases hjP with ⟨_, hSV, hCLj⟩ | ⟨_, hSA⟩
  · right; refine ⟨hSV, ?_⟩; unfold argT; rw [hCLj]; rfl
  · left; exact hSA

/-- The last bump child propagates strict value growth for general V'. -/
theorem ruleB_G (hRk : Rk (M.take x) rk) {r p : Nat} (hrx : r < x) (hxp : par M 0 x = some p)
    {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') (hvr : τ.v r = V) :
    ∀ w j k, w < x → HighD M r w → w ≠ p → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w) → j ≠ p → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k →
      (FPV M x (fun d => τ.v d < shf V V' (τ.v d)) k ∨
        FPA M x (fun d => argT (M.take x) τ d <
          sh V V' (argT (M.take x) τ d)) k) →
      τ.v w < shf V V' (τ.v w) := by
  intro w j k hwx hwH hwp hj hjb hlater hjp hk hkmax hkH hkP
  have hwr : w ≠ r := fun h => hwH.2.1 h.symm
  have hjx : j < x := child_lt_xG hx hxp hwp hj
  have hkx : k < x := child_lt_xG hx hxp hjp hk
  have hkN : k < (M.take x).length := by rw [List.length_take]; omega
  have hjN : j < (M.take x).length := by rw [List.length_take]; omega
  have hwN : w < (M.take x).length := by rw [List.length_take]; omega
  -- `o(k)` grows
  have hVk : V < τ.v k := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr k hkx hkH).1
  have hok : τ.o k < sh V V' (τ.o k) := by
    rw [o_cl_eq hτ hG hkN]
    rcases hkP with ⟨_, hSV, _⟩ | ⟨_, hSA⟩
    · exact lt_sh_of_shf hV hV' hVV hVk hSV
    · exact lt_sh_of_arg hV hV' hVV (hG.ot_v k hkN) hVk hSA
  -- the sum of the children of `j` grows
  have hchj : children (M.take x) j = (children M j).filter (fun d => decide (d < k)) ++ [k] := by
    rw [children_take, List.filter_eq_self.mpr (fun c hc => by simpa using child_lt_xG hx hxp hjp hc)]
    exact split_last_max _ k (children_sorted M j) hk hkmax
  have hchot : ∀ u ∈ (children (M.take x) j).map τ.o, isOT u = true := by
    intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu; exact hG.ot_o d (mem_children hd).2
  have hGlt : sumN ((children (M.take x) j).map τ.o) <
      sh V V' (sumN ((children (M.take x) j).map τ.o)) := by
    rw [hchj, List.map_append, List.map_singleton]
    apply sumN_snoc_lt_sh hV hV' hVV _ (hG.ot_o k hkN) hok
    intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
    have hdk := (List.mem_filter.mp hd).2
    have : d < k := by simpa using hdk
    exact hG.ot_o d (by omega)
  -- the bump term of `j` grows
  have hbt : bumpTerm (M.take x) τ w j = omega (sumN ((children (M.take x) j).map τ.o)) := by
    unfold bumpTerm; rw [if_pos (by rw [col_take M hjx, bump_take M hwx]; exact hjb)]
  -- the later children of `w` are not bumps
  have hjwN : j ∈ children (M.take x) w := by
    rw [children_take]; exact List.mem_filter.mpr ⟨hj, by simpa using hjx⟩
  obtain ⟨A, Bs, hcw⟩ := List.append_of_mem hjwN
  have hBz : ∀ t ∈ Bs.map (bumpTerm (M.take x) τ w), t = z := by
    intro t ht
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    have hbw : b ∈ children (M.take x) w := by
      rw [hcw]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)
    have hjb' : j < b := by
      have hs := children_sorted (M.take x) w
      rw [hcw] at hs
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b hb
    rw [children_take] at hbw
    obtain ⟨hbM, hbx⟩ := List.mem_filter.mp hbw
    have hbx' : b < x := by simpa using hbx
    unfold bumpTerm
    rw [if_neg (by rw [col_take M hbx', bump_take M hwx]; exact hlater b hbM hjb' hbx')]
  have hbtot : ∀ t ∈ one :: A.map (bumpTerm (M.take x) τ w), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG w b
  have hW : sumN (one :: (children (M.take x) w).map (bumpTerm (M.take x) τ w)) =
      sumN ((one :: A.map (bumpTerm (M.take x) τ w)) ++ [bumpTerm (M.take x) τ w j]) := by
    rw [hcw, List.map_append, List.map_cons]
    rw [show one :: (A.map (bumpTerm (M.take x) τ w) ++ (bumpTerm (M.take x) τ w j ::
        Bs.map (bumpTerm (M.take x) τ w))) = ((one :: A.map (bumpTerm (M.take x) τ w)) ++
        [bumpTerm (M.take x) τ w j]) ++ Bs.map (bumpTerm (M.take x) τ w) by simp]
    apply sumN_append_zeros
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hbtot t ht
      · simp at ht; rw [ht]; exact isOT_bumpTerm hG w j
    · exact hBz
  have hWot : isOT (sumN (one :: (children (M.take x) w).map (bumpTerm (M.take x) τ w))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG w b
  have hWlt : sumN (one :: (children (M.take x) w).map (bumpTerm (M.take x) τ w)) <
      sh V V'
        (sumN (one :: (children (M.take x) w).map (bumpTerm (M.take x) τ w))) := by
    rw [hW]
    apply sumN_snoc_lt_sh hV hV' hVV hbtot (isOT_bumpTerm hG w j)
    rw [hbt]; exact omega_lt_sh hV hV' hVV (isOT_sumN _ hchot) hGlt
  -- the `v` equation of `w`
  obtain ⟨m, hm, hVm, _⟩ := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr w hwx hwH).2
  have he1w : entry M 1 w ≠ 0 := by have := hwH.2.2 w hwH.1 (Anc0.refl w) hwr; omega
  have he2w : entry M 2 w ≠ 0 := by have := I.be w j hj hjb; omega
  have hvw : τ.v w = sf (add (τ.v m)
      (omega (sumN (one :: (children (M.take x) w).map (bumpTerm (M.take x) τ w))))) := by
    rw [(hτ w hwN).2]; unfold vRhs
    rw [entry_take M 1 hwx, entry_take M 2 hwx, if_neg he1w, if_neg he2w, par_take M 1 w hwx, hm]
    rfl
  rw [hvw]
  exact shf_lt_of_omega hV hV' hVV (hG.ot_v m (by have := par_lt M 1 w m hm; omega)) hWot hVm hWlt

/-- The root cannot upgrade into a high child. -/
theorem ruleNR_G (hRk : Rk (M.take x) rk)
    (hux : ∀ c, upg M (x - 1) = some c → c = x) {r : Nat}
    (hrx : r < x) {V : T} (hvr : τ.v r = V) :
    ∀ j ∈ children M r, j < x → HighD M r j → upg M r ≠ some j := by
  intro j hj hjx hjH hu
  have heq := v_upg_takeG I hx hτ hG hux hu hjx
  have hlt := (high_v I.e00 I.r01 (by omega) hτ hG hRk hvr j hjx hjH).1
  rw [← heq, hvr] at hlt
  exact lt_irrefl' _ hlt

end

#print axioms v_upg_takeG
#print axioms ruleC_G
#print axioms ruleB_G
#print axioms ruleNR_G

end Ytosk.V3Main.SeedPF
