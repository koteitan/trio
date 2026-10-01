/-
**3 行・t = 0: (r, x) の列の v は M.take x で強く下がる（hWk の証明）。**

`bump_rel_nw`: 落とす補題ののりしろの枠 `bump_rel` で、弱い源（o(k) = ψ_w(0) で v′ ⋪ v の子）が
ないときは強い関係だけが出る（証明は `bump_rel` の弱い場合を除いた写し）。
-/
import Ytosk.V3T0G

namespace Ytosk

open T

theorem bump_rel_nw {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M x ρ) (hWS : BumpWeakSrc M x ρ ρ')
    {i : Nat} (hi : i < x)
    (hIH : ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
      PO ρ ρ' k ∧ PV M ρ ρ' k)
    (hCv : ChgX M x false i) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hNW : ∀ jl ∈ children M i, col M jl = bump M i → ∀ k ∈ children M jl,
      (∃ w, w ≠ z ∧ ρ.o k = psi w z z) →
      ((k = x ∧ children M jl = [x]) ∨ (k < x ∧ ρ'.o k ≠ ρ.o k ∧ ¬ LhdE (ρ'.v k) (ρ.v k))) → False) :
    isOT (ρ'.v i) = true ∧ (LhdE (ρ'.v i) (ρ.v i) ∨ False) := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have he2 : entry M 2 i = 1 := by have := hZ2 i; omega
  have hoff := chg_off hx hC hG hC' hRk'
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hi
  have hV : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
    rw [par_take M 1 i hi]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      show ρ'.v m = ρ.v m
      have hm := par_lt M 1 i m hp
      apply (hoff m (by omega)).2
      intro hCm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  set V := vOpt ρ (par M 1 i) with hVdef
  have hAb := bump_children_take hR0 hZ2 hSD hZ1 hi he2 hT
  obtain ⟨XI, hXI, hXIc⟩ := children_M_eq hx i
  have hpot := isOT_bumpP hG i
  have ev : ρ.v i = add V (omega (sumN (one :: (children M i).map (bumpTerm M ρ i)))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev'0 : ρ'.v i = sf (add V (omega (sumN (one :: (children (M.take x) i).map
      (bumpTerm (M.take x) ρ' i))))) := by
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_neg h2, hV]
  rcases List.eq_nil_or_concat (children (M.take x) i) with hA | ⟨A0, jl, hA⟩
  · -- no child in `M.take x`
    rw [hA] at ev'0 hXI
    simp only [List.map_nil, List.nil_append] at ev'0 hXI
    have hone : sumN [one] = one := sumN_singleton ⟨rfl, z, z, rfl⟩
    rw [hone] at ev'0
    have hot1 : isOT (add V (omega one)) = true := isOT_add hVot (isOT_omega rfl)
    rw [sf_ot hot1] at ev'0
    rcases hXIc with rfl | ⟨rfl, hxi⟩
    · have he : ρ'.v i = ρ.v i := by rw [ev'0, ev, hXI]; simp [hone]
      exact ⟨he ▸ hG.ot_v i hiM, Or.inl (Or.inl he)⟩
    · have hxc : children M x = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc; have := mem_children hc; omega
      by_cases hxb : col M x = bump M i
      · have hbx : bumpTerm M ρ i x = one := by
          unfold bumpTerm; rw [if_pos hxb, hxc]
          simp only [List.map_nil, sumN_nil]
          rw [omega_small (T.z_lt_psi _ _ _)]; rfl
        have htwo : sumN [one, one] = two := by
          rw [sumN_pair_one (t := one) ⟨rfl, z, z, rfl⟩, if_neg (lt_irrefl' _)]; rfl
        rw [hXI] at ev
        simp only [List.map_cons, List.map_nil, hbx, htwo] at ev
        rw [omega_small two_lt_E0] at ev
        rw [omega_small one_lt_E0] at ev'0
        refine ⟨by rw [ev'0]; exact isOT_add hVot (isOT_omega (show isOT one = true from rfl)), Or.inl ?_⟩
        rw [ev'0, ev]
        have hWE : psi z two z < E0 := psi_z_lt_E0 two_lt_E0
        have hWot : isOT (psi z two z) = true := by
          have := isOT_omega isOT_two; rwa [omega_small two_lt_E0] at this
        have hW'ot : isOT (psi z one z) = true := by
          have := isOT_omega (show isOT one = true from rfl); rwa [omega_small one_lt_E0] at this
        have hlt : psi z one z < psi z two z := by
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, one_lt_two⟩
        exact v_strong hVot ⟨hW'ot, _, _, rfl⟩ ⟨hWot, _, _, rfl⟩
          (Or.inr (lhd_lt_small hW'ot hWE hlt))
          (fun r hr _ hlt' => lhd_lt_small (isOT_mem_summands hVot hr) hWE hlt')
      · have hbx : bumpTerm M ρ i x = z := by unfold bumpTerm; rw [if_neg hxb]
        have he : ρ'.v i = ρ.v i := by
          rw [ev'0, ev, hXI]
          simp only [List.map_cons, List.map_nil, hbx]
          rw [show [one, z] = [one] ++ [z] from rfl, sumN_snoc_z (by simp; rfl), hone]
        exact ⟨he ▸ hG.ot_v i hiM, Or.inl (Or.inl he)⟩
  · rw [List.concat_eq_append] at hA
    have hjlT : jl ∈ children (M.take x) i := by rw [hA]; simp
    obtain ⟨hjlx, hjlM⟩ := mem_children_take hjlT
    have hjlb : col M jl = bump M i := hAb jl hjlT
    have hA0T : ∀ j ∈ A0, j ∈ children (M.take x) i := fun j hj => by rw [hA]; simp [hj]
    have hA0lt : ∀ j ∈ A0, j < jl := by
      have hs := children_sorted (M.take x) i
      rw [hA] at hs
      exact fun j hj => (List.pairwise_append.mp hs).2.2 j hj jl (by simp)
    have hearly : ∀ j ∈ A0, bumpTerm (M.take x) ρ' i j = bumpTerm M ρ i j := fun j hj =>
      (early_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h2 (mem_children_take (hA0T j hj)).2
        hjlT (hA0lt j hj)).2.2
    obtain ⟨hsG', hGrel⟩ := g_level hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hKD hWS h1 h2 hjlM
      hjlb (hIH jl hjlM hjlb)
    set G' := sumN ((children (M.take x) jl).map ρ'.o) with hG'def
    set G := sumN ((children M jl).map ρ.o) with hGdef
    have hG'ot : isOT G' = true := isOT_sumN _ (fun t ht => (hsG' t ht).1)
    have hGot : isOT G = true := isOT_sumN _ (fun t ht => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    have hbjl' : bumpTerm (M.take x) ρ' i jl = omega G' := by
      unfold bumpTerm; rw [col_take M hjlx, bump_take M hi, if_pos hjlb]
    have hbjl : bumpTerm M ρ i jl = omega G := by unfold bumpTerm; rw [if_pos hjlb]
    set Pl := A0.map (bumpTerm M ρ i) with hPldef
    have hmapT : (children (M.take x) i).map (bumpTerm (M.take x) ρ' i) = Pl ++ [omega G'] := by
      rw [hA, List.map_append, List.map_singleton, hbjl']
      congr 1; exact List.map_congr_left hearly
    have hmapM : (children M i).map (bumpTerm M ρ i) = Pl ++ [omega G] ++ XI.map (bumpTerm M ρ i) := by
      rw [hXI, hA]; simp [hbjl, hPldef]
    have hsP : ∀ q ∈ Pl, Single q := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hjb : col M j = bump M i := hAb j (hA0T j hj)
      have := isOT_bumpTerm hG i j
      unfold bumpTerm at this ⊢; rw [if_pos hjb] at this ⊢
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    have hdecP := hTD i h1 h2
    rw [hmapM, nzs_append, nzs_append, nzs_eq_self (fun t ht => single_ne_z (hsP t ht)),
      nzs_single (omega_ne_z G)] at hdecP
    have hpre := (List.pairwise_append.mp (List.pairwise_append.mp hdecP).1)
    have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
    have hPt : ∀ q ∈ Pl, omega G ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
    have hsL : ∀ t ∈ Pl ++ [omega G'], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hsP t ht
      · simp at ht; rw [ht]; exact single_omega hG'ot
    have hp'ot : isOT (sumN (one :: Pl ++ [omega G'])) = true := by
      apply isOT_sumN; intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact (hsL t ht).1
    have ev' : ρ'.v i = add V (omega (sumN (one :: Pl ++ [omega G']))) := by
      rw [ev'0, hmapT, ← List.cons_append, sf_ot (isOT_add hVot (isOT_omega hp'ot))]
    have hv'ot : isOT (ρ'.v i) = true := by rw [ev']; exact isOT_add hVot (isOT_omega hp'ot)
    refine ⟨hv'ot, ?_⟩
    rcases hGrel with hS | ⟨hWk, k, hk, w, hw, hok, hkx⟩
    · -- the strong case
      -- no collapse: a bump child with the only child `x` has `v(x) = 0`
      have hexcl : ∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z := by
        intro j hj _ hjx
        by_contra hvx
        have hxj : x ∈ children M j := by rw [hjx]; simp
        have hjxlt : j < x := (mem_children hxj).1
        have hjT : j ∈ children (M.take x) i := by
          rw [children_take, List.mem_filter]; exact ⟨hj, by simpa using hjxlt⟩
        have hjjl : j = jl := by
          rcases Nat.lt_trichotomy j jl with h | h | h
          · exfalso
            have hAx : Anc0 M j x := Anc0.step (mem_children_iff.mp hxj).2 (Anc0.refl j)
            have h1' := anc_between hAx jl (by omega) (by omega)
            have hpjl : par M 0 jl = some i := (mem_children_iff.mp hjlM).2
            have := (anc0_par h1' (by omega) hpjl).le
            have := (mem_children hj).1; omega
          · exact h
          · exfalso
            rw [hA] at hjT
            rcases List.mem_append.mp hjT with h' | h'
            · have := hA0lt j h'; omega
            · simp at h'; omega
        subst hjjl
        have hT' : children (M.take x) j = [] := by rw [children_take, hjx]; simp
        have hG'z : G' = z := by rw [hG'def, hT']; rfl
        have hox : ρ.o x = psi (ρ.v x) z z := o_of_no_counted hC (by omega) (hG.ot_v x (by omega))
          (fun c hc => by have := mem_children hc; omega)
        have hGx : G = psi (ρ.v x) z z := by
          rw [hGdef, hjx, List.map_singleton, sumN_singleton (single_o hC hG (by omega)), hox]
        rw [hG'z, hGx] at hS
        exact hvx (brelS_z_psi hS)
      have ht := brelS_omega hG'ot hGot hS
      have hp := brelS_p hsP hpP hPt (single_omega hG'ot) (single_omega hGot) ht
      have hsLM : ∀ t ∈ one :: (Pl ++ [omega G]), Single t := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨rfl, z, z, rfl⟩
        · rcases List.mem_append.mp ht with ht | ht
          · exact hsP t ht
          · simp at ht; rw [ht]; exact single_omega hGot
      have hpM : BRelS (sumN (one :: Pl ++ [omega G'])) (sumN (one :: (children M i).map (bumpTerm M ρ i))) := by
        rw [hmapM]
        rcases hXIc with rfl | ⟨rfl, hxi⟩
        · simpa using hp
        · have hxc : children M x = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro c hc; have := mem_children hc; omega
          by_cases hxb : col M x = bump M i
          · have hbx : bumpTerm M ρ i x = one := by
              unfold bumpTerm; rw [if_pos hxb, hxc]
              simp only [List.map_nil, sumN_nil]
              rw [omega_small (T.z_lt_psi _ _ _)]; rfl
            simp only [List.map_cons, List.map_nil, hbx]
            rw [show one :: (Pl ++ [omega G] ++ [one]) = (one :: (Pl ++ [omega G])) ++ [one] from rfl,
              sumN_snoc_ot (t := one) hsLM ⟨rfl, z, z, rfl⟩, add_one_eq_app]
            apply brelS_tail hp
            intro hz
            have := two_le_sumN_one_cons (l := Pl ++ [omega G]) (by simp)
              (fun t ht => hsLM t (List.mem_cons_of_mem _ ht))
            have hz' : sumN (one :: (Pl ++ [omega G])) = z := hz
            rw [hz'] at this
            exact absurd this (not_le_of_gt (T.z_lt_psi _ _ _))
          · have hbx : bumpTerm M ρ i x = z := by unfold bumpTerm; rw [if_neg hxb]
            simp only [List.map_cons, List.map_nil, hbx]
            rw [show one :: (Pl ++ [omega G] ++ [z]) = (one :: (Pl ++ [omega G])) ++ [z] from rfl,
              sumN_snoc_z (fun t ht => (hsLM t ht).1)]
            exact hp
      have hW := brelS_lhdE (brelS_omega hp'ot hpot hpM)
      left
      rw [ev', ev]
      apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
      intro r hr hn hlt
      by_cases hWE : omega (sumN (one :: (children M i).map (bumpTerm M ρ i))) < E0
      · exact lhd_lt_small (isOT_mem_summands hVot hr) hWE hlt
      · apply hAbs i h1 h2 hexcl r hr _ hlt
        intro hr2
        apply hn
        have h2le : two ≤ sumN (one :: Pl ++ [omega G']) :=
          two_le_sumN_one_cons (by simp) hsL
        have hom : psi z two z ≤ omega (sumN (one :: Pl ++ [omega G'])) := by
          rw [← omega_small two_lt_E0]
          rcases (le_iff _ _).mp h2le with h' | h'
          · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
          · rw [h']
        exact lt_of_lt_of_le hr2 hom
    · -- the weak case: excluded
      exact absurd hkx (fun h => hNW jl hjlM hjlb k hk ⟨w, hw, hok⟩ h)


/-- **Every column strictly between the parent `r` of `x` and `x` has `v′ ⊴ v`**: by induction from the
right. `x − 1` is strong (as in `pv_of`); a row-2-zero column reads the next column; a bump-type column
is `bump_rel_nw`, a weak source below it would be a column further right with `v′ ⋪ v`. -/
theorem v_lhd_B {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hp : par M 0 x = some r)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M x ρ) (hWS : BumpWeakSrc M x ρ ρ')
    (hX1 : UpgAbsX M x ρ)
    (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i) :
    ∀ d, r < d → d < x → LhdE (ρ'.v d) (ρ.v d) := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hoff := chg_off hx hC hG hC' hRk'
  have hrx : r < x := par_lt M 0 x r hp
  have hoot : ∀ k, ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun k j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  have key : ∀ m, ∀ d, x - d = m → r < d → d < x → LhdE (ρ'.v d) (ρ.v d) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro d hdm hrd hdx
      have IH : ∀ d', d < d' → d' < x → LhdE (ρ'.v d') (ρ.v d') :=
        fun d' h1 h2 => ih (x - d') (by omega) d' rfl (by omega) h2
      have hiT : d < (M.take x).length := by omega
      have hiM : d < M.length := by omega
      by_cases hCv : ChgX M x false d
      swap
      · rw [(hoff d hdx).2 hCv]; exact Or.inl rfl
      have h1 := chgx_e1 hCv
      by_cases h2 : entry M 2 d = 0
      swap
      · -- bump type
        have h := bump_rel_nw hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hKD hTD hAbs hWS hdx
          (fun j _ _ k _ hkx => hdrop k hkx) hCv h1 h2 (by
            intro jl hjl _ k hk _ hcase
            have hdj := (mem_children hjl).1
            have hjk := (mem_children hk).1
            rcases hcase with ⟨rfl, hjx⟩ | ⟨hkx, _, hnl⟩
            · have hxj : k ∈ children M jl := by rw [hjx]; simp
              have := (mem_children_iff.mp hxj).2; rw [hp] at this
              cases this; omega
            · exact hnl (IH k (by omega) hkx))
        rcases h.2 with h | h
        · exact h
        · exact h.elim
      -- row 2 is zero
      have hV : vOpt ρ' (par (M.take x) 1 d) = vOpt ρ (par M 1 d) := by
        rw [par_take M 1 d hdx]
        cases hpm : par M 1 d with
        | none => rfl
        | some m' =>
          show ρ'.v m' = ρ.v m'
          have hm := par_lt M 1 d m' hpm
          apply (hoff m' (by omega)).2
          intro hCm
          exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 d hdx hpm
      have hVot : isOT (vOpt ρ (par M 1 d)) = true := by
        cases hpm : par M 1 d with
        | none => rfl
        | some m' => exact hG.ot_v m' (by have := par_lt M 1 d m' hpm; omega)
      have hv1 : upg (M.take x) d = none → ρ'.v d = sf (add (vOpt ρ (par M 1 d)) one) := by
        intro hu
        rw [(hC' d hiT).2]; unfold vRhs
        rw [entry_take M 1 hdx, entry_take M 2 hdx, if_neg h1, if_pos h2, hu, hV]
      by_cases hix : d + 1 < x
      · have hupT : upg (M.take x) d = upg M d := upg_take M hix
        cases hu : upg M d with
        | none =>
          have e1 := hv1 (by rw [hupT, hu])
          have e2 : ρ.v d = sf (add (vOpt ρ (par M 1 d)) one) := by
            rw [(hC d hiM).2]; unfold vRhs; rw [if_neg h1, if_pos h2, hu]
          rw [e1, ← e2]; exact Or.inl rfl
        | some k =>
          have huT : upg (M.take x) d = some k := by rw [hupT, hu]
          have ek : ρ.v d = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
          have hkx : k < x := by
            have := upg_lt hiT huT; rw [hlenT] at this; exact this
          have ek' : ρ'.v d = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hdx]; exact h1)
            (by rw [entry_take M 2 hdx]; exact h2) huT (by rw [hV]; exact hVot)
            (fun j hj _ k' hk' => by
              have hk'x : k' < x := by
                have := (mem_children hk').2; rw [hlenT] at this; exact this
              exact (hdrop k' hk'x).1.2.1)
          rw [ek, ek']
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
          rcases hcase with rfl | ⟨hA, hki⟩
          · exact IH (d + 1) (by omega) hkx
          · by_cases hCk : ChgX M x false k
            · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
                ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl hkx) hkx hu hA hki).elim
            · rw [(hoff k hkx).2 hCk]; exact Or.inl rfl
      · -- `d = x − 1`
        have hixe : d + 1 = x := by omega
        have huT : upg (M.take x) d = none := by
          have : d = x - 1 := by omega
          rw [this]; exact upg_take_last M (by omega) (by omega)
        have e1 := hv1 huT
        have hot1 : isOT (add (vOpt ρ (par M 1 d)) one) = true := isOT_add hVot rfl
        rw [e1, sf_ot hot1]
        cases hu : upg M d with
        | none =>
          have e2 : ρ.v d = sf (add (vOpt ρ (par M 1 d)) one) := by
            rw [(hC d hiM).2]; unfold vRhs; rw [if_neg h1, if_pos h2, hu]
          rw [e2, sf_ot hot1]; exact Or.inl rfl
        | some k =>
          have ek : ρ.v d = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
          have hk := upg_lt hiM hu
          obtain ⟨m', hm1, hm2, hcol, _⟩ := upg_spec hu
          have hk1 : entry M 1 k ≠ 0 := by
            have : entry M 1 k = (col M k).2.1 := rfl
            rw [this, hcol]; exact h1
          have hk2 : entry M 2 k ≠ 0 := by
            have : entry M 2 k = (col M k).2.2 := rfl
            rw [this, hcol]; simp
          have hVk : vOpt ρ (par M 1 k) = vOpt ρ (par M 1 d) := by rw [hm1, hm2]
          obtain ⟨sW, yW, hvk, hWot, hW1⟩ := v_bump_form hC hk hk1 hk2 (by rw [hVk]; exact hVot) (hoot k)
          rw [hVk] at hvk
          rw [ek, hvk]
          have := v_frame_xm1 hVot hWot hW1 (fun r' hr' _ hlt =>
            hX1 d k _ hixe hu hvk (by simp) r' hr' hlt)
          rw [sf_ot hot1] at this
          exact this
  exact fun d h1 h2 => key (x - d) d rfl h1 h2

end Ytosk
