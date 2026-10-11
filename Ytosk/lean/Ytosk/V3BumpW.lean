/-
**のりしろの枠の吸収の仮定を弱めた形 `BumpAbsW`（`BumpAbsC` は標準形で偽）。**

`BumpAbsC`（`DropRes.ab`）は T0Ext の標準形で偽: M = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(3,0,0)、
i = 7、v(P_1 i) の加数 r = ω² と W = bumpW i = Ω_{ω²} で ω² ◁ Ω_{ω²} が偽（試す元 Ω_1）。落とす補題の結論は正しい
（v′(7) = ω² + Ω_1 = Ω_1 ◁ Ω_{ω²}、ω² は新しい項に吸収される）。`bump_rel` が使う（`v_strong` の hR）のは、
新しい v′(i) = V + W′ に残る加数（¬ r < W′）だけなので、その形 `BumpAbsW` に弱める（T0Ext・C′・deep3 で例外 0）。
-/
import Ytosk.V3BumpDrop

namespace Ytosk

open T

/-- **Hypothesis on the drop** (weak form of `BumpAbsC`): only the summands of `v(P_1 i)` that survive the
new bump term `W′ = bumpW (M.take x) σ′ i` need `◁ W`. -/
def BumpAbsW (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ σ', Cons (M.take x) σ' → ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    (∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z) →
    (StrongG M x ρ i ∨ XParNB M x ∨ ρ.v x = z) →
    ∀ r ∈ summands (vOpt ρ (par M 1 i)), ¬ r < bumpW (M.take x) σ' i → r < bumpW M ρ i →
      Lhd z r (bumpW M ρ i)

/-- **The bump-type `v` frame** (relation and standardness): `v′(i) ⊴ v(i)`, or weakly below with no
counted child of `i` in `M`. -/
theorem bump_relW {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsW M x ρ) (hWS : BumpWeakSrc M x ρ ρ')
    {i : Nat} (hi : i < x)
    (hIH : ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
      PO ρ ρ' k ∧ PV M ρ ρ' k)
    (hCv : ChgX M x false i) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) :
    isOT (ρ'.v i) = true ∧
      (LhdE (ρ'.v i) (ρ.v i) ∨ (WkVA (ρ'.v i) (ρ.v i) ∧ WCSP M ρ i (ρ'.v i) ∧ ∀ c ∈ children M i, ¬ Counted M i c)) := by
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
      · have hSG : StrongG M x ρ i := by
          refine ⟨ρ', hC', fun j hjT hjb => ?_⟩
          rw [hA] at hjT
          rcases List.mem_append.mp hjT with hj0 | hj0
          · obtain ⟨hch, ho, -⟩ := early_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h2
              (mem_children_take (hA0T j hj0)).2 hjlT (hA0lt j hj0)
            rw [hch, List.map_congr_left ho]
            exact brelS_refl
          · simp at hj0; subst hj0; exact hS
        apply hAbs ρ' hC' i h1 h2 hexcl (Or.inl hSG) r hr _ hlt
        unfold bumpW
        rw [hmapT]
        simpa using hn
    · -- the weak case
      by_cases hli : LhdE (ρ'.v i) (ρ.v i)
      · exact Or.inl hli
      have hkx' : (k = x ∧ children M jl = [x] ∧ ¬ LhdE (ρ'.v i) (ρ.v i)) ∨
          (k < x ∧ ρ'.o k ≠ ρ.o k ∧ ¬ LhdE (ρ'.v k) (ρ.v k)) := by
        rcases hkx with ⟨hk1, hk2⟩ | hk'
        · exact Or.inl ⟨hk1, hk2, hli⟩
        · exact Or.inr hk'
      obtain ⟨hone, _, hcsV⟩ := hWS i h1 h2 jl hjlM hjlb k hk ⟨w, hw, hok⟩ hkx'
      have hnil : A0 = [] ∧ XI = [] := by
        rw [hXI, hA] at hone
        have hl := congrArg List.length hone
        simp only [List.length_append, List.length_singleton] at hl
        exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
      obtain ⟨rfl, rfl⟩ := hnil
      have ht := bwk_omega hG'ot hGot hWk
      have hp := bwk_onep (single_omega hG'ot) (single_omega hGot) ht
      have hpot1 : isOT (sumN [one, omega G]) = true := by
        apply isOT_sumN; intro t ht; simp at ht; rcases ht with rfl | rfl
        · rfl
        · exact isOT_omega hGot
      have hp'ot1 : isOT (sumN [one, omega G']) = true := by
        apply isOT_sumN; intro t ht; simp at ht; rcases ht with rfl | rfl
        · rfl
        · exact isOT_omega hG'ot
      have hW := bwk_omega hp'ot1 hpot1 hp
      have e' : ρ'.v i = add V (omega (sumN [one, omega G'])) := by rw [ev']; simp [hPldef]
      have e : ρ.v i = add V (omega (sumN [one, omega G])) := by rw [ev, hmapM]; simp [hPldef]
      rw [e', e]
      rcases v_weak hVot hcsV (single_omega hp'ot1) (single_omega hpot1) hW with heq | hwk
      · exact Or.inl (Or.inl heq)
      · refine Or.inr ⟨hwk.1, hwk.2, fun c hc hcnt => ?_⟩
        rw [hone] at hc
        simp at hc
        rw [hc] at hcnt
        exact hcnt.1 hjlb

/-- **The bump-type `v` frame of the drop** (`hBump` of `drop_all`). -/
theorem bump_dropW {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsW M x ρ) (hWS : BumpWeakSrc M x ρ ρ') :
    ∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      PV M ρ ρ' i := by
  intro i hi hIH hCv h1 h2
  obtain ⟨hot, hrel⟩ := bump_relW hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hKD hTD hAbs hWS hi hIH
    hCv h1 h2
  exact ⟨hrel, hot⟩

end Ytosk
