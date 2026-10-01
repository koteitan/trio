/-
**二つの行列の D の伝播（一般形）。**

行列 M（x と D = DepX M x）と別の行列 N（割り当て σ）について、範囲 bnd より前の D の呼び出しが
すべて Buchholz 氏の ◁ で真に下がる（`dep_lhd_gen`）。M の順位についての帰納法。
- 種の述語 Seed の呼び出しは仮定 hSeed（帰納法の仮定つき）で与える。
- 種でない o の呼び出し: v が D なら数える子がない（M と N で）。そうでなければ数える子の並びが M と N で
  同じ Lc ++ [c] で、c だけが D（`o_frame_lhd`）。
- 種でない v の呼び出し: 行 1・2、P_1、上げが M と N で同じ。bump 型ならのりしろの子 j が最後の子で、
  その最後の子 k だけが D（`g_brel`・`v_bump_lhd`）。
t = 0 の `t0_dep_lhd` と同じ証明を、構造の仮定を外に出して書いたもの（t = 2 などで使う）。
-/
import Ytosk.V3T0D

namespace Ytosk

open T

/-- **The `◁` propagation through `D`** for two matrices agreeing in structure off the seeds. -/
theorem dep_lhd_gen {M N : Mat} {x bnd : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ) (hRM : Rk M rk)
    (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (Seed : Bool → Nat → Prop)
    (hoff : ∀ i, i < bnd → (¬ DepX M x true i → σ.o i = ρ.o i) ∧ (¬ DepX M x false i → σ.v i = ρ.v i))
    (hSeed : ∀ b i, Seed b i → i < bnd → DepX M x b i →
      (∀ b' i', rk b' i' < rk b i → DepX M x b' i' → i' < bnd → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i))
    (hDvNil : ∀ c, c < bnd → DepX M x false c → CL M c = [])
    (hCLnil : ∀ c, c < bnd → CL M c = [] → CL N c = [])
    (hOc : ∀ i, i < bnd → ¬ Seed true i → DepX M x true i → ¬ DepX M x false i →
      ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ DepX M x true c ∧ c < bnd ∧
        ∀ d ∈ Lc, ¬ DepX M x true d ∧ d < bnd)
    (hVNN : ∀ i, i < bnd → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hVc : ∀ i, i < bnd → ¬ Seed false i → DepX M x false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepX M x false k → k < bnd) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < bnd ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepX M x true d ∧ d < bnd) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepX M x true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d)))
    (hAbs : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    ∀ b i, DepX M x b i → i < bnd → Lhd z (valB σ b i) (valB ρ b i) := by
  -- a call outside `D` with a changed `v` has argument `0` in `N`
  have hnoc : ∀ c, c < bnd → DepX M x false c → σ.o c = psi (σ.v c) z z := by
    intro c hc hd
    exact o_of_no_counted hCN (by omega) (hGN.ot_v c (by omega))
      (no_cnt_of_cl_nil (hCLnil c hc (hDvNil c hc hd)))
  have key : ∀ K, ∀ b i, rk b i ≤ K → DepX M x b i → i < bnd → Lhd z (valB σ b i) (valB ρ b i) := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hD hi
      have hiM : i < M.length := by omega
      have hiN : i < N.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      by_cases hs : Seed b i
      · exact hSeed b i hs hi hD (fun b' i' hlt hD' hi' => ih _ (by omega) b' i' (le_refl _) hD' hi')
      cases b with
      | true =>
        show Lhd z (σ.o i) (ρ.o i)
        by_cases hv : DepX M x false i
        · -- through `v`
          have hIH : Lhd z (σ.v i) (ρ.v i) := ih _ (by omega) false i (le_refl _) hv hi
          have hclM := hDvNil i hi hv
          rw [hnoc i hi hv, o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclM)]
          exact lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hIH)) (psi_lt_psi_z_iff.mpr (Or.inl hIH.1))
        · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hs hD hv
          have hv' := (hoff i hi).2 hv
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcch := cl_mem_children hcCL
          have hcnt : Counted M i c := by
            unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          have hIH : Lhd z (σ.o c) (ρ.o c) :=
            ih _ (by have := hRc c hcch hcnt.1 hcnt.2; omega) true c (le_refl _) hdc hcb
          have hcM : c < M.length := (mem_children hcch).2
          have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => (hoff d (hLc d hd).2).1 (hLc d hd).1
          have hfr := hVS i hiM Lc c [] (by rw [hclM])
          have hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c := by
            intro s y h
            obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
            rw [h] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hG.ot_v c hcM)]
          have hchv : σ.v c ≠ ρ.v c → σ.o c = psi (σ.v c) z z := by
            intro hne
            have hdv : DepX M x false c := by by_contra hn'; exact hne ((hoff c hcb).2 hn')
            exact hnoc c hcb hdv
          have hsv : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → σ.v c = ρ.v c → s' = s := by
            intro s y s' y' hsy hs'y' hvc
            obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show c < N.length by omega)
            rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hGN.ot_v c (by omega)), hvc, ← hvM s y hsy]
          apply o_frame_lhd hC hG hF hCN hGN hiM hiN hv' hclN hclM hsame hIH
          · intro s y hsy hrw
            rw [hvM s y hsy]; exact (hfr.2 s y hsy hrw).subSmall _
          · intro s y s' y' hsy hs'y' hrw
            by_cases hvc : σ.v c = ρ.v c
            · have hss := hsv s y s' y' hsy hs'y' hvc
              subst hss
              have hle : psi s' y' z ≤ psi s' y z := by rw [← hs'y', ← hsy]; exact le_of_lt hIH.1
              have hold : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧
                  lt (psi (ρ.v i) z z) (psi s' y z) = true := by
                rcases hrw with hn' | ho
                · have hyy : y' ≤ y := by
                    rcases (le_iff _ _).mp hle with hl | hl
                    · rcases psi_lt_psi_z_iff.mp hl with hl | ⟨_, hl⟩
                      · exact absurd hl (lt_irrefl' _)
                      · exact le_of_lt hl
                    · simp only [psi.injEq] at hl; rw [hl.2.1]
                  exact ⟨lt_of_lt_of_le hn'.1 hyy, lt_of_lt_of_le hn'.2 hle⟩
                · exact ho
              rw [hvM s' y hsy]; exact (hfr.2 s' y hsy hold).subSmall _
            · have ho0 := hchv hvc
              rw [hs'y'] at ho0; simp only [psi.injEq] at ho0
              rcases hrw with hn' | ho
              · exfalso; have := hn'.1; rw [ho0.2.1] at this; exact T.not_lt_z _ this
              · rw [ho0.1]; exact (hVNN i hi Lc c hclM hvc s y hsy ho).subSmall _
          · intro s hs
            have hclc : CL M c = [] := by
              by_contra hne
              have hlt := arg_lt_of_cl hC hG hcM hne
              rw [o_cl_eq hC hG hcM] at hs
              simp only [psi.injEq] at hs
              rw [hs.2.1] at hlt; exact lt_irrefl' _ hlt
            exact ⟨_, o_of_no_counted hCN (by omega) (hGN.ot_v c (by omega))
              (no_cnt_of_cl_nil (hCLnil c hcb hclc))⟩
          · intro s y s' y' hsy hs'y' hy'
            apply hsv s y s' y' hsy hs'y'
            by_contra hvc
            have := hchv hvc
            rw [hs'y'] at this; simp only [psi.injEq] at this; exact hy' this.2.1
      | false =>
        show Lhd z (σ.v i) (ρ.v i)
        obtain ⟨he1, he2, hpar, hpnd, hupg, hupgb, hbsh⟩ := hVc i hi hs hD
        have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
          cases hpp : par M 1 i with
          | none => rfl
          | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
        have hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i) := by
          rw [hpar]
          cases hpp : par M 1 i with
          | none => rfl
          | some m =>
            have := par_lt M 1 i m hpp
            exact (hoff m (by omega)).2 (hpnd m hpp)
        cases hD with
        | vpar h1 hpm hdm => exact absurd hdm (hpnd _ hpm)
        | @vupg _ k h1 h2 hu hdk =>
          have hkb := hupgb k hu hdk
          have hIH : Lhd z (σ.v k) (ρ.v k) :=
            ih _ (by have := (hRr h1).2.1 h2 k hu; omega) false k (le_refl _) hdk hkb
          have hVot' : isOT (vOpt σ (par N 1 i)) = true := by
            cases hpp : par N 1 i with
            | none => rfl
            | some m => exact hGN.ot_v m (by have := par_lt N 1 i m hpp; omega)
          have ek : ρ.v i = ρ.v k :=
            v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          have ek' : σ.v i = σ.v k :=
            v_upg_eq hCN hiN (by rw [he1]; exact h1) (by rw [he2]; exact h2) (by rw [hupg]; exact hu) hVot'
              (fun _ _ _ k' hk' => hGN.ot_o k' (mem_children hk').2)
          rw [ek, ek']; exact hIH
        | @vbump _ j0 k0 h1 h2 hj0 hjb0 hk0 hdk0 =>
          obtain ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN, hkb, he1k, hKnd, hLnd, hbL⟩ := hbsh h2
          have hjj : j0 = j := by
            rw [hch] at hj0
            rcases List.mem_append.mp hj0 with h | h
            · exact absurd hdk0 (hLnd j0 h k0 hk0)
            · exact List.mem_singleton.mp h
          subst hjj
          have hkk : k0 = k := by
            rw [hchj] at hk0
            rcases List.mem_append.mp hk0 with h | h
            · exact absurd hdk0 (hKnd k0 h).1
            · exact List.mem_singleton.mp h
          subst hkk
          have hkM : k0 < M.length := (mem_children (show k0 ∈ children M j0 by rw [hchj]; simp)).2
          have hj : j0 ∈ children M i := by rw [hch]; simp
          have hk : k0 ∈ children M j0 := by rw [hchj]; simp
          have hIH : Lhd z (σ.o k0) (ρ.o k0) :=
            ih _ (by have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega) true k0 (le_refl _) hdk0 hkb
          have hKv : Kb.map σ.o = Kb.map ρ.o :=
            List.map_congr_left (fun d hd => (hoff d (hKnd d hd).2).1 (hKnd d hd).1)
          have hbjM : bumpTerm M ρ i j0 = omega (sumN (Kb.map ρ.o ++ [ρ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
          have hbjN : bumpTerm N σ i j0 = omega (sumN (Kb.map ρ.o ++ [σ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjbN, hchjN, List.map_append, List.map_singleton, hKv]
          have hdec := hKD i h1 h2 j0 hj hjb
          rw [hchj, List.map_append, List.map_singleton] at hdec
          have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
            exact single_o hC hG (by have := (hKnd d hd).2; omega)
          have hform : (∃ s y y', ρ.o k0 = psi s y z ∧ σ.o k0 = psi s y' z) ∨
              (∃ w' w Y, σ.o k0 = psi w' z z ∧ ρ.o k0 = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
            obtain ⟨y1, hy1⟩ := o_psi_sub hC hkM
            rw [sf_ot (hG.ot_v k0 hkM)] at hy1
            by_cases hvk : σ.v k0 = ρ.v k0
            · obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show k0 < N.length by omega)
              rw [sf_ot (hGN.ot_v k0 (by omega)), hvk] at hy0
              exact Or.inl ⟨_, _, _, hy1, hy0⟩
            · have hdv : DepX M x false k0 := by by_contra hn'; exact hvk ((hoff k0 hkb).2 hn')
              have ho0 := hnoc k0 hkb hdv
              have hvIH : Lhd z (σ.v k0) (ρ.v k0) :=
                ih _ (by have := (hRM k0 hkM).1; have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega)
                  false k0 (le_refl _) hdv hkb
              have he1k' : entry M 1 k0 ≠ 0 := by
                intro he; apply hvk
                rw [v_z_of_e1 hC hkM he, v_z_of_e1 hCN (by omega) (by rw [he1k]; exact he)]
              have hv0 : σ.v k0 ≠ z := v_ne_z_of_e1 hCN (by omega) (by rw [he1k]; exact he1k')
              exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
          obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG hkM)
            (single_o hCN hGN (by omega)) hIH hform
          have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k0])) = true := isOT_sumN _ (fun u hu => by
            rcases List.mem_append.mp hu with h | h
            · exact (hsK u h).1
            · simp at h; rw [h]; exact hG.ot_o k0 hkM)
          exact v_bump_lhd hC hG hCN hiM hiN h1 h2 he1 he2 hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt
            hTD (hAbs i hi h1 h2)
  exact fun b i hD hi => key _ b i (le_refl _) hD hi

/-- **The closure of a set of seed calls** under the dependency edges of `M` (`DepX M x` is the closure
of `o(x)`). -/
inductive DepS (M : Mat) (S : Bool → Nat → Prop) : Bool → Nat → Prop
  | seed {b : Bool} {i : Nat} : S b i → DepS M S b i
  | ochild {i c : Nat} : c ∈ children M i → col M c ≠ bump M i →
      ¬ (isUpg M c = true ∧ topped M c = true) → DepS M S true c → DepS M S true i
  | ov {i : Nat} : DepS M S false i → DepS M S true i
  | vpar {i m : Nat} : entry M 1 i ≠ 0 → par M 1 i = some m → DepS M S false m → DepS M S false i
  | vupg {i k : Nat} : entry M 1 i ≠ 0 → entry M 2 i = 0 → upg M i = some k → DepS M S false k →
      DepS M S false i
  | vbump {i j k : Nat} : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → DepS M S true k → DepS M S false i

/-- **The `◁` propagation through a seeded closure `DepS M S`** for two matrices agreeing in structure off the seeds. -/
theorem deps_lhd_gen {M N : Mat} {S : Bool → Nat → Prop} {bnd : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ) (hRM : Rk M rk)
    (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hoff : ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i))
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ b' i', rk b' i' < rk b i → DepS M S b' i' → i' < bnd → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i))
    (hDvNil : ∀ c, c < bnd → DepS M S false c → CL M c = [])
    (hCLnil : ∀ c, c < bnd → CL M c = [] → CL N c = [])
    (hOc : ∀ i, i < bnd → ¬ S true i → DepS M S true i → ¬ DepS M S false i →
      ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ DepS M S true c ∧ c < bnd ∧
        ∀ d ∈ Lc, ¬ DepS M S true d ∧ d < bnd)
    (hVNN : ∀ i, i < bnd → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hVc : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepS M S false k → k < bnd) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < bnd ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepS M S true d ∧ d < bnd) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d)))
    (hAbs : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    ∀ b i, DepS M S b i → i < bnd → Lhd z (valB σ b i) (valB ρ b i) := by
  -- a call outside `D` with a changed `v` has argument `0` in `N`
  have hnoc : ∀ c, c < bnd → DepS M S false c → σ.o c = psi (σ.v c) z z := by
    intro c hc hd
    exact o_of_no_counted hCN (by omega) (hGN.ot_v c (by omega))
      (no_cnt_of_cl_nil (hCLnil c hc (hDvNil c hc hd)))
  have key : ∀ K, ∀ b i, rk b i ≤ K → DepS M S b i → i < bnd → Lhd z (valB σ b i) (valB ρ b i) := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hD hi
      have hiM : i < M.length := by omega
      have hiN : i < N.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      by_cases hs : S b i
      · exact hSeed b i hs hi hD (fun b' i' hlt hD' hi' => ih _ (by omega) b' i' (le_refl _) hD' hi')
      cases b with
      | true =>
        show Lhd z (σ.o i) (ρ.o i)
        by_cases hv : DepS M S false i
        · -- through `v`
          have hIH : Lhd z (σ.v i) (ρ.v i) := ih _ (by omega) false i (le_refl _) hv hi
          have hclM := hDvNil i hi hv
          rw [hnoc i hi hv, o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclM)]
          exact lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hIH)) (psi_lt_psi_z_iff.mpr (Or.inl hIH.1))
        · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hs hD hv
          have hv' := (hoff i hi).2 hv
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcch := cl_mem_children hcCL
          have hcnt : Counted M i c := by
            unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          have hIH : Lhd z (σ.o c) (ρ.o c) :=
            ih _ (by have := hRc c hcch hcnt.1 hcnt.2; omega) true c (le_refl _) hdc hcb
          have hcM : c < M.length := (mem_children hcch).2
          have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => (hoff d (hLc d hd).2).1 (hLc d hd).1
          have hfr := hVS i hiM Lc c [] (by rw [hclM])
          have hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c := by
            intro s y h
            obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
            rw [h] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hG.ot_v c hcM)]
          have hchv : σ.v c ≠ ρ.v c → σ.o c = psi (σ.v c) z z := by
            intro hne
            have hdv : DepS M S false c := by by_contra hn'; exact hne ((hoff c hcb).2 hn')
            exact hnoc c hcb hdv
          have hsv : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → σ.v c = ρ.v c → s' = s := by
            intro s y s' y' hsy hs'y' hvc
            obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show c < N.length by omega)
            rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hGN.ot_v c (by omega)), hvc, ← hvM s y hsy]
          apply o_frame_lhd hC hG hF hCN hGN hiM hiN hv' hclN hclM hsame hIH
          · intro s y hsy hrw
            rw [hvM s y hsy]; exact (hfr.2 s y hsy hrw).subSmall _
          · intro s y s' y' hsy hs'y' hrw
            by_cases hvc : σ.v c = ρ.v c
            · have hss := hsv s y s' y' hsy hs'y' hvc
              subst hss
              have hle : psi s' y' z ≤ psi s' y z := by rw [← hs'y', ← hsy]; exact le_of_lt hIH.1
              have hold : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧
                  lt (psi (ρ.v i) z z) (psi s' y z) = true := by
                rcases hrw with hn' | ho
                · have hyy : y' ≤ y := by
                    rcases (le_iff _ _).mp hle with hl | hl
                    · rcases psi_lt_psi_z_iff.mp hl with hl | ⟨_, hl⟩
                      · exact absurd hl (lt_irrefl' _)
                      · exact le_of_lt hl
                    · simp only [psi.injEq] at hl; rw [hl.2.1]
                  exact ⟨lt_of_lt_of_le hn'.1 hyy, lt_of_lt_of_le hn'.2 hle⟩
                · exact ho
              rw [hvM s' y hsy]; exact (hfr.2 s' y hsy hold).subSmall _
            · have ho0 := hchv hvc
              rw [hs'y'] at ho0; simp only [psi.injEq] at ho0
              rcases hrw with hn' | ho
              · exfalso; have := hn'.1; rw [ho0.2.1] at this; exact T.not_lt_z _ this
              · rw [ho0.1]; exact (hVNN i hi Lc c hclM hvc s y hsy ho).subSmall _
          · intro s hs
            have hclc : CL M c = [] := by
              by_contra hne
              have hlt := arg_lt_of_cl hC hG hcM hne
              rw [o_cl_eq hC hG hcM] at hs
              simp only [psi.injEq] at hs
              rw [hs.2.1] at hlt; exact lt_irrefl' _ hlt
            exact ⟨_, o_of_no_counted hCN (by omega) (hGN.ot_v c (by omega))
              (no_cnt_of_cl_nil (hCLnil c hcb hclc))⟩
          · intro s y s' y' hsy hs'y' hy'
            apply hsv s y s' y' hsy hs'y'
            by_contra hvc
            have := hchv hvc
            rw [hs'y'] at this; simp only [psi.injEq] at this; exact hy' this.2.1
      | false =>
        show Lhd z (σ.v i) (ρ.v i)
        obtain ⟨he1, he2, hpar, hpnd, hupg, hupgb, hbsh⟩ := hVc i hi hs hD
        have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
          cases hpp : par M 1 i with
          | none => rfl
          | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
        have hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i) := by
          rw [hpar]
          cases hpp : par M 1 i with
          | none => rfl
          | some m =>
            have := par_lt M 1 i m hpp
            exact (hoff m (by omega)).2 (hpnd m hpp)
        cases hD with
        | seed h => exact absurd h hs
        | vpar h1 hpm hdm => exact absurd hdm (hpnd _ hpm)
        | @vupg _ k h1 h2 hu hdk =>
          have hkb := hupgb k hu hdk
          have hIH : Lhd z (σ.v k) (ρ.v k) :=
            ih _ (by have := (hRr h1).2.1 h2 k hu; omega) false k (le_refl _) hdk hkb
          have hVot' : isOT (vOpt σ (par N 1 i)) = true := by
            cases hpp : par N 1 i with
            | none => rfl
            | some m => exact hGN.ot_v m (by have := par_lt N 1 i m hpp; omega)
          have ek : ρ.v i = ρ.v k :=
            v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          have ek' : σ.v i = σ.v k :=
            v_upg_eq hCN hiN (by rw [he1]; exact h1) (by rw [he2]; exact h2) (by rw [hupg]; exact hu) hVot'
              (fun _ _ _ k' hk' => hGN.ot_o k' (mem_children hk').2)
          rw [ek, ek']; exact hIH
        | @vbump _ j0 k0 h1 h2 hj0 hjb0 hk0 hdk0 =>
          obtain ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN, hkb, he1k, hKnd, hLnd, hbL⟩ := hbsh h2
          have hjj : j0 = j := by
            rw [hch] at hj0
            rcases List.mem_append.mp hj0 with h | h
            · exact absurd hdk0 (hLnd j0 h k0 hk0)
            · exact List.mem_singleton.mp h
          subst hjj
          have hkk : k0 = k := by
            rw [hchj] at hk0
            rcases List.mem_append.mp hk0 with h | h
            · exact absurd hdk0 (hKnd k0 h).1
            · exact List.mem_singleton.mp h
          subst hkk
          have hkM : k0 < M.length := (mem_children (show k0 ∈ children M j0 by rw [hchj]; simp)).2
          have hj : j0 ∈ children M i := by rw [hch]; simp
          have hk : k0 ∈ children M j0 := by rw [hchj]; simp
          have hIH : Lhd z (σ.o k0) (ρ.o k0) :=
            ih _ (by have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega) true k0 (le_refl _) hdk0 hkb
          have hKv : Kb.map σ.o = Kb.map ρ.o :=
            List.map_congr_left (fun d hd => (hoff d (hKnd d hd).2).1 (hKnd d hd).1)
          have hbjM : bumpTerm M ρ i j0 = omega (sumN (Kb.map ρ.o ++ [ρ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
          have hbjN : bumpTerm N σ i j0 = omega (sumN (Kb.map ρ.o ++ [σ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjbN, hchjN, List.map_append, List.map_singleton, hKv]
          have hdec := hKD i h1 h2 j0 hj hjb
          rw [hchj, List.map_append, List.map_singleton] at hdec
          have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
            exact single_o hC hG (by have := (hKnd d hd).2; omega)
          have hform : (∃ s y y', ρ.o k0 = psi s y z ∧ σ.o k0 = psi s y' z) ∨
              (∃ w' w Y, σ.o k0 = psi w' z z ∧ ρ.o k0 = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
            obtain ⟨y1, hy1⟩ := o_psi_sub hC hkM
            rw [sf_ot (hG.ot_v k0 hkM)] at hy1
            by_cases hvk : σ.v k0 = ρ.v k0
            · obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show k0 < N.length by omega)
              rw [sf_ot (hGN.ot_v k0 (by omega)), hvk] at hy0
              exact Or.inl ⟨_, _, _, hy1, hy0⟩
            · have hdv : DepS M S false k0 := by by_contra hn'; exact hvk ((hoff k0 hkb).2 hn')
              have ho0 := hnoc k0 hkb hdv
              have hvIH : Lhd z (σ.v k0) (ρ.v k0) :=
                ih _ (by have := (hRM k0 hkM).1; have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega)
                  false k0 (le_refl _) hdv hkb
              have he1k' : entry M 1 k0 ≠ 0 := by
                intro he; apply hvk
                rw [v_z_of_e1 hC hkM he, v_z_of_e1 hCN (by omega) (by rw [he1k]; exact he)]
              have hv0 : σ.v k0 ≠ z := v_ne_z_of_e1 hCN (by omega) (by rw [he1k]; exact he1k')
              exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
          obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG hkM)
            (single_o hCN hGN (by omega)) hIH hform
          have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k0])) = true := isOT_sumN _ (fun u hu => by
            rcases List.mem_append.mp hu with h | h
            · exact (hsK u h).1
            · simp at h; rw [h]; exact hG.ot_o k0 hkM)
          exact v_bump_lhd hC hG hCN hiM hiN h1 h2 he1 he2 hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt
            hTD (hAbs i hi h1 h2)
  exact fun b i hD hi => key _ b i (le_refl _) hD hi

/-- **The `◁` propagation through `DepS M S` with weak calls `W`** (excluded from the conclusion; only seeds read them) for two matrices agreeing in structure off the seeds. -/
theorem deps_lhd_genW {M N : Mat} {S W : Bool → Nat → Prop} {bnd : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ) (hRM : Rk M rk)
    (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hoff : ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i))
    (hWv : ∀ i, ¬ W false i)
    (hWo : ∀ i c, c ∈ children M i → Counted M i c → W true c → S true i)
    (hWb : ∀ i j c, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → W true c → S false i)
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ b' i', rk b' i' < rk b i → DepS M S b' i' → i' < bnd → ¬ W b' i' →
        Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i))
    (hDvNil : ∀ c, c < bnd → DepS M S false c → CL M c = [])
    (hCLnil : ∀ c, c < bnd → CL M c = [] → CL N c = [])
    (hOc : ∀ i, i < bnd → ¬ S true i → DepS M S true i → ¬ DepS M S false i →
      ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ DepS M S true c ∧ c < bnd ∧
        ∀ d ∈ Lc, ¬ DepS M S true d ∧ d < bnd)
    (hVNN : ∀ i, i < bnd → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hVc : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepS M S false k → k < bnd) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < bnd ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepS M S true d ∧ d < bnd) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d)))
    (hAbs : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    ∀ b i, DepS M S b i → i < bnd → ¬ W b i → Lhd z (valB σ b i) (valB ρ b i) := by
  -- a call outside `D` with a changed `v` has argument `0` in `N`
  have hnoc : ∀ c, c < bnd → DepS M S false c → σ.o c = psi (σ.v c) z z := by
    intro c hc hd
    exact o_of_no_counted hCN (by omega) (hGN.ot_v c (by omega))
      (no_cnt_of_cl_nil (hCLnil c hc (hDvNil c hc hd)))
  have key : ∀ K, ∀ b i, rk b i ≤ K → DepS M S b i → i < bnd → ¬ W b i →
      Lhd z (valB σ b i) (valB ρ b i) := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hD hi hWi
      have hiM : i < M.length := by omega
      have hiN : i < N.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      by_cases hs : S b i
      · exact hSeed b i hs hi hD (fun b' i' hlt hD' hi' hW' => ih _ (by omega) b' i' (le_refl _) hD' hi' hW')
      cases b with
      | true =>
        show Lhd z (σ.o i) (ρ.o i)
        by_cases hv : DepS M S false i
        · -- through `v`
          have hIH : Lhd z (σ.v i) (ρ.v i) := ih _ (by omega) false i (le_refl _) hv hi (hWv i)
          have hclM := hDvNil i hi hv
          rw [hnoc i hi hv, o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclM)]
          exact lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hIH)) (psi_lt_psi_z_iff.mpr (Or.inl hIH.1))
        · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hs hD hv
          have hv' := (hoff i hi).2 hv
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcch := cl_mem_children hcCL
          have hcnt : Counted M i c := by
            unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          have hIH : Lhd z (σ.o c) (ρ.o c) :=
            ih _ (by have := hRc c hcch hcnt.1 hcnt.2; omega) true c (le_refl _) hdc hcb
              (fun hw => hs (hWo i c hcch hcnt hw))
          have hcM : c < M.length := (mem_children hcch).2
          have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => (hoff d (hLc d hd).2).1 (hLc d hd).1
          have hfr := hVS i hiM Lc c [] (by rw [hclM])
          have hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c := by
            intro s y h
            obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
            rw [h] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hG.ot_v c hcM)]
          have hchv : σ.v c ≠ ρ.v c → σ.o c = psi (σ.v c) z z := by
            intro hne
            have hdv : DepS M S false c := by by_contra hn'; exact hne ((hoff c hcb).2 hn')
            exact hnoc c hcb hdv
          have hsv : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → σ.v c = ρ.v c → s' = s := by
            intro s y s' y' hsy hs'y' hvc
            obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show c < N.length by omega)
            rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hGN.ot_v c (by omega)), hvc, ← hvM s y hsy]
          apply o_frame_lhd hC hG hF hCN hGN hiM hiN hv' hclN hclM hsame hIH
          · intro s y hsy hrw
            rw [hvM s y hsy]; exact (hfr.2 s y hsy hrw).subSmall _
          · intro s y s' y' hsy hs'y' hrw
            by_cases hvc : σ.v c = ρ.v c
            · have hss := hsv s y s' y' hsy hs'y' hvc
              subst hss
              have hle : psi s' y' z ≤ psi s' y z := by rw [← hs'y', ← hsy]; exact le_of_lt hIH.1
              have hold : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧
                  lt (psi (ρ.v i) z z) (psi s' y z) = true := by
                rcases hrw with hn' | ho
                · have hyy : y' ≤ y := by
                    rcases (le_iff _ _).mp hle with hl | hl
                    · rcases psi_lt_psi_z_iff.mp hl with hl | ⟨_, hl⟩
                      · exact absurd hl (lt_irrefl' _)
                      · exact le_of_lt hl
                    · simp only [psi.injEq] at hl; rw [hl.2.1]
                  exact ⟨lt_of_lt_of_le hn'.1 hyy, lt_of_lt_of_le hn'.2 hle⟩
                · exact ho
              rw [hvM s' y hsy]; exact (hfr.2 s' y hsy hold).subSmall _
            · have ho0 := hchv hvc
              rw [hs'y'] at ho0; simp only [psi.injEq] at ho0
              rcases hrw with hn' | ho
              · exfalso; have := hn'.1; rw [ho0.2.1] at this; exact T.not_lt_z _ this
              · rw [ho0.1]; exact (hVNN i hi Lc c hclM hvc s y hsy ho).subSmall _
          · intro s hs
            have hclc : CL M c = [] := by
              by_contra hne
              have hlt := arg_lt_of_cl hC hG hcM hne
              rw [o_cl_eq hC hG hcM] at hs
              simp only [psi.injEq] at hs
              rw [hs.2.1] at hlt; exact lt_irrefl' _ hlt
            exact ⟨_, o_of_no_counted hCN (by omega) (hGN.ot_v c (by omega))
              (no_cnt_of_cl_nil (hCLnil c hcb hclc))⟩
          · intro s y s' y' hsy hs'y' hy'
            apply hsv s y s' y' hsy hs'y'
            by_contra hvc
            have := hchv hvc
            rw [hs'y'] at this; simp only [psi.injEq] at this; exact hy' this.2.1
      | false =>
        show Lhd z (σ.v i) (ρ.v i)
        obtain ⟨he1, he2, hpar, hpnd, hupg, hupgb, hbsh⟩ := hVc i hi hs hD
        have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
          cases hpp : par M 1 i with
          | none => rfl
          | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
        have hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i) := by
          rw [hpar]
          cases hpp : par M 1 i with
          | none => rfl
          | some m =>
            have := par_lt M 1 i m hpp
            exact (hoff m (by omega)).2 (hpnd m hpp)
        cases hD with
        | seed h => exact absurd h hs
        | vpar h1 hpm hdm => exact absurd hdm (hpnd _ hpm)
        | @vupg _ k h1 h2 hu hdk =>
          have hkb := hupgb k hu hdk
          have hIH : Lhd z (σ.v k) (ρ.v k) :=
            ih _ (by have := (hRr h1).2.1 h2 k hu; omega) false k (le_refl _) hdk hkb (hWv k)
          have hVot' : isOT (vOpt σ (par N 1 i)) = true := by
            cases hpp : par N 1 i with
            | none => rfl
            | some m => exact hGN.ot_v m (by have := par_lt N 1 i m hpp; omega)
          have ek : ρ.v i = ρ.v k :=
            v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          have ek' : σ.v i = σ.v k :=
            v_upg_eq hCN hiN (by rw [he1]; exact h1) (by rw [he2]; exact h2) (by rw [hupg]; exact hu) hVot'
              (fun _ _ _ k' hk' => hGN.ot_o k' (mem_children hk').2)
          rw [ek, ek']; exact hIH
        | @vbump _ j0 k0 h1 h2 hj0 hjb0 hk0 hdk0 =>
          obtain ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN, hkb, he1k, hKnd, hLnd, hbL⟩ := hbsh h2
          have hjj : j0 = j := by
            rw [hch] at hj0
            rcases List.mem_append.mp hj0 with h | h
            · exact absurd hdk0 (hLnd j0 h k0 hk0)
            · exact List.mem_singleton.mp h
          subst hjj
          have hkk : k0 = k := by
            rw [hchj] at hk0
            rcases List.mem_append.mp hk0 with h | h
            · exact absurd hdk0 (hKnd k0 h).1
            · exact List.mem_singleton.mp h
          subst hkk
          have hkM : k0 < M.length := (mem_children (show k0 ∈ children M j0 by rw [hchj]; simp)).2
          have hj : j0 ∈ children M i := by rw [hch]; simp
          have hk : k0 ∈ children M j0 := by rw [hchj]; simp
          have hIH : Lhd z (σ.o k0) (ρ.o k0) :=
            ih _ (by have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega) true k0 (le_refl _) hdk0 hkb
              (fun hw => hs (hWb i j0 k0 h1 h2 hj hjb hk hw))
          have hKv : Kb.map σ.o = Kb.map ρ.o :=
            List.map_congr_left (fun d hd => (hoff d (hKnd d hd).2).1 (hKnd d hd).1)
          have hbjM : bumpTerm M ρ i j0 = omega (sumN (Kb.map ρ.o ++ [ρ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
          have hbjN : bumpTerm N σ i j0 = omega (sumN (Kb.map ρ.o ++ [σ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjbN, hchjN, List.map_append, List.map_singleton, hKv]
          have hdec := hKD i h1 h2 j0 hj hjb
          rw [hchj, List.map_append, List.map_singleton] at hdec
          have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
            exact single_o hC hG (by have := (hKnd d hd).2; omega)
          have hform : (∃ s y y', ρ.o k0 = psi s y z ∧ σ.o k0 = psi s y' z) ∨
              (∃ w' w Y, σ.o k0 = psi w' z z ∧ ρ.o k0 = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
            obtain ⟨y1, hy1⟩ := o_psi_sub hC hkM
            rw [sf_ot (hG.ot_v k0 hkM)] at hy1
            by_cases hvk : σ.v k0 = ρ.v k0
            · obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show k0 < N.length by omega)
              rw [sf_ot (hGN.ot_v k0 (by omega)), hvk] at hy0
              exact Or.inl ⟨_, _, _, hy1, hy0⟩
            · have hdv : DepS M S false k0 := by by_contra hn'; exact hvk ((hoff k0 hkb).2 hn')
              have ho0 := hnoc k0 hkb hdv
              have hvIH : Lhd z (σ.v k0) (ρ.v k0) :=
                ih _ (by have := (hRM k0 hkM).1; have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega)
                  false k0 (le_refl _) hdv hkb (hWv k0)
              have he1k' : entry M 1 k0 ≠ 0 := by
                intro he; apply hvk
                rw [v_z_of_e1 hC hkM he, v_z_of_e1 hCN (by omega) (by rw [he1k]; exact he)]
              have hv0 : σ.v k0 ≠ z := v_ne_z_of_e1 hCN (by omega) (by rw [he1k]; exact he1k')
              exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
          obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG hkM)
            (single_o hCN hGN (by omega)) hIH hform
          have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k0])) = true := isOT_sumN _ (fun u hu => by
            rcases List.mem_append.mp hu with h | h
            · exact (hsK u h).1
            · simp at h; rw [h]; exact hG.ot_o k0 hkM)
          exact v_bump_lhd hC hG hCN hiM hiN h1 h2 he1 he2 hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt
            hTD (hAbs i hi h1 h2)
  exact fun b i hD hi hW => key _ b i (le_refl _) hD hi hW

end Ytosk
