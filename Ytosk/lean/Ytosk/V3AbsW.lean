/-
**弱い吸収の仮定 AbsWN（のりしろの v の枠）。**

v(P_1 i) の加数 q のうち、N の新しいのりしろの項 bumpW N σ i に吸収されないもの（¬ q < W′）だけについて
q ◁ bumpW M ρ i を求める。強い形（すべての q ≥ ω²、BumpAbsS）は標準形で偽（drop-fix、ext1 の 22 件）。
`v_bump_lhdW` は V3T0D の v_bump_lhd を弱い仮定にした写し（使うのは v_strong の吸収されない加数だけ）。
落とし（N = M.take x）では drop-fix の BumpAbsC がこの形、展開（N = M[n]）では N 側の残り。
-/
import Ytosk.V3T0D

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **The weak absorption** before `bnd`: summands of `v(P_1 i)` that survive the new bump term. -/
def AbsWN (M N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
    ¬ q < psi z two z → ¬ q < bumpW N σ i → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)

theorem AbsWN.of_strong {M N : Mat} {bnd : Nat} {ρ σ : Valn}
    (h : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) : AbsWN M N bnd ρ σ :=
  fun i hi h1 h2 q hq hq2 _ hlt => h i hi h1 h2 q hq hq2 hlt

/-- **The bump-type `v` frame of two matrices**, with the absorption only for the summands of `v(P_1 i)` that
survive the new bump term `bumpW N σ i` (the weak form; see `v_bump_lhd` in V3T0D for the strong one).
The rest as in `v_bump_lhd`: with the same children at `i` and at its last (bump)
child `j`, where the sum `G` of the children of `j` changes in the strong relation and strictly. -/
theorem v_bump_lhdW {M N : Mat} {ρ σ : Valn} {i j : Nat} {L : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = omega G) (hbjN : bumpTerm N σ i j = omega G')
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : BRelS G' G) (hlt : G' < G)
    (hTD : BumpTermDec M ρ)
    (hAbs : ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z → ¬ q < bumpW N σ i →
      q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    Lhd z (σ.v i) (ρ.v i) := by
  set V := vOpt ρ (par M 1 i) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef]
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  set Lb := L.map (bumpTerm M ρ i) with hLb
  have hLbot : ∀ t ∈ Lb, isOT t = true := fun t ht => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hmapM : (children M i).map (bumpTerm M ρ i) = Lb ++ [omega G] := by
    rw [hchM, List.map_append, List.map_singleton, hbjM]
  have hmapN : (children N i).map (bumpTerm N σ i) = Lb ++ [omega G'] := by
    rw [hchN, List.map_append, List.map_singleton, hbjN, List.map_congr_left hbL]
  set Pl := nzs Lb with hPl
  have hsumM : sumN (one :: (Lb ++ [omega G])) = sumN (one :: Pl ++ [omega G]) := by
    rw [sumN_nzs (l := one :: (Lb ++ [omega G])) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · simp at ht; rw [ht]; exact isOT_omega hGot)]
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one, omega_ne_z G]
    rw [hPl, nzs]; simp
  have hsumN : sumN (one :: (Lb ++ [omega G'])) = sumN (one :: Pl ++ [omega G']) := by
    rw [sumN_nzs (l := one :: (Lb ++ [omega G'])) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · simp at ht; rw [ht]; exact isOT_omega hG'ot)]
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one, omega_ne_z G']
    rw [hPl, nzs]; simp
  have hsP : ∀ q ∈ Pl, Single q := by
    intro q hq
    rw [hPl, nzs, List.mem_filter] at hq
    obtain ⟨hq, hqz⟩ := hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    unfold bumpTerm at hqz ⊢
    by_cases hb : col M d = bump M i
    · rw [if_pos hb]
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    · rw [if_neg hb] at hqz; simp at hqz
  have hdecP := hTD i h1 h2
  rw [hmapM, nzs_append, nzs_single (omega_ne_z G)] at hdecP
  have hpre := List.pairwise_append.mp hdecP
  have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
  have hPt : ∀ q ∈ Pl, omega G ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
  have hPot : ∀ t ∈ one :: Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact (hsP t ht).1
  have hp'ot : isOT (sumN (one :: Pl ++ [omega G'])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot)
  have hpot : isOT (sumN (one :: Pl ++ [omega G])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact isOT_omega hGot)
  have ev : ρ.v i = add V (omega (sumN (one :: Pl ++ [omega G]))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hmapM, hsumM, sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev' : σ.v i = add V (omega (sumN (one :: Pl ++ [omega G']))) := by
    rw [(hCN i hiN).2]; unfold vRhs
    rw [he1, he2, if_neg h1, if_neg h2, hV, hmapN, hsumN, sf_ot (isOT_add hVot (isOT_omega hp'ot))]
  have hp := brelS_p hsP hpP hPt (single_omega hG'ot) (single_omega hGot) (brelS_omega hG'ot hGot hS)
  have hW := brelS_lhdE (brelS_omega hp'ot hpot hp)
  have hbW : bumpW M ρ i = omega (sumN (one :: Pl ++ [omega G])) := by
    unfold bumpW; rw [hmapM, hsumM]
  have hE : LhdE (σ.v i) (ρ.v i) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
    intro q hq hn hlt'
    by_cases hWE : omega (sumN (one :: Pl ++ [omega G])) < E0
    · exact lhd_lt_small (isOT_mem_summands hVot hq) hWE hlt'
    · rw [← hbW]
      have hbWN : bumpW N σ i = omega (sumN (one :: Pl ++ [omega G'])) := by
        unfold bumpW; rw [hmapN, hsumN]
      apply hAbs q hq _ (by rw [hbWN]; exact hn) (by rw [hbW]; exact hlt')
      intro hq2
      apply hn
      have h2le : two ≤ sumN (one :: Pl ++ [omega G']) :=
        two_le_sumN_one_cons (by simp) (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hsP t h
          · simp at h; rw [h]; exact single_omega hG'ot)
      have hom : psi z two z ≤ omega (sumN (one :: Pl ++ [omega G'])) := by
        rw [← omega_small two_lt_E0]
        rcases (le_iff _ _).mp h2le with h' | h'
        · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
        · rw [h']
      exact lt_of_lt_of_le hq2 hom
  apply lhd_of_lhdE_lt hE
  rw [ev', ev]
  apply add_lt_add_left
  apply omega_lt_omega hp'ot hpot
  exact sumN_snoc_lt hPot hPot (isOT_omega hG'ot) (isOT_omega hGot) (le_refl _)
    (omega_lt_omega hG'ot hGot hlt)

end Ytosk
