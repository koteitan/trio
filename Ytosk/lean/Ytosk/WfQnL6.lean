/-
**WfQnL6 (2026-11-01): (E2) — the value of the glue at a bump call of `D` without the absorption field.**
- `BumpNA`: the `ζ`-data of a bump frame of `D` (shape, `W = ω^{P + ω^G}`, `W[ζ] = ω^{P + ω^{G'}}`), which
  `vlocal_t1_at` computes before it uses the absorption field; `bump_na` gives it at every bump call of `D`.
- `bumpW_glue_na`: the bump term of the glue is `W[ζ]`.
- `vRhs_glue_bad` (E2): the right side of the glue at a bump call of `D` is `sf(add v(P₁ i) W[ζ])`; at a bad call
  (`W = A = o(r)`) this is `sf(add v(P₁ i) A[ζ])`, the non-absorbed value (measured, WfQnE notes).
-/
import Ytosk.WfQnL1

namespace Ytosk.WfQnL6
open T Ytosk

/-- The `ζ`-data of a bump frame of `D` (no absorption). -/
def BumpNA (M : Mat) (x : Nat) (ρ : Valn) (ζ : T) (i : Nat) : Prop :=
  ∃ L K j k, children M i = L ++ [j] ∧ col M j = bump M i ∧ children M j = K ++ [k] ∧
    DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
    (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e) ∧
    fsD (bumpW M ρ i) ζ =
      omega (sumN (one :: (L.map (bumpTerm M ρ i) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))])))

/-- **The bump term of the glue** is `W[ζ]`. -/
theorem bumpW_glue_na {M : Mat} {x : Nat} {ρ ρN : Valn} {ζ : T} {i : Nat} (hx : x + 1 = M.length)
    (hxN : ρN.o x = fsD (ρ.o x) ζ) (hna : BumpNA M x ρ ζ i) :
    bumpW M (glueZ M x ρ ρN (fun _ => ζ)) i = fsD (bumpW M ρ i) ζ := by
  obtain ⟨L, K, j, k, hch, hjb, hchj, hkd, hKnd, hLnd, hW⟩ := hna
  have hk : k ∈ children M j := by rw [hchj]; simp
  have hkx : k ≤ x := by have := (mem_children hk).2; omega
  have hko : (glueZ M x ρ ρN (fun _ => ζ)).o k = fsD (ρ.o k) ζ := by
    rcases Nat.lt_or_ge k x with h | h
    · exact glueZ_o_dep ρ ρN _ h hkd
    · have : k = x := by omega
      subst this; rw [glueZ_o_ge ρ ρN _ (le_refl _)]; exact hxN
  have hK : ∀ d ∈ K, (glueZ M x ρ ρN (fun _ => ζ)).o d = ρ.o d := by
    intro d hd'
    have hsort := children_sorted M j
    rw [hchj] at hsort
    have hdk : d < k := (List.pairwise_append.mp hsort).2.2 d hd' k (List.mem_singleton_self _)
    exact glueZ_o_lt ρ ρN _ (by omega) (hKnd d hd')
  have hL : ∀ d ∈ L, bumpTerm M (glueZ M x ρ ρN (fun _ => ζ)) i d = bumpTerm M ρ i d := by
    intro d hd'
    unfold bumpTerm
    split
    · congr 2
      apply List.map_congr_left
      intro e he
      exact glueZ_o_lt ρ ρN _ (hLnd d hd' e he).1 (hLnd d hd' e he).2
    · rfl
  rw [hW]
  unfold bumpW
  rw [hch, List.map_append, List.map_congr_left hL, List.map_singleton]
  unfold bumpTerm
  rw [if_pos hjb, hchj, List.map_append, List.map_congr_left hK, List.map_singleton, hko]


/-- **(E2)**: the right side of the glue at a bump call of `D` is `sf(add v(P₁ i) W[ζ])`. -/
theorem vRhs_glue_na {M : Mat} {x : Nat} {ρ ρN : Valn} {ζ : T} {i : Nat} (hx : x + 1 = M.length)
    (hxN : ρN.o x = fsD (ρ.o x) ζ) (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m) (hna : BumpNA M x ρ ζ i) :
    vRhs M (glueZ M x ρ ρN (fun _ => ζ)) i = sf (add (vOpt ρ (par M 1 i)) (fsD (bumpW M ρ i) ζ)) := by
  rw [← bumpW_glue_na hx hxN hna]
  have hA : vOpt (glueZ M x ρ ρN (fun _ => ζ)) (par M 1 i) = vOpt ρ (par M 1 i) :=
    vOpt_glue (ρN := ρN) (ζ := ζ) hx hi hpd
  unfold vRhs
  rw [if_neg h1, if_neg h2, hA]
  rfl

/-- **(E2) at a bad call**: with `W = A = o(r)` the value is `sf(add v(P₁ i) A[ζ])`, still below `A`. -/
theorem vRhs_glue_bad {M : Mat} {x r : Nat} {ρ ρN : Valn} {ζ a b : T} {i : Nat} (hx : x + 1 = M.length)
    (hxN : ρN.o x = fsD (ρ.o x) ζ) (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m) (hna : BumpNA M x ρ ζ i)
    (hW : bumpW M ρ i = ρ.o r) (hro : ρ.o r = psi a b z)
    (hVot : isOT (vOpt ρ (par M 1 i)) = true) (hfot : isOT (fsD (psi a b z) ζ) = true)
    (hVlt : vOpt ρ (par M 1 i) < psi a b z) (hflt : fsD (psi a b z) ζ < psi a b z) :
    vRhs M (glueZ M x ρ ρN (fun _ => ζ)) i = sf (add (vOpt ρ (par M 1 i)) (fsD (ρ.o r) ζ)) ∧
      sf (add (vOpt ρ (par M 1 i)) (fsD (ρ.o r) ζ)) < ρ.o r := by
  refine ⟨by rw [vRhs_glue_na hx hxN hi h1 h2 hpd hna, hW], ?_⟩
  rw [hro]
  exact WfQnE2.bad_v_lt hVot hfot hVlt hflt

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ X : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
  (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
  (hHx : HoleT μ br vr (ρ.o x))
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
  (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
    DepX M x true k → k ≤ r)
  (hTPLζ : ∀ c, c < M.length → DepX M x true c → ∀ s y, ρ.o c = psi s y z →
    (split y (psi (succ s) z z)).2 = z → ∀ a, last y = psi a z z → isSucc a = false →
    OHole a → holeLev y = μ → ¬ psi (fsD a ζ) z z < psi (succ s) z z) (hAUζ : ∀ i k, i < x → DepX M x false i → upg M i = some k →
    OHole (last (ρ.v k)) → holeLev (last (ρ.v k)) = μ →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) ζ) (hbrl : last br ≠ psi (succ μ) z z)
  (hζ : ζ = psi μ X z) (hXz : X ≠ z) (hζfix : omega ζ = ζ) (hζΩ : etaOm μ ≤ ζ)
  (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hHx hF1 hOS hS2 hS3
  hTPLζ hAUζ hbrl hζ hXz hζfix hζΩ hok

omit hAUζ in
/-- **The `ζ`-data at every bump call of `D`** (the part of `vlocal_t1_at` before the absorption). -/
theorem bump_na (i : Nat) (hi : i < x) (hv : DepX M x false i) (h2i : entry M 2 i ≠ 0) :
    BumpNA M x ρ ζ i := by
  have hH := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hHx
    hF1 hOS hS2 hS3
  have hζz : ζ ≠ z := by rw [hζ]; simp
  obtain ⟨h1, hpd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  rcases hcase with ⟨h2, hu, hk, hdk⟩ | ⟨h2, L, K, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
  · exact absurd h2 h2i
  · -- the bump frame
    have hkM : k < M.length := by
      have : k ∈ children M j := by rw [hchj]; simp
      exact (mem_children this).2
    obtain ⟨hHk, _, _⟩ := hH true k hdk (by
      rcases Nat.lt_or_ge k x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩)
    simp only [valB, cond_true] at hHk
    obtain ⟨hBD, _, _, _⟩ := v_bump_D hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hi h1 h2
      hch hjb hchj hHk
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hHG : HoleT μ br vr G := by rw [hGe]; exact holeT_app _ (single_ne_z hkS) hHk
    have hHωG := holeT_omega hGot hHG hBD.passG
    have hωGz : omega G ≠ z := holeT_ne_z hHωG
    have hHY2 : HoleT μ br vr (app (sumN P) (omega G)) := holeT_app _ hωGz hHωG
    have hHW := holeT_omega hBD.potW hHY2 hBD.passP
    -- `fsD(o(k), ζ)`
    obtain ⟨hfkot, hfklt⟩ := hok _ (hG.ot_o k hkM) hHk
    have hfkS : Single (fsD (ρ.o k) ζ) := by
      apply single_fsD (o_psi_form hC hkM) (holeT_not_succ hHk)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHk)) ⟨μ, X, hζ⟩ hfkot
    have hfkz : fsD (ρ.o k) ζ ≠ z := single_ne_z hfkS
    set G' := sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]) with hG'def
    have hsK' : ∀ t ∈ K.map ρ.o ++ [fsD (ρ.o k) ζ], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.sK t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht]; exact hfkS
    have hpK' : (K.map ρ.o ++ [fsD (ρ.o k) ζ]).Pairwise (fun a b => b ≤ a) := by
      have hpK := hBD.pK
      rw [List.pairwise_append] at hpK ⊢
      refine ⟨hpK.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans (le_of_lt hfklt) (hpK.2.2 a ha _ (List.mem_singleton_self _))
    have hG'ot : isOT G' = true := (sumN_dec _ hsK' hpK').1
    have hG'e : G' = app (sumN (K.map ρ.o)) (fsD (ρ.o k) ζ) := sumN_snoc_dec hsK' hpK'
    have hG'z : G' ≠ z := by rw [hG'e]; intro he; exact hfkz (app_eq_z he).2
    have hG'lt : G' < G := by rw [hG'e, hGe]; exact app_lt_app_left _ hfklt
    have hωle : omega G' ≤ omega G := le_of_lt (omega_lt_omega hG'ot hGot hG'lt)
    have hfG : fsD G ζ = G' := by rw [hGe, hG'e]; exact fsD_app _ (single_ne_z hkS) ζ
    -- TPL for `G` and for `P + ω^G`
    have hTG : ∀ s b, G = psi s b z → (split b (psi (succ s) z z)).2 = z → ∀ a, last b = psi a z z →
        isSucc a = false → OHole a → ¬ psi (fsD a ζ) z z < psi (succ s) z z := by
      intro s b hGsb hl a hla has hOa
      have hK0 : sumN (K.map ρ.o) = z := by
        by_contra hK
        exact app_single_ne hK (single_ne_z hkS) (by rw [← hGe]; exact hGsb)
      have hok' : ρ.o k = psi s b z := by rw [← hGsb, hGe, hK0]; rfl
      have hb : b ≠ z := by
        intro hb0; rw [hb0] at hla; simp [last] at hla
      have hHb := holeT_arg hb (by rw [← hok']; exact hHk) hcb
      exact hTPLζ k hkM hdk s b hok' hl a hla has hOa (holeLev_holeT hHb)
    have hTY2 : ∀ s b, app (sumN P) (omega G) = psi s b z → (split b (psi (succ s) z z)).2 = z →
        ∀ a, last b = psi a z z → isSucc a = false → OHole a →
        ¬ psi (fsD a ζ) z z < psi (succ s) z z := by
      intro s b hY hl
      have hP0 : sumN P = z := by
        by_contra hP; exact app_single_ne hP hωGz hY
      rw [hP0] at hY
      have hY' : omega G = psi s b z := hY
      have hfix := omega_single_nolo hGot (holeT_ne_z hHG) hY' hl
      exact hTG s b (by rw [← hfix]; exact hY') hl
    have hωGfs : fsD (omega G) ζ = omega G' := by
      rw [omega_fsD_hole_at hGot hHG hcb hbrl hζ hXz hζfix hζΩ hok hTG, hfG]
    have hωp : fsD (omega (app (sumN P) (omega G))) ζ = omega (app (sumN P) (omega G')) := by
      rw [omega_fsD_hole_at hBD.potW hHY2 hcb hbrl hζ hXz hζfix hζΩ hok hTY2,
        fsD_app _ hωGz ζ, hωGfs]
    have hpp' : (P ++ [omega G']).Pairwise (fun a b => b ≤ a) := by
      have hpp := hBD.pp
      rw [List.pairwise_append] at hpp ⊢
      refine ⟨hpp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans hωle (hpp.2.2 a ha _ (List.mem_singleton_self _))
    have hgt' : ∀ t ∈ P ++ [omega G'], one < t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.gt t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht, ← omega_z]
        exact omega_lt_omega rfl hG'ot (lt_of_le_of_ne (z_le _) (Ne.symm hG'z))
    have hωG' : Single (omega G') := single_omega hG'ot
    have hnz : nzs (L.map (bumpTerm M ρ i) ++ [omega G']) = P ++ [omega G'] := by
      rw [nzs_append, nzs_single (single_ne_z hωG')]
    have hsl : ∀ t ∈ L.map (bumpTerm M ρ i) ++ [omega G'], t = z ∨ Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.sL t ht
      · rw [List.mem_singleton] at ht; rw [ht]; exact Or.inr hωG'
    have hsP : ∀ t ∈ P ++ [omega G'], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · simp only [hPdef, nzs, List.mem_filter] at ht
        rcases hBD.sL t ht.1 with h | h
        · exact absurd h (by simpa using ht.2)
        · exact h
      · rw [List.mem_singleton] at ht; rw [ht]; exact hωG'
    refine ⟨L, K, j, k, hch, hjb, hchj, hdk, hKnd, hLnd, ?_⟩
    rw [hBD.W, hωp, sumN_one_cons hsl (by rw [hnz]; exact hpp') (by rw [hnz]; exact hgt') (by rw [hnz]; simp),
      hnz, sumN_snoc_dec hsP hpp']

end

end Ytosk.WfQnL6
