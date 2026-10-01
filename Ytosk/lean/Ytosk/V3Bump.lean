/-
**3 行: のりしろの枠（行 2 が 1 の列の添字）。**

v(i) = v(P_1 i) + ω(1 + Σ_j ω(Σ o(j の子)))（j はのりしろの子）。D に入る形では、最後の子 j がのりしろの子で、
その最後の子 k だけが D に入る。o(k) が fsD(o(k), ζ) に変わるとき、
G = Σ o(j の子) → fsD(G)、ω^G → ω^{fsD G}、p = 1 + … + ω^G（1 は吸収）→ fsD(p)、ω^p → ω^{fsD p}、
v(P_1 i) は 0 か吸収、の順に交換する。ω 冪の交換（`V3Omega`）は仮定 `hωG`・`hωp` に置く。
-/
import Ytosk.V3Omega

namespace Ytosk

open T

theorem one_lt_single {t : T} (h : Single t) (hne : t ≠ one) : one < t := by
  obtain ⟨_, s, y, rfl⟩ := h
  unfold one
  rw [T.psi_lt_psi]
  by_cases hs : s = z
  · subst hs
    by_cases hy : y = z
    · subst hy; exact absurd rfl hne
    · exact Or.inr (Or.inl ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hy)⟩)
  · exact Or.inl (lt_of_le_of_ne (z_le _) (Ne.symm hs))

/-- The leading `1` of `sumN (one :: l)` is absorbed when the first non-zero entry exceeds `1`. -/
theorem sumN_one_cons {l : List T} (hs : ∀ t ∈ l, t = z ∨ Single t)
    (hp : (nzs l).Pairwise (fun a b => b ≤ a)) (hgt : ∀ t ∈ nzs l, one < t) (hne : nzs l ≠ []) :
    sumN (one :: l) = sumN (nzs l) := by
  unfold sumN
  simp only [List.foldl_cons, add_z_left]
  have hone : isOT one = true := rfl
  rw [sf_ot hone]
  induction l with
  | nil => exact absurd rfl hne
  | cons t l ih =>
    rcases hs t List.mem_cons_self with rfl | ht
    · have hn : nzs (z :: l) = nzs l := by simp [nzs]
      rw [hn] at hp hgt hne ⊢
      simp only [List.foldl_cons, add_z_right, sf_ot hone]
      exact ih (fun t' h' => hs t' (List.mem_cons_of_mem _ h')) hp hgt hne
    · have htz := single_ne_z ht
      have hn : nzs (t :: l) = t :: nzs l := by simp [nzs, htz]
      rw [hn] at hp hgt ⊢
      have h1t : one < t := hgt t List.mem_cons_self
      obtain ⟨hot, s, y, rfl⟩ := ht
      have hstep : sf (add one (psi s y z)) = psi s y z := by
        unfold one
        rw [add_psi_psi, if_pos (by simpa [one] using h1t), sf_ot hot]
      simp only [List.foldl_cons, add_z_left, sf_ot hot, hstep]
      apply foldl_skip_z l _ hot (fun t' h' => hs t' (List.mem_cons_of_mem _ h'))
      simpa [summands] using hp

/-- **The bump frame.** -/
theorem hF_v_bump {M : Mat} {x i j k : Nat} {ρ ρN : Valn} {ζ : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K : List Nat} (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k])
    (hk : (glue M x ρ ρN ζ).o k = fsD (ρ.o k) ζ)
    (hK : ∀ d ∈ K, (glue M x ρ ρN ζ).o d = ρ.o d)
    (hL : ∀ d ∈ L, bumpTerm M (glue M x ρ ρN ζ) i d = bumpTerm M ρ i d)
    (hA : vOpt (glue M x ρ ρN ζ) (par M 1 i) = vOpt ρ (par M 1 i))
    -- the children of `j`
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t)
    (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsk' : Single (fsD (ρ.o k) ζ)) (hle : fsD (ρ.o k) ζ ≤ ρ.o k)
    -- the bump terms before `j`
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    -- the `ω` exchange at the top (the caller builds it from the one at `G`, `V3Omega`)
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
      (fun a b => b ≤ a))
    (hpp' : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))]).Pairwise
      (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hgt' : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))],
      one < t)
    (hωp : fsD (omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) ζ =
      omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ])))))
    (hAbs : ∀ X ∈ [omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [ρ.o k])))),
        omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))))],
      add (vOpt ρ (par M 1 i)) X = X) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ := by
  have hiM : i < M.length := by omega
  set ρ' := glue M x ρ ρN ζ with hρ'
  set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  set G' := sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]) with hG'def
  -- the bump term of `j`
  have hbj : ∀ σ : Valn, bumpTerm M σ i j = omega (sumN ((children M j).map σ.o)) := by
    intro σ; unfold bumpTerm; rw [if_pos hjb]
  have hGj : sumN ((children M j).map ρ.o) = G := by rw [hchj, List.map_append]; rfl
  have hGj' : sumN ((children M j).map ρ'.o) = G' := by
    rw [hchj, List.map_append, List.map_congr_left hK]; simp [hk, hG'def]
  have hl : (children M i).map (bumpTerm M ρ i) = L.map (bumpTerm M ρ i) ++ [omega G] := by
    rw [hch, List.map_append, List.map_singleton, hbj, hGj]
  have hl' : (children M i).map (bumpTerm M ρ' i) = L.map (bumpTerm M ρ i) ++ [omega G'] := by
    rw [hch, List.map_append, List.map_singleton, List.map_congr_left hL, hbj, hGj']
  -- `ω^G` is a single standard summand
  have hGot : isOT G := (sumN_dec _ hsK hpK).1
  have hsK' : ∀ t ∈ K.map ρ.o ++ [fsD (ρ.o k) ζ], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsK t (List.mem_append_left _ ht)
    · rw [List.mem_singleton] at ht; subst ht; exact hsk'
  have hpK' : (K.map ρ.o ++ [fsD (ρ.o k) ζ]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append] at hpK ⊢
    refine ⟨hpK.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans hle (hpK.2.2 a ha _ (List.mem_singleton_self _))
  have hG'ot : isOT G' := (sumN_dec _ hsK' hpK').1
  have hsω : ∀ Y, isOT Y = true → Single (omega Y) := by
    intro Y hY
    refine ⟨isOT_omega hY, ?_⟩
    unfold omega
    split
    · exact ⟨_, _, rfl⟩
    · split
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
  -- the sums `p`
  have hsl : ∀ t ∈ L.map (bumpTerm M ρ i) ++ [omega G], t = z ∨ Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; subst ht; exact Or.inr (hsω G hGot)
  have hsl' : ∀ t ∈ L.map (bumpTerm M ρ i) ++ [omega G'], t = z ∨ Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; subst ht; exact Or.inr (hsω G' hG'ot)
  have hnz : nzs (L.map (bumpTerm M ρ i) ++ [omega G]) = P ++ [omega G] := by
    rw [nzs_append, nzs_single (single_ne_z (hsω G hGot))]
  have hnz' : nzs (L.map (bumpTerm M ρ i) ++ [omega G']) = P ++ [omega G'] := by
    rw [nzs_append, nzs_single (single_ne_z (hsω G' hG'ot))]
  have hsP : ∀ t ∈ P ++ [omega G], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simp only [hPdef, nzs, List.mem_filter] at ht
      rcases hsL t ht.1 with h | h
      · exact absurd h (by simpa using ht.2)
      · exact h
    · rw [List.mem_singleton] at ht; subst ht; exact hsω G hGot
  have hsP' : ∀ t ∈ P ++ [omega G'], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsP t (List.mem_append_left _ ht)
    · rw [List.mem_singleton] at ht; subst ht; exact hsω G' hG'ot
  have hp : sumN (one :: (children M i).map (bumpTerm M ρ i)) = app (sumN P) (omega G) := by
    rw [hl, sumN_one_cons hsl (by rw [hnz]; exact hpp) (by rw [hnz]; exact hgt)
      (by rw [hnz]; simp), hnz, sumN_snoc_dec hsP hpp]
  have hp' : sumN (one :: (children M i).map (bumpTerm M ρ' i)) = app (sumN P) (omega G') := by
    rw [hl', sumN_one_cons hsl' (by rw [hnz']; exact hpp') (by rw [hnz']; exact hgt')
      (by rw [hnz']; simp), hnz', sumN_snoc_dec hsP' hpp']
  -- assemble
  have hpot : isOT (app (sumN P) (omega G)) = true := by
    rw [← sumN_snoc_dec hsP hpp]; exact (sumN_dec _ hsP hpp).1
  have hpot' : isOT (app (sumN P) (omega G')) = true := by
    rw [← sumN_snoc_dec hsP' hpp']; exact (sumN_dec _ hsP' hpp').1
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, hA, hp, hp',
    hAbs _ (List.mem_cons_self), hAbs _ (List.mem_cons_of_mem _ List.mem_cons_self),
    sf_ot (isOT_omega hpot), sf_ot (isOT_omega hpot'), hωp]

end Ytosk
