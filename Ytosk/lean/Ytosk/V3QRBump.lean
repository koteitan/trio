/-
**3 行・t = 1: のりしろの枠の一般形（任意の割り当て、子と親で添字が違ってよい）。**

`vRhs_bump_gen`: 子 k の値が fsD(o(k), ζc)、親の交換が fsD(W, ζp) = W′ なら v(i) の右辺は fsD(v(i), ζp)。
q = r の引き上げ（ζp = next ζc など）にも、ζ が列ごとの貼り合わせ（glueZ）にも使える。
-/
import Ytosk.V3QRFrame

namespace Ytosk

open T

theorem vRhs_bump_gen {M : Mat} {i j k : Nat} {ρ ρ' : Valn} {ζc ζp : T} (hC : Cons M ρ)
    (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K : List Nat} (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k])
    (hk : ρ'.o k = fsD (ρ.o k) ζc)
    (hK : ∀ d ∈ K, ρ'.o d = ρ.o d)
    (hL : ∀ d ∈ L, bumpTerm M ρ' i d = bumpTerm M ρ i d)
    (hA : vOpt ρ' (par M 1 i) = vOpt ρ (par M 1 i))
    -- the children of `j`
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t)
    (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsk' : Single (fsD (ρ.o k) ζc)) (hle : fsD (ρ.o k) ζc ≤ ρ.o k)
    -- the bump terms before `j`
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    -- the `ω` exchange at the top (the caller builds it from the one at `G`, `V3Omega`)
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
      (fun a b => b ≤ a))
    (hpp' : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζc]))]).Pairwise
      (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hgt' : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζc]))],
      one < t)
    (hωp : fsD (omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) ζp =
      omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζc])))))
    (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hAW : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k])))) →
      q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζc]))))):
    vRhs M ρ' i = fsD (ρ.v i) ζp := by
  set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  set G' := sumN (K.map ρ.o ++ [fsD (ρ.o k) ζc]) with hG'def
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
  have hsK' : ∀ t ∈ K.map ρ.o ++ [fsD (ρ.o k) ζc], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsK t (List.mem_append_left _ ht)
    · rw [List.mem_singleton] at ht; subst ht; exact hsk'
  have hpK' : (K.map ρ.o ++ [fsD (ρ.o k) ζc]).Pairwise (fun a b => b ≤ a) := by
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
  have hle' : omega (app (sumN P) (omega G')) ≤ omega (app (sumN P) (omega G)) := by
    rcases (le_iff _ _).mp hle with h | h
    · have hG'G : G' < G := by
        rw [hG'def, hGdef, sumN_snoc_dec hsK' hpK', sumN_snoc_dec hsK hpK]
        exact app_lt_app_left _ h
      have hωlt := omega_lt_omega hG'ot hGot hG'G
      exact le_of_lt (omega_lt_omega hpot' hpot (app_lt_app_left _ hωlt))
    · rw [hG'def, h]
  obtain ⟨B, hB1, hB2⟩ := add_exchange hAot (single_omega hpot) (single_omega hpot') hle' hAW
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, hA, hp, hp',
    sf_ot (isOT_add hAot (isOT_omega hpot)), sf_ot (isOT_add hAot (isOT_omega hpot')), hB1, hB2,
    fsD_app B (single_ne_z (single_omega hpot)), hωp]

end Ytosk
