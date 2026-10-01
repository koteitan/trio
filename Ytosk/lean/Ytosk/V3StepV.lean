/-
**3 行・t = 1: のりしろの枠の 1 段（穴の追跡つき）。**

`v_bump_value`: v(i) = ω^{P + ω^G}（G = のりしろの子 j の子の値の和、P = j より前ののりしろの項、v(P_1 i) は吸収）。
`stepV_bump`: 交換（`hF_v_bump`）と穴の追跡（`holeT_omega`・`holeT_app`）。
-/
import Ytosk.V3StepO

namespace Ytosk

open T

theorem single_omega {Y : T} (hY : isOT Y = true) : Single (omega Y) := by
  refine ⟨isOT_omega hY, ?_⟩
  unfold omega
  split
  · exact ⟨_, _, rfl⟩
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- **The value of a bump-type subscript.** -/
theorem v_bump_value {M : Mat} {i j k : Nat} {ρ : Valn} (hC : Cons M ρ) (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K : List Nat} (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k])
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t)
    (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
      (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hAbs : add (vOpt ρ (par M 1 i)) (omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
      (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) =
      omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) :
    ρ.v i = omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) := by
  set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  have hbj : bumpTerm M ρ i j = omega (sumN ((children M j).map ρ.o)) := by
    unfold bumpTerm; rw [if_pos hjb]
  have hGj : sumN ((children M j).map ρ.o) = G := by rw [hchj, List.map_append]; rfl
  have hl : (children M i).map (bumpTerm M ρ i) = L.map (bumpTerm M ρ i) ++ [omega G] := by
    rw [hch, List.map_append, List.map_singleton, hbj, hGj]
  have hGot : isOT G := (sumN_dec _ hsK hpK).1
  have hsω : ∀ Y, isOT Y = true → Single (omega Y) := fun _ h => single_omega h
  have hsl : ∀ t ∈ L.map (bumpTerm M ρ i) ++ [omega G], t = z ∨ Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; subst ht; exact Or.inr (hsω G hGot)
  have hnz : nzs (L.map (bumpTerm M ρ i) ++ [omega G]) = P ++ [omega G] := by
    rw [nzs_append, nzs_single (single_ne_z (hsω G hGot))]
  have hsP : ∀ t ∈ P ++ [omega G], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simp only [hPdef, nzs, List.mem_filter] at ht
      rcases hsL t ht.1 with h | h
      · exact absurd h (by simpa using ht.2)
      · exact h
    · rw [List.mem_singleton] at ht; subst ht; exact hsω G hGot
  have hp : sumN (one :: (children M i).map (bumpTerm M ρ i)) = app (sumN P) (omega G) := by
    rw [hl, sumN_one_cons hsl (by rw [hnz]; exact hpp) (by rw [hnz]; exact hgt)
      (by rw [hnz]; simp), hnz, sumN_snoc_dec hsP hpp]
  have hpot : isOT (app (sumN P) (omega G)) = true := by
    rw [← sumN_snoc_dec hsP hpp]; exact (sumN_dec _ hsP hpp).1
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_neg h2, hp, hAbs, sf_ot (isOT_omega hpot)]


/-- **One bump frame** with hole tracking: `v(i) = ω^{P + ω^G}` and the hole of `o(k)` goes through
`G`, `ω^G`, `P + ω^G` and `ω^{P + ω^G}`. -/
theorem stepV_bump {M : Mat} {x i j k : Nat} {ρ ρN : Valn} {ζ μ br vr : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K : List Nat} (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k])
    (hk : (glue M x ρ ρN ζ).o k = fsD (ρ.o k) ζ)
    (hK : ∀ d ∈ K, (glue M x ρ ρN ζ).o d = ρ.o d)
    (hL : ∀ d ∈ L, bumpTerm M (glue M x ρ ρN ζ) i d = bumpTerm M ρ i d)
    (hA : vOpt (glue M x ρ ρN ζ) (par M 1 i) = vOpt ρ (par M 1 i))
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t)
    (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsk' : Single (fsD (ρ.o k) ζ)) (hle : fsD (ρ.o k) ζ ≤ ρ.o k)
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
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
      add (vOpt ρ (par M 1 i)) X = X)
    (hHk : HoleT μ br vr (ρ.o k))
    (hpassG : ∀ s b c, sumN (K.map ρ.o ++ [ρ.o k]) = psi s b c →
      cof (sumN (K.map ρ.o ++ [ρ.o k])) = .big μ → lt μ s = true)
    (hpassP : ∀ s b c, app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k]))) = psi s b c →
      cof (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) =
        .big μ → lt μ s = true) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ ∧ HoleT μ br vr (ρ.v i) := by
  have hiM : i < M.length := by omega
  refine ⟨hF_v_bump hC hx hi h1 h2 hch hjb hchj hk hK hL hA hsK hpK hsk' hle hsL hpp hpp' hgt hgt'
    hωp hAbs, ?_⟩
  rw [v_bump_value hC hiM h1 h2 hch hjb hchj hsK hpK hsL hpp hgt (hAbs _ List.mem_cons_self)]
  set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  have hGot : isOT G = true := (sumN_dec _ hsK hpK).1
  have hkS : Single (ρ.o k) := hsK _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hHG : HoleT μ br vr G := by
    have hsK0 : ∀ t ∈ K.map ρ.o, Single t := fun t ht => hsK t (List.mem_append_left _ ht)
    have hG : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hsK hpK
    rw [hG]; exact holeT_app _ (single_ne_z hkS) hHk
  have hHωG := holeT_omega hGot hHG hpassG
  have hωGz : omega G ≠ z := holeT_ne_z hHωG
  have hsP : ∀ t ∈ P ++ [omega G], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simp only [hPdef, nzs, List.mem_filter] at ht
      rcases hsL t ht.1 with h | h
      · exact absurd h (by simpa using ht.2)
      · exact h
    · rw [List.mem_singleton] at ht; subst ht; exact single_omega hGot
  have hpot : isOT (app (sumN P) (omega G)) = true := by
    rw [← sumN_snoc_dec hsP hpp]; exact (sumN_dec _ hsP hpp).1
  exact holeT_omega hpot (holeT_app _ hωGz hHωG) hpassP
/-- **One upgrade frame, general form**: `v(i) = v(P_1 i) + v(U i)` where the summands of `v(P_1 i)`
absorbed by `v(U i)` are also absorbed by `fsD(v(U i), ζ)`. -/
theorem stepV_upgA {M : Mat} {x i k : Nat} {ρ ρN : Valn} {ζ μ br vr : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x) (hk : k < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m)
    (hkd : DepX M x false k) (hV : Single (ρ.v k)) (hV' : Single (fsD (ρ.v k) ζ))
    (hle : fsD (ρ.v k) ζ ≤ ρ.v k)
    (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hAV : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < ρ.v k → q < fsD (ρ.v k) ζ)
    (hHk : HoleT μ br vr (ρ.v k)) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ ∧ HoleT μ br vr (ρ.v i) := by
  have hiM : i < M.length := by omega
  have hA : vOpt (glue M x ρ ρN ζ) (par M 1 i) = vOpt ρ (par M 1 i) := by
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      have hm : m < i := par_lt M 1 i m hp
      exact glue_v_lt ρ ρN ζ (by omega) (hpd m hp)
  set A := vOpt ρ (par M 1 i) with hAdef
  obtain ⟨hVot, s, y, hsy⟩ := hV
  obtain ⟨hV'ot, s', y', hsy'⟩ := hV'
  obtain ⟨B, X, hAB, hX, hadd⟩ := add_prefix s y A
  have hvi : ρ.v i = app B (ρ.v k) := by
    rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu]
    simp only
    rw [← hAdef, hsy]; simp only [last]
    rw [sf_ot (isOT_add hAot (by rw [← hsy]; exact hVot)), hadd]
  -- the summands of `B` are not below `v(k)`
  have hBge : ∀ q ∈ summands B, ¬ q < psi s y z := by
    intro q hq hlt
    have hq' : q ∈ summands (add A (psi s y z)) := by
      rw [hadd, summands_app]; exact List.mem_append_left _ hq
    exact lt_irrefl' _ (lt_of_le_of_lt (add_summands_ge A q hq') hlt)
  refine ⟨?_, ?_⟩
  · have hfsd : fsD (ρ.v i) ζ = app B (psi s' y' z) := by
      rw [hvi, fsD_app B (by rw [hsy]; simp) ζ, hsy']
    rw [hfsd]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu, hA]
    simp only
    rw [glue_v_dep ρ ρN ζ hk hkd, hsy']
    simp only [last]
    rw [sf_ot (isOT_add hAot (by rw [← hsy']; exact hV'ot)), hAB]
    apply add_app_drop
    · intro q hq hlt
      apply hBge q hq
      have : psi s' y' z ≤ psi s y z := by rw [← hsy, ← hsy']; exact hle
      exact lt_of_lt_of_le hlt this
    · cases hXc : X with
      | z => exact Or.inl rfl
      | psi a b c =>
        right
        have hhX : head X ∈ summands A := by
          rw [hAB, summands_app, hXc]; apply List.mem_append_right; simp [summands, head]
        have h3 : head X < ρ.v k := by
          rw [hsy]; exact lt_of_le_of_lt (head_le_self X) hX
        have := hAV _ hhX h3
        rw [hsy', hXc] at this; exact this
  · rw [hvi]; exact holeT_app B (by rw [hsy]; simp) hHk

end Ytosk
