/-
**3 行・t = 1: v の枠の一般形（v(P_1 i) が吸収されなくてよい）。**

- `add_exchange`: A の加数で W 未満のものが W′ 未満でもあれば、同じ前半 B で A + W = B ++ W、A + W′ = B ++ W′。
- のりしろの枠 `hF_v_bumpG`・`stepV_bumpG`: v(i) = v(P_1 i) + W（W = ω^{P + ω^G}）、v(P_1 i) は吸収されなくてよい。
- 上げの枠 `stepV_upgL`: v(k) の代わりに最後の項 last v(k) で（v(k) は単一の項でなくてよい）。
-/
import Ytosk.V3StepV

namespace Ytosk

open T

/-- **Exchanging the absorbed tail.** -/
theorem add_exchange {A W W' : T} (hAot : isOT A = true) (hW : Single W) (hW' : Single W')
    (hle : W' ≤ W) (hAW : ∀ q ∈ summands A, q < W → q < W') :
    ∃ B, add A W = app B W ∧ add A W' = app B W' := by
  obtain ⟨_, s, y, rfl⟩ := hW
  obtain ⟨_, s', y', rfl⟩ := hW'
  obtain ⟨B, X, hAB, hX, hadd⟩ := add_prefix s y A
  refine ⟨B, hadd, ?_⟩
  have hBge : ∀ q ∈ summands B, ¬ q < psi s y z := by
    intro q hq hlt
    have hq' : q ∈ summands (add A (psi s y z)) := by
      rw [hadd, summands_app]; exact List.mem_append_left _ hq
    exact lt_irrefl' _ (lt_of_le_of_lt (add_summands_ge A q hq') hlt)
  rw [hAB]
  apply add_app_drop
  · intro q hq hlt
    exact hBge q hq (lt_of_lt_of_le hlt hle)
  · cases hXc : X with
    | z => exact Or.inl rfl
    | psi a b c =>
      right
      have hhX : head X ∈ summands A := by
        rw [hAB, summands_app, hXc]; apply List.mem_append_right; simp [summands, head]
      have h3 : head X < psi s y z := lt_of_le_of_lt (head_le_self X) hX
      have := hAW _ hhX h3
      rw [hXc] at this; exact this

/-- **The bump frame, general form**: `v(P_1 i)` need not be absorbed; its summands absorbed by `W` are
also absorbed by `W′`. -/
theorem hF_v_bumpG {M : Mat} {x i j k : Nat} {ρ ρN : Valn} {ζ : T} (hC : Cons M ρ)
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
    (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hAW : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k])))) →
      q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))))):
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

/-- **The value of a bump-type subscript**, general form: `v(i) = v(P_1 i) + W`. -/
theorem v_bump_valueG {M : Mat} {i j k : Nat} {ρ : Valn} (hC : Cons M ρ) (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K : List Nat} (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k])
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t)
    (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
      (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hAot : isOT (vOpt ρ (par M 1 i)) = true) :
    ρ.v i = add (vOpt ρ (par M 1 i)) (omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) := by
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
  rw [if_neg h1, if_neg h2, hp, sf_ot (isOT_add hAot (isOT_omega hpot))]



/-- **One bump frame** with hole tracking: `v(i) = ω^{P + ω^G}` and the hole of `o(k)` goes through
`G`, `ω^G`, `P + ω^G` and `ω^{P + ω^G}`. -/
theorem stepV_bumpG {M : Mat} {x i j k : Nat} {ρ ρN : Valn} {ζ μ br vr : T} (hC : Cons M ρ)
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
    (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hAW : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k])))) →
      q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ])))))
    (hHk : HoleT μ br vr (ρ.o k))
    (hpassG : ∀ s b c, sumN (K.map ρ.o ++ [ρ.o k]) = psi s b c →
      cof (sumN (K.map ρ.o ++ [ρ.o k])) = .big μ → lt μ s = true)
    (hpassP : ∀ s b c, app (sumN (nzs (L.map (bumpTerm M ρ i))))
        (omega (sumN (K.map ρ.o ++ [ρ.o k]))) = psi s b c →
      cof (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) =
        .big μ → lt μ s = true) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ ∧ HoleT μ br vr (ρ.v i) := by
  have hiM : i < M.length := by omega
  refine ⟨hF_v_bumpG hC hx hi h1 h2 hch hjb hchj hk hK hL hA hsK hpK hsk' hle hsL hpp hpp' hgt hgt'
    hωp hAot hAW, ?_⟩
  rw [v_bump_valueG hC hiM h1 h2 hch hjb hchj hsK hpK hsL hpp hgt hAot]
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
  have hHW := holeT_omega hpot (holeT_app _ hωGz hHωG) hpassP
  obtain ⟨_, s0, y0, hW0⟩ := single_omega hpot
  obtain ⟨B, X, _, _, hadd⟩ := add_prefix s0 y0 (vOpt ρ (par M 1 i))
  rw [hW0, hadd]; rw [hW0] at hHW
  exact holeT_app B (by simp) hHW

theorem last_ne_z_g : ∀ {t : T}, t ≠ z → last t ≠ z
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last]
  | psi a b (psi c d e), _ => by
    show last (psi c d e) ≠ z
    exact last_ne_z_g (by simp)

theorem holeT_last_g {μ br vr : T} : ∀ {t : T}, HoleT μ br vr t → HoleT μ br vr (last t)
  | z, h => absurd rfl (holeT_ne_z h)
  | psi a b z, h => h
  | psi a b (psi c d e), h => by
    show HoleT μ br vr (last (psi c d e))
    rcases h with h | ⟨a', ha', hD⟩
    · exact holeT_last_g (Or.inl (by simpa [cof] using h))
    · cases hD with
      | rest h' => exact holeT_last_g (Or.inr ⟨a', ha', h'⟩)

/-- `fsD` acts on the last summand. -/
theorem last_fsD {t ζ : T} (ht : t ≠ z) (hs : Single (fsD (last t) ζ)) :
    last (fsD t ζ) = fsD (last t) ζ := by
  conv => lhs; rw [← init_app_last t]
  rw [fsD_app _ (last_ne_z_g ht) ζ, last_app _ (single_ne_z hs)]
  obtain ⟨_, s, y, he⟩ := hs
  rw [he]; rfl

/-- **One upgrade frame, with the last summand of `v(U i)`** (`v(U i)` need not be a single term). -/
theorem stepV_upgL {M : Mat} {x i k : Nat} {ρ ρN : Valn} {ζ μ br vr : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x) (hk : k < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m)
    (hkd : DepX M x false k) (hV : Single (last (ρ.v k))) (hV' : Single (fsD (last (ρ.v k)) ζ))
    (hle : fsD (last (ρ.v k)) ζ ≤ last (ρ.v k))
    (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hAV : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) ζ)
    (hHk : HoleT μ br vr (ρ.v k)) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ ∧ HoleT μ br vr (ρ.v i) := by
  have hiM : i < M.length := by omega
  have hA : vOpt (glue M x ρ ρN ζ) (par M 1 i) = vOpt ρ (par M 1 i) := by
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      have hm : m < i := par_lt M 1 i m hp
      exact glue_v_lt ρ ρN ζ (by omega) (hpd m hp)
  have hkz : ρ.v k ≠ z := by
    intro h; have := single_ne_z hV; rw [h] at this; exact this rfl
  have hlast' : last ((glue M x ρ ρN ζ).v k) = fsD (last (ρ.v k)) ζ := by
    rw [glue_v_dep ρ ρN ζ hk hkd]; exact last_fsD hkz hV'
  obtain ⟨B, h1B, h2B⟩ := add_exchange hAot hV hV' hle hAV
  have hvi : ρ.v i = app B (last (ρ.v k)) := by
    rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu]
    simp only
    rw [sf_ot (isOT_add hAot hV.1), h1B]
  refine ⟨?_, ?_⟩
  · rw [hvi, fsD_app B (single_ne_z hV)]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu, hA]
    simp only
    rw [hlast', sf_ot (isOT_add hAot hV'.1), h2B]
  · rw [hvi]; exact holeT_app B (single_ne_z hV) (holeT_last_g hHk)

/-- The value of an upgrade-type subscript: `v(i) = B ++ last v(U i)`. -/
theorem upg_valL {M : Mat} {ρ : Valn} {i k : Nat} (hC : Cons M ρ) (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k) (hV : Single (last (ρ.v k)))
    (hAot : isOT (vOpt ρ (par M 1 i)) = true) : ∃ B, ρ.v i = app B (last (ρ.v k)) := by
  obtain ⟨hVot, s, y, hsy⟩ := hV
  obtain ⟨B, X, _, _, hadd⟩ := add_prefix s y (vOpt ρ (par M 1 i))
  refine ⟨B, ?_⟩
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_pos h2, hu]
  simp only
  rw [hsy, sf_ot (isOT_add hAot (by rw [← hsy]; exact hVot)), hadd]

theorem DiagAt.last_g {a b μ : T} : ∀ {t : T}, DiagAt a b μ t → DiagAt a b μ (last t)
  | z, h => by cases h
  | psi _ _ z, h => h
  | psi _ _ (psi c d e), h => by
    show DiagAt a b μ (last (psi c d e))
    cases h with
    | rest h' => exact DiagAt.last_g h'

/-- The cofinality is that of the last summand. -/
theorem cof_last_g : ∀ (t : T), cof (last t) = cof t
  | z => rfl
  | psi _ _ z => rfl
  | psi _ _ (psi c d e) => by
    show cof (last (psi c d e)) = cof (psi c d e)
    exact cof_last_g (psi c d e)

end Ytosk
