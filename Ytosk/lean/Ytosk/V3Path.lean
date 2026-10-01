/-
**3 行: D の呼び出しの枠の補題（割り当ての側）。**

貼り合わせた割り当て `glue` で、D の呼び出しの右辺が fsD(M の値, ζ) になること（`cons_glue_lt` の仮定 `hF`）を、
局所的な形ごとに示す。
- `hF_o_last`: v(i) は D の外、数える子のうち最後の子 c だけが D（c の後ろの子は数えない子）。
- `hF_o_sub`: v(i) が D、数える子はない。
- `hF_v_upg`: 行 2 が 0、v(P_1 i) = 0、上げ U(i) が D で v(U i) は項 1 つ。
-/
import Ytosk.V3Frame

namespace Ytosk

open T

theorem nzs_append (a b : List T) : nzs (a ++ b) = nzs a ++ nzs b := by
  simp [nzs, List.filter_append]

theorem nzs_single {t : T} (h : t ≠ z) : nzs [t] = [t] := by simp [nzs, h]

theorem nzs_zeros : ∀ (l : List T), (∀ t ∈ l, t = z) → nzs l = []
  | [], _ => rfl
  | t :: l, h => by
    have ht := h t List.mem_cons_self
    subst ht
    simp only [nzs, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    exact nzs_zeros l (fun t' h' => h t' (List.mem_cons_of_mem _ h'))

theorem single_ne_z {t : T} (h : Single t) : t ≠ z := by
  obtain ⟨_, s, y, rfl⟩ := h; simp

/-- Uncounted children contribute `0` under any valuation. -/
theorem cnt_unc {M : Mat} {i d : Nat} (ρ : Valn)
    (h : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) : cnt M ρ i d = z := by
  unfold cnt
  rcases h with h | h
  · rw [if_pos h]
  · by_cases hb : col M d = bump M i
    · rw [if_pos hb]
    · rw [if_neg hb, if_pos h]

theorem cnt_cnt {M : Mat} {i d : Nat} (ρ : Valn) (hb : col M d ≠ bump M i)
    (hu : ¬ (isUpg M d = true ∧ topped M d = true)) : cnt M ρ i d = ρ.o d := by
  unfold cnt; rw [if_neg hb, if_neg hu]

/-- **The last counted child changes.** -/
theorem hF_o_last {M : Mat} {x i : Nat} {ρ ρN : Valn} {ζ : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x) {L R : List Nat} {c : Nat}
    (hch : children M i = L ++ c :: R)
    (hcb : col M c ≠ bump M i) (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hcz : (glue M x ρ ρN ζ).o c = fsD (ρ.o c) ζ)
    (hL : ∀ d ∈ L, cnt M (glue M x ρ ρN ζ) i d = cnt M ρ i d)
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hv : ¬ DepX M x false i) (hvot : isOT (ρ.v i) = true)
    (hs : ∀ t ∈ L.map (cnt M ρ i), t = z ∨ Single t)
    (hcS : Single (ρ.o c)) (hcS' : Single (fsD (ρ.o c) ζ))
    (hp : (nzs (L.map (cnt M ρ i)) ++ [ρ.o c]).Pairwise (fun a b => b ≤ a))
    (hle : fsD (ρ.o c) ζ ≤ ρ.o c)
    (hF : FrameD (ρ.v i) (spArg (ρ.v i) z (sumN (nzs (L.map (cnt M ρ i))))) (ρ.o c) ζ) :
    oRhs M (glue M x ρ ρN ζ) i = fsD (ρ.o i) ζ := by
  have hiM : i < M.length := by omega
  set ρ' := glue M x ρ ρN ζ with hρ'
  have hv' : ρ'.v i = ρ.v i := glue_v_lt ρ ρN ζ hi hv
  -- the two lists of contributions
  have hlist : (children M i).map (cnt M ρ' i) =
      L.map (cnt M ρ i) ++ [fsD (ρ.o c) ζ] ++ R.map (cnt M ρ' i) := by
    rw [hch, List.map_append, List.map_cons, List.map_congr_left hL, cnt_cnt ρ' hcb hcu, hcz]
    simp
  have hlistM : (children M i).map (cnt M ρ i) =
      L.map (cnt M ρ i) ++ [ρ.o c] ++ R.map (cnt M ρ i) := by
    rw [hch, List.map_append, List.map_cons, cnt_cnt ρ hcb hcu]
    simp
  have hRz : ∀ (σ : Valn), ∀ t ∈ R.map (cnt M σ i), t = z := by
    intro σ t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact cnt_unc σ (hR d hd)
  have hcne := single_ne_z hcS
  have hcne' := single_ne_z hcS'
  have hnz' : nzs ((children M i).map (cnt M ρ' i)) = nzs (L.map (cnt M ρ i)) ++ [fsD (ρ.o c) ζ] := by
    rw [hlist, nzs_append, nzs_append, nzs_single hcne', nzs_zeros _ (hRz ρ'), List.append_nil]
  have hnzM : nzs ((children M i).map (cnt M ρ i)) = nzs (L.map (cnt M ρ i)) ++ [ρ.o c] := by
    rw [hlistM, nzs_append, nzs_append, nzs_single hcne, nzs_zeros _ (hRz ρ), List.append_nil]
  have hp' : (nzs (L.map (cnt M ρ i)) ++ [fsD (ρ.o c) ζ]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append] at hp ⊢
    refine ⟨hp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans hle (hp.2.2 a ha _ (List.mem_singleton_self _))
  have hsL : ∀ t ∈ nzs (L.map (cnt M ρ i)), Single t := by
    intro t ht
    simp only [nzs, List.mem_filter] at ht
    rcases hs t ht.1 with h | h
    · exact absurd h (by simpa using ht.2)
    · exact h
  have hsl : ∀ t ∈ nzs (L.map (cnt M ρ i)) ++ [ρ.o c], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; subst ht; exact hcS
  have hszM : ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t := by
    intro t ht
    rw [hlistM] at ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact hs t ht
      · rw [List.mem_singleton] at ht; subst ht; exact Or.inr hcS
    · exact Or.inl (hRz ρ t ht)
  have hsz' : ∀ t ∈ (children M i).map (cnt M ρ' i), t = z ∨ Single t := by
    intro t ht
    rw [hlist] at ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact hs t ht
      · rw [List.mem_singleton] at ht; subst ht; exact Or.inr hcS'
    · exact Or.inl (hRz ρ' t ht)
  rw [(hC i hiM).1]
  unfold oRhs
  rw [hv', sumN_skip_z hsz' (by rw [hnz']; exact hp'),
    sumN_skip_z hszM (by rw [hnzM]; exact hp), hnz', hnzM]
  exact (frame_last hvot hsl hp hcS' hp' rfl hF).symm

/-- **Only the subscript changes** (no counted children). -/
theorem hF_o_sub {M : Mat} {x i : Nat} {ρ ρN : Valn} {ζ : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x)
    (hnc : ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hv : DepX M x false i) (hvot : isOT (ρ.v i) = true) (hvot' : isOT (fsD (ρ.v i) ζ) = true)
    (hvz : ρ.v i ≠ z) (hvs : isSucc (ρ.v i) = false) :
    oRhs M (glue M x ρ ρN ζ) i = fsD (ρ.o i) ζ := by
  have hiM : i < M.length := by omega
  have hzero : ∀ σ : Valn, sumN ((children M i).map (cnt M σ i)) = z := by
    intro σ
    have : (children M i).map (cnt M σ i) = (children M i).map (fun _ => z) :=
      List.map_congr_left (fun d hd => cnt_unc σ (hnc d hd))
    rw [this, sumN_skip_z (fun t ht => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; exact Or.inl rfl)
      (by rw [nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]; simp),
      nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]
    rfl
  rw [(hC i hiM).1]
  unfold oRhs
  rw [hzero, hzero, glue_v_dep ρ ρN ζ hi hv]
  exact (frame_sub hvot hvot' hvz hvs).symm

/-- **The upgrade case.** -/
theorem hF_v_upg {M : Mat} {x i k : Nat} {ρ ρN : Valn} {ζ : T} (hC : Cons M ρ)
    (hx : x + 1 = M.length) (hi : i < x) (hk : k < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hp : vOpt (glue M x ρ ρN ζ) (par M 1 i) = z) (hpM : vOpt ρ (par M 1 i) = z)
    (hkd : DepX M x false k) (hV : Single (ρ.v k)) (hV' : Single (fsD (ρ.v k) ζ)) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ := by
  have hiM : i < M.length := by omega
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, hu, hp, hpM]
  simp only
  rw [glue_v_dep ρ ρN ζ hk hkd]
  exact (frame_upg hV hV').symm

end Ytosk
