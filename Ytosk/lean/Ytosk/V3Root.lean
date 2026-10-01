/-
**3 行: 行列の値（根の和）と、t = 1・q ≠ r での降下。**

- `root_eq_roots`: 根の値が項 1 つずつで減っていくなら、行列の値は根の値の連結。
- `depX_ge`: D の呼び出しは x の根 R 以後の列（D は R の木の中）。したがって R より前の根の値は変わらない。
- `root_N_t1`: M[n] の値は (R より前の根) ++ fsD(o_M(R), ζ)。R の値が下がれば行列の値も下がる。
-/
import Ytosk.V3Rank
import Ytosk.TwoRowE
import Ytosk.V3Bump

namespace Ytosk

open T

theorem nzs_map_ite (p : Nat → Prop) [DecidablePred p] (f : Nat → T) :
    ∀ (l : List Nat), (∀ i ∈ l, p i → f i ≠ z) →
      nzs (l.map (fun i => if p i then f i else z)) = (l.filter (fun i => decide (p i))).map f
  | [], _ => rfl
  | a :: l, hf => by
    have ih := nzs_map_ite p f l (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    by_cases ha : p a
    · have hfa := hf a List.mem_cons_self ha
      simp only [List.map_cons, if_pos ha, List.filter_cons, decide_eq_true ha, ↓reduceIte]
      simp only [nzs, List.filter_cons, ne_eq, hfa, not_false_eq_true, decide_true, ↓reduceIte,
        List.map_cons, List.cons.injEq, true_and]
      exact ih
    · simp only [List.map_cons, if_neg ha, List.filter_cons, decide_eq_false ha]
      simp only [nzs, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact ih

/-- **The value as the sum of the roots.** -/
theorem root_eq_roots {M : Mat} {ρ : Valn} (hs : ∀ i ∈ roots M, Single (ρ.o i))
    (hp : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    root M ρ = sumN ((roots M).map ρ.o) := by
  unfold root
  have hnz : nzs ((List.range M.length).map fun i => if col M i = (0, 0, 0) then ρ.o i else z) =
      (roots M).map ρ.o :=
    nzs_map_ite (fun i => col M i = (0, 0, 0)) ρ.o _ (fun i hi hc =>
      single_ne_z (hs i (mem_roots.mpr ⟨List.mem_range.mp hi, hc⟩)))
  rw [sumN_skip_z (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      by_cases hc : col M i = (0, 0, 0)
      · rw [if_pos hc]; exact Or.inr (hs i (mem_roots.mpr ⟨List.mem_range.mp hi, hc⟩))
      · rw [if_neg hc]; exact Or.inl rfl) (by rw [hnz]; exact hp), hnz]

/-! ## D は x の根の木の中 -/

/-- A column after the last root `R` (and up to `x`) has its row-0 parent at or after `R`. -/
theorem par0_ge_root {M : Mat} {R x : Nat} (hR0 : entry M 0 R = 0)
    (hRlast : ∀ j, R < j → j ≤ x → entry M 0 j ≠ 0) {c p : Nat} (hc : R < c) (hcx : c ≤ x)
    (hp : par M 0 c = some p) : R ≤ p := by
  obtain ⟨hpc, hlt, hbet⟩ := (par0_spec M).mp hp
  by_contra h
  have := hbet R (by omega) hc
  have := hRlast c hc hcx
  omega

/-- A root has no row-0 parent. -/
theorem par0_root_none {M : Mat} {R p : Nat} (hR0 : entry M 0 R = 0) : par M 0 R ≠ some p := by
  intro hp
  have := ((par0_spec M).mp hp).2.1
  omega

/-- An upgrade to the next column lands on a column with row 0 at least `1`. -/
theorem upg_next_e0 {M : Mat} {i : Nat} (h : upg M i = some (i + 1)) : entry M 0 (i + 1) ≠ 0 := by
  unfold upg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i m hm
      simp only at h
      split at h
      · rename_i hcl
        have : entry M 0 (i + 1) = (col M (i + 1)).1 := rfl
        rw [this, hcl.2]; simp
      · rw [upgClimb_find] at h
        have := mem_ancL_lt (List.mem_of_find?_eq_some h)
        omega

/-- **The calls in `D` are in the tree of the last root `R`.** -/
theorem depX_ge {M : Mat} {R x : Nat} (hx : x + 1 = M.length) (hR0 : entry M 0 R = 0) (hRx : R ≤ x)
    (hRlast : ∀ j, R < j → j ≤ x → entry M 0 j ≠ 0) {b : Bool} {i : Nat}
    (h : DepX M x b i) : R ≤ i := by
  induction h with
  | leaf => exact hRx
  | @ochild i c hc _ _ _ ih =>
    have hpc := (mem_children_iff.mp hc).2
    have hcl := (mem_children hc).2
    rcases Nat.eq_or_lt_of_le ih with heq | hlt
    · subst heq; exact absurd hpc (par0_root_none hR0)
    · exact par0_ge_root hR0 hRlast hlt (by omega) hpc
  | ov _ ih => exact ih
  | @vpar i m _ hm _ ih =>
    have := par_lt M 1 i m hm; omega
  | @vupg i k _ _ hu _ ih =>
    have hle := upg_le hu
    rcases Nat.lt_or_ge k (i + 1) with h1 | h1
    · omega
    · have hk : k = i + 1 := by omega
      subst hk
      have := upg_next_e0 hu
      rcases Nat.eq_or_lt_of_le ih with heq | hlt
      · rw [← heq] at this; exact absurd hR0 this
      · omega
  | @vbump i j k _ _ hj _ hk _ ih =>
    have hpk := (mem_children_iff.mp hk).2
    have hpj := (mem_children_iff.mp hj).2
    have hkl := (mem_children hk).2
    have hjl := (mem_children hj).2
    have hjk := (mem_children hk).1
    rcases Nat.eq_or_lt_of_le ih with heq | hlt
    · subst heq; exact absurd hpk (par0_root_none hR0)
    · have hRj := par0_ge_root hR0 hRlast hlt (by omega) hpk
      rcases Nat.eq_or_lt_of_le hRj with heq | hlt2
      · subst heq; exact absurd hpj (par0_root_none hR0)
      · exact par0_ge_root hR0 hRlast hlt2 (by omega) hpj

theorem range_filter_cut (m k : Nat) (p : Nat → Bool) (hk : k ≤ m)
    (hp : ∀ i, k ≤ i → i < m → p i = false) :
    (List.range m).filter p = (List.range k).filter p := by
  rw [show m = k + (m - k) by omega, List.range_add, List.filter_append]
  have : (List.map (fun x => k + x) (List.range (m - k))).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := List.mem_range.mp hj
    rw [hp (k + j) (by omega) (by omega)]; simp
  rw [this, List.append_nil]

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The roots of `M[n]` are those of `M`** (all before `x`). -/
theorem roots_N_t1 : roots (TRIO.gexp M r L d0 0 n) = roots M := by
  have hlN := len_N (d0 := d0) hlen hn
  have hex : 0 < entry M 0 (r + L) := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  have hd0 : 0 < d0 := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  unfold roots
  rw [range_filter_cut _ (r + L) _ (by omega) (fun i h1 h2 => by
      simp only [decide_eq_false_iff_not]
      intro h
      have he : entry (TRIO.gexp M r L d0 0 n) 0 i = 0 := by unfold entry; unfold col at h; rw [h]; rfl
      rcases Nat.eq_or_lt_of_le h1 with heq | hlt
      · subst heq; rw [e0_gexp_x hlen hL hd0e hn] at he; omega
      · rw [show i = r + L + (i - (r + L)) by omega,
          e0_copy (d0 := d0) hlen hL hn (show i - (r + L) < (n - 1) * L by omega)] at he
        omega),
    range_filter_cut M.length (r + L) _ (by omega) (fun i h1 h2 => by
      simp only [decide_eq_false_iff_not]
      intro h
      have he : entry M 0 i = 0 := by unfold entry; unfold col at h; rw [h]; rfl
      rw [show i = r + L by omega] at he; omega)]
  apply List.filter_congr
  intro i hi
  rw [col_gexp_pre hlen (by omega) (List.mem_range.mp hi)]

/-- **The value of `M[n]` drops** (`t = 1`, `q ≠ r`), given the drop at the root `R` of `x`. -/
theorem root_N_t1 {ρ ρN : Valn} {Z : Nat → T} {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsR : Single (fsD (ρ.o Rt) (Z Rt))) (hlt : fsD (ρ.o Rt) (Z Rt) < ρ.o Rt) :
    isOT (root (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ ρN Z)) = true ∧
      root (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ ρN Z) < root M ρ := by
  have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
  have hRx := hRA.le
  have hsplit := roots_split hlen hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hpre_nd : ∀ c ∈ pre, ¬ DepX M (r + L) true c := by
    intro c hc hd
    have := depX_ge (by omega) hR0e hRx hRlast hd
    have := hpre_lt c hc; omega
  have hglue : (roots M).map (glueZ M (r + L) ρ ρN Z).o = pre.map ρ.o ++ [fsD (ρ.o Rt) (Z Rt)] := by
    rw [hsplit, List.map_append, List.map_singleton, glueZ_o_dep ρ ρN Z (by
      rcases Nat.eq_or_lt_of_le hRx with h | h
      · exfalso
        have h1 : entry M 0 (r + L) ≠ 0 := by
          have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
        rw [h] at hR0e
        exact h1 hR0e
      · exact h) hRd]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact glueZ_o_lt ρ ρN Z (by have := hpre_lt c hc; omega) (hpre_nd c hc)
  have hMl : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  rw [hMl] at hpM
  have hsl : ∀ t ∈ pre.map ρ.o ++ [ρ.o Rt], Single t := by
    intro t ht
    rw [← hMl] at ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hsM i hi
  have hsl' : ∀ t ∈ pre.map ρ.o ++ [fsD (ρ.o Rt) (Z Rt)], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsl t (List.mem_append_left _ ht)
    · rw [List.mem_singleton] at ht; subst ht; exact hsR
  have hpl' : (pre.map ρ.o ++ [fsD (ρ.o Rt) (Z Rt)]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append] at hpM ⊢
    refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt hlt) (hpM.2.2 a ha _ (List.mem_singleton_self _))
  have hrootN : root (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ ρN Z) =
      sumN (pre.map ρ.o ++ [fsD (ρ.o Rt) (Z Rt)]) := by
    rw [root_eq_roots, roots_N_t1 hlen hL hA hd0e hn, hglue]
    · intro i hi
      rw [roots_N_t1 hlen hL hA hd0e hn] at hi
      have : (glueZ M (r + L) ρ ρN Z).o i ∈ (roots M).map (glueZ M (r + L) ρ ρN Z).o :=
        List.mem_map.mpr ⟨i, hi, rfl⟩
      rw [hglue] at this
      exact hsl' _ this
    · rw [roots_N_t1 hlen hL hA hd0e hn, hglue]; exact hpl'
  have hrootM : root M ρ = sumN (pre.map ρ.o ++ [ρ.o Rt]) := by
    rw [root_eq_roots hsM (by rw [hMl]; exact hpM), hMl]
  rw [hrootN, hrootM]
  refine ⟨(sumN_dec _ hsl' hpl').1, ?_⟩
  rw [sumN_snoc_dec hsl' hpl', sumN_snoc_dec hsl hpM]
  exact app_lt_app_left _ hlt

end

end Ytosk
