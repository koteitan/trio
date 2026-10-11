/-
**TailNR を、尾に x を含まない場合だけの残り TailNRL に狭める（2026-10-11、drop-fix）。**

CL M i = CL(M.take x) i ++ Tl の尾 Tl に x が入るとき、x は Tl の最後で o(x) = ψ_{v(x)}(0)（x に子はない）。
引数 0 の子は書き換えない（B < 0 は成り立たない）ので、x の分は足すだけ。残りは x の前の尾 Tl′ で、
それが TailNRL（実測では Tl′ = [] か Tl′ = [P_0(x)]）。
-/
import Ytosk.V3DropR

namespace Ytosk

open T

/-- **Drop hypothesis** (narrowed `TailNR`): the children of `i` in `M` after its last counted child in
`M.take x`, other than `x`, do not rewrite. -/
def TailNRL (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat) (Tl R : List Nat), CL (M.take x) i = Lc ++ [cs] →
    CL M i = Lc ++ [cs] ++ Tl ++ R → Tl ≠ [] → x ∉ Tl →
    spArg (ρ.v i) z (sumN ((Lc ++ [cs] ++ Tl).map ρ.o)) =
      app (spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o))) (sumN (Tl.map ρ.o))

/-- A child with argument `0` does not rewrite. -/
theorem spArg_leaf {a A w : T} (hA : ∀ q ∈ summands A, psi w z z ≤ q) :
    spArg a A (psi w z z) = app A (psi w z z) := by
  rw [spArg_single]; unfold step
  rw [if_neg (fun h => not_lt_z A h.1)]
  exact add_eq_app_of_ge ⟨w, z, rfl⟩ A hA

/-- **`TailNR` from `TailNRL`.** -/
theorem tailNR_of {M : Mat} {x : Nat} {ρ : Valn} (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hT : TailNRL M x ρ) : TailNR M x ρ := by
  intro i hi Lc cs Tl hcl hclM hTl
  have hiM : i < M.length := by omega
  by_cases hxT : x ∈ Tl
  swap
  · exact hT i hi Lc cs Tl [] hcl (by rw [hclM, List.append_nil]) hTl hxT
  have hsort : (CL M i).Pairwise (· < ·) := by unfold CL; exact (children_sorted M i).filter _
  rw [hclM] at hsort
  -- `x` is the last element of `Tl`
  obtain ⟨Tl', rfl⟩ : ∃ Tl', Tl = Tl' ++ [x] := by
    rcases List.eq_nil_or_concat Tl with h | ⟨T0, e, he⟩
    · exact absurd h hTl
    · rw [List.concat_eq_append] at he
      refine ⟨T0, ?_⟩
      rw [he]
      by_cases hex : e = x
      · rw [hex]
      exfalso
      have hxT0 : x ∈ T0 := by
        rw [he] at hxT
        rcases List.mem_append.mp hxT with h | h
        · exact h
        · simp at h; exact absurd h.symm hex
      have heM : e ∈ CL M i := by rw [hclM, he]; simp
      have he_lt : e < M.length := (mem_children (cl_mem_children heM)).2
      rw [he] at hsort
      have h2 := (List.pairwise_append.mp hsort).2.1
      have : x < e := (List.pairwise_append.mp h2).2.2 x hxT0 e (by simp)
      omega
  have hxnot : x ∉ Tl' := by
    intro h
    have h2 := (List.pairwise_append.mp hsort).2.1
    exact lt_irrefl _ ((List.pairwise_append.mp h2).2.2 x h x (by simp))
  -- `o(x) = ψ_{v(x)}(0)`
  have hox : ρ.o x = psi (ρ.v x) z z :=
    o_nocnt hC hG (by omega) (fun d hd => by have := mem_children hd; omega)
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  have hW : (CL M i).map ρ.o = ((Lc ++ [cs]).map ρ.o ++ Tl'.map ρ.o) ++ [ρ.o x] := by
    rw [hclM]; simp
  rw [hW] at hsM hpM
  have hge : ∀ t ∈ (Lc ++ [cs]).map ρ.o ++ Tl'.map ρ.o, ρ.o x ≤ t := fun t ht =>
    (List.pairwise_append.mp hpM).2.2 t ht (ρ.o x) (by simp)
  have hsW : ∀ t ∈ (Lc ++ [cs]).map ρ.o ++ Tl'.map ρ.o, Single t := fun t ht =>
    hsM t (List.mem_append_left _ ht)
  have hpW := (List.pairwise_append.mp hpM).1
  have hsP : ∀ t ∈ (Lc ++ [cs]).map ρ.o, Single t := fun t ht => hsW t (List.mem_append_left _ ht)
  have hpP := (List.pairwise_append.mp hpW).1
  have hsT : ∀ t ∈ Tl'.map ρ.o ++ [ρ.o x], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsW t (List.mem_append_right _ h)
    · exact hsM t (List.mem_append_right _ h)
  have hpT : (Tl'.map ρ.o ++ [ρ.o x]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append]
    refine ⟨(List.pairwise_append.mp hpW).2.1, by simp, ?_⟩
    intro t ht u hu
    simp at hu; rw [hu]; exact hge t (List.mem_append_right _ ht)
  -- the tail before `x`
  have hE : spArg (ρ.v i) z (sumN ((Lc ++ [cs] ++ Tl').map ρ.o)) =
      app (spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o))) (sumN (Tl'.map ρ.o)) := by
    by_cases h0 : Tl' = []
    · subst h0; simp [sumN]
    · exact hT i hi Lc cs Tl' [x] hcl (by rw [hclM]; simp) h0 hxnot
  -- the bound of the state before `x`
  have hP := sumN_dec _ hsP hpP
  have hTd := sumN_dec _ (fun t ht => hsW t (List.mem_append_right _ ht)) (List.pairwise_append.mp hpW).2.1
  have hbound : ∀ q ∈ summands (app (spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o))) (sumN (Tl'.map ρ.o))),
      psi (ρ.v x) z z ≤ q := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · apply spArg_summands_ge ⟨ρ.v x, z, rfl⟩ _ z hP.1 _ (by simp [summands]) q hq
      rw [hP.2]; intro t ht; rw [← hox]; exact hge t (List.mem_append_left _ ht)
    · rw [hTd.2] at hq; rw [← hox]; exact hge q (List.mem_append_right _ hq)
  have hL : (Lc ++ [cs] ++ (Tl' ++ [x])).map ρ.o = (Lc ++ [cs] ++ Tl').map ρ.o ++ [ρ.o x] := by simp
  have hsL : ∀ t ∈ (Lc ++ [cs] ++ Tl').map ρ.o ++ [ρ.o x], Single t := by
    rw [List.map_append]; exact hsM
  have hpL : ((Lc ++ [cs] ++ Tl').map ρ.o ++ [ρ.o x]).Pairwise (fun a b => b ≤ a) := by
    rw [List.map_append]; exact hpM
  rw [hL, sumN_append_dec hsL hpL, spArg_app, hE, sumN_singleton (hsM _ (by simp)), hox, spArg_leaf hbound,
    show (Tl' ++ [x]).map ρ.o = Tl'.map ρ.o ++ [ρ.o x] by simp, sumN_append_dec hsT hpT, sumN_singleton (hsM _ (by simp)), hox,
    app_assoc]

end Ytosk
