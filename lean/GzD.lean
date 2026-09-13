/-
GzD.lean: 最上段の語の中身が遠い字 1 個だけの語（遠い語）と、その展開の塔。

    (0,u,0)(1,u+1,1)(2,u+1,1)⟦m+1⟧ = (0,u,0) :: towT u 0 m
    towT b o 0     = [(1, b+o+1, 1)]
    towT b o (k+1) = towT b o k ++ [(2k+2, b+o+k+1, 0), (2k+3, b+o+k+2, 1)]
                   = (1, b+o+1, 1) :: ((1, b+o+1, 0) :: (towT b (o+1) k)↑1)↑1

塔の各段は、字の中身の F とその子の語（錨の列 [o+k-1, …, o]）なので、GyK の規則で出る。
-/
import GyK

namespace TRIO
namespace GzD

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK

/-! ## 塔 -/

def towT (b o : ℕ) : ℕ → TrioSeq
  | 0 => [((1, b + o + 1, 1) : ℕ × ℕ × ℕ)]
  | k + 1 => towT b o k ++
      [((2 * k + 2, b + o + k + 1, 0) : ℕ × ℕ × ℕ), ((2 * k + 3, b + o + k + 2, 1) : ℕ × ℕ × ℕ)]

theorem towT_succ (b o : ℕ) : ∀ k, towT b o (k + 1)
    = ((1, b + o + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, b + o + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towT b (o + 1) k))
  | 0 => by
      simp only [towT, shiftr01, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
      simp only [List.cons.injEq, Prod.mk.injEq]
      simp only [and_true, true_and]; omega
  | k + 1 => by
      rw [towT, towT_succ b o k, towT]
      simp only [shiftr01, List.map_cons, List.map_append, List.map_nil, List.cons_append]
      refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
      refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
      congr 1
      simp only [List.cons.injEq, Prod.mk.injEq]
      simp only [and_true]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem tower_PVF0 {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) : PVF A o b [] := by
  rcases Nat.lt_or_ge o 2 with h | h
  · have ho1 : o = 1 := by omega
    subst ho1
    have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
    subst hA0
    exact PVF_nil1 b
  · exact PVF_nil hA h b

/-- ★ 塔の子の並びは、錨の列 A、行 1 の差 o の節点の子の並び。 -/
theorem tower_GPF : ∀ (k : ℕ) {A : List ℕ} {o : ℕ} (b : ℕ), (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → GPF A o b (towT b o k)
  | 0, A, o, b, hA, hA1, ho => by
      have := PVF_snoc hA (tower_PVF0 hA hA1 ho b) (RLF_nil hA hA1 ho b)
      simp only [List.nil_append, shiftr01, List.map_nil] at this
      exact GPF_of_PVF this
  | k + 1, A, o, b, hA, hA1, ho => by
      have hA' : ∀ a ∈ o :: A, a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hA1' : ∀ a ∈ o :: A, 1 ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ho
        · exact hA1 a ha
      have hL := tower_GPF k (A := o :: A) (o := o + 1) b hA' hA1' (by omega)
      have hf : (o :: A).filter (fun a => decide (a < o + 1)) = o :: A :=
        List.filter_eq_self.mpr (fun a ha => decide_eq_true (hA' a ha))
      have hR := RLF_child hA hA1 ho (τ := o + 1) (o :: A) hf le_rfl (RLF_nil hA hA1 ho b) hL
      have := PVF_snoc hA (tower_PVF0 hA hA1 ho b) hR
      simp only [List.nil_append, show b + (o + 1) = b + o + 1 by omega] at this
      rw [towT_succ]
      exact GPF_of_PVF this

/-! ## 遠い語の展開 -/

theorem mlift_one_letter (u k : ℕ) :
    mlift [((1, u + 1, 1) : ℕ × ℕ × ℕ)] u k = [((1, u + 1 + k, 1) : ℕ × ℕ × ℕ)] := by
  have := mlift_letter (show u < u + 1 by omega) (V := []) Fr_nil k
  simpa [shiftr01, mlift_nil] using this

theorem farword_flat (u : ℕ) : ∀ m, (List.range (m + 1)).flatMap (fun k =>
    shiftr01 (k * 2) 0 (((0, u + k, 0) : ℕ × ℕ × ℕ) :: mlift [((1, u + 1, 1) : ℕ × ℕ × ℕ)] u k))
      = ((0, u, 0) : ℕ × ℕ × ℕ) :: towT u 0 m
  | 0 => by simp [mlift_one_letter, shiftr01, towT]
  | m + 1 => by
      rw [List.range_succ, List.flatMap_append, farword_flat u m]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, mlift_one_letter, towT,
        shiftr01, List.map_cons, List.map_nil, List.cons_append]
      congr 1
      congr 1
      simp only [List.cons.injEq, Prod.mk.injEq]
      simp only [and_true]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem Fr_one_letter (u : ℕ) : Fr [((1, u + 1, 1) : ℕ × ℕ × ℕ)] := by
  intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega

theorem farword_cone (u : ℕ) :
    coneV ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u
      [((1, u + 1, 1) : ℕ × ℕ × ℕ)].length := by
  have e : [((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]
      = shiftr01 1 0 [((0, u + 1, 1) : ℕ × ℕ × ℕ), ((1, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]
  have h1 := amin_cons_root (Fr_one_letter u) (u + 1) 1 (j := 0) (by simp)
  simp only [Nat.add_zero] at h1
  rw [coneV_iff_amin, e, amin_shift0, List.length_singleton, h1, amin_zero]
  simp [entry]

theorem farword_oper (u m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]))⟦m + 1⟧
      = ((0, u, 0) : ℕ × ℕ × ℕ) :: towT u 0 m := by
  rw [oper_zcone (Fr_one_letter u) (by omega) (farword_cone u) (m + 1)]
  exact farword_flat u m

theorem tower_Wg (u : ℕ) : ∀ m, (((0, u, 0) : ℕ × ℕ × ℕ) :: towT u 0 m) ∈ Wg (2 * u)
  | 0 => by
      have h := Wg_of_starOK (starOK_wordsG (v := u) (WordsG_consT (TF_nil u) (WordsG_nil u)))
      simpa [rword, rcol, shiftr01, towT] using h
  | k + 1 => by
      have hG := tower_GPF k (A := []) (o := 1) u (fun a ha => by simp at ha)
        (fun a ha => by simp at ha) le_rfl
      have h := Wg_of_starOK (starOK_wordsG (v := u)
        (WordsG_consT (TF_tieG (u := u) (TF_nil u) (GF_of_GPF hG)) (WordsG_nil u)))
      rw [towT_succ]
      simpa [rword, rcol] using h

/-- ★ 遠い語の木は、全ての段で Wg。 -/
theorem farword_Wg (u a : ℕ) (ha : 2 * u ≤ a) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)])) ∈ Wg a := by
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom (Fr_one_letter u) (by omega) (farword_cone u),
    fun n hn => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [farword_oper]
  exact Wg_mono ha (tower_Wg u m)

theorem BwT_farword (v : ℕ) : BwT v [[((1, v + 1, 1) : ℕ × ℕ × ℕ)]] := by
  intro u hu _ a ha
  have e : rword 0 u ([[((1, v + 1, 1) : ℕ × ℕ × ℕ)]].map (fun X => mlift X v (u - v)))
      = [((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp only [List.map_cons, List.map_nil]
    rw [mlift_one_letter, show v + 1 + (u - v) = u + 1 by omega]
    simp [rword, rcol, shiftr01]
  show (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u ([[((1, v + 1, 1) : ℕ × ℕ × ℕ)]].map
    (fun X => mlift X v (u - v)))) ∈ Wg a
  rw [e]
  exact farword_Wg u a ha

/-- 遠い語のあとに、中身の閉包 GT を持つ語を並べる。 -/
theorem BwT_farwords {v : ℕ} : ∀ (Ls : List TrioSeq), WordsG v Ls →
    BwT v ([[((1, v + 1, 1) : ℕ × ℕ × ℕ)]] ++ Ls) := by
  intro Ls
  induction Ls using List.reverseRecOn with
  | nil => intro _; simpa using BwT_farword v
  | append_singleton Ls K ih =>
      intro hW
      have hK := hW K (by simp)
      rw [← List.append_assoc]
      refine hK.1 _ (fun X hX => ?_) (ih (fun X hX => hW X (List.mem_append_left _ hX)))
      rcases List.mem_append.mp hX with h | h
      · simp at h; subst h; intro x hx; simp at hx; subst hx; show 1 ≤ 1; omega
      · exact (hW X (List.mem_append_left _ h)).2

theorem starOK_farwords {v : ℕ} {Ls : List TrioSeq} (h : WordsG v Ls) :
    StarOK v (rword 0 v ([[((1, v + 1, 1) : ℕ × ℕ × ℕ)]] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_farwords Ls h v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- ★ シート行 1317。 -/
theorem R1317_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := W0_of_starOK (starOK_farwords (v := 0) (WordsG_nil 0))
  simpa [rword, rcol, shiftr01] using h

end GzD
end TRIO
