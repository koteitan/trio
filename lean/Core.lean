/-
Core.lean: ArgDomCore の ST 帰納（yapss argDomCoreOn の trio 移植）。

コアは任意 cnf では偽（プローブ 19050/232120 違反、z-jump 型 cex）—
標準性が本質。導出帰納: diag 基底 / (0,0,0)-末尾 / 左文脈除去 /
bad 枝（コピー数の強帰納 + 位置三分 bad_A1/bad_B/bad_A2）。
unlift 保存はプローブ 132417/0、(T,F)-f=0 は SpineOK+経路補題で演繹死。
-/
import Peel2

namespace TRIO

open Classical

/-- The per-form core predicate. -/
def ArgDomCoreOn (N : TrioSeq) : Prop :=
  ∀ ⦃X A1 B A2 Z : TrioSeq⦄ ⦃u w1 z e f : ℕ⦄,
    N = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z →
    0 < e → (f = 0 ∨ z = 0) →
    (∀ x ∈ A1, u < x.1) →
    (∀ x ∈ B, u + e < x.1) →
    (∀ x ∈ A2, u < x.1) →
    (A2 = [] ∨ (A2.headI).1 ≤ u + e) →
    (Z = [] ∨ (Z.headI).1 ≤ u) →
    SpineOK A1 (u + e) w1 →
    sle B (hshift w1 e f (A1 ++ (u + e, w1 + f, z) :: (B ++ A2)))

theorem argDomCore_of_on (H : ∀ N, ST_TS N → ArgDomCoreOn N) : ArgDomCore := by
  intro X A1 B A2 Z u w1 z e f hST hd hz h1 h2 h3 h4 h5 h6
  exact H _ hST rfl hd hz h1 h2 h3 h4 h5 h6

/-- The two marked columns of an instance, by position. -/
theorem argdom_pos {N X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : N = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z) :
    N.getD X.length (0, 0, 0) = (u, w1, z) ∧
    N.getD (X.length + (A1.length + 1)) (0, 0, 0) = (u + e, w1 + f, z) ∧
    X.length + (A1.length + 1) < N.length := by
  have hN : N = X ++ ((u, w1, z)
      :: (A1 ++ (u + e, w1 + f, z) :: ((B ++ A2) ++ Z))) := by
    rw [heq]
    simp [List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hN, getD_app_right _ _ le_rfl, Nat.sub_self]
    rfl
  · rw [hN, getD_app_right _ _ (by omega),
      show X.length + (A1.length + 1) - X.length = A1.length + 1 from by omega,
      List.getD_cons_succ,
      getD_app_right _ _ le_rfl, Nat.sub_self]
    rfl
  · rw [hN]
    simp only [List.length_append, List.length_cons]
    omega

/-- **Base case**: on the capped diagonal no instance has `0 < e`. -/
theorem argDomCoreOn_diag (v : ℕ) : ArgDomCoreOn (diagSeqT 0 v) := by
  intro X A1 B A2 Z u w1 z e f heq he hzf _ _ _ _ _ _
  exfalso
  obtain ⟨hp, hq, hlt⟩ := argdom_pos heq
  rw [diagSeqT_length] at hlt
  rw [diagSeqT_getD (by omega)] at hp
  rw [diagSeqT_getD (by omega)] at hq
  have h1 : X.length = u := congrArg (fun t => t.1) hp
  have h2 : X.length = w1 := congrArg (fun t => t.2.1) hp
  have h2' : min X.length 1 = z := congrArg (fun t => t.2.2) hp
  have h3 : X.length + (A1.length + 1) = u + e := congrArg (fun t => t.1) hq
  have h4 : X.length + (A1.length + 1) = w1 + f := congrArg (fun t => t.2.1) hq
  have h4' : min (X.length + (A1.length + 1)) 1 = z :=
    congrArg (fun t => t.2.2) hq
  rcases hzf with hf | hz0
  · omega
  · rw [hz0] at h2' h4'
    omega

/-- **`(0,0,0)`-last branch**: the dropped column joins the trailing context. -/
theorem argDomCoreOn_snoc_zero {N : TrioSeq} {p : ℕ × ℕ × ℕ} (hp : p.1 = 0)
    (H : ArgDomCoreOn (N ++ [p])) : ArgDomCoreOn N := by
  intro X A1 B A2 Z u w1 z e f heq he hzf h1 h2 h3 h4 h5 h6
  refine H (X := X) (A1 := A1) (B := B) (A2 := A2) (Z := Z ++ [p]) ?_ he hzf
    h1 h2 h3 h4 ?_ h6
  · rw [heq]
    simp [List.append_assoc]
  · rcases Z with _ | ⟨z', Z'⟩
    · exact Or.inr (by simp [hp])
    · refine Or.inr ?_
      rcases h5 with hc | hc
      · exact absurd hc (by simp)
      · exact hc

/-- Instances do not see the material to their left. -/
theorem argDomCoreOn_drop_left {P S : TrioSeq} (H : ArgDomCoreOn (P ++ S)) :
    ArgDomCoreOn S := by
  intro X A1 B A2 Z u w1 z e f heq he hzf h1 h2 h3 h4 h5 h6
  refine H (X := P ++ X) (A1 := A1) (B := B) (A2 := A2) (Z := Z) ?_ he hzf
    h1 h2 h3 h4 h5 h6
  rw [heq]
  simp [List.append_assoc]

end TRIO
