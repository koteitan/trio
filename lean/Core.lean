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

/-! ## bad 枝の小道具 -/

theorem split_prefix_left {C D E F : TrioSeq} (h : C ++ D = E ++ F)
    (hle : E.length ≤ C.length) :
    C = E ++ C.drop E.length ∧ F = C.drop E.length ++ D := by
  have hC : C = C.take E.length ++ C.drop E.length :=
    (List.take_append_drop _ _).symm
  have h' : (C.take E.length) ++ (C.drop E.length ++ D) = E ++ F := by
    rw [← List.append_assoc, ← hC]
    exact h
  have hlen : (C.take E.length).length = E.length := by
    rw [List.length_take]
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h' hlen
  refine ⟨?_, h2.symm⟩
  calc C = C.take E.length ++ C.drop E.length := hC
    _ = E ++ C.drop E.length := by rw [h1]

theorem split_prefix_right {C D E F : TrioSeq} (h : C ++ D = E ++ F)
    (hle : C.length ≤ E.length) :
    E = C ++ E.drop C.length ∧ D = E.drop C.length ++ F :=
  split_prefix_left h.symm hle

/-- Split a column list at the first column at or below level `L`. -/
theorem arg_split (L : ℕ) : ∀ (E : TrioSeq),
    ∃ Bp Rp : TrioSeq, E = Bp ++ Rp ∧ (∀ x ∈ Bp, L < x.1)
      ∧ (Rp = [] ∨ (Rp.headI).1 ≤ L) := by
  intro E
  induction E with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | cons a E' ih =>
    by_cases ha : L < a.1
    · obtain ⟨Bp, Rp, hE, hBp, hRp⟩ := ih
      refine ⟨a :: Bp, Rp, by rw [List.cons_append, ← hE], ?_, hRp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact hBp x hx
    · exact ⟨[], a :: E', rfl, by simp, Or.inr (by simp; omega)⟩

/-- **The splice at the dropped column, bound-relative form.** -/
theorem seqlex_of_sle_snoc' : ∀ {X V E : TrioSeq} {lp q : ℕ × ℕ × ℕ},
    sle (X ++ [lp]) (V ++ E) → collt q lp → X.length < V.length →
    ∀ (S' E' : TrioSeq), seqlex (X ++ q :: S') (V ++ E') := by
  intro X
  induction X with
  | nil =>
    intro V E lp q h hq hlen S' E'
    rcases V with _ | ⟨v, V'⟩
    · simp at hlen
    · rw [List.nil_append, List.cons_append]
      refine Or.inl ?_
      rw [List.nil_append, List.cons_append] at h
      rcases h with he | hs
      · have : lp = v := by simpa using congrArg List.headI he
        rw [← this]
        exact hq
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨he, -⟩
        · exact collt_trans hq hp
        · rw [← he]
          exact hq
  | cons x X' ih =>
    intro V E lp q h hq hlen S' E'
    rcases V with _ | ⟨v, V'⟩
    · simp at hlen
    · simp only [List.length_cons] at hlen
      rw [List.cons_append, List.cons_append] at h
      rw [List.cons_append, List.cons_append, seqlex_cons_cons]
      rcases h with he | hs
      · have hxy : x = v := by simpa using congrArg List.headI he
        have hrest : X' ++ [lp] = V' ++ E := by
          simpa using congrArg List.tail he
        exact Or.inr ⟨hxy, ih (Or.inl hrest) hq (by omega) S' E'⟩
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inl hp
        · exact Or.inr ⟨rfl, ih (Or.inr hs') hq (by omega) S' E'⟩

/-! ## インスタンスの橋（比較子の宿主係留 map 化） -/

/-- Any core instance's `hshift` comparator equals the host-anchored guarded
map over the instance segment. -/
theorem instance_bridge {N X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : N = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1) :
    hshift w1 e f (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))
      = (List.range' (X.length + 1) (A1.length + (1 + (B.length + A2.length)))).map
          (fun p => ((entry N 0 p + e,
            entry N 1 p + (if le1 N X.length p then f else 0),
            entry N 2 p) : ℕ × ℕ × ℕ)) := by
  set r := X.length with hrdef
  set l := A1.length + (1 + (B.length + A2.length)) with hldef
  set LIST := A1 ++ (u + e, w1 + f, z) :: (B ++ A2) with hLISTdef
  have hLISTlen : LIST.length = l := by
    rw [hLISTdef, hldef]
    simp only [List.length_append, List.length_cons]
    omega
  have hNP : N = (X ++ [(u, w1, z)]) ++ (LIST ++ Z) := by
    rw [heq, hLISTdef]
    simp [List.append_assoc]
  have hPlen : (X ++ [(u, w1, z)]).length = r + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hrdef]
  have hNlen : r + 1 + l ≤ N.length := by
    rw [hNP]
    simp only [List.length_append, hPlen, ← hLISTlen]
    omega
  have hseg : seg N (r + 1) l = LIST := by
    have h := seg_append_context (X ++ [(u, w1, z)]) (LIST ++ Z)
      (l := l) (by
        simp only [List.length_append, ← hLISTlen]
        omega)
    rw [hPlen] at h
    rw [hNP, h, ← hLISTlen, List.take_left]
  have hLISTgt : ∀ x ∈ LIST, u < x.1 := by
    intro x hx
    rw [hLISTdef] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h1 x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · dsimp only
        omega
      · rcases List.mem_append.1 hx with hx | hx
        · have := h2 x hx
          omega
        · exact h3 x hx
  have hdict : ∀ i, i < l → N.getD (r + 1 + i) (0, 0, 0)
      = LIST.getD i (0, 0, 0) := by
    intro i hi
    have h := congrArg (fun t => t.getD i (0, 0, 0)) hseg
    dsimp only at h
    rw [seg_getD hi, ← getD_triple] at h
    exact h
  have hgr : N.getD r (0, 0, 0) = (u, w1, z) := by
    rw [show N = X ++ ((u, w1, z) :: (LIST ++ Z)) from by
        rw [hNP]
        simp,
      getD_app_right _ _ (show X.length ≤ r from by omega),
      show r - X.length = 0 from by omega]
    rfl
  have he1r : entry N 1 r = w1 := by
    show (N.getD r (0, 0, 0)).2.1 = w1
    rw [hgr]
  have hupSeg : ∀ j, r + 1 ≤ j → j < r + 1 + l → entry N 0 r < entry N 0 j := by
    intro j hj1 hj2
    have hji : j - r - 1 < l := by omega
    show (N.getD r (0, 0, 0)).1 < (N.getD j (0, 0, 0)).1
    rw [hgr, show j = r + 1 + (j - r - 1) from by omega, hdict _ hji]
    have hmem := getD_mem_of_lt (A := LIST) (j := j - r - 1)
      (by rw [hLISTlen]; exact hji)
    exact hLISTgt _ hmem
  have hrN : r < N.length := by omega
  have h := hshift_gseg (M := N) (r := r) (e := e) (f := f) l
    (a := r + 1) (pa := r) (le1_refl hrN) (by omega) hNlen
    (fun j hj1 hj2 => hupSeg j hj1 hj2)
    (fun j hj1 hj2 => absurd hj1 (by omega))
  rw [he1r] at h
  have hsegd : ((List.range' (r + 1) l).map fun j =>
      ((entry N 0 j, entry N 1 j, entry N 2 j) : ℕ × ℕ × ℕ)) = LIST := hseg
  rw [hsegd] at h
  exact h.symm

end TRIO
