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
    SpineOK A1 (u + e) (w1 + 1) →
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

/-! ## bad_B: ホスト検証（key） -/

/-- **The host's verdict, map form**: for any admissible resplit of the
host tail, the argument is dominated by the host-anchored map over the
instance prefix. -/
theorem bad_B_key {M P A1 D : TrioSeq} {u w1 z e f : ℕ} {lp : ℕ × ℕ × ℕ}
    (hMon : ArgDomCoreOn M)
    (hMeq : M = (P ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)])) ++ (D ++ [lp]))
    (he : 0 < e) (hzf : f = 0 ∨ z = 0)
    (h1 : ∀ x ∈ A1, u < x.1) (h6 : SpineOK A1 (u + e) (w1 + 1))
    {B' A2' Z' : TrioSeq}
    (hsplit : D ++ [lp] = B' ++ (A2' ++ Z'))
    (hB' : ∀ x ∈ B', u + e < x.1) (hA2' : ∀ x ∈ A2', u < x.1)
    (hA2'hd : A2' = [] ∨ (A2'.headI).1 ≤ u + e)
    (hZ'hd : Z' = [] ∨ (Z'.headI).1 ≤ u) :
    sle B' ((List.range' (P.length + 1) (A1.length + 1 + B'.length)).map
        (fun p => ((entry M 0 p + e,
          entry M 1 p + (if le1 M P.length p then f else 0),
          entry M 2 p) : ℕ × ℕ × ℕ))) := by
  have hMeq' : M = (P ++ (u, w1, z)
      :: (A1 ++ (u + e, w1 + f, z) :: (B' ++ A2'))) ++ Z' := by
    rw [hMeq, hsplit]
    simp [List.append_assoc]
  have hcore := hMon hMeq' he hzf h1 hB' hA2' hA2'hd hZ'hd h6
  rw [instance_bridge hMeq' he h1 hB' hA2'] at hcore
  have hsp : A1.length + (1 + (B'.length + A2'.length))
      = (A1.length + 1 + B'.length) + A2'.length := by
    omega
  rw [hsp, ← List.range'_append_1, List.map_append] at hcore
  exact sle_take_of_short hcore (by
    rw [List.length_map, List.length_range']
    omega)

set_option maxHeartbeats 4000000 in
/-- **Case B** — both marked columns lie inside `G ++ blk`. -/
theorem argDomCoreOn_bad_B {M G R : TrioSeq} {v0 w10 z0 d0 d1 n : ℕ}
    {lp : ℕ × ℕ × ℕ}
    (hMon : ArgDomCoreOn M)
    (hMeq : M = G ++ ((v0, w10, z0) :: R) ++ [lp])
    (hqlt : collt (v0 + d0, w10 + d1, z0) lp)
    (hn : 1 ≤ n)
    {X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : G ++ gcopies M G.length (R.length + 1) d0 d1 n
      = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (hzf : f = 0 ∨ z = 0)
    (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1) (h4 : A2 = [] ∨ (A2.headI).1 ≤ u + e)
    (h5 : Z = [] ∨ (Z.headI).1 ≤ u) (h6 : SpineOK A1 (u + e) (w1 + 1))
    (hcase : X.length + (A1.length + 1) < G.length + (R.length + 1)) :
    sle B (hshift w1 e f (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set j0 := G.length with hj0def
  set Lb := R.length + 1 with hLbdef
  set p0 := j0 + Lb with hp0def
  set ipos := X.length with hiposdef
  set jpos := X.length + (A1.length + 1) with hjposdef
  -- block identification and copy-0 peel
  have hblk : seg M j0 Lb = (v0, w10, z0) :: R := by
    have h := seg_append_context G (((v0, w10, z0) :: R) ++ [lp])
      (l := Lb) (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
    have hM2 : M = G ++ (((v0, w10, z0) :: R) ++ [lp]) := by
      rw [hMeq]
      simp
    rw [hj0def, hM2, h]
    rw [show Lb = ((v0, w10, z0) :: R).length from by
      simp only [List.length_cons]; omega]
    exact List.take_left
  have hTsplit : G ++ gcopies M j0 Lb d0 d1 (m + 1)
      = (G ++ ((v0, w10, z0) :: R)) ++ gcopiesFrom M j0 Lb d0 d1 1 m := by
    rw [gcopies_eq_from, gcopiesFrom_succ, gcopy_zero, hblk]
    simp
  -- host coordinates
  have hMlen : M.length = p0 + 1 := by
    rw [hMeq]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hPlen : (G ++ ((v0, w10, z0) :: R)).length = p0 := by
    simp only [List.length_append, List.length_cons]
    omega
  have hagree : ∀ x, x < p0 →
      (G ++ gcopies M j0 Lb d0 d1 (m + 1)).getD x (0, 0, 0)
        = M.getD x (0, 0, 0) := by
    intro x hx
    rw [hTsplit,
      getD_append_left (G := G ++ ((v0, w10, z0) :: R)) (by rw [hPlen]; omega),
      hMeq,
      show G ++ ((v0, w10, z0) :: R) ++ [lp]
        = (G ++ ((v0, w10, z0) :: R)) ++ [lp] from by simp,
      getD_append_left (G := G ++ ((v0, w10, z0) :: R)) (by rw [hPlen]; omega)]
  -- the instance prefix sits inside the shared part
  have hNsplit : (G ++ ((v0, w10, z0) :: R)) ++ gcopiesFrom M j0 Lb d0 d1 1 m
      = (X ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)])) ++ (B ++ (A2 ++ Z)) := by
    rw [← hTsplit, heq]
    simp [List.append_assoc]
  have hClen : (X ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)])).length ≤ p0 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨hPD, hBAZ⟩ := split_prefix_left hNsplit (by rw [hPlen]; exact hClen)
  set D := (G ++ ((v0, w10, z0) :: R)).drop
    (X ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)])).length with hDdef
  have hDlen : D.length = p0 - (jpos + 1) := by
    rw [hDdef, List.length_drop, hPlen]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hMsplit : M = (X ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)]))
      ++ (D ++ [lp]) := by
    rw [hMeq, ← List.append_assoc, hPD, List.append_assoc]
  -- the two anchored maps agree strictly below the host end
  have hguardeq : ∀ p, p < p0 →
      (le1 (G ++ gcopies M j0 Lb d0 d1 (m + 1)) ipos p ↔ le1 M ipos p) := by
    intro p hp
    have hlenT : p < (G ++ gcopies M j0 Lb d0 d1 (m + 1)).length := by
      rw [List.length_append, gcopies_length]
      have : (m + 1) * Lb = m * Lb + Lb := Nat.succ_mul m Lb
      omega
    constructor
    · intro h
      exact le1_of_agree (X := M) (M := G ++ gcopies M j0 Lb d0 d1 (m + 1))
        (by omega) hlenT (fun x hx => (hagree x (by omega)).symm) h
    · intro h
      exact le1_of_agree (X := G ++ gcopies M j0 Lb d0 d1 (m + 1)) (M := M)
        hlenT (by omega) (fun x hx => hagree x (by omega)) h
  have hmapeq : ∀ a l, ipos ≤ a → a + l ≤ p0 →
      (List.range' a l).map (fun p => ((entry
          (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 0 p + e,
        entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 1 p
          + (if le1 (G ++ gcopies M j0 Lb d0 d1 (m + 1)) ipos p then f else 0),
        entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 2 p) : ℕ × ℕ × ℕ))
      = (List.range' a l).map (fun p => ((entry M 0 p + e,
        entry M 1 p + (if le1 M ipos p then f else 0),
        entry M 2 p) : ℕ × ℕ × ℕ)) := by
    intro a l ha hl
    refine List.map_congr_left ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := List.mem_range'_1.1 hp
    have hplt : p < p0 := by omega
    have he0 : entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 0 p = entry M 0 p := by
      unfold entry
      rw [hagree p hplt]
    have he1 : entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 1 p = entry M 1 p := by
      unfold entry
      rw [hagree p hplt]
    have he2 : entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 2 p = entry M 2 p := by
      unfold entry
      rw [hagree p hplt]
    rw [he0, he1, he2]
    by_cases hg : le1 M ipos p
    · rw [if_pos hg, if_pos ((hguardeq p hplt).2 hg)]
    · rw [if_neg hg, if_neg (fun hc => hg ((hguardeq p hplt).1 hc))]
  -- goal in map form
  rw [instance_bridge heq he h1 h2 h3]
  -- split off the A2 part of the goal comparator
  have hgsp : A1.length + (1 + (B.length + A2.length))
      = (A1.length + 1 + B.length) + A2.length := by
    omega
  rw [hgsp, ← List.range'_append_1, List.map_append]
  refine sle_append_mono ?_ _
  rcases Nat.lt_or_ge B.length D.length with hBD | hBD
  · -- #### `B` stops strictly inside the shared part
    obtain ⟨hDr, hArest⟩ := split_prefix_right hBAZ (le_of_lt hBD)
    set Dr := D.drop B.length with hDrdef
    have hDrne : Dr ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      rw [hDrdef, List.length_drop] at this
      simp at this
      omega
    obtain ⟨A2', Z', hsp, hA2'gt, hZ'hd⟩ := arg_split u (Dr ++ [lp])
    have hA2'hd : A2' = [] ∨ (A2'.headI).1 ≤ u + e := by
      by_cases hA2e : A2' = []
      · exact Or.inl hA2e
      · refine Or.inr ?_
        have hh1 : (Dr ++ [lp]).headI = A2'.headI := by
          rw [hsp, headI_append_left hA2e]
        have hDrhd : (Dr.headI).1 ≤ u + e := by
          have hhd : (A2 ++ Z).headI = Dr.headI := by
            rw [hArest, headI_append_left hDrne]
          have hne : A2 ++ Z ≠ [] := by
            rw [hArest]
            rcases hdd : Dr with _ | ⟨dr, Dr'⟩
            · exact absurd hdd hDrne
            · simp
          by_cases hA2n : A2 = []
          · rw [hA2n, List.nil_append] at hhd
            have hZne : Z ≠ [] := by
              rw [hA2n, List.nil_append] at hne
              exact hne
            rcases h5 with hc | hc
            · exact absurd hc hZne
            · rw [← hhd]
              omega
          · rw [headI_append_left hA2n] at hhd
            rcases h4 with hc | hc
            · exact absurd hc hA2n
            · rw [← hhd]
              exact hc
        rw [← hh1, headI_append_left hDrne]
        exact hDrhd
    have hverd := bad_B_key (B' := B) (A2' := A2') (Z' := Z')
      hMon hMsplit he hzf h1 h6
      (by rw [hDr, List.append_assoc, ← hsp]) h2 hA2'gt hA2'hd hZ'hd
    rw [← hmapeq (ipos + 1) (A1.length + 1 + B.length) (by omega) (by
      rw [hDlen] at hBD
      omega)] at hverd
    exact hverd
  · -- #### `B` reaches the end of the shared part
    obtain ⟨hB2, hT⟩ := split_prefix_left hBAZ hBD
    set B2 := B.drop D.length with hB2def
    have hDgt : ∀ x ∈ D, u + e < x.1 := by
      intro x hx
      refine h2 x ?_
      rw [hB2]
      exact List.mem_append_left _ hx
    -- the head of the next copy is the lifted block root
    have hhead : ∀ (q : ℕ × ℕ × ℕ) (B2' : TrioSeq), B2 = q :: B2' →
        q = (v0 + d0, w10 + d1, z0) := by
      intro q B2' hB2'
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        rcases m with _ | m'
        · exfalso
          rw [gcopiesFrom_zero, hB2'] at hT
          simp at hT
        · exact ⟨m', rfl⟩
      rw [gcopiesFrom_succ,
        gcopy_root_cons M j0 Lb d0 d1 1 (by omega) (by rw [hMlen]; omega),
        hB2', List.cons_append] at hT
      have hqe := (List.cons_eq_cons.1 hT).1
      have hm0 : M.getD j0 (0, 0, 0) = (v0, w10, z0) := by
        rw [hMeq, show G ++ ((v0, w10, z0) :: R) ++ [lp]
          = G ++ (((v0, w10, z0) :: R) ++ [lp]) from by simp,
          getD_app_right _ _ le_rfl, Nat.sub_self]
        rfl
      have he0 : entry M 0 j0 = v0 := by
        show (M.getD j0 (0, 0, 0)).1 = v0
        rw [hm0]
      have he1 : entry M 1 j0 = w10 := by
        show (M.getD j0 (0, 0, 0)).2.1 = w10
        rw [hm0]
      have he2 : entry M 2 j0 = z0 := by
        show (M.getD j0 (0, 0, 0)).2.2 = z0
        rw [hm0]
      rw [← hqe, he0, he1, he2, Nat.one_mul, Nat.one_mul]
    by_cases hlpg : u + e < lp.1
    · -- the host's argument is `D ++ [lp]`
      have hB'gt : ∀ x ∈ D ++ [lp], u + e < x.1 := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hDgt x hx
        · rw [List.mem_singleton.1 hx]
          exact hlpg
      have hverd := bad_B_key (B' := D ++ [lp]) (A2' := []) (Z' := [])
        hMon hMsplit he hzf h1 h6
        (by simp) hB'gt (by simp) (Or.inl rfl) (Or.inl rfl)
      -- split the comparator into the shared prefix and the lp image
      have hsp2 : A1.length + 1 + (D ++ [lp]).length
          = (A1.length + 1 + D.length) + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hsp2, ← List.range'_append_1, List.map_append] at hverd
      rcases hB2e : B2 with _ | ⟨q, B2'⟩
      · -- `B` is exactly the shared part
        have hBeq : B = D := by
          rw [hB2, hB2e, List.append_nil]
        have hshort := sle_take_of_short (sle_of_append_left hverd) (by
          rw [List.length_map, List.length_range']
          omega)
        rw [hBeq]
        rw [← hmapeq (ipos + 1) (A1.length + 1 + D.length) (by omega) (by
          rw [hDlen] at hBD
          omega)] at hshort
        exact hshort
      · -- `B` runs into the next copy: replace `lp` by the copy root
        refine Or.inr ?_
        have hqval := hhead q B2' hB2e
        have hgB : B = D ++ q :: B2' := by
          rw [hB2, hB2e]
        have hVlen : (((List.range' (ipos + 1) (A1.length + 1 + D.length)).map
            (fun p => ((entry M 0 p + e,
              entry M 1 p + (if le1 M ipos p then f else 0),
              entry M 2 p) : ℕ × ℕ × ℕ)))).length
            = A1.length + 1 + D.length := by
          rw [List.length_map, List.length_range']
        have hres := seqlex_of_sle_snoc' (q := q) hverd (by
            rw [hqval]
            exact hqlt) (by
            rw [hVlen]
            omega) B2'
          (((List.range' (ipos + 1 + (A1.length + 1 + D.length))
              (B2'.length + 1)).map
            (fun p => ((entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 0 p + e,
              entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 1 p
                + (if le1 (G ++ gcopies M j0 Lb d0 d1 (m + 1)) ipos p
                  then f else 0),
              entry (G ++ gcopies M j0 Lb d0 d1 (m + 1)) 2 p) : ℕ × ℕ × ℕ))))
        have hgsp2 : A1.length + 1 + B.length
            = (A1.length + 1 + D.length) + (B2'.length + 1) := by
          rw [hgB]
          simp only [List.length_append, List.length_cons]
          omega
        rw [hgsp2, ← List.range'_append_1, List.map_append, hgB]
        rw [← hmapeq (ipos + 1) (A1.length + 1 + D.length) (by omega) (by
          rw [hDlen] at hBD ⊢
          omega)] at hres
        exact hres
    · -- the dropped column is at or below the deeper marked level
      have hqle : v0 + d0 ≤ lp.1 := by
        rcases hqlt with h | ⟨h, -⟩
        · exact le_of_lt h
        · omega
      have hB2nil : B2 = [] := by
        rcases hB2e : B2 with _ | ⟨q, B2'⟩
        · rfl
        · exfalso
          have hqval := hhead q B2' hB2e
          have hqmem : q ∈ B := by
            rw [hB2, hB2e]
            exact List.mem_append_right _ (by simp)
          have := h2 q hqmem
          rw [hqval] at this
          dsimp only at this
          omega
      have hBeq : B = D := by
        rw [hB2, hB2nil, List.append_nil]
      by_cases hu : u < lp.1
      · have hverd := bad_B_key (B' := B) (A2' := [lp]) (Z' := [])
          hMon hMsplit he hzf h1 h6
          (by rw [hBeq]; simp) h2
          (by
            intro x hx
            rw [List.mem_singleton.1 hx]
            exact hu)
          (Or.inr (by simp only [List.headI]; omega))
          (Or.inl rfl)
        rw [← hmapeq (ipos + 1) (A1.length + 1 + B.length) (by omega) (by
          rw [hBeq, hDlen]
          omega)] at hverd
        exact hverd
      · have hverd := bad_B_key (B' := B) (A2' := []) (Z' := [lp])
          hMon hMsplit he hzf h1 h6
          (by rw [hBeq]; simp) h2 (by simp) (Or.inl rfl)
          (Or.inr (by simp only [List.headI]; omega))
        rw [← hmapeq (ipos + 1) (A1.length + 1 + B.length) (by omega) (by
          rw [hBeq, hDlen]
          omega)] at hverd
        exact hverd

/-! ## 自己相似窓の鏡映（hkey 機構の第一部品） -/

/-- In a host whose window `[b, b+s)` holds the `(e, f)`-guarded-map image of
`[a, a+s)`, row-0 parent steps mirror from the source window into the copy. -/
theorem nextrel0_window_mirror {T : TrioSeq} {a b s e f r : ℕ}
    (hab : a ≤ b)
    (hcopy : ∀ t, t < s → T.getD (b + t) (0, 0, 0)
      = ((entry T 0 (a + t) + e,
          entry T 1 (a + t) + (if le1 T r (a + t) then f else 0),
          entry T 2 (a + t)) : ℕ × ℕ × ℕ))
    (hbs : b + s ≤ T.length)
    {ta tb : ℕ} (hta : ta < s) (htb : tb < s)
    (h : nextrel0 T (a + ta) (a + tb)) :
    nextrel0 T (b + ta) (b + tb) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · show entry T 0 (b + ta) < entry T 0 (b + tb)
    show (T.getD (b + ta) (0, 0, 0)).1 < (T.getD (b + tb) (0, 0, 0)).1
    rw [hcopy ta hta, hcopy tb htb]
    have h4' : (T.getD (a + ta) (0, 0, 0)).1 < (T.getD (a + tb) (0, 0, 0)).1 := h4
    dsimp only
    show entry T 0 (a + ta) + e < entry T 0 (a + tb) + e
    have e1 : entry T 0 (a + ta) = (T.getD (a + ta) (0, 0, 0)).1 := rfl
    have e2 : entry T 0 (a + tb) = (T.getD (a + tb) (0, 0, 0)).1 := rfl
    omega
  · intro l hl
    have hlt : ∃ tl, ta < tl ∧ tl < tb ∧ l = b + tl :=
      ⟨l - b, by omega, by omega, by omega⟩
    obtain ⟨tl, htl1, htl2, rfl⟩ := hlt
    show entry T 0 (b + tb) ≤ entry T 0 (b + tl)
    show (T.getD (b + tb) (0, 0, 0)).1 ≤ (T.getD (b + tl) (0, 0, 0)).1
    rw [hcopy tb htb, hcopy tl (by omega)]
    have h5' := h5 (a + tl) ⟨by omega, by omega⟩
    dsimp only
    show entry T 0 (a + tb) + e ≤ entry T 0 (a + tl) + e
    have e1 : entry T 0 (a + tb) = (T.getD (a + tb) (0, 0, 0)).1 := rfl
    have e2 : entry T 0 (a + tl) = (T.getD (a + tl) (0, 0, 0)).1 := rfl
    have h5'' : (T.getD (a + tb) (0, 0, 0)).1 ≤ (T.getD (a + tl) (0, 0, 0)).1 := h5'
    omega

/-- Chains mirror within self-similar windows. -/
theorem rtg0_window_mirror {T : TrioSeq} {a b s e f r : ℕ}
    (hab : a ≤ b)
    (hcopy : ∀ t, t < s → T.getD (b + t) (0, 0, 0)
      = ((entry T 0 (a + t) + e,
          entry T 1 (a + t) + (if le1 T r (a + t) then f else 0),
          entry T 2 (a + t)) : ℕ × ℕ × ℕ))
    (hbs : b + s ≤ T.length)
    {ta : ℕ} (hta : ta < s) :
    ∀ {c : ℕ}, Relation.ReflTransGen (nextrel0 T) (a + ta) c →
      ∀ tb, c = a + tb → tb < s →
      Relation.ReflTransGen (nextrel0 T) (b + ta) (b + tb) := by
  intro c h
  induction h with
  | refl =>
    intro tb hc _
    have : ta = tb := by omega
    rw [this]
  | @tail y z hay hyz ih =>
    intro tb hc htb
    have hy0 : a + ta ≤ y := nextrel0_rtrancl_index_le hay
    have hyz' : y < z := nextrel0_index_less hyz
    have hye : y = a + (y - a) := by omega
    refine (ih (y - a) hye (by omega)).tail ?_
    rw [hc] at hyz
    rw [hye] at hyz
    exact nextrel0_window_mirror hab hcopy hbs (by omega) htb hyz

/-! ## hkey: 整列対のガード継承 -/

set_option maxHeartbeats 4000000 in
/-- **hkey** (probe: 494982 aligned pairs, 0 violations): if the window after
`jpos` copies the guarded-map image of the window after `ipos`, the root
guard descends from the copy endpoint to the source endpoint. -/
theorem hkey_aligned {T : TrioSeq} {r ipos jpos s e f : ℕ}
    (hri : r ≤ ipos) (hij : ipos < jpos)
    (hlen : jpos + 1 + s < T.length)
    (hprefix : ∀ t, t < s → T.getD (jpos + 1 + t) (0, 0, 0)
      = ((entry T 0 (ipos + 1 + t) + e,
          entry T 1 (ipos + 1 + t)
            + (if le1 T ipos (ipos + 1 + t) then f else 0),
          entry T 2 (ipos + 1 + t)) : ℕ × ℕ × ℕ))
    (hrow0 : entry T 0 (jpos + 1 + s) = entry T 0 (ipos + 1 + s) + e)
    (hupI : ∀ l, ipos < l → l ≤ jpos + 1 + s → entry T 0 ipos < entry T 0 l)
    (hupR : ∀ l, r < l → l ≤ jpos + 1 + s → entry T 0 r < entry T 0 l)
    (hrow1 : ¬ le1 T ipos (ipos + 1 + s) →
      entry T 1 r < entry T 1 (ipos + 1 + s))
    (hgB : le1 T r (jpos + 1 + s)) :
    le1 T r (ipos + 1 + s) := by
  have hlenI : ipos + 1 + s < T.length := by omega
  have hchI : Relation.ReflTransGen (nextrel0 T) r (ipos + 1 + s) := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l h1 h2
    exact hupR l h1 (by omega)
  have hchii : Relation.ReflTransGen (nextrel0 T) ipos (ipos + 1 + s) := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l h1 h2
    exact hupI l h1 (by omega)
  have hchJi : Relation.ReflTransGen (nextrel0 T) ipos (jpos + 1 + s) := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l h1 h2
    exact hupI l h1 (by omega)
  have hwJ := le1_chain_window hgB.2.2
  have hw_ipos : ipos ≠ r → entry T 1 r < entry T 1 ipos := by
    intro hne
    refine hwJ ipos ?_ hchJi hne
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l h1 h2
    exact hupR l h1 (by omega)
  -- row 1 of a guarded source node exceeds the root's
  have hnode : ∀ x, ipos < x → x ≤ ipos + 1 + s →
      Relation.ReflTransGen (nextrel0 T) x (ipos + 1 + s) →
      le1 T ipos x → entry T 1 r < entry T 1 x := by
    intro x hx1 hx2 hxch hgx
    have hxi : entry T 1 ipos < entry T 1 x := by
      refine le1_chain_window hgx.2.2 x ?_ .refl (by omega)
      refine rtg0_of_window (by omega) (by omega) ?_
      intro l h1 h2
      exact hupI l h1 (by omega)
    rcases Nat.eq_or_lt_of_le hri with rfl | hlt
    · -- `ipos = r`
      omega
    · have := hw_ipos (by omega)
      omega
  refine (le1_iff_chain_window hlenI hchI).2 ?_
  intro x hrx hxp hxne
  have hx0 : r ≤ x := nextrel0_rtrancl_index_le hrx
  have hxup : x ≤ ipos + 1 + s := nextrel0_rtrancl_index_le hxp
  rcases Nat.lt_or_ge x (ipos + 1) with hxlo | hxhi
  · rcases Nat.eq_or_lt_of_le (show x ≤ ipos from by omega) with rfl | hxlt
    · exact hw_ipos hxne
    · have hxJ : Relation.ReflTransGen (nextrel0 T) x (jpos + 1 + s) := by
        have hxi : Relation.ReflTransGen (nextrel0 T) x ipos :=
          rtg0_comparable hxp hchii (by omega)
        exact hxi.trans hchJi
      exact hwJ x hrx hxJ hxne
  · rcases Nat.eq_or_lt_of_le hxup with rfl | hxstrict
    · -- the endpoint itself
      by_cases hgx : le1 T ipos (ipos + 1 + s)
      · exact hnode _ (by omega) le_rfl .refl hgx
      · exact hrow1 hgx
    · -- a strict source-window node: mirror it into the copy
      set tx := x - ipos - 1 with htxdef
      have htx : x = ipos + 1 + tx := by omega
      have htxs : tx < s := by omega
      by_cases hgx : le1 T ipos x
      · exact hnode x (by omega) (by omega) hxp hgx
      · -- unguarded node: its mirror carries the same row 1
        -- build the chain from the mirror to the copy endpoint
        rw [htx] at hxp
        rcases hxp.cases_tail with heq | ⟨y, hxy, hyp⟩
        · exfalso
          omega
        · have hy0 : ipos + 1 + tx ≤ y := nextrel0_rtrancl_index_le hxy
          have hyup : y < ipos + 1 + s := nextrel0_index_less hyp
          set ty := y - ipos - 1 with htydef
          have hty : y = ipos + 1 + ty := by omega
          have htys : ty < s := by omega
          have hmirch : Relation.ReflTransGen (nextrel0 T)
              (jpos + 1 + tx) (jpos + 1 + ty) := by
            have h := rtg0_window_mirror (a := ipos + 1) (b := jpos + 1)
              (s := s) (e := e) (f := f) (r := ipos) (by omega)
              (by
                intro t ht
                have h2 := hprefix t ht
                rw [show jpos + 1 + t = jpos + 1 + t from rfl] at h2
                exact h2)
              (by omega) (ta := tx) (by omega) (c := y) hxy ty hty htys
            exact h
          have hstep : nextrel0 T (jpos + 1 + ty) (jpos + 1 + s) := by
            rw [hty] at hyp
            obtain ⟨g1, g2, g3, g4, g5⟩ := hyp
            refine ⟨by omega, by omega, by omega, ?_, ?_⟩
            · show entry T 0 (jpos + 1 + ty) < entry T 0 (jpos + 1 + s)
              have hv : entry T 0 (jpos + 1 + ty)
                  = entry T 0 (ipos + 1 + ty) + e := by
                show (T.getD (jpos + 1 + ty) (0, 0, 0)).1 = _
                rw [hprefix ty htys]
              rw [hv, hrow0]
              have g4' : entry T 0 (ipos + 1 + ty)
                  < entry T 0 (ipos + 1 + s) := g4
              omega
            · intro l hl
              have htl : ∃ tl, ty < tl ∧ tl < s ∧ l = jpos + 1 + tl :=
                ⟨l - jpos - 1, by omega, by omega, by omega⟩
              obtain ⟨tl, htl1, htl2, rfl⟩ := htl
              show entry T 0 (jpos + 1 + s) ≤ entry T 0 (jpos + 1 + tl)
              have hv : entry T 0 (jpos + 1 + tl)
                  = entry T 0 (ipos + 1 + tl) + e := by
                show (T.getD (jpos + 1 + tl) (0, 0, 0)).1 = _
                rw [hprefix tl htl2]
              rw [hv, hrow0]
              have g5' := g5 (ipos + 1 + tl) ⟨by omega, by omega⟩
              have g5'' : entry T 0 (ipos + 1 + s)
                  ≤ entry T 0 (ipos + 1 + tl) := g5'
              omega
          have hmir : Relation.ReflTransGen (nextrel0 T)
              (jpos + 1 + tx) (jpos + 1 + s) := hmirch.tail hstep
          have hrmir : Relation.ReflTransGen (nextrel0 T) r (jpos + 1 + tx) := by
            refine rtg0_of_window (by omega) (by omega) ?_
            intro l h1 h2
            exact hupR l h1 (by omega)
          have hwx := hwJ (jpos + 1 + tx) hrmir hmir (by omega)
          have hv1 : entry T 1 (jpos + 1 + tx) = entry T 1 (ipos + 1 + tx) := by
            show (T.getD (jpos + 1 + tx) (0, 0, 0)).2.1 = _
            rw [hprefix tx htxs]
            dsimp only
            rw [if_neg (by rw [← htx]; exact hgx), Nat.add_zero]
          rw [hv1, ← htx] at hwx
          exact hwx

/-! ## 塔の周期性（コピー数に依らない読み出し） -/

/-- The tower's entries do not depend on the copy count. -/
theorem gexp_getD_indep {M : TrioSeq} {j0 Lb d0 d1 n n' p : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hp : p < j0 + n * Lb) (hp' : p < j0 + n' * Lb) :
    (gexp M j0 Lb d0 d1 n).getD p (0, 0, 0)
      = (gexp M j0 Lb d0 d1 n').getD p (0, 0, 0) := by
  rcases Nat.lt_or_ge p j0 with h | h
  · rw [gexp_getD_low hlen h, gexp_getD_low hlen h]
  · obtain ⟨k, q, hk, hq, hpe⟩ := gexp_pos_decomp (j0 := j0) (Lb := Lb)
      (n := n) (p := p) hLb h hp
    have hk' : k < n' := by
      by_contra hc
      have hmul : n' * Lb ≤ k * Lb := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [hpe, gexp_getD_mir hlen hk hq, gexp_getD_mir hlen hk' hq]

/-- One period up: row 0 rises by `d0` and row 1 by the block guard's `d1`. -/
theorem gexp_period {M : TrioSeq} {j0 Lb d0 d1 n c q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hc1 : c + 1 < n) (hq : q < Lb) :
    (gexp M j0 Lb d0 d1 n).getD (j0 + ((c + 1) * Lb + q)) (0, 0, 0)
      = (entry M 0 (j0 + q) + c * d0 + d0,
         entry M 1 (j0 + q) + (if le1 M j0 (j0 + q) then c * d1 else 0)
           + (if le1 M j0 (j0 + q) then d1 else 0),
         entry M 2 (j0 + q)) := by
  rw [gexp_getD_mir hlen hc1 hq]
  have h0 : (c + 1) * d0 = c * d0 + d0 := Nat.succ_mul c d0
  have h1 : (c + 1) * d1 = c * d1 + d1 := Nat.succ_mul c d1
  by_cases hg : le1 M j0 (j0 + q)
  · simp only [if_pos hg]
    exact Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) rfl)
  · simp only [if_neg hg, Nat.add_zero]
    exact Prod.ext (by dsimp only; omega) (Prod.ext rfl rfl)

/-! ## 添字での分割 -/

theorem getD_drop (N : TrioSeq) (m i : ℕ) :
    (N.drop m).getD i (0, 0, 0) = N.getD (m + i) (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem split_one {N : TrioSeq} {a : ℕ} (ha : a < N.length) :
    N = N.take a ++ N.getD a (0, 0, 0) :: N.drop (a + 1) := by
  conv_lhs => rw [← List.take_append_drop a N]
  refine congrArg (fun t => N.take a ++ t) ?_
  rcases hd : N.drop a with _ | ⟨x, V⟩
  · exfalso
    have hh := congrArg List.length hd
    rw [List.length_drop, List.length_nil] at hh
    omega
  · have hx : N.getD a (0, 0, 0) = x := by
      have hh := getD_drop N a 0
      rw [hd, Nat.add_zero] at hh
      rw [← hh, List.getD_cons_zero]
    have hdr : N.drop (a + 1) = V := by
      have hh : (N.drop a).drop 1 = N.drop (a + 1) := by
        rw [List.drop_drop]
      rw [← hh, hd, List.drop_succ_cons, List.drop_zero]
    rw [hx, hdr]

theorem getD_take_drop {N : TrioSeq} {a l t : ℕ} (ht : t < l) :
    ((N.drop a).take l).getD t (0, 0, 0) = N.getD (a + t) (0, 0, 0) := by
  rw [getD_take ht, getD_drop]

theorem mem_index {A : TrioSeq} {x : ℕ × ℕ × ℕ} (hx : x ∈ A) :
    ∃ t, t < A.length ∧ x = A.getD t (0, 0, 0) := by
  obtain ⟨t, ht, hxe⟩ := List.getElem_of_mem hx
  refine ⟨t, ht, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, hxe]
  rfl

theorem mem_take_drop_index {N : TrioSeq} {a l : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ (N.drop a).take l) :
    ∃ t, t < l ∧ x = N.getD (a + t) (0, 0, 0) := by
  obtain ⟨t, ht, hxe⟩ := mem_index hx
  rw [List.length_take, List.length_drop] at ht
  have htl : t < l := lt_of_lt_of_le ht (min_le_left _ _)
  exact ⟨t, htl, by rw [hxe, getD_take_drop htl]⟩

theorem mem_take_index {N : TrioSeq} {l : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ N.take l) : ∃ t, t < l ∧ x = N.getD t (0, 0, 0) := by
  have hx' : x ∈ (N.drop 0).take l := by rwa [List.drop_zero]
  obtain ⟨t, ht, hxe⟩ := mem_take_drop_index hx'
  exact ⟨t, ht, by rw [hxe, Nat.zero_add]⟩

theorem split_two {N : TrioSeq} {a b : ℕ} (hab : a < b) (hb : b < N.length) :
    N = N.take a ++ N.getD a (0, 0, 0) ::
      ((N.drop (a + 1)).take (b - a - 1) ++ N.getD b (0, 0, 0)
        :: N.drop (b + 1)) := by
  have hin : b - a - 1 < (N.drop (a + 1)).length := by
    rw [List.length_drop]
    omega
  have h1 := split_one (N := N) (a := a) (by omega)
  have h2 := split_one (N := N.drop (a + 1)) (a := b - a - 1) hin
  have hg : (N.drop (a + 1)).getD (b - a - 1) (0, 0, 0)
      = N.getD b (0, 0, 0) := by
    rw [getD_drop, show a + 1 + (b - a - 1) = b from by omega]
  have hdd : (N.drop (a + 1)).drop (b - a - 1 + 1) = N.drop (b + 1) := by
    rw [List.drop_drop, show a + 1 + (b - a - 1 + 1) = b + 1 from by omega]
  rw [hg, hdd] at h2
  conv_lhs => rw [h1, h2]

/-! ## `SpineOK` の位置形 -/

/-- **Positional form of `SpineOK`**: a column strictly between the two
marked positions which is right-visible up to the deeper one and sits below
its level carries row 1 at least `w1`. -/
theorem spineOK_pos {N X A1 B A2 Z : TrioSeq} {u w1 z e f w : ℕ}
    (heq : N = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z)
    (h6 : SpineOK A1 (u + e) w) :
    ∀ p, X.length < p → p < X.length + (A1.length + 1) →
      entry N 0 p < u + e →
      (∀ p', p < p' → p' < X.length + (A1.length + 1) →
        entry N 0 p < entry N 0 p') →
      w ≤ entry N 1 p := by
  have hN : N = X ++ ((u, w1, z)
      :: (A1 ++ ((u + e, w1 + f, z) :: ((B ++ A2) ++ Z)))) := by
    rw [heq]
    simp [List.append_assoc]
  have hget : ∀ t, t < A1.length →
      N.getD (X.length + 1 + t) (0, 0, 0) = A1.getD t (0, 0, 0) := by
    intro t ht
    rw [hN, getD_app_right _ _ (by omega),
      show X.length + 1 + t - X.length = t + 1 from by omega,
      List.getD_cons_succ, getD_append_left ht]
  intro p hp1 hp2 hp3 hp4
  obtain ⟨t, rfl⟩ : ∃ t, p = X.length + 1 + t := ⟨p - X.length - 1, by omega⟩
  have ht : t < A1.length := by omega
  have hsplit : A1 = A1.take t ++ A1.drop t := (List.take_append_drop t A1).symm
  have htlen : (A1.take t).length = t := by
    rw [List.length_take]
    omega
  rcases hd : A1.drop t with _ | ⟨x, V⟩
  · exfalso
    have hh := congrArg List.length hd
    rw [List.length_drop] at hh
    simp only [List.length_nil] at hh
    omega
  have hA1 : A1 = A1.take t ++ x :: V := by
    rw [← hd]
    exact hsplit
  have hx : A1.getD t (0, 0, 0) = x := by
    conv_lhs => rw [hA1]
    rw [getD_app_right _ _ (le_of_eq htlen), htlen, Nat.sub_self,
      List.getD_cons_zero]
  have hVlen : t + 1 + V.length = A1.length := by
    have hh := congrArg List.length hA1
    simp only [List.length_append, List.length_cons, htlen] at hh
    omega
  have hxlt : x.1 < u + e := by
    have hh : (N.getD (X.length + 1 + t) (0, 0, 0)).1 < u + e := hp3
    rw [hget t ht, hx] at hh
    exact hh
  have hV : ∀ y ∈ V, x.1 < y.1 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hy
    have hVget : V.getD s (0, 0, 0) = V[s] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
    have hidx : A1.getD (t + 1 + s) (0, 0, 0) = V[s] := by
      conv_lhs => rw [hA1]
      rw [getD_app_right _ _ (by omega), htlen,
        show t + 1 + s - t = s + 1 from by omega, List.getD_cons_succ, hVget]
    have hh : (N.getD (X.length + 1 + t) (0, 0, 0)).1
        < (N.getD (X.length + 1 + (t + 1 + s)) (0, 0, 0)).1 :=
      hp4 (X.length + 1 + (t + 1 + s)) (by omega) (by omega)
    rw [hget t ht, hget (t + 1 + s) (by omega), hx, hidx] at hh
    exact hh
  show w ≤ (N.getD (X.length + 1 + t) (0, 0, 0)).2.1
  rw [hget t ht, hx]
  exact h6 (A1.take t) V x hA1 hxlt hV

/-- Positional criterion for `SpineOK` on a take/drop slice. -/
theorem spineOK_of_pos {N : TrioSeq} {a l L w : ℕ} (hfull : a + l ≤ N.length)
    (h : ∀ p, a ≤ p → p < a + l → entry N 0 p < L →
      (∀ p', p < p' → p' < a + l → entry N 0 p < entry N 0 p') →
      w ≤ entry N 1 p) :
    SpineOK ((N.drop a).take l) L w := by
  intro U V x hA hxlt hV
  have hlen : U.length + 1 + V.length = ((N.drop a).take l).length := by
    rw [hA]
    simp only [List.length_append, List.length_cons]
    omega
  have hlt : U.length + 1 + V.length = l := by
    rw [hlen, List.length_take, List.length_drop]
    omega
  have hx : x = N.getD (a + U.length) (0, 0, 0) := by
    have hh : ((N.drop a).take l).getD U.length (0, 0, 0) = x := by
      rw [hA, getD_app_right _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rw [← hh, getD_take_drop (by omega)]
  have hVget : ∀ s, s < V.length →
      V.getD s (0, 0, 0) = N.getD (a + (U.length + 1 + s)) (0, 0, 0) := by
    intro s hs
    have hh : ((N.drop a).take l).getD (U.length + 1 + s) (0, 0, 0)
        = V.getD s (0, 0, 0) := by
      rw [hA, getD_app_right _ _ (by omega),
        show U.length + 1 + s - U.length = s + 1 from by omega,
        List.getD_cons_succ]
    rw [← hh, getD_take_drop (by omega)]
  rw [hx]
  refine h (a + U.length) (by omega) (by omega) ?_ ?_
  · show (N.getD (a + U.length) (0, 0, 0)).1 < L
    rw [← hx]
    exact hxlt
  · intro p' hp1 hp2
    obtain ⟨s, rfl⟩ : ∃ s, p' = a + (U.length + 1 + s) :=
      ⟨p' - a - U.length - 1, by omega⟩
    have hs : s < V.length := by omega
    have hmem : V.getD s (0, 0, 0) ∈ V := getD_mem_of_lt hs
    have := hV _ hmem
    rw [hVget s hs] at this
    show (N.getD (a + U.length) (0, 0, 0)).1 < _
    rw [← hx]
    exact this

/-! ## ガード付き持ち上げの `sle` 輸送 -/

/-- Pointwise guarded lift of a list, guards read at absolute positions. -/
noncomputable def gliftAt (d0 d1 : ℕ) (g : ℕ → Prop) : ℕ → TrioSeq → TrioSeq
  | _, [] => []
  | o, p :: rest =>
      ((p.1 + d0, p.2.1 + (if g o then d1 else 0), p.2.2) : ℕ × ℕ × ℕ)
        :: gliftAt d0 d1 g (o + 1) rest

@[simp] theorem gliftAt_nil (d0 d1 : ℕ) (g : ℕ → Prop) (o : ℕ) :
    gliftAt d0 d1 g o [] = [] := rfl

@[simp] theorem gliftAt_cons (d0 d1 : ℕ) (g : ℕ → Prop) (o : ℕ)
    (p : ℕ × ℕ × ℕ) (rest : TrioSeq) :
    gliftAt d0 d1 g o (p :: rest)
      = ((p.1 + d0, p.2.1 + (if g o then d1 else 0), p.2.2) : ℕ × ℕ × ℕ)
        :: gliftAt d0 d1 g (o + 1) rest := rfl

theorem gliftAt_length (d0 d1 : ℕ) (g : ℕ → Prop) :
    ∀ (o : ℕ) (A : TrioSeq), (gliftAt d0 d1 g o A).length = A.length
  | _, [] => rfl
  | o, _ :: rest => by
      rw [gliftAt_cons, List.length_cons, List.length_cons,
        gliftAt_length d0 d1 g (o + 1) rest]

/-- Head-splitting form of `sle`. -/
theorem sle_cons_cons {p q : ℕ × ℕ × ℕ} {M N : TrioSeq} :
    sle (p :: M) (q :: N) ↔ collt p q ∨ (p = q ∧ sle M N) := by
  constructor
  · intro h
    rcases h with heq | h
    · refine Or.inr ⟨(List.cons.injEq _ _ _ _ ▸ heq).1,
        Or.inl ((List.cons.injEq _ _ _ _ ▸ heq).2)⟩
    · rw [seqlex_cons_cons] at h
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inr h2⟩
  · intro h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inr (by rw [seqlex_cons_cons]; exact Or.inl h)
    · rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [seqlex_cons_cons]; exact Or.inr ⟨rfl, h⟩)

set_option maxHeartbeats 1000000 in
/-- **Guarded-lift transport of `sle`** (the `hkey` interface): if at every
index where the two lists agree in row 0 and the argument's row 1 does not
exceed the comparator's the argument's guard implies the comparator's, then
the guarded lift preserves `sle`.  The `(F, T)` mismatch wins early, the
`(T, F)` one is exactly what `hkey` excludes. -/
theorem sle_gliftAt {d0 d1 : ℕ} (hd1 : 0 < d1) {gB gc : ℕ → Prop} :
    ∀ (B0 c0 : TrioSeq) (o : ℕ),
      (∀ k, k < B0.length → k < c0.length →
        (∀ s, s < k → B0.getD s (0, 0, 0) = c0.getD s (0, 0, 0)
          ∧ (gB (o + s) ↔ gc (o + s))) →
        (B0.getD k (0, 0, 0)).1 = (c0.getD k (0, 0, 0)).1 →
        (B0.getD k (0, 0, 0)).2.1 ≤ (c0.getD k (0, 0, 0)).2.1 →
        gB (o + k) → gc (o + k)) →
      sle B0 c0 →
      sle (gliftAt d0 d1 gB o B0) (gliftAt d0 d1 gc o c0) := by
  intro B0
  induction B0 with
  | nil =>
    intro c0 o _ _
    rcases c0 with _ | ⟨q, c0'⟩
    · exact Or.inl rfl
    · exact Or.inr (by
        rw [gliftAt_nil, gliftAt_cons]
        exact List.cons_ne_nil _ _)
  | cons p B0' ih =>
    intro c0 o hkey h
    rcases c0 with _ | ⟨q, c0'⟩
    · exact absurd h (by
        rintro (h | h)
        · exact absurd h (by simp)
        · exact h)
    have hstep : p = q → (gB o ↔ gc o) →
        ∀ k, k < B0'.length → k < c0'.length →
        (∀ s, s < k → B0'.getD s (0, 0, 0) = c0'.getD s (0, 0, 0)
          ∧ (gB (o + 1 + s) ↔ gc (o + 1 + s))) →
        (B0'.getD k (0, 0, 0)).1 = (c0'.getD k (0, 0, 0)).1 →
        (B0'.getD k (0, 0, 0)).2.1 ≤ (c0'.getD k (0, 0, 0)).2.1 →
        gB (o + 1 + k) → gc (o + 1 + k) := by
      intro hpq hg0 k h1 h2 hpre h3 h4
      have hh := hkey (k + 1) (by simpa using h1) (by simpa using h2)
        (by
          intro s hs
          rcases Nat.eq_zero_or_pos s with rfl | hsp
          · refine ⟨by simpa using hpq, ?_⟩
            rw [Nat.add_zero]
            exact hg0
          · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
            have hh2 := hpre s' (by omega)
            refine ⟨by simpa using hh2.1, ?_⟩
            rw [show o + (s' + 1) = o + 1 + s' from by omega]
            exact hh2.2)
        (by simpa using h3) (by simpa using h4)
      rw [show o + (k + 1) = o + 1 + k from by omega] at hh
      exact hh
    have hk0 : p.1 = q.1 → p.2.1 ≤ q.2.1 → gB o → gc o := by
      intro h1 h2 h3
      have hh := hkey 0 (by simp) (by simp) (by omega)
        (by simpa using h1) (by simpa using h2)
      rw [Nat.add_zero] at hh
      exact hh h3
    rw [gliftAt_cons, gliftAt_cons, sle_cons_cons]
    rw [sle_cons_cons] at h
    rcases h with hlt | ⟨rfl, h⟩
    · -- the heads already decide
      refine Or.inl ?_
      rcases Nat.lt_or_ge p.1 q.1 with h1 | h1
      · unfold collt
        dsimp only
        omega
      · have h2 : p.1 = q.1 := by
          unfold collt at hlt
          omega
        have h3 : p.2.1 ≤ q.2.1 := by
          unfold collt at hlt
          omega
        by_cases hgb : gB o
        · rw [if_pos hgb, if_pos (hk0 h2 h3 hgb)]
          unfold collt at hlt ⊢
          dsimp only at hlt ⊢
          omega
        · rw [if_neg hgb]
          by_cases hgc : gc o
          · rw [if_pos hgc]
            unfold collt at hlt ⊢
            dsimp only at hlt ⊢
            omega
          · rw [if_neg hgc]
            unfold collt at hlt ⊢
            dsimp only at hlt ⊢
            omega
    · -- equal heads: the guards decide
      by_cases hgb : gB o
      · have hgc0 := hk0 rfl le_rfl hgb
        rw [if_pos hgb, if_pos hgc0]
        exact Or.inr ⟨rfl, ih c0' (o + 1)
          (hstep rfl ⟨fun _ => hgc0, fun _ => hgb⟩) h⟩
      · rw [if_neg hgb]
        by_cases hgc : gc o
        · refine Or.inl ?_
          rw [if_pos hgc]
          unfold collt
          dsimp only
          omega
        · rw [if_neg hgc]
          exact Or.inr ⟨rfl, ih c0' (o + 1)
            (hstep rfl ⟨fun hh => absurd hh hgb, fun hh => absurd hh hgc⟩) h⟩

/-- Same-guard specialisation (probe: in the straddling cases the two guard
words agree at every index — 179673 checks, 0 mismatches). -/
theorem sle_gliftAt_same {d0 d1 : ℕ} (hd1 : 0 < d1) {g : ℕ → Prop}
    (B0 c0 : TrioSeq) (o : ℕ) (h : sle B0 c0) :
    sle (gliftAt d0 d1 g o B0) (gliftAt d0 d1 g o c0) :=
  sle_gliftAt hd1 B0 c0 o (fun _ _ _ _ _ _ hg => hg) h

/-! ## 交差ケース (c) の反駁 -/

/-- The first row-1 chain node at or above `i`: walking the row-1 ancestry of
`c` from below, the first node that reaches `i` carries row 1 at most `i`'s
(by the `nextrel1` minimality clause at the step that jumps over `i`). -/
theorem chain_first_above {M : TrioSeq} {i c : ℕ}
    (hi0 : Relation.ReflTransGen (nextrel0 M) i c) :
    ∀ (a : ℕ), Relation.ReflTransGen (nextrel1 M) a c → a < i → i ≤ c →
      ∃ b, i ≤ b ∧ b ≤ c ∧ Relation.ReflTransGen (nextrel1 M) b c ∧
        entry M 1 b ≤ entry M 1 i := by
  intro a h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro hai hic; omega
  | @head a y hay hyc ih =>
    intro hai hic
    rcases Nat.lt_or_ge y i with hlt | hge
    · exact ih hlt hic
    · refine ⟨y, hge, rtg1_index_le hyc, hyc, ?_⟩
      have hy0 : Relation.ReflTransGen (nextrel0 M) y c := rtg1_rtg0 hyc
      have hiy : Relation.ReflTransGen (nextrel0 M) i y :=
        rtg0_comparable hi0 hy0 hge
      exact hay.2.2.2.2.2 i ⟨hai, ⟨lt_of_le_of_lt hge hay.2.1, hay.2.1, hiy⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The shallower column is marked.**  If `i` sits on the bad column's
row-0 chain below the copy level and the block spine never drops below `i`'s
row 1, then the first row-1 chain node at or above `i` carries *exactly*
`i`'s row 1, so `zjump` transports the bad column's mark down to `i`. -/
theorem mark_of_spine {M : TrioSeq} (hM : ST_TS M) {j0 x i d0 d1 : ℕ}
    (np2 : nextrel2 M j0 x)
    (hd0 : entry M 0 x = entry M 0 j0 + d0)
    (hd1 : entry M 1 x = entry M 1 j0 + d1)
    (hji : j0 < i) (hix : i < x)
    (hu : entry M 0 i < entry M 0 j0 + d0)
    (hroot : entry M 1 i ≤ entry M 1 j0 + d1)
    (hA1blk : ∀ l, i < l → l < x → entry M 0 i < entry M 0 l)
    (hspblk : ∀ p, i < p → p < x → entry M 0 p < entry M 0 x →
      (∀ p', p < p' → p' < x → entry M 0 p < entry M 0 p') →
      entry M 1 i ≤ entry M 1 p) :
    entry M 2 i = 1 := by
  have hxlen : x < M.length := np2.2.1
  have hilen : i < M.length := by omega
  have hle1x : le1 M j0 x := np2.2.2.2.2.1
  have hx2 : entry M 2 x = 1 := by
    have h1 := np2.2.2.2.1
    have h2 := z2ok_ST_TS hM x hxlen
    have e2 : entry M 2 x = (M.getD x (0, 0, 0)).2.2 := rfl
    omega
  have hrtgix : Relation.ReflTransGen (nextrel0 M) i x := by
    refine rtg0_of_window hxlen (by omega) ?_
    intro l h1 h2
    rcases Nat.lt_or_ge l x with hlt | hge
    · exact hA1blk l h1 hlt
    · have hlx : l = x := by omega
      rw [hlx, hd0]
      omega
  obtain ⟨b, hib, hbx, hchb, hble⟩ :=
    chain_first_above hrtgix j0 hle1x.2.2 hji (by omega)
  have hblen : b < M.length := by omega
  have hb2 : 1 ≤ entry M 2 b := by
    rcases Nat.eq_or_lt_of_le hbx with hbeq | hblt
    · rw [hbeq]
      omega
    · have := np2.2.2.2.2.2 b ⟨by omega, ⟨hblen, hxlen, hchb⟩⟩
      omega
  have hzi : 1 ≤ entry M 2 i := by
    rcases Nat.eq_or_lt_of_le hib with hbeq | hilt
    · rw [← hbeq] at hb2
      exact hb2
    · have hb0x : entry M 0 b ≤ entry M 0 x := by
        rcases Nat.eq_or_lt_of_le hbx with hbeq | hblt
        · rw [hbeq]
        · exact (le0_interval_gt (rtg1_rtg0 hchb) x ⟨hblt, le_rfl⟩).le
      have hwb : entry M 1 i ≤ entry M 1 b := by
        rcases Nat.eq_or_lt_of_le hbx with hbeq | hblt
        · rw [hbeq, hd1]
          exact hroot
        · refine hspblk b hilt hblt
            (le0_interval_gt (rtg1_rtg0 hchb) x ⟨hblt, le_rfl⟩) ?_
          intro p' h1 h2
          exact le0_interval_gt (rtg1_rtg0 hchb) p' ⟨h1, by omega⟩
      have heq1 : entry M 1 b = entry M 1 i := by omega
      have hsub : ∀ l, i < l → l ≤ b → entry M 0 i < entry M 0 l := by
        intro l h1 h2
        rcases Nat.lt_or_ge l x with hlt | hge
        · exact hA1blk l h1 hlt
        · have hlx : l = x := by omega
          rw [hlx, hd0]
          omega
      have hsp : ∀ l, i < l → l < b → entry M 0 l < entry M 0 b →
          (∀ l', l < l' → l' < b → entry M 0 l < entry M 0 l') →
          entry M 1 i ≤ entry M 1 l := by
        intro l h1 h2 h3 h4
        refine hspblk l h1 (by omega) (by omega) ?_
        intro p' hp1 hp2
        rcases Nat.lt_or_ge p' b with hpb | hpb
        · exact h4 p' hp1 hpb
        · rcases Nat.eq_or_lt_of_le hpb with hpe | hpl
          · rw [← hpe]
            exact h3
          · have hbp : entry M 0 b < entry M 0 p' :=
              le0_interval_gt (rtg1_rtg0 hchb) p' ⟨hpl, by omega⟩
            omega
      have hzj := zjump_ST_TS hM i b hilt hblen hsub heq1 hsp
      omega
  have h2 := z2ok_ST_TS hM i hilen
  have e2 : entry M 2 i = (M.getD i (0, 0, 0)).2.2 := rfl
  omega

set_option maxHeartbeats 4000000 in
/-- **Case A2 (c)** — the shallower marked column sits strictly inside the
block while the deeper one mirrors an *earlier* block position (`qj < i`).

Refuted: `i` lies on the row-0 chain of the bad column `x`, so the first
row-1 chain node `b ≥ i` carries row 1 at most `i`'s, while the spine
carries it at least `i`'s — equality, so `zjump` transports `b`'s mark down
to `i`.  A marked `i` forces `f = 0`, and the guard equation then puts
row 1 of `i` strictly above the copy-1 root, contradicting the spine. -/
theorem cross_absurd {M : TrioSeq} (hM : ST_TS M) {j0 x i qj d0 d1 k : ℕ}
    (np2 : nextrel2 M j0 x)
    (hd0 : entry M 0 x = entry M 0 j0 + d0)
    (hd1 : entry M 1 x = entry M 1 j0 + d1)
    (hji : j0 < i) (hix : i < x) (hj0q : j0 ≤ qj) (hqx : qj < x) (hk : 1 ≤ k)
    (hu : entry M 0 i < entry M 0 j0 + d0)
    (hroot : entry M 1 i ≤ entry M 1 j0 + d1)
    (hf : entry M 1 i ≤ entry M 1 qj + k * (if le1 M j0 qj then d1 else 0))
    (hzeq : entry M 2 i = entry M 2 qj)
    (hzf : entry M 1 i = entry M 1 qj + k * (if le1 M j0 qj then d1 else 0)
      ∨ entry M 2 i = 0)
    (hA1blk : ∀ l, i < l → l < x → entry M 0 i < entry M 0 l)
    (hspblk : ∀ p, i < p → p < x → entry M 0 p < entry M 0 x →
      (∀ p', p < p' → p' < x → entry M 0 p < entry M 0 p') →
      entry M 1 i ≤ entry M 1 p)
    (hspcpy : ∀ c, j0 ≤ c → c < qj → entry M 0 c < entry M 0 qj →
      (∀ c', c < c' → c' < qj → entry M 0 c < entry M 0 c') →
      entry M 1 i ≤ entry M 1 c + k * (if le1 M j0 c then d1 else 0)) :
    False := by
  have hxlen : x < M.length := np2.2.1
  have hj0len : j0 < M.length := np2.1
  have hilen : i < M.length := by omega
  have hqlen : qj < M.length := by omega
  have hle1x : le1 M j0 x := np2.2.2.2.2.1
  have hch0 : Relation.ReflTransGen (nextrel0 M) j0 x := rtg1_rtg0 hle1x.2.2
  have hwin0 : ∀ k, j0 < k → k ≤ x → entry M 0 j0 < entry M 0 k :=
    fun k h1 h2 => le0_interval_gt hch0 k ⟨h1, h2⟩
  have hd1pos : 0 < d1 := by
    have := rtg1_entry1_lt hle1x.2.2 (by omega : j0 ≠ x)
    omega
  have hx2 : entry M 2 x = 1 := by
    have h1 := np2.2.2.2.1
    have h2 := z2ok_ST_TS hM x hxlen
    have e2 : entry M 2 x = (M.getD x (0, 0, 0)).2.2 := rfl
    omega
  have hj02 : entry M 2 j0 = 0 := by
    have h1 := np2.2.2.2.1
    omega
  -- `i` sits on the row-0 chain of the bad column
  have hrtgji : Relation.ReflTransGen (nextrel0 M) j0 i :=
    rtg0_of_window hilen (by omega) (fun l h1 h2 => hwin0 l h1 (by omega))
  have hrtgix : Relation.ReflTransGen (nextrel0 M) i x := by
    refine rtg0_of_window hxlen (by omega) ?_
    intro l h1 h2
    rcases Nat.lt_or_ge l x with hlt | hge
    · exact hA1blk l h1 hlt
    · have hlx : l = x := by omega
      rw [hlx, hd0]
      omega
  have hwgt : entry M 1 j0 < entry M 1 i :=
    le1_chain_window hle1x.2.2 i hrtgji hrtgix (by omega)
  -- the mirror source is guarded
  have hgj : le1 M j0 qj := by
    by_contra hg
    rcases Nat.eq_or_lt_of_le hj0q with hqe | hlt
    · exact hg (hqe ▸ le1_refl hj0len)
    have hrtgjq : Relation.ReflTransGen (nextrel0 M) j0 qj :=
      rtg0_of_window hqlen (by omega) (fun l h1 h2 => hwin0 l h1 (by omega))
    obtain ⟨b, hb1, hb2, hb3, hb4⟩ := blocker_of_not_le1 hrtgjq hqlen hg
    have hbj : j0 ≤ b := nextrel0_rtrancl_index_le hb1
    have hbq : b ≤ qj := nextrel0_rtrancl_index_le hb2
    have hgb : ¬ le1 M j0 b := by
      intro hc
      have := rtg1_entry1_lt hc.2.2 (Ne.symm hb3)
      omega
    rcases Nat.eq_or_lt_of_le hbq with hbeq | hblt
    · rw [if_neg hg] at hf
      rw [hbeq] at hb4
      omega
    · have hb0 : entry M 0 b < entry M 0 qj :=
        le0_interval_gt hb2 qj ⟨hblt, le_rfl⟩
      have hbvis : ∀ c', b < c' → c' < qj → entry M 0 b < entry M 0 c' :=
        fun c' h1 h2 => le0_interval_gt hb2 c' ⟨h1, by omega⟩
      have hh := hspcpy b hbj hblt hb0 hbvis
      rw [if_neg hgb] at hh
      omega
  have hzi1 : entry M 2 i = 1 :=
    mark_of_spine hM np2 hd0 hd1 hji hix hu hroot hA1blk hspblk
  rcases hzf with hfe | hz0
  · rw [if_pos hgj] at hfe
    rcases Nat.eq_or_lt_of_le hj0q with hqe | hqlt
    · rw [← hqe] at hzeq
      omega
    · have hkd : d1 ≤ k * d1 := Nat.le_mul_of_pos_left d1 (by omega)
      have := rtg1_entry1_lt hgj.2.2 (by omega : j0 ≠ qj)
      omega
  · omega

/-! ## bad_A2 の交差ケース (c) -/

/-- Positional form of the `A1` row-0 condition. -/
theorem argdom_A1_pos {N X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : N = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z)
    (h1 : ∀ x ∈ A1, u < x.1) :
    ∀ p, X.length < p → p < X.length + (A1.length + 1) → u < entry N 0 p := by
  have hN : N = X ++ ((u, w1, z)
      :: (A1 ++ ((u + e, w1 + f, z) :: ((B ++ A2) ++ Z)))) := by
    rw [heq]
    simp [List.append_assoc]
  intro p hp1 hp2
  obtain ⟨t, rfl⟩ : ∃ t, p = X.length + 1 + t := ⟨p - X.length - 1, by omega⟩
  have ht : t < A1.length := by omega
  have hget : N.getD (X.length + 1 + t) (0, 0, 0) = A1.getD t (0, 0, 0) := by
    rw [hN, getD_app_right _ _ (by omega),
      show X.length + 1 + t - X.length = t + 1 from by omega,
      List.getD_cons_succ, getD_append_left ht]
  show u < (N.getD (X.length + 1 + t) (0, 0, 0)).1
  rw [hget]
  exact h1 _ (getD_mem_of_lt ht)

theorem mul_ite_zero (c : Prop) [Decidable c] (k d : ℕ) :
    (if c then k * d else 0) = k * (if c then d else 0) := by
  split_ifs <;> simp

set_option maxHeartbeats 4000000 in
/-- **Case A2, inner branch**: in the straddling case the shallower marked
column is never *strictly inside* the block.  Probe: not one of the 73527 +
8606 + 6270 straddling instances has `j0 < ipos`. -/
theorem argDomCoreOn_bad_A2_inner {M : TrioSeq} (hM : ST_TS M)
    {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLbpos : 0 < Lb)
    (np2 : nextrel2 M j0 (j0 + Lb))
    (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hd1e : entry M 1 (j0 + Lb) = entry M 1 j0 + d1)
    {X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : gexp M j0 Lb d0 d1 n
      = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (hzf : f = 0 ∨ z = 0)
    (h1 : ∀ x ∈ A1, u < x.1) (h6 : SpineOK A1 (u + e) (w1 + 1))
    (hcaseL : X.length < j0 + Lb) (hj0i : j0 < X.length)
    (hcaseR : j0 + Lb ≤ X.length + (A1.length + 1)) :
    False := by
  classical
  obtain ⟨hpi, hpj, hjlt⟩ := argdom_pos heq
  have hTlen : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hjlt' : X.length + (A1.length + 1) < j0 + n * Lb := by
    rw [← hTlen]
    exact hjlt
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hmul : n * Lb ≤ 1 * Lb := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.one_mul] at hmul
    omega
  obtain ⟨k, q, hk, hq, hjeq⟩ := gexp_pos_decomp (j0 := j0) (Lb := Lb)
    (n := n) hLbpos (by omega) hjlt'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [Nat.zero_mul] at hjeq
      omega
    · exact h
  -- host readings
  have hagree : ∀ p, p < j0 + Lb →
      (gexp M j0 Lb d0 d1 n).getD p (0, 0, 0) = M.getD p (0, 0, 0) := by
    intro p hp
    rcases Nat.lt_or_ge p j0 with h | h
    · exact gexp_getD_low hlen h
    · have h2 := gexp_getD_mir (M := M) (d0 := d0) (d1 := d1) (n := n) hlen
        (k := 0) (q := p - j0) (by omega) (by omega)
      rw [Nat.zero_mul, Nat.zero_add, show j0 + (p - j0) = p from by omega] at h2
      rw [h2]
      simp only [Nat.zero_mul, ite_self, Nat.add_zero]
      rfl
  have hentry : ∀ r p, p < j0 + Lb →
      entry (gexp M j0 Lb d0 d1 n) r p = entry M r p := by
    intro r p hp
    unfold entry
    rw [hagree p hp]
  have hmir : ∀ c q', c < n → q' < Lb →
      (gexp M j0 Lb d0 d1 n).getD (j0 + (c * Lb + q')) (0, 0, 0)
        = (entry M 0 (j0 + q') + c * d0,
           entry M 1 (j0 + q') + (if le1 M j0 (j0 + q') then c * d1 else 0),
           entry M 2 (j0 + q')) :=
    fun c q' hc hq' => gexp_getD_mir hlen hc hq'
  have hvi : M.getD X.length (0, 0, 0) = (u, w1, z) := by
    rw [← hagree X.length hcaseL]
    exact hpi
  have hvj := hpj
  rw [hjeq, hmir k q hk hq] at hvj
  have hu0 : entry M 0 X.length = u := by
    show (M.getD X.length (0, 0, 0)).1 = u
    rw [hvi]
  have hu1 : entry M 1 X.length = w1 := by
    show (M.getD X.length (0, 0, 0)).2.1 = w1
    rw [hvi]
  have hu2 : entry M 2 X.length = z := by
    show (M.getD X.length (0, 0, 0)).2.2 = z
    rw [hvi]
  have hj0v : entry M 0 (j0 + q) + k * d0 = u + e := congrArg Prod.fst hvj
  have hj1v : entry M 1 (j0 + q)
      + (if le1 M j0 (j0 + q) then k * d1 else 0) = w1 + f :=
    congrArg (fun p => p.2.1) hvj
  have hj2v : entry M 2 (j0 + q) = z := congrArg (fun p => p.2.2) hvj
  -- host chain window
  have hch0 : Relation.ReflTransGen (nextrel0 M) j0 (j0 + Lb) :=
    rtg1_rtg0 np2.2.2.2.2.1.2.2
  have hwin0 : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l :=
    fun l ha hb => le0_interval_gt hch0 l ⟨ha, hb⟩
  have hd0pos : 0 < d0 := by
    have := hwin0 (j0 + Lb) (by omega) le_rfl
    omega
  have hqge : entry M 0 j0 ≤ entry M 0 (j0 + q) := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · rw [Nat.add_zero]
    · exact (hwin0 (j0 + q) (by omega) (by omega)).le
  have hkd0 : d0 ≤ k * d0 := Nat.le_mul_of_pos_left d0 (by omega)
  have hkLb : Lb ≤ k * Lb := Nat.le_mul_of_pos_left Lb (by omega)
  -- row 0 of positions at or above the copy level
  have hhigh : ∀ p', j0 + Lb ≤ p' → p' < j0 + n * Lb →
      entry M 0 j0 + d0 ≤ entry (gexp M j0 Lb d0 d1 n) 0 p' := by
    intro p' ha hb
    obtain ⟨c, q'', hc, hq'', hp'e⟩ := gexp_pos_decomp (j0 := j0) (Lb := Lb)
      (n := n) hLbpos (by omega) hb
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · rw [Nat.zero_mul] at hp'e
        omega
      · exact h
    have hcd : d0 ≤ c * d0 := Nat.le_mul_of_pos_left d0 (by omega)
    have hge : entry M 0 j0 ≤ entry M 0 (j0 + q'') := by
      rcases Nat.eq_zero_or_pos q'' with hz | hp
      · rw [hz, Nat.add_zero]
      · exact (hwin0 (j0 + q'') (by omega) (by omega)).le
    have hval : entry (gexp M j0 Lb d0 d1 n) 0 p'
        = entry M 0 (j0 + q'') + c * d0 := by
      show ((gexp M j0 Lb d0 d1 n).getD p' (0, 0, 0)).1 = _
      rw [hp'e, hmir c q'' hc hq'']
    omega
  -- the shallower column is below the copy level
  have hulow : entry M 0 X.length < entry M 0 j0 + d0 := by
    by_cases hjp : j0 + Lb < X.length + (A1.length + 1)
    · have hA1p := argdom_A1_pos heq h1 (j0 + Lb) (by omega) (by omega)
      have hval : entry (gexp M j0 Lb d0 d1 n) 0 (j0 + Lb)
          = entry M 0 j0 + d0 := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + Lb) (0, 0, 0)).1 = _
        have hh := hmir 1 0 (by omega) hLbpos
        simp only [Nat.one_mul, Nat.add_zero] at hh
        rw [hh]
      omega
    · have hkq : k * Lb + q = Lb := by omega
      have hk1' : k = 1 := by
        rcases Nat.lt_or_ge k 2 with h | h
        · omega
        · have : 2 * Lb ≤ k * Lb := Nat.mul_le_mul_right _ h
          omega
      have hq0 : q = 0 := by
        rw [hk1', Nat.one_mul] at hkq
        omega
      rw [hk1', hq0, Nat.one_mul, Nat.add_zero] at hj0v
      omega
  -- the block part of `A1`
  have hA1blk : ∀ l, X.length < l → l < j0 + Lb →
      entry M 0 X.length < entry M 0 l := by
    intro l ha hb
    have h := argdom_A1_pos heq h1 l ha (by omega)
    have he0 := hentry 0 l hb
    omega
  -- the spine on the block part
  have hspblk : ∀ p, X.length < p → p < j0 + Lb →
      entry M 0 p < entry M 0 (j0 + Lb) →
      (∀ p', p < p' → p' < j0 + Lb → entry M 0 p < entry M 0 p') →
      entry M 1 X.length ≤ entry M 1 p := by
    intro p ha hb hc hd
    have hep0 := hentry 0 p hb
    have hep1 := hentry 1 p hb
    have hlt : entry (gexp M j0 Lb d0 d1 n) 0 p < u + e := by
      rw [hep0]
      omega
    have hvis : ∀ p', p < p' → p' < X.length + (A1.length + 1) →
        entry (gexp M j0 Lb d0 d1 n) 0 p
          < entry (gexp M j0 Lb d0 d1 n) 0 p' := by
      intro p' h1' h2'
      rcases Nat.lt_or_ge p' (j0 + Lb) with hlow | hhi
      · have hep0' := hentry 0 p' hlow
        rw [hep0, hep0']
        exact hd p' h1' hlow
      · have := hhigh p' hhi (by omega)
        rw [hep0]
        omega
    have hsp := spineOK_pos heq h6 p ha (by omega) hlt hvis
    rw [hep1] at hsp
    omega
  -- the copy-1 root bounds row 1 from above
  have hj0len : j0 < M.length := np2.1
  have hroot : entry M 1 X.length ≤ entry M 1 j0 + d1 := by
    by_cases hjp : j0 + Lb < X.length + (A1.length + 1)
    · have hval := hmir 1 0 (by omega) hLbpos
      simp only [Nat.one_mul, Nat.add_zero, if_pos (le1_refl hj0len)] at hval
      have hep0 : entry (gexp M j0 Lb d0 d1 n) 0 (j0 + Lb)
          = entry M 0 j0 + d0 := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + Lb) (0, 0, 0)).1 = _
        rw [hval]
      have hep1 : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + Lb)
          = entry M 1 j0 + d1 := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + Lb) (0, 0, 0)).2.1 = _
        rw [hval]
      have hlt : entry (gexp M j0 Lb d0 d1 n) 0 (j0 + Lb) < u + e := by
        rw [hep0]
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have hkq : k = 1 := by omega
          have hqp : 0 < q := by
            rcases Nat.eq_zero_or_pos q with hz | hp
            · rw [hkq, Nat.one_mul, hz, Nat.add_zero] at hjeq
              omega
            · exact hp
          have := hwin0 (j0 + q) (by omega) (by omega)
          rw [hkq, Nat.one_mul] at hj0v
          omega
        · have : 2 * d0 ≤ k * d0 := Nat.mul_le_mul_right _ hk2
          omega
      have hvis : ∀ p', j0 + Lb < p' → p' < X.length + (A1.length + 1) →
          entry (gexp M j0 Lb d0 d1 n) 0 (j0 + Lb)
            < entry (gexp M j0 Lb d0 d1 n) 0 p' := by
        intro p' h1' h2'
        obtain ⟨c, q'', hc, hq'', hp'e⟩ := gexp_pos_decomp (j0 := j0) (Lb := Lb)
          (n := n) (p := p') hLbpos (by omega) (by omega)
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · rw [Nat.zero_mul] at hp'e
            omega
          · exact h
        have hval' : entry (gexp M j0 Lb d0 d1 n) 0 p'
            = entry M 0 (j0 + q'') + c * d0 := by
          show ((gexp M j0 Lb d0 d1 n).getD p' (0, 0, 0)).1 = _
          rw [hp'e, hmir c q'' hc hq'']
        rw [hep0, hval']
        rcases Nat.lt_or_ge c 2 with hc2 | hc2
        · have hce : c = 1 := by omega
          have hqp : 0 < q'' := by
            rcases Nat.eq_zero_or_pos q'' with hz | hp
            · rw [hce, Nat.one_mul, hz, Nat.add_zero] at hp'e
              omega
            · exact hp
          have := hwin0 (j0 + q'') (by omega) (by omega)
          rw [hce, Nat.one_mul]
          omega
        · have : 2 * d0 ≤ c * d0 := Nat.mul_le_mul_right _ hc2
          have hge : entry M 0 j0 ≤ entry M 0 (j0 + q'') := by
            rcases Nat.eq_zero_or_pos q'' with hz | hp
            · rw [hz, Nat.add_zero]
            · exact (hwin0 (j0 + q'') (by omega) (by omega)).le
          omega
      have hsp := spineOK_pos heq h6 (j0 + Lb) (by omega) (by omega) hlt hvis
      rw [hep1] at hsp
      omega
    · have hkq : k * Lb + q = Lb := by omega
      have hk1' : k = 1 := by
        rcases Nat.lt_or_ge k 2 with h | h
        · omega
        · have : 2 * Lb ≤ k * Lb := Nat.mul_le_mul_right _ h
          omega
      have hq0 : q = 0 := by
        rw [hk1', Nat.one_mul] at hkq
        omega
      rw [hk1', hq0, Nat.one_mul, Nat.add_zero,
        if_pos (le1_refl hj0len)] at hj1v
      omega
  -- the spine on the copy-`k` part
  have hspcpy : ∀ c, j0 ≤ c → c < j0 + q → entry M 0 c < entry M 0 (j0 + q) →
      (∀ c', c < c' → c' < j0 + q → entry M 0 c < entry M 0 c') →
      entry M 1 X.length ≤ entry M 1 c + k * (if le1 M j0 c then d1 else 0) := by
    intro c ha hb hc hd
    have hcq : c - j0 < Lb := by omega
    have hce : j0 + (c - j0) = c := by omega
    have hval := hmir k (c - j0) hk hcq
    rw [hce] at hval
    have hep0 : entry (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + (c - j0)))
        = entry M 0 c + k * d0 := by
      show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + (c - j0))) (0, 0, 0)).1
        = _
      rw [hval]
    have hep1 : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + (c - j0)))
        = entry M 1 c + (if le1 M j0 c then k * d1 else 0) := by
      show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + (c - j0))) (0, 0, 0)).2.1
        = _
      rw [hval]
    have hlt : entry (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + (c - j0)))
        < u + e := by
      rw [hep0]
      omega
    have hvis : ∀ p', j0 + (k * Lb + (c - j0)) < p' →
        p' < X.length + (A1.length + 1) →
        entry (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + (c - j0)))
          < entry (gexp M j0 Lb d0 d1 n) 0 p' := by
      intro p' h1' h2'
      obtain ⟨q'', hq''⟩ : ∃ q'', p' = j0 + (k * Lb + q'') ∧ q'' < Lb :=
        ⟨p' - j0 - k * Lb, by omega, by omega⟩
      have hep0' : entry (gexp M j0 Lb d0 d1 n) 0 p'
          = entry M 0 (j0 + q'') + k * d0 := by
        show ((gexp M j0 Lb d0 d1 n).getD p' (0, 0, 0)).1 = _
        rw [hq''.1, hmir k q'' hk hq''.2]
      have := hd (j0 + q'') (by omega) (by omega)
      rw [hep0, hep0']
      omega
    have hsp := spineOK_pos heq h6 (j0 + (k * Lb + (c - j0)))
      (by omega) (by omega) hlt hvis
    rw [hep1] at hsp
    rw [hu1, ← mul_ite_zero]
    omega
  have hfc : entry M 1 X.length
      ≤ entry M 1 (j0 + q) + k * (if le1 M j0 (j0 + q) then d1 else 0) := by
    rw [hu1, ← mul_ite_zero]
    omega
  refine cross_absurd hM np2 hd0e hd1e (i := X.length) (qj := j0 + q) (k := k)
    hj0i hcaseL (by omega) (by omega) hk1 hulow hroot hfc ?_ ?_
    hA1blk hspblk hspcpy
  · rw [hu2, hj2v]
  · rcases hzf with rfl | hz0
    · refine Or.inl ?_
      rw [hu1, ← mul_ite_zero]
      omega
    · exact Or.inr (by rw [hu2]; exact hz0)

/-! ## bad_A2 のブロック根整列ケース -/

theorem map_range'_getD (F : ℕ → ℕ × ℕ × ℕ) {a l t : ℕ} (ht : t < l) :
    ((List.range' a l).map F).getD t (0, 0, 0) = F (a + t) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using ht)]
  rw [Nat.one_mul]
  rfl

theorem list_eq_of_getD {A C : TrioSeq} (hlen : A.length = C.length)
    (h : ∀ t, t < A.length → A.getD t (0, 0, 0) = C.getD t (0, 0, 0)) : A = C := by
  refine List.ext_getElem hlen ?_
  intro t h1 h2
  have hh := h t h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hh
  simpa using hh

/-- Positional form of the argument segment. -/
theorem argdom_B_getD {N X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : N = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z) :
    ∀ t, t < B.length →
      N.getD (X.length + (A1.length + 1) + 1 + t) (0, 0, 0)
        = B.getD t (0, 0, 0) := by
  have hN : N = (X ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)]))
      ++ (B ++ (A2 ++ Z)) := by
    rw [heq]
    simp [List.append_assoc]
  have hPlen : (X ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)])).length
      = X.length + (A1.length + 1) + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  intro t ht
  rw [hN, getD_app_right _ _ (by rw [hPlen]; omega), hPlen,
    show X.length + (A1.length + 1) + 1 + t - (X.length + (A1.length + 1) + 1) = t
      from by omega, getD_append_left ht]

set_option maxHeartbeats 4000000 in
/-- **Case A2, aligned at the block root**: the shallower marked column is the
block root and the deeper one is the copy-1 root.  The tower is then
self-similar with period `Lb`, so the argument is literally an initial
segment of the comparator. -/
theorem argDomCoreOn_bad_A2_root {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLbpos : 0 < Lb)
    (hd0pos : 0 < d0) (hd1pos : 0 < d1)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hle1lp : le1 M j0 (j0 + Lb))
    {X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ}
    (heq : gexp M j0 Lb d0 d1 n
      = (X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1)
    (hipos : X.length = j0)
    (hjpos : X.length + (A1.length + 1) = j0 + Lb) :
    sle B (hshift w1 e f (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) := by
  classical
  subst hipos
  obtain ⟨hpi, hpj, hjlt⟩ := argdom_pos heq
  have hTlen : (gexp M X.length Lb d0 d1 n).length = X.length + n * Lb :=
    gexp_length hlen
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hmul : n * Lb ≤ 1 * Lb := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.one_mul] at hmul
    omega
  -- the two marked columns are the block root and the copy-1 root
  have hval_i : (gexp M X.length Lb d0 d1 n).getD X.length (0, 0, 0)
      = (entry M 0 X.length, entry M 1 X.length, entry M 2 X.length) := by
    have hh := gexp_getD_mir (M := M) (d0 := d0) (d1 := d1) (n := n) hlen
      (k := 0) (q := 0) (by omega) hLbpos
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, ite_self] at hh
    rw [hh]
  have hval_j : (gexp M X.length Lb d0 d1 n).getD (X.length + Lb) (0, 0, 0)
      = (entry M 0 X.length + d0, entry M 1 X.length + d1, entry M 2 X.length) := by
    have hh := gexp_getD_mir (M := M) (d0 := d0) (d1 := d1) (n := n) hlen
      (k := 1) (q := 0) (by omega) hLbpos
    simp only [Nat.one_mul, Nat.add_zero] at hh
    rw [hh, if_pos (le1_refl (by omega))]
  rw [hjpos] at hpj
  rw [hval_i] at hpi
  rw [hval_j] at hpj
  have hue : e = d0 := by
    have ha := congrArg Prod.fst hpi
    have hb := congrArg Prod.fst hpj
    simp only [] at ha hb
    omega
  have hwf : f = d1 := by
    have ha := congrArg (fun p => p.2.1) hpi
    have hb := congrArg (fun p => p.2.1) hpj
    simp only [] at ha hb
    omega
  -- the argument fits inside the tower
  have hBbound : X.length + (A1.length + 1) + 1 + B.length
      ≤ (gexp M X.length Lb d0 d1 n).length := by
    have hh := congrArg List.length heq
    simp only [List.length_append, List.length_cons] at hh
    omega
  rw [instance_bridge heq he h1 h2 h3]
  have hlensum : A1.length + (1 + (B.length + A2.length))
      = B.length + (A1.length + 1 + A2.length) := by omega
  rw [hlensum, ← List.range'_append_1, List.map_append]
  refine sle_append_mono (Or.inl ?_) _
  refine list_eq_of_getD (by rw [List.length_map, List.length_range']) ?_
  intro t ht
  rw [map_range'_getD _ ht, ← argdom_B_getD heq t ht]
  -- position bookkeeping
  have hple : X.length ≤ X.length + 1 + t := by omega
  have hplt : X.length + 1 + t < X.length + n * Lb := by omega
  obtain ⟨k, q, hk, hq, hpe⟩ := gexp_pos_decomp (j0 := X.length) (Lb := Lb) (n := n)
    hLbpos hple hplt
  have hposb : X.length + (A1.length + 1) + 1 + t < X.length + n * Lb := by
    rw [← hTlen]
    omega
  have hk1 : k + 1 < n := by
    by_contra hc
    have hmul : n * Lb ≤ (k + 1) * Lb := Nat.mul_le_mul_right _ (by omega)
    have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    rw [hjpos] at hposb
    omega
  have hshift : X.length + (A1.length + 1) + 1 + t
      = X.length + ((k + 1) * Lb + q) := by
    have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    rw [hjpos, hsm]
    omega
  have hlo := gexp_getD_mir (M := M) (d0 := d0) (d1 := d1) (n := n) hlen hk hq
  have hhi := gexp_getD_mir (M := M) (d0 := d0) (d1 := d1) (n := n) hlen hk1 hq
  have hguard := gexp_guard_transport (M := M) (d0 := d0) (d1 := d1) (n := n)
    hlen hk hq hup hd0pos hd0e hd1pos hle1lp
  rw [← hpe] at hlo hguard
  rw [← hshift] at hhi
  rw [hhi]
  have hg0 : entry (gexp M X.length Lb d0 d1 n) 0 (X.length + 1 + t)
      = entry M 0 (X.length + q) + k * d0 := by
    show ((gexp M X.length Lb d0 d1 n).getD (X.length + 1 + t) (0, 0, 0)).1 = _
    rw [hlo]
  have hg1 : entry (gexp M X.length Lb d0 d1 n) 1 (X.length + 1 + t)
      = entry M 1 (X.length + q) + (if le1 M X.length (X.length + q) then k * d1 else 0) := by
    show ((gexp M X.length Lb d0 d1 n).getD (X.length + 1 + t) (0, 0, 0)).2.1 = _
    rw [hlo]
  have hg2 : entry (gexp M X.length Lb d0 d1 n) 2 (X.length + 1 + t)
      = entry M 2 (X.length + q) := by
    show ((gexp M X.length Lb d0 d1 n).getD (X.length + 1 + t) (0, 0, 0)).2.2 = _
    rw [hlo]
  rw [hg0, hg1, hg2, hue, hwf]
  have hsm0 : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
  have hsm1 : (k + 1) * d1 = k * d1 + d1 := Nat.succ_mul k d1
  have h0 : entry M 0 (X.length + q) + (k + 1) * d0
      = entry M 0 (X.length + q) + k * d0 + d0 := by omega
  have h1' : entry M 1 (X.length + q) + (k + 1) * d1
      = entry M 1 (X.length + q) + k * d1 + d1 := by omega
  by_cases hgm : le1 M X.length (X.length + q)
  · have hg' := hguard.2 hgm
    simp only [if_pos hgm, if_pos hg']
    rw [h0, h1']
  · have hg' : ¬ le1 (gexp M X.length Lb d0 d1 n) X.length (X.length + 1 + t) :=
      fun hc => hgm (hguard.1 hc)
    simp only [if_neg hgm, if_neg hg', Nat.add_zero]
    rw [h0]

end TRIO
