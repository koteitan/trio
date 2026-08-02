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

/-! ## bad_B: ホスト検証（key） -/

/-- **The host's verdict, map form**: for any admissible resplit of the
host tail, the argument is dominated by the host-anchored map over the
instance prefix. -/
theorem bad_B_key {M P A1 D : TrioSeq} {u w1 z e f : ℕ} {lp : ℕ × ℕ × ℕ}
    (hMon : ArgDomCoreOn M)
    (hMeq : M = (P ++ (u, w1, z) :: (A1 ++ [(u + e, w1 + f, z)])) ++ (D ++ [lp]))
    (he : 0 < e) (hzf : f = 0 ∨ z = 0)
    (h1 : ∀ x ∈ A1, u < x.1) (h6 : SpineOK A1 (u + e) w1)
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
    (h5 : Z = [] ∨ (Z.headI).1 ≤ u) (h6 : SpineOK A1 (u + e) w1)
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

end TRIO
