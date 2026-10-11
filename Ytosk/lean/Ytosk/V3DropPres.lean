/-
**値の不変条件は 1 列落とし M → M.take x で保たれる**（落とす補題 `drop_all` の結論 PO・PV から）。

M.take x の枠は、変わらないデータだけを使う:
- 数える子を持つ列の v は変わらない（TopC）。最後の数える子より前の数える子の o は変わらない（`chg_last`）。
- 行 2 が 0 でない列の子は、最後の子の部分木の中しか変わらない（`chg_only_last`、のりしろの子も行 2 は 1）。
これから Good3・VSmallF（VSmallNew とあわせて）・FrameOT・FrameClosed・BumpKidsDec・BumpTermDec が保たれる（`ValInv`）。
SRO から到達する行列で偽になる大域の形（VSmall・BumpWeakShape・BumpAbs・UpgAbs）は不変条件に入れず、落とす補題が
実際に使う形を各段の仮定にする（`DropRes`: argT・VSmallNew・BumpWeakSrc・UpgAbsX・BumpAbsC）。
まとめ: 残りの仮定 `DropRes` だけで述べた n = 0（`t1_n0r`）。
-/
import Ytosk.V3InvTake2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 和の単調性（続き） -/

theorem le_foldl_sf : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, isOT t = true) →
    acc ≤ l.foldl (fun a b => sf (add a b)) acc
  | [], _, _, _ => le_refl _
  | t :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    have ht := hl t List.mem_cons_self
    have hot : isOT (add acc t) = true := isOT_add h ht
    rw [sf_ot hot]
    have h1 : acc ≤ add acc t := by
      have := add_le_add_left acc (z_le t); rwa [add_z_right] at this
    exact le_trans h1 (le_foldl_sf l _ hot (fun u hu => hl u (List.mem_cons_of_mem _ hu)))

/-- Appending summands does not lower the sum. -/
theorem le_sumN_append (l m : List T) (hl : ∀ t ∈ l, isOT t = true) (hm : ∀ t ∈ m, isOT t = true) :
    sumN l ≤ sumN (l ++ m) := by
  unfold sumN
  rw [List.foldl_append]
  exact le_foldl_sf m _ (isOT_sumN l hl) hm

theorem omega_le_omega {X Y : T} (hX : isOT X = true) (hY : isOT Y = true) (h : X ≤ Y) :
    omega X ≤ omega Y := by
  rcases (le_iff _ _).mp h with h | h
  · exact le_of_lt (omega_lt_omega hX hY h)
  · rw [h]

theorem cvals_eq_map' {N : Mat} {σ : Valn} (i : Nat) (h : ∀ c ∈ children N i, σ.o c ≠ z) :
    cvals N σ i = (CL N i).map σ.o := by
  classical
  unfold cvals CL
  have : (children N i).map (cnt N σ i) =
      (children N i).map (fun c => if Counted N i c then σ.o c else z) := by
    apply List.map_congr_left; intro c _; exact cnt_eq_ite N σ i c
  rw [this]
  apply nzs_map_ite
  intro c hc _
  exact h c hc

theorem lenT {M : Mat} {x : Nat} (hx : x + 1 = M.length) : (M.take x).length = x := by
  rw [List.length_take]; omega

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

omit hdrop in
/-- A column with a counted child in `M.take x` keeps its `v`. -/
theorem v_same_of_cnt {i c : Nat} (hi : i < x) (hc : c ∈ children (M.take x) i)
    (hcnt : Counted (M.take x) i c) : ρ'.v i = ρ.v i := by
  apply (chg_off hx hC hG hC' hRk' i hi).2
  intro h
  exact ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB h).1 rfl hi).2.1 c hc hcnt

omit hdrop in
/-- A counted child of `M.take x` before another counted child keeps its `o`. -/
theorem o_same_before_cnt {i d c : Nat} (hd : d ∈ children (M.take x) i) (hc : c ∈ children (M.take x) i)
    (hdc : d < c) (hcnt : Counted (M.take x) i c) : ρ'.o d = ρ.o d := by
  have hdx : d < x := by have := (mem_children hd).2; rw [lenT hx] at this; exact this
  apply (chg_off hx hC hG hC' hRk' d hdx).1
  intro hCd
  exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hd hCd c hc hdc hcnt

omit hdrop in
/-- Under a column with row 2 nonzero, a child of `M.take x` before another keeps its `o`. -/
theorem o_same_before_e2 {p d d' : Nat} (h2 : entry M 2 p ≠ 0) (hd : d ∈ children (M.take x) p)
    (hd' : d' ∈ children (M.take x) p) (hdd : d < d') : ρ'.o d = ρ.o d := by
  have hdM : d ∈ children M p := by rw [children_take, List.mem_filter] at hd; exact hd.1
  have hdx : d < x := by have := (mem_children hd).2; rw [lenT hx] at this; exact this
  apply (chg_off hx hC hG hC' hRk' d hdx).1
  intro hCd
  exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hdM hd' hdd hCd (Anc0.refl d)

omit hdrop in
/-- Under a column with row 2 nonzero, nothing changes below a child of `M.take x` before another. -/
theorem below_same_e2 {p d d' e : Nat} (h2 : entry M 2 p ≠ 0) (hd : d ∈ children (M.take x) p)
    (hd' : d' ∈ children (M.take x) p) (hdd : d < d') (hde : Anc0 M d e) (he : e < x) :
    ρ'.o e = ρ.o e := by
  have hdM : d ∈ children M p := by rw [children_take, List.mem_filter] at hd; exact hd.1
  apply (chg_off hx hC hG hC' hRk' e he).1
  intro hCe
  exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hdM hd' hdd hCe hde

/-! ## Good3 -/

theorem cl_take_vals {i : Nat} (hi : i < x) :
    (∀ c ∈ CL (M.take x) i, Single (ρ'.o c)) ∧
    ((CL (M.take x) i).map ρ'.o).Pairwise (fun a b => b ≤ a) := by
  have hiM : i < M.length := by omega
  refine ⟨fun c hc => (hdrop c (by
    have := (mem_children (cl_mem_children hc)).2; rw [lenT hx] at this; exact this)).1.2, ?_⟩
  obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hi
  rcases List.eq_nil_or_concat (CL (M.take x) i) with hnil | ⟨Lc, cs, hcl⟩
  · rw [hnil]; exact List.Pairwise.nil
  rw [List.concat_eq_append] at hcl
  have hcsT : cs ∈ children (M.take x) i ∧ Counted (M.take x) i cs := by
    have : cs ∈ CL (M.take x) i := by rw [hcl]; simp
    unfold CL at this; rw [List.mem_filter] at this; exact ⟨this.1, by simpa using this.2⟩
  have hcsx : cs < x := by have := (mem_children hcsT.1).2; rw [lenT hx] at this; exact this
  have hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d := by
    intro d hd
    have hdT : d ∈ CL (M.take x) i := by rw [hcl]; simp [hd]
    have hdcs : d < cs := by
      have hs := cl_sorted (M.take x) i
      rw [hcl] at hs
      exact (List.pairwise_append.mp hs).2.2 d hd cs (by simp)
    exact o_same_before_cnt hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' (cl_mem_children hdT)
      hcsT.1 hdcs hcsT.2
  obtain ⟨_, hpM⟩ := cl_vals hC hG hiM
  rw [hTl, hcl] at hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hpM
  have hp1 := List.pairwise_append.mp hpM
  have hpL := (List.pairwise_append.mp hp1.1)
  rw [hcl, List.map_append, List.map_singleton, List.map_congr_left hsame]
  exact List.pairwise_append.mpr ⟨hpL.1, by simp, fun t ht b hb => by
    simp at hb; rw [hb]; exact le_trans (hdrop cs hcsx).1.le (hpL.2.2 t ht _ (by simp))⟩

/-- **Good3 passes to `M.take x`.** -/
theorem good3_take : Good3 (M.take x) ρ' where
  ot_o := fun i hi => (hdrop i (by rw [lenT hx] at hi; exact hi)).1.2.1
  ot_v := fun i hi => (hdrop i (by rw [lenT hx] at hi; exact hi)).2.2
  dec := by
    intro i hi
    rw [lenT hx] at hi
    rw [cvals_eq_map' i (fun c hc => single_ne_z (hdrop c (by
      have := (mem_children hc).2; rw [lenT hx] at this; exact this)).1.2)]
    exact (cl_take_vals hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi).2

/-! ## FrameOT・FrameClosed -/

omit hdrop in
/-- The frames of `M.take x`: `v` and the earlier counted values are those of `M`, and the frame
extends to one of `M`. -/
theorem frame_take {i : Nat} (hi : i < x) {L : List Nat} {c : Nat} {R : List Nat}
    (h : CL (M.take x) i = L ++ c :: R) :
    ρ'.v i = ρ.v i ∧ L.map ρ'.o = L.map ρ.o ∧ ∃ Tl, CL M i = L ++ c :: (R ++ Tl) := by
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcc := cl_mem_children hcT
  have hcnt : Counted (M.take x) i c := by unfold CL at hcT; simpa using (List.mem_filter.mp hcT).2
  refine ⟨v_same_of_cnt hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi hcc hcnt, ?_, ?_⟩
  · apply List.map_congr_left
    intro d hd
    have hdT : d ∈ CL (M.take x) i := by rw [h]; simp [hd]
    have hdc : d < c := by
      have hs := cl_sorted (M.take x) i
      rw [h] at hs
      exact (List.pairwise_append.mp hs).2.2 d hd c (by simp)
    exact o_same_before_cnt hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' (cl_mem_children hdT) hcc hdc hcnt
  · obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hi
    exact ⟨Tl, by rw [hTl, h]; simp⟩

omit hdrop in
/-- **FrameOT passes to `M.take x`.** -/
theorem frameOT_take (hFO : FrameOT M ρ) : FrameOT (M.take x) ρ' := by
  intro i hi L c R h
  rw [lenT hx] at hi
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  rw [hv, hL]
  exact hFO i (by omega) L c (R ++ Tl) hM

/-- **A rewrite in `M.take x` is a rewrite in `M`** (the child drops by `◁`, or has argument `0` and
cannot rewrite; a rewriting new child keeps its `v`). -/
theorem rewrite_take {i : Nat} (hi : i < x) {L : List Nat} {c : Nat} {R : List Nat}
    (h : CL (M.take x) i = L ++ c :: R) {s' y' : T} (hc' : ρ'.o c = psi s' y' z)
    (ht' : lt (spArg (ρ.v i) z (sumN (L.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true)
    {s y : T} (hsy : ρ.o c = psi s y z) :
    lt (spArg (ρ.v i) z (sumN (L.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true := by
  have hiM : i < M.length := by omega
  obtain ⟨_, _, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcx : c < x := by have := (mem_children (cl_mem_children hcT)).2; rw [lenT hx] at this; exact this
  set a := ρ.v i
  set B := spArg a z (sumN (L.map ρ.o)) with hB
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  rw [hM] at hsM hpM
  -- the rewrite in `M`
  by_cases heq : ρ'.o c = ρ.o c
  · rw [heq, hsy] at hc'; simp only [psi.injEq] at hc'; obtain ⟨rfl, rfl, -⟩ := hc'; exact ht'
  have hPO := (hdrop c hcx).1
  have hlt : psi s' y' z < psi s y z := by
    rw [← hc', ← hsy]; exact lt_of_le_of_ne hPO.le heq
  have hsL : ∀ t ∈ L.map ρ.o, Single t := fun t ht => hsM t (by
    rw [List.map_append]; exact List.mem_append_left _ ht)
  have hpL : (L.map ρ.o).Pairwise (fun a b => b ≤ a) := by
    simp only [List.map_append, List.map_cons] at hpM
    exact (List.pairwise_append.mp hpM).1
  have hLc : ∀ t ∈ L.map ρ.o, ρ.o c ≤ t := by
    simp only [List.map_append, List.map_cons] at hpM
    intro t ht; exact (List.pairwise_append.mp hpM).2.2 t ht _ List.mem_cons_self
  have hLs := sumN_dec _ hsL hpL
  have hBc : ∀ q ∈ summands B, psi s y z ≤ q := by
    intro q hq
    apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN (L.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hsy]; exact hLc q hq
    · simp [summands]
    · exact hq
  rcases hPO.1 with hl | ⟨⟨w', w, X, hw', _, _⟩, _⟩
  · rcases hl with he | hl
    · exact absurd he heq
    rw [hc', hsy] at hl
    refine ⟨?_, lt_trans ht'.2 hlt⟩
    rcases psi_lt_psi_z_iff.mp hlt with hss | ⟨rfl, hyy⟩
    · -- a rewriting new child keeps its `v`, so the subscripts are equal
      exfalso
      have hvs := new_rewrite_same_v hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc'
        (ne_z_of_lt ht'.1)
      obtain ⟨y0, hy0⟩ := o_psi_sub hC' (show c < (M.take x).length by rw [lenT hx]; exact hcx)
      rw [hc'] at hy0; simp only [psi.injEq] at hy0
      obtain ⟨y1, hy1⟩ := o_psi_sub hC (show c < M.length by omega)
      rw [hsy] at hy1; simp only [psi.injEq] at hy1
      rw [hy0.1, hy1.1, hvs] at hss
      exact lt_irrefl' _ hss
    · exact lt_trans ht'.1 hyy
  · exfalso
    rw [hc'] at hw'; simp only [psi.injEq] at hw'
    have := ht'.1; rw [hw'.2.1] at this; exact T.not_lt_z _ this

/-- **FrameClosed passes to `M.take x`**: a rewriting new child has the same subscript and a smaller
argument, so its frame is that of `M` with a smaller `H`. -/
theorem frameClosed_take (hF : FrameClosed M ρ) : FrameClosed (M.take x) ρ' := by
  intro i hi L c R h s' y' hc' ht'
  rw [lenT hx] at hi
  have hiM : i < M.length := by omega
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  rw [hv, hL] at ht' ⊢
  obtain ⟨hsM, _⟩ := cl_vals hC hG hiM
  rw [hM] at hsM
  obtain ⟨s, y, hsy⟩ := (hsM (ρ.o c) (by simp)).2
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcx : c < x := by have := (mem_children (cl_mem_children hcT)).2; rw [lenT hx] at this; exact this
  have hD := hF i hiM L c (R ++ Tl) hM s y hsy
    (rewrite_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi h hc' ht' hsy)
  -- the same subscript
  have hvs := new_rewrite_same_v hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc'
    (ne_z_of_lt ht'.1)
  obtain ⟨y0, hy0⟩ := o_psi_sub hC' (show c < (M.take x).length by rw [lenT hx]; exact hcx)
  rw [hc'] at hy0; simp only [psi.injEq] at hy0
  obtain ⟨y1, hy1⟩ := o_psi_sub hC (show c < M.length by omega)
  rw [hsy] at hy1; simp only [psi.injEq] at hy1
  have hss : s' = s := by rw [hy0.1, hy1.1, hvs]
  subst hss
  have hle : psi s' y' z ≤ psi s' y z := by
    rw [← hc', ← hsy]
    exact DRelOA.le ((hdrop c hcx).1.1.elim (fun h => Or.inl h) (fun h => Or.inr h.1))
  have hyy : y' ≤ y := by
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  have hc1 : isOT (psi s' y' z) = true := by rw [← hc']; exact (hdrop c hcx).1.2.1
  have hc2 : isOT (psi s' y z) = true := by rw [← hsy]; exact hG.ot_o c (by omega)
  exact FrameDom.mono hD (H_mono hc1 hc2 hyy)

/-- **VSmallF passes to `M.take x`**, given the new subscripts of the drop (`VSmallNew`). -/
theorem vsmallF_take (hVF : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') : VSmallF (M.take x) ρ' := by
  intro i hi L c R h
  rw [lenT hx] at hi
  have hiM : i < M.length := by omega
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  have hfr := hVF i hiM L c (R ++ Tl) hM
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcc := cl_mem_children hcT
  have hcx : c < x := by have := (mem_children hcc).2; rw [lenT hx] at this; exact this
  rw [hv, hL]
  by_cases hvc : ρ'.v c = ρ.v c
  · rw [hvc]; exact hfr
  · -- `c` changes, so it is the last counted child
    have hR : R = [] := by
      rcases R with _ | ⟨d, R'⟩
      · rfl
      · exfalso
        have hdT : d ∈ CL (M.take x) i := by rw [h]; simp
        have hcd : c < d := by
          have hs := cl_sorted (M.take x) i
          rw [h] at hs
          exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 d (by simp)
        have hCc : ChgX M x true c := by
          apply ChgX.ov; by_contra hn; exact hvc ((chg_off hx hC hG hC' hRk' c hcx).2 hn)
        exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hcc hCc d (cl_mem_children hdT) hcd
          (by unfold CL at hdT; simpa using (List.mem_filter.mp hdT).2)
    subst hR
    exact hVN i hi L c h hvc

/-! ## のりしろの枠 -/

omit hdrop in
theorem lt_of_e1_take {i : Nat} (h1 : entry (M.take x) 1 i ≠ 0) : i < x := by
  by_contra h
  exact h1 (entry_out' (by rw [lenT hx]; omega) 1)

omit hdrop in
/-- The row-1 parent's `v` does not change. -/
theorem vOpt_take {i : Nat} (hi : i < x) : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
  rw [par_take M 1 i hi]
  cases hp : par M 1 i with
  | none => rfl
  | some m =>
    show ρ'.v m = ρ.v m
    have hm := par_lt M 1 i m hp
    apply (chg_off hx hC hG hC' hRk' m (by omega)).2
    intro hCm
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp

/-- The sum of the children's values drops weakly. -/
theorem sum_children_take_le (j : Nat) :
    sumN ((children (M.take x) j).map ρ'.o) ≤ sumN ((children M j).map ρ.o) := by
  have hfx : ∀ d ∈ (children M j).filter (fun d => decide (d < x)), d < x := by
    intro d hd; rw [List.mem_filter] at hd; simpa using hd.2
  have hot' : ∀ t ∈ ((children M j).filter (fun d => decide (d < x))).map ρ'.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact (hdrop d (hfx d hd)).1.2.1
  have hot : ∀ t ∈ (children M j).map ρ.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o d (mem_children hd).2
  have hle : sumN (((children M j).filter (fun d => decide (d < x))).map ρ'.o) ≤
      sumN (((children M j).filter (fun d => decide (d < x))).map ρ.o) :=
    sumN_le2 (forall2_map_le (fun d hd => (hdrop d (hfx d hd)).1.le)) hot'
      (fun t ht => hot t (by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
        exact List.mem_map_of_mem (List.mem_filter.mp hd).1))
  rw [children_take]
  by_cases hxj : x ∈ children M j
  · apply le_trans hle
    conv_rhs => rw [children_split_x hx hxj, List.map_append]
    apply le_sumN_append
    · intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
      exact hG.ot_o d (mem_children (List.mem_filter.mp hd).1).2
    · intro t ht; simp at ht; rw [ht]; exact hG.ot_o x (by omega)
  · rw [children_filter_x hx hxj] at hle ⊢; exact hle

/-- **A bump term drops weakly.** -/
theorem bumpTerm_take_le {i j : Nat} (hi : i < x) (hj : j ∈ children (M.take x) i) :
    bumpTerm (M.take x) ρ' i j ≤ bumpTerm M ρ i j := by
  have hjx : j < x := by have := (mem_children hj).2; rw [lenT hx] at this; exact this
  unfold bumpTerm
  rw [col_take M hjx, bump_take M hi]
  split
  · apply omega_le_omega _ _ (sum_children_take_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop j)
    · exact isOT_sumN _ (fun t ht => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
        exact (hdrop d (by have := (mem_children hd).2; rw [lenT hx] at this; exact this)).1.2.1)
    · exact isOT_sumN _ (fun t ht => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o d (mem_children hd).2)
  · exact le_refl _

/-- **The bump term `ω^p` drops weakly.** -/
theorem bumpW_take_le {i : Nat} (hi : i < x) : bumpW (M.take x) ρ' i ≤ bumpW M ρ i := by
  have hG' := good3_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop
  unfold bumpW
  have hotT : ∀ t ∈ one :: (children (M.take x) i).map (bumpTerm (M.take x) ρ' i), isOT t = true := by
    intro t ht; rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG' i d
  have hotM : ∀ l : List Nat, ∀ t ∈ one :: l.map (bumpTerm M ρ i), isOT t = true := by
    intro l t ht; rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  apply omega_le_omega (isOT_sumN _ hotT) (isOT_sumN _ (hotM _))
  have hle : sumN (one :: (children (M.take x) i).map (bumpTerm (M.take x) ρ' i)) ≤
      sumN (one :: (children (M.take x) i).map (bumpTerm M ρ i)) :=
    sumN_le2 (.cons (le_refl _) (forall2_map_le (fun j hj =>
      bumpTerm_take_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi hj))) hotT (hotM _)
  apply le_trans hle
  rw [children_take]
  by_cases hxi : x ∈ children M i
  · conv_rhs => rw [children_split_x hx hxi, List.map_append, ← List.cons_append]
    exact le_sumN_append _ _ (hotM _) (fun t ht => by simp at ht; rw [ht]; exact isOT_bumpTerm hG i x)
  · rw [children_filter_x hx hxi]

/-- **BumpKidsDec passes to `M.take x`.** -/
theorem bumpKidsDec_take (hKD : BumpKidsDec M ρ) : BumpKidsDec (M.take x) ρ' := by
  intro i h1 h2 j hj hjb
  have hi := lt_of_e1_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' h1
  rw [entry_take M 1 hi] at h1
  rw [entry_take M 2 hi] at h2
  have hjM : j ∈ children M i := by rw [children_take, List.mem_filter] at hj; exact hj.1
  have hjx : j < x := by have := (mem_children hj).2; rw [lenT hx] at this; exact this
  rw [col_take M hjx, bump_take M hi] at hjb
  have hj2 : entry M 2 j ≠ 0 := by
    have : entry M 2 j = (col M j).2.2 := rfl
    rw [this, hjb]; simp [bump]
  have hP : (children (M.take x) j).Pairwise (fun d1 d2 => ρ.o d2 ≤ ρ.o d1) := by
    have := List.pairwise_map.mp (hKD i h1 h2 j hjM hjb)
    rw [children_take]; exact this.sublist (List.filter_sublist)
  apply List.pairwise_map.mpr
  refine ((hP.and (children_sorted (M.take x) j))).imp_of_mem ?_
  intro d1 d2 hd1 hd2 ⟨hle, hlt⟩
  have hd2x : d2 < x := by have := (mem_children hd2).2; rw [lenT hx] at this; exact this
  rw [o_same_before_e2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hj2 hd1 hd2 hlt]
  exact le_trans (hdrop d2 hd2x).1.le hle

/-- **BumpTermDec passes to `M.take x`.** -/
theorem bumpTermDec_take (hTD : BumpTermDec M ρ) : BumpTermDec (M.take x) ρ' := by
  intro i h1 h2
  have hi := lt_of_e1_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' h1
  rw [entry_take M 1 hi] at h1
  rw [entry_take M 2 hi] at h2
  have hP : (children (M.take x) i).Pairwise (fun j1 j2 => bumpTerm M ρ i j1 ≠ z →
      bumpTerm M ρ i j2 ≠ z → bumpTerm M ρ i j2 ≤ bumpTerm M ρ i j1) := by
    have := hTD i h1 h2
    unfold nzs at this
    rw [List.pairwise_filter, List.pairwise_map] at this
    rw [children_take]
    exact (this.sublist (List.filter_sublist)).imp (fun h a b => h (by simpa using a) (by simpa using b))
  unfold nzs
  rw [List.pairwise_filter, List.pairwise_map]
  refine ((hP.and (children_sorted (M.take x) i))).imp_of_mem ?_
  intro j1 j2 hj1 hj2 ⟨hle, hlt⟩ hz1 hz2
  have hz1' : bumpTerm (M.take x) ρ' i j1 ≠ z := by simpa using hz1
  have hz2' : bumpTerm (M.take x) ρ' i j2 ≠ z := by simpa using hz2
  have hj1x : j1 < x := by have := (mem_children hj1).2; rw [lenT hx] at this; exact this
  -- the earlier bump term does not change
  have he1 : bumpTerm (M.take x) ρ' i j1 = bumpTerm M ρ i j1 := by
    have hj2x : j2 < x := by have := (mem_children hj2).2; rw [lenT hx] at this; exact this
    have hpj2 : par M 0 j2 = some i := by
      rw [children_take, List.mem_filter] at hj2; exact (mem_children_iff.mp hj2.1).2
    have hpj1 : par M 0 j1 = some i := by
      rw [children_take, List.mem_filter] at hj1; exact (mem_children_iff.mp hj1.1).2
    have hkx : ∀ k ∈ children M j1, k < j2 := by
      intro k hk
      by_contra hkj
      have hA : Anc0 M j1 k := Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j1)
      have h1' := anc_between hA j2 (by omega) (by omega)
      have := (anc0_par h1' (by omega) hpj2).le
      have := par_lt M 0 j1 i hpj1; omega
    unfold bumpTerm
    rw [col_take M hj1x, bump_take M hi]
    split
    · have hch : children (M.take x) j1 = children M j1 := by
        rw [children_take, List.filter_eq_self]
        intro k hk; simp only [decide_eq_true_eq]; have := hkx k hk; omega
      rw [hch]
      congr 2
      apply List.map_congr_left
      intro k hk
      exact below_same_e2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' h2 hj1 hj2 hlt
        (Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j1)) (by have := hkx k hk; omega)
    · rfl
  have hle2 := bumpTerm_take_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi hj2
  have hz2M : bumpTerm M ρ i j2 ≠ z := by
    intro h; rw [h] at hle2; exact hz2' (le_antisymm hle2 (z_le _))
  rw [he1] at hz1' ⊢
  exact le_trans hle2 (hle hz1' hz2M)

/-- **BumpAbs passes to `M.take x`.** -/
theorem bumpAbs_take (hAbs : BumpAbs M ρ) : BumpAbs (M.take x) ρ' := by
  intro i h1 h2 r hr hr2 hrW
  have hi := lt_of_e1_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' h1
  rw [entry_take M 1 hi] at h1
  rw [entry_take M 2 hi] at h2
  rw [vOpt_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi] at hr
  have hW := bumpW_take_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi
  exact lhd_restrict (hAbs i h1 h2 r hr hr2 (lt_of_lt_of_le hrW hW)) hrW hW

/-- **UpgAbs passes to `M.take x`.** -/
theorem upgAbs_take (hUA : UpgAbs M ρ) : UpgAbs (M.take x) ρ' := by
  intro i k W hu hv hWz r hr hrW
  obtain ⟨hix, hu'⟩ := upg_of_take hu
  have hi : i < x := by omega
  rw [vOpt_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi] at hv hr
  obtain ⟨m, hm1, hm2, hcol, hcase⟩ := upg_spec hu'
  have hkx : k < x := by
    rcases hcase with h | ⟨_, h⟩
    · omega
    · omega
  have hkM : k < M.length := by omega
  by_cases hk : ρ'.v k = ρ.v k
  · rw [hk] at hv
    exact hUA i k W hu' hv hWz r hr hrW
  · have hk1 : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact (upg_e12 hu').1
    have hk2 : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
    have hVk : vOpt ρ (par M 1 k) = vOpt ρ (par M 1 i) := by rw [hm1, hm2]
    have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
      rw [hm1]; exact hG.ot_v m (by have := par_lt M 1 i m hm1; omega)
    obtain ⟨sW, yW, hvk, hWot, _⟩ := v_bump_form hC hkM hk1 hk2 (by rw [hVk]; exact hVot)
      (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
    rw [hVk] at hvk
    have hWle : W ≤ psi sW yW z := by
      by_contra hlt
      have hlt' : psi sW yW z < W := lt_of_not_ge hlt
      have := add_lt_add_left (vOpt ρ (par M 1 i)) hlt'
      rw [← hvk, ← hv] at this
      exact absurd (hdrop k hkx).2.le (not_le.mpr this)
    exact lhd_restrict (hUA i k _ hu' hvk (by simp) r hr (lt_of_lt_of_le hrW hWle)) hrW hWle

end

/-! ## 保存の定理と鎖 -/

/-- The value invariants carried along the drops. -/
structure ValInv (N : Mat) (σ : Valn) : Prop where
  g : Good3 N σ
  vs : VSmallF N σ
  fc : FrameClosed N σ
  fo : FrameOT N σ
  kd : BumpKidsDec N σ
  td : BumpTermDec N σ

/-- The remaining hypotheses of one drop (in the forms the drop lemma uses): the frame-argument condition,
the smallness of the changed subscripts, the shape of the weak sources that occur, the absorption at
`x − 1`, and the bump absorption outside the collapse. -/
structure DropRes (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  argT : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (N.take x) i = Lc ++ [cs] →
    ∀ s y, σ'.o cs = psi s y z → ¬ lt s (σ.v i) = true →
    ∀ g ∈ comps (σ.v i) y, g ≤ step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y z
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrc N x σ σ'
  ua : UpgAbsX N x σ
  ab : BumpAbsC N x σ

theorem DropHypV.of {N : Mat} {x : Nat} {σ σ' : Valn} (hI : ValInv N σ) (hD : DropRes N x σ σ') :
    DropHypV N x σ σ' :=
  ⟨hI.g, hI.vs, hI.fc, hI.fo, hD.argT, hI.kd, hI.td, hD.ab, hD.ws, hD.vst, hD.ua⟩

/-- **The value invariants pass to `N.take x`** (given the remaining hypotheses of the drop). -/
theorem drop_pres {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hD : DropRes N x σ σ')
    (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) : ValInv (N.take x) σ' := by
  have hdrop := drop_all hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.vs hD.vst hI.fc hI.fo hD.argT
    (bump_drop hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.kd hI.td hD.ab hD.ws)
    hD.ua
  exact ⟨good3_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop,
    vsmallF_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop hI.vs hD.vst,
    frameClosed_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop hI.fc,
    frameOT_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.fo,
    bumpKidsDec_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop hI.kd,
    bumpTermDec_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop hI.td⟩

/-- **`t = 1`, `q ≠ r`, `n = 0`**, with only the remaining hypotheses `DropRes` of the drops
`M.take (j + 1) → M.take j` (`r ≤ j < x`) and the new weak sources of the first drop `M → M.take x`;
the value invariants of the prefixes come from those of `M`. -/
theorem t1_n0r {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {ζ μ : T} (hVL : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ ζ μ i)
    (hres : ∀ j, r ≤ j → j < r + L →
      DropRes (M.take (j + 1)) j (drop1 M (j + 1) rkM) (drop1 M j rkM)) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 0) ρN ∧ Rk (TRIO.gexp M r L d0 0 0) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 0) ρN) = true ∧ root (TRIO.gexp M r L d0 0 0) ρN < root M ρ := by
  have hlj : ∀ j, j ≤ r + L → (M.take (j + 1)).length = j + 1 := by
    intro j hj; rw [List.length_take]; omega
  have hUATt := fun k => UAT_take hR0 hZ2 hSD hZ1 hUAB k
  -- the ranking of every prefix
  have hRkj : ∀ m j, r + L - j ≤ m → j ≤ r + L → Rk (M.take j) rkM := by
    intro m
    induction m with
    | zero =>
      intro j hm hj
      have hjx : j = r + L := by omega
      subst hjx
      exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
    | succ m ih =>
      intro j hm hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
      · have hN := ih (j + 1) (by omega) hjx
        have hcnt := counted_take_last (M := M.take (j + 1)) (by rw [hlj j (by omega)]; omega)
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
        rw [hlj j (by omega), show j + 1 - 1 = j by omega] at hcnt
        have := rk_take (by rw [hlj j (by omega)]; omega) hN hcnt
        rwa [take_take_succ] at this
  have hRk : ∀ j, j ≤ r + L → Rk (M.take j) rkM := fun j h => hRkj _ j (le_refl _) h
  have hCj : ∀ j, j ≤ r + L → Cons (M.take j) (drop1 M j rkM) := fun j h => cons_of_rk (hRk j h)
  -- the invariants of `M.take x`
  have hIx : ValInv (M.take (r + L)) (drop1 M (r + L) rkM) :=
    drop_pres (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC ⟨hG, hVS, hF, hFO, hKD, hTD⟩
      ⟨hArgT, hVSt, hWS, hUA, hAbs⟩ (hCj _ (le_refl _)) (hRk _ (le_refl _))
  -- down the chain
  have hIj : ∀ m j, r + L - j ≤ m → r ≤ j → j ≤ r + L → ValInv (M.take j) (drop1 M j rkM) := by
    intro m
    induction m with
    | zero =>
      intro j hm _ hj
      have hjx : j = r + L := by omega
      subst hjx; exact hIx
    | succ m ih =>
      intro j hm hrj hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact hIx
      · have hN := ih (j + 1) (by omega) (by omega) hjx
        have := drop_pres (N := M.take (j + 1)) (x := j) (hlj j (by omega)).symm
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
          (UAB_take hUAB _) (hCj _ hjx) hN (hres j hrj hjx)
          (by rw [take_take_succ]; exact hCj j (by omega))
          (by rw [take_take_succ]; exact hRk j (by omega))
        rwa [take_take_succ] at this
  exact t1_n0v hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM hVS hF hFO hArgT
    hKD hTD hAbs hWS hVSt hUA hVL (fun j hrj hjx =>
      DropHypV.of (hIj _ (j + 1) (le_refl _) (by omega) hjx) (hres j hrj hjx))

/-! ## UpgAbsX を 1 つの行列の条件から -/

/-- **Value invariant** (a single matrix): `UpgAbs` at the upgrades `i → k` with `k < i` or `k` a leaf.
The global `UpgAbs` is false on standard matrices only at `k = i + 1` with children (e.g. at `i = 11` of
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0),
`ω ⋪ Ω_1`). SRO からの乱択の展開とその M[n] の接頭辞閉包（標準形 40 万個）で例外 0. -/
def UpgAbsL (M : Mat) (ρ : Valn) : Prop :=
  ∀ i k W, upg M i = some k → (k < i ∨ children M k = []) → ρ.v k = add (vOpt ρ (par M 1 i)) W →
    W ≠ z → ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W

/-- **`UpgAbsX` from `UpgAbsL`**: the upgrade of `x − 1` goes to `x` (a leaf) or to an ancestor. -/
theorem UpgAbsL.x {M : Mat} {ρ : Valn} (h : UpgAbsL M ρ) {x : Nat} (hx : x + 1 = M.length) :
    UpgAbsX M x ρ := by
  intro i k W hix hu hv hW
  obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
  refine h i k W hu ?_ hv hW
  rcases hcase with hk | ⟨_, hk⟩
  · right; rw [hk, hix]; exact children_last hx
  · left; exact hk

/-! ## argT を M.take x の Good3 と局所性から -/

/-- **`argT` from the standardness of `M.take x`** (an `Inv3` field of a standard prefix) and the locality
`LocA`: where `i` has a counted child in `M.take x`, its `v` and the earlier counted siblings' `o` do not change
(SRO からの展開の接頭辞閉包 40 万個で LocA は例外 0). -/
theorem argT_of_take {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hGT : Good3 (M.take x) ρ')
    (hLoc : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] →
      ¬ ChgX M x false i ∧ ∀ d ∈ Lc, ¬ ChgX M x true d) :
    ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] →
      ∀ s y, ρ'.o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z := by
  intro i hi Lc cs hcl s y ho hsa
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hoff := chg_off hx hC hG hC' hRk'
  obtain ⟨hvi, hLc⟩ := hLoc i hi Lc cs hcl
  have hv : ρ'.v i = ρ.v i := (hoff i hi).2 hvi
  have hmem : ∀ d ∈ Lc ++ [cs], d < x := fun d hd => by
    have h1 : d ∈ CL (M.take x) i := by rw [hcl]; exact hd
    have := (mem_children (cl_mem_children h1)).2
    omega
  have hmap : Lc.map ρ.o = Lc.map ρ'.o := List.map_congr_left (fun d hd =>
    ((hoff d (hmem d (List.mem_append_left _ hd))).1 (hLc d hd)).symm)
  rw [← hv, hmap]
  have hiT : i < (M.take x).length := by omega
  have hoi := o_cl_eq hC' hGT hiT
  obtain ⟨hs, hp⟩ := cl_vals hC' hGT hiT
  rw [hcl] at hoi hs hp
  rw [List.map_append, List.map_singleton] at hoi hs hp
  rw [sumN_snoc_dec hs hp, spArg_app, ho, spArg_single] at hoi
  have hX : isOT (psi (ρ'.v i) (step (ρ'.v i) (spArg (ρ'.v i) z (sumN (Lc.map ρ'.o))) s y z) z) = true := by
    rw [← hoi]; exact hGT.ot_o i hiT
  have hcs : isOT (psi s y z) = true := by
    rw [← ho]; exact hGT.ot_o cs (by have := hmem cs (by simp); omega)
  exact comps_le_step_of_ot hX hcs (by rw [hv]; exact hsa)

/-- **`LocA`, the `v` half**: a column with a counted child in `M.take x` keeps its `v` (a changed `v`
sits on a topped column with no counted child, `chg_struct`). -/
theorem locA_v {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {i : Nat} (hi : i < x) {Lc : List Nat} {cs : Nat} (hcl : CL (M.take x) i = Lc ++ [cs]) :
    ¬ ChgX M x false i := by
  intro hCv
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hi
  have hcsT : cs ∈ CL (M.take x) i := by rw [hcl]; simp
  unfold CL at hcsT
  rw [List.mem_filter] at hcsT
  exact hT.2.1 cs hcsT.1 (by simpa using hcsT.2)

theorem upg_last_none {M : Mat} {x : Nat} (hx : x + 1 = M.length) : upg M x = none := by
  unfold upg; rw [if_pos (Or.inr (Or.inr hx))]

/-- **Nothing changes strictly between `i` and its last counted child `cs` in `M.take x`.** -/
theorem chg_none_before {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {i : Nat} {Lc : List Nat} {cs : Nat} (hcl : CL (M.take x) i = Lc ++ [cs]) :
    ∀ b d, ChgX M x b d → i < d → d < cs → False := by
  have hcsT : cs ∈ CL (M.take x) i := by rw [hcl]; simp
  unfold CL at hcsT
  rw [List.mem_filter] at hcsT
  have hcsCnt : Counted (M.take x) i cs := by simpa using hcsT.2
  obtain ⟨hcsx, hcsM⟩ := mem_children_take hcsT.1
  have hpcs : par M 0 cs = some i := (mem_children_iff.mp hcsM).2
  -- the subtree of a column strictly between `i` and `cs` ends before `cs`
  have hsub : ∀ d y, i < d → d < cs → Anc0 M d y → y < cs := by
    intro d y hid hdc hA
    by_contra hge
    have hAc : Anc0 M d cs := anc_between hA cs (by omega) (by omega)
    have := (anc0_par hAc (by omega) hpcs).le
    omega
  -- `cs` is not upgraded-and-topped in `M.take x`
  have hcsU : ∀ d, d + 1 = cs → upg M d = some cs → ChgX M x false cs → False := by
    intro d hd hu hC
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).1 rfl hcsx
    apply hcsCnt.2
    refine ⟨(isUpg_take M (by omega) cs).mpr ⟨d, by omega, hu⟩, hT.1⟩
  intro b d hC
  induction hC with
  | leaf => intro _ h; omega
  | supg _ => intro _ h; omega
  | @scnt d c hc hcx hne =>
    intro hid hdc
    have hcd := (mem_children hc).1
    have hAc : Anc0 M d c := Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl d)
    have hccs := hsub d c hid hdc hAc
    apply hne
    have hxc : x ∉ children M c := fun h =>
      absurd (hsub d x hid hdc (Anc0.step (mem_children_iff.mp h).2 hAc)) (by omega)
    have hU : isUpg (M.take x) c = isUpg M c := by
      apply Bool.eq_iff_iff.mpr
      rw [isUpg_take M (by omega) c]
      unfold isUpg
      rw [List.any_eq_true]
      constructor
      · rintro ⟨j, hj, hu⟩
        exact ⟨j, List.mem_range.mpr (by omega), by simpa using hu⟩
      · rintro ⟨j, hj, hu⟩
        have hu' : upg M j = some c := by simpa using hu
        have hjl := List.mem_range.mp hj
        refine ⟨j, ?_, hu'⟩
        by_contra hjx
        rcases Nat.lt_or_ge j x with hjx' | hjx'
        · -- `j = x − 1`
          have hj1 : j = x - 1 := by omega
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
          rcases hcase with h' | ⟨hA, _⟩
          · omega
          · have := hsub d j hid hdc (Anc0.trans hAc hA); omega
        · have hjx2 : j = x := by omega
          rw [hjx2, upg_last_none hx] at hu'; cases hu'
    unfold Counted
    rw [col_take M (by omega), bump_take M (by omega), hU, topped_take_eq hx (by omega) hxc]
  | snb _ _ hxc _ =>
    intro hid hdc
    have := hsub _ x hid hdc (Anc0.step (mem_children_iff.mp hxc).2 (Anc0.refl _))
    omega
  | @ochild d c hc _ _ _ ih =>
    intro hid hdc
    have hcd := (mem_children hc).1
    have hccs := hsub d c hid hdc (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl d))
    exact ih (by omega) hccs
  | ov _ ih => exact ih
  | @vpar d m _ hp hCm _ =>
    intro hid hdc
    have hmd := par_lt M 1 d m hp
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega)
    exact hT.2.2 d (by omega) hp
  | @vupg d k _ _ hu hCk ih =>
    intro hid hdc
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with hk | ⟨hA, hkd⟩
    · rcases Nat.lt_or_ge k cs with hkc | hkc
      · exact ih (by omega) hkc
      · exact hcsU d (by omega) (by rw [hu]; congr 1; omega) (by rw [show cs = k by omega]; exact hCk)
    · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl (by omega)
      exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT (by omega) hu hA hkd
  | @vbump d j k _ _ hj _ hk _ ih =>
    intro hid hdc
    have hjd := (mem_children hj).1
    have hkj := (mem_children hk).1
    have hAk : Anc0 M d k := Anc0.step (mem_children_iff.mp hk).2
      (Anc0.step (mem_children_iff.mp hj).2 (Anc0.refl d))
    exact ih (by omega) (hsub d k hid hdc hAk)

/-- **`LocA`** (structural): where `i` has a counted child in `M.take x`, its `v` and the earlier counted
children's `o` do not change. -/
theorem locA {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M) :
    ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] →
      ¬ ChgX M x false i ∧ ∀ d ∈ Lc, ¬ ChgX M x true d := by
  intro i hi Lc cs hcl
  refine ⟨locA_v hx hR0 hZ2 hSD hZ1 hUAT hUAB hi hcl, fun d hd hCd => ?_⟩
  have hdT : d ∈ CL (M.take x) i := by rw [hcl]; simp [hd]
  have hdc : d < cs := by
    have hs : (CL (M.take x) i).Pairwise (· < ·) := by
      unfold CL; exact (children_sorted (M.take x) i).filter _
    rw [hcl] at hs
    exact (List.pairwise_append.mp hs).2.2 d hd cs (by simp)
  have hid := (mem_children (cl_mem_children hdT)).1
  exact chg_none_before hx hR0 hZ2 hSD hZ1 hUAT hUAB hcl true d hCd hid hdc

/-- **`argT` from single-matrix invariants**: the structural invariants of `M` and `Good3` of `M.take x`
(a standard prefix). -/
theorem argT_std {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hGT : Good3 (M.take x) ρ') :
    ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] →
      ∀ s y, ρ'.o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z :=
  argT_of_take hx hC hG hC' hRk' hGT (locA hx hR0 hZ2 hSD hZ1 hUAT hUAB)

end Ytosk
