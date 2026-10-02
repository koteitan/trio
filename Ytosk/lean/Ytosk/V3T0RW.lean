/-
**3 行・t = 0: 書き換える枠の値の不変条件（TP1C・TP1WC・TrigOmC の形）の、子の並びの形と数える子の形の行き来。**

`RWC P M ρ`: 数える子 c が書き換える枠（状態 B = preState、子 ψ_s(y)）で P(v(i), B, s, y)。
`QP P a Lv cv`: 数える子の並び Lv の後の子 cv の枠で同じこと（`frameQ_N_t0` に渡す形）。
-/
import Ytosk.V3T0Frm

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **A property of the rewriting frames** (children form, with the state `preState`). -/
def RWC (P : T → T → T → T → Prop) (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → Counted M i c → ∀ s y, ρ.o c = psi s y z →
    lt (preState M ρ i L) y = true → lt (psi (ρ.v i) z z) (psi s y z) = true →
    P (ρ.v i) (preState M ρ i L) s y

/-- The same property in the counted form. -/
abbrev QP (P : T → T → T → T → Prop) (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true → lt (psi a z z) (psi s y z) = true →
    P a (spArg a z (sumN Lv)) s y

/-- The state before a child is the state of the counted ones before it. -/
theorem preState_eq {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hO : GoodOT M ρ) {i : Nat} {L : List Nat}
    (hL : ∀ d ∈ L, d < M.length) :
    preState M ρ i L = spArg (ρ.v i) z (sumN ((L.filter (fun d => decide (Counted M i d))).map ρ.o)) := by
  classical
  unfold preState
  congr 2
  have : L.map (cnt M ρ i) = L.map (fun d => if Counted M i d then ρ.o d else z) := by
    apply List.map_congr_left; intro d _; exact cnt_eq_ite M ρ i d
  rw [this]
  exact nzs_map_ite _ _ L (fun d hd _ => single_ne_z (single_oT hC hO (hL d hd)))

/-- **From the counted form to the children form.** -/
theorem rwc_of_cl {P : T → T → T → T → Prop} {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hO : GoodOT M ρ)
    (h : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QP P (ρ.v i) (Lc.map ρ.o) (ρ.o c)) : RWC P M ρ := by
  classical
  intro i L c R hch hcnt s y hsy hlt htr
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hiM : i < M.length := by
    have := (mem_children hcM).1; have := (mem_children hcM).2; omega
  have hL : ∀ d ∈ L, d < M.length := fun d hd => (mem_children (show d ∈ children M i by
    rw [hch]; simp [hd])).2
  rw [preState_eq hC hO hL] at hlt ⊢
  have hCL : CL M i = L.filter (fun d => decide (Counted M i d)) ++ c ::
      R.filter (fun d => decide (Counted M i d)) := by
    unfold CL; rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
  exact h i hiM _ c _ hCL s y hsy hlt htr

/-- **The rewriting-frame properties depend only on the values in range.** -/
theorem rwc_congr {P : T → T → T → T → Prop} {M : Mat} {σ τ : Valn} (h : RWC P M σ)
    (hA : ∀ i, i < M.length → σ.o i = τ.o i ∧ σ.v i = τ.v i) :
    RWC P M τ := by
  intro i L c R hch hcnt s y hsy hlt htr
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hcl := (mem_children hcM).2
  have hiM : i < M.length := by have := (mem_children hcM).1; omega
  have hpre : preState M σ i L = preState M τ i L := by
    unfold preState
    rw [(hA i hiM).2]
    congr 3
    apply List.map_congr_left
    intro d hd
    have hdM : d ∈ children M i := by rw [hch]; simp [hd]
    unfold cnt
    split_ifs
    · rfl
    · rfl
    · exact (hA d (mem_children hdM).2).1
  have := h i L c R hch hcnt s y (by rw [(hA c hcl).1]; exact hsy) (by rw [hpre]; exact hlt)
    (by rw [(hA i hiM).2]; exact htr)
  rwa [hpre, (hA i hiM).2] at this

/-- Equal prefixes before an element that occurs in neither. -/
theorem prefix_eq_of_not_mem {α : Type} {A B P Q : List α} {c : α} (hA : c ∉ A) (hP : c ∉ P)
    (h : A ++ c :: B = P ++ c :: Q) : A = P := by
  rcases append_split_cons A (c :: B) P Q c h with ⟨R0, hR⟩ | ⟨P2, hP2, hD⟩
  · exact absurd (by rw [hR]; simp) hA
  · cases P2 with
    | nil => simpa using hP2.symm
    | cons a P2' =>
      simp only [List.cons_append, List.cons.injEq] at hD
      exact absurd (by rw [hP2, ← hD.1]; simp) hP

/-- **From the children form to the counted form.** -/
theorem cl_of_rwc {P : T → T → T → T → Prop} {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hO : GoodOT M ρ)
    (h : RWC P M ρ) :
    ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QP P (ρ.v i) (Lc.map ρ.o) (ρ.o c) := by
  classical
  intro i hi Lc c R hCL s y hsy hlt htr
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcM : c ∈ children M i := cl_mem_children hcCL
  have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  obtain ⟨L, R0, hch⟩ := List.append_of_mem hcM
  have hL : ∀ d ∈ L, d < M.length := fun d hd => (mem_children (show d ∈ children M i by
    rw [hch]; simp [hd])).2
  have hsort := children_sorted M i
  obtain ⟨hLs, _⟩ := sib_order hsort hch
  have hCL' : CL M i = L.filter (fun d => decide (Counted M i d)) ++ c ::
      R0.filter (fun d => decide (Counted M i d)) := by
    unfold CL; rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
  have hsortCL : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ hsort
  have hLc : Lc = L.filter (fun d => decide (Counted M i d)) := by
    apply prefix_eq_of_not_mem _ _ (hCL.symm.trans hCL')
    · intro hm
      rw [hCL] at hsortCL
      have := (List.pairwise_append.mp hsortCL).2.2 c hm c (by simp)
      exact lt_irrefl _ this
    · intro hm
      have := hLs c (List.mem_filter.mp hm).1
      exact lt_irrefl _ this
  have := h i L c R0 hch hcnt s y hsy
  rw [preState_eq hC hO hL, ← hLc] at this
  exact this hlt htr

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG

omit hCN hGN in
/-- **A later copy root of `g` does not rewrite** (`j ≥ 1` middle values before it). -/
theorem qp_later_copy (P : T → T → T → T → Prop) {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn}
    (hcnt : Counted M g r) (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    {Lc : List Nat} (hclM : CL M g = Lc ++ [r]) {j : Nat} (hj : 1 ≤ j) {cv : T}
    (hcv : cv = omid M r L ρ ∨ cv = ρ'.o r) :
    QP P (ρ.v g) (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)) cv := by
  intro s y hsy ht1 ht2
  exfalso
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  set v := ρ.v r with hv
  set a := ρ.v g with ha
  set Y0 := spArg v z (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))
    with hY0
  have hgr : g < r := par_lt M 0 r g hg
  have hXot : isOT (psi v (app Y0 one) z) = true := by rw [← hor]; exact hG.ot_o r (by omega)
  have hOot : isOT (psi v Y0 z) = true := by
    have := isOT_arg hXot
    rw [isOT_psi_iff]; refine ⟨isOT_sub hXot, isOT_app_left this, rfl, z_le _, ?_⟩
    intro q hq
    have h2 := comps_lt hXot q (by rw [comps_app]; exact List.mem_append_left _ hq)
    exact comps_lt_prefix hq h2
  have hcvle : cv ≤ psi v Y0 z := by
    rcases hcv with rfl | rfl
    · rw [hom]
    · rw [← hom]; exact hO'le
  have hcvss : y ≠ z → s = v := by
    intro hy
    rcases hcv with rfl | rfl
    · rw [hom] at hsy; simp only [psi.injEq] at hsy; exact hsy.1.symm
    · by_contra hne; exact hy (hy' s y hsy hne)
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG (show g < M.length by omega)
  rw [hclM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hOr : psi v Y0 z < ρ.o r := by
    rw [hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  have hLge : ∀ q ∈ Lc.map ρ.o, ρ.o r ≤ q := fun q hq => (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
  have hOs : Single (psi v Y0 z) := ⟨hOot, _, _, rfl⟩
  have hsum : sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)) =
      app (sumN (Lc.map ρ.o)) (mulT (psi v Y0 z) j) := by
    rw [hom, sumN_append_dec, sumN_replicate hOs]
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hsM t (List.mem_append_left _ ht)
      · rw [(List.mem_replicate.mp ht).2]; exact hOs
    · refine List.pairwise_append.mpr ⟨(List.pairwise_append.mp hpM).1,
        List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun q hq b hb => ?_⟩
      rw [(List.mem_replicate.mp hb).2]; exact le_trans (le_of_lt hOr) (hLge q hq)
  rw [hsum, spArg_app] at ht1
  have hnr := no_rw_after (a := a) (B := spArg a z (sumN (Lc.map ρ.o))) hOot hj
  apply hnr
  rw [hsy] at hcvle
  have hy0 : y ≠ z := fun h => by rw [h] at ht1; exact T.not_lt_z _ ht1
  obtain rfl := hcvss hy0
  have hyy : y ≤ Y0 := by
    rcases (le_iff _ _).mp hcvle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  exact ⟨lt_of_lt_of_le (show _ < y from ht1) hyy, lt_of_lt_of_le (show _ < psi v y z from ht2) hcvle⟩

include hCN hGN in
/-- **A rewriting-frame property of `N = M[n]`** (`t = 0`) from `M`, `M.take x`, the frames before `r`
whose child is in `D` (`hD`), and the first copy root of `g` (`hG0`). -/
theorem rwc_N_t0 (P : T → T → T → T → Prop) {ρ' : Valn} (hM : RWC P M ρ)
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ') (hT : RWC P (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hD : ∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        QP P (ρ.v i) (Lc.map ρ.o) (σ.o c))
    (hG0 : ∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = ρ'.o r) → QP P (ρ.v g) (Lc.map ρ.o) cv) :
    RWC P (TRIO.gexp M r L 0 0 n) σ := by
  have hx : r + L + 1 = M.length := hlen
  refine rwc_of_cl (P := P) hCN hGN ?_
  apply frameQ_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN (QP P) (ρ' := ρ')
    (cl_of_rwc hC hG.toOT hM) (cl_of_rwc hC1 hGT.toOT hT) hσB hoffD
  · intro g hg hcnt
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := (hoffD g hgr).2 (fun hd =>
      uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hd hrc hcnt)
    apply g_frames_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN (QP P) hg hcnt
      (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast (hLast g hg hcnt)
      (fun Lc c R h => cl_of_rwc hC hG.toOT hM g (by omega) Lc c R h)
    intro Lc j cv hclM hcv
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simpa using hG0 g hg hcnt Lc hclM cv hcv
    · exact qp_later_copy hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG P hg hcnt hO'le hy'
        hclM hj hcv
  · exact hD

end

end Ytosk
