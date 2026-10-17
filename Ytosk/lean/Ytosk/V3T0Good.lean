/-
**3 行・t = 0: 展開 N = M[n] の評価の Good3（数える子の値が減ること）。**

N の値が標準形であること（`GoodOT`）を前提に、数える子の値の減少を全列で示す（`good3_of_OT` で Good3）。
- r 以後のコピーの列 r + (kL + q): 子は M の r + q の子（x を除く）をずらしたもの、数え方も M と同じ
  （`counted_copy0`）。値は中間のコピーでは M の値、最後のコピーでは M.take x の値（`tauN`）。
  M.take x と M で (r, x) の子の数え方は同じ（x − 1 の祖先型の上げの的は行 0 が r 以下: `cnt_same_B`）。
-/
import Ytosk.V3T0W

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The counting below `r` is the same in `M.take x` and `M`.** -/
theorem cnt_same_B {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hR0 : R0P M)
    (hp : par M 0 (r + L) = some r) {i d : Nat} (hri : r ≤ i) (hix : i < r + L)
    (hd : d ∈ children M i) (hdx : d < r + L) :
    Counted (M.take (r + L)) i d ↔ Counted M i d := by
  by_contra hne
  have hx : r + L + 1 = M.length := hlen
  have hAx : Anc0 M r (r + L) := Anc0.step hp (Anc0.refl r)
  have hAi : Anc0 M r i := anc_between hAx i hri (by omega)
  have hid := (mem_children hd).1
  have hAd : Anc0 M r d := Anc0.step (mem_children_iff.mp hd).2 hAi
  rcases cnt_change hx hix hdx hne with h | h
  · have := (mem_children_iff.mp h).2
    rw [hp] at this; cases this; omega
  · have hne1 : d ≠ r + L - 1 + 1 := by omega
    have he := upg_climb_e0 h hne1
    rw [show r + L - 1 + 1 = r + L by omega, hR0 _ _ hp] at he
    have := anc0_e0_lt hAd (by omega)
    omega

/-- **Lowering only a last element keeps the decrease**: values change only at elements with no later
element, and there they decrease. -/
theorem pairwise_lower_last {l : List Nat} {f g : Nat → T} {P : Nat → Prop}
    (hs : l.Pairwise (· < ·)) (hp : (l.map f).Pairwise (fun a b => b ≤ a))
    (hP : ∀ d ∈ l, P d → ∀ e ∈ l, d < e → False)
    (heq : ∀ d ∈ l, ¬ P d → g d = f d) (hle : ∀ d ∈ l, P d → g d ≤ f d) :
    (l.map g).Pairwise (fun a b => b ≤ a) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.map_cons, List.pairwise_cons] at hp ⊢
    rw [List.pairwise_cons] at hs
    have hge : ∀ e ∈ t, g e ≤ f e := fun e he => by
      by_cases hPe : P e
      · exact hle e (by simp [he]) hPe
      · rw [heq e (by simp [he]) hPe]
    refine ⟨fun b hb => ?_, ih hs.2 hp.2 (fun d hd hPd e he hde => hP d (by simp [hd]) hPd e (by simp [he]) hde)
      (fun d hd => heq d (by simp [hd])) (fun d hd => hle d (by simp [hd]))⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    have hPa : ¬ P a := fun hPa => hP a (by simp) hPa e (by simp [he]) (hs.1 e he)
    rw [heq a (by simp) hPa]
    exact le_trans (hge e he) (hp.1 _ (List.mem_map_of_mem he))

/-! ## 値の標準形: v は o から -/

/-- **The `v` values are standard when the `o` values are** (by the ranking of the `v` calls). -/
theorem ot_v_of_o {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hR : Rk N rk)
    (hO : ∀ i, i < N.length → isOT (σ.o i) = true) : ∀ i, i < N.length → isOT (σ.v i) = true := by
  have key : ∀ K, ∀ i, rk false i ≤ K → i < N.length → isOT (σ.v i) = true := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro i hK hi
      obtain ⟨_, _, hRr⟩ := hR i hi
      have hV : entry N 1 i ≠ 0 → isOT (vOpt σ (par N 1 i)) = true := by
        intro h1
        cases hpm : par N 1 i with
        | none => rfl
        | some m =>
          exact ih _ (by have := (hRr h1).1 m hpm; omega) m (le_refl _)
            (by have := par_lt N 1 i m hpm; omega)
      rw [(hC i hi).2]; unfold vRhs
      split_ifs with h1 h2
      · rfl
      · cases hu : upg N i with
        | none =>
          have h' : isOT (add (vOpt σ (par N 1 i)) one) = true := isOT_add (hV h1) rfl
          show isOT (sf (add (vOpt σ (par N 1 i)) one)) = true
          rw [sf_ot h']; exact h'
        | some k =>
          have hk : isOT (last (σ.v k)) = true :=
            isOT_last (ih _ (by have := (hRr h1).2.1 h2 k hu; omega) k (le_refl _) (upg_lt hi hu))
          have h' : isOT (add (vOpt σ (par N 1 i)) (last (σ.v k))) = true := isOT_add (hV h1) hk
          show isOT (sf (add (vOpt σ (par N 1 i)) (last (σ.v k)))) = true
          rw [sf_ot h']; exact h'
      · have hB : isOT (omega (sumN (one :: (children N i).map (bumpTerm N σ i)))) = true := by
          apply isOT_omega; apply isOT_sumN
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · rfl
          · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
            unfold bumpTerm
            split
            · apply isOT_omega; apply isOT_sumN
              intro t' ht'
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht'
              exact hO k (mem_children hk).2
            · rfl
        rw [sf_ot (isOT_add (hV h1) hB)]; exact isOT_add (hV h1) hB
  exact fun i hi => key _ i (le_refl _) hi


section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

omit hC hG hCN hGN in
/-- **The counted children of a copy column.** -/
theorem cl_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    CL (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) =
      (((children M (r + q)).filter (fun c => decide (c < r + L))).filter
        (fun d => decide (Counted M (r + q) d))).map (shk r (k * L)) := by
  unfold CL
  rw [children_copy0 hlen hL hp hn hk hq, List.filter_map]
  congr 1
  apply List.filter_congr
  intro d hd
  have h := List.mem_filter.mp hd
  have h1 := (mem_children h.1).1
  have h2 : d < r + L := by simpa using h.2
  obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
  simp only [Function.comp, shk, if_pos (show r ≤ r + q' by omega)]
  rw [show r + q' + k * L = r + (k * L + q') by omega]
  simp only [decide_eq_decide]
  exact counted_copy0 hlen hL hp hn hR0 hZ2 he2 hk hq (by omega) (by omega)

omit hC hG hCN hGN in
/-- **The counted children of `r + q` in `M.take x`** are those of `M` below `x`. -/
theorem cl_take_B {q : Nat} (hq : q < L) :
    CL (M.take (r + L)) (r + q) =
      ((children M (r + q)).filter (fun c => decide (c < r + L))).filter
        (fun d => decide (Counted M (r + q) d)) := by
  unfold CL
  rw [children_take]
  apply List.filter_congr
  intro d hd
  have h := List.mem_filter.mp hd
  simp only [decide_eq_decide]
  exact cnt_same_B hlen hR0 hp (by omega) (by omega) h.1 (by simpa using h.2)

/-- **The decrease at a copy column.** -/
theorem dec_copy0 {ρ' : Valn} {oMid : T} (hC' : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length → σ.o i = (tauN r L n ρ ρ' oMid).o i)
    {k q : Nat} (hk : k < n) (hq : q < L) :
    ((CL (TRIO.gexp M r L 0 0 n) (r + (k * L + q))).map σ.o).Pairwise (fun a b => b ≤ a) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hkL : k * L + L ≤ n * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  set F := (children M (r + q)).filter (fun c => decide (c < r + L)) with hF
  have hFm : ∀ d ∈ F, d ∈ children M (r + q) ∧ r + q < d ∧ d < r + L := fun d hd => by
    have h := List.mem_filter.mp hd
    exact ⟨h.1, (mem_children h.1).1, by simpa using h.2⟩
  have hCL : CL (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) =
      (F.filter (fun d => decide (Counted M (r + q) d))).map (shk r (k * L)) := by
    unfold CL
    rw [children_copy0 hlen hL hp hn hk hq, ← hF, List.filter_map]
    congr 1
    apply List.filter_congr
    intro d hd
    obtain ⟨_, h1, h2⟩ := hFm d hd
    obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
    simp only [Function.comp, shk, if_pos (show r ≤ r + q' by omega)]
    rw [show r + q' + k * L = r + (k * L + q') by omega]
    simp only [decide_eq_decide]
    exact counted_copy0 hlen hL hp hn hR0 hZ2 he2 hk hq (by omega) (by omega)
  rw [hCL, List.map_map]
  -- the values along the copy
  have hval : ∀ d ∈ F.filter (fun d => decide (Counted M (r + q) d)),
      (σ.o ∘ shk r (k * L)) d = if k + 1 < n then ρ.o d else ρ'.o d := by
    intro d hd
    obtain ⟨_, h1, h2⟩ := hFm d (List.mem_filter.mp hd).1
    obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
    simp only [Function.comp, shk, if_pos (show r ≤ r + q' by omega)]
    rw [show r + q' + k * L = r + (k * L + q') by omega, hσB _ (by omega) (by rw [hlN]; omega)]
    split
    · rename_i hkn; exact tau_o_mid hkn (by omega) (by omega)
    · have hk' : k = n - 1 := by omega
      subst hk'
      exact tau_o_last (by omega)
  rw [List.map_congr_left hval]
  split
  · -- a middle copy: the values of `M`
    have hsub : (F.filter (fun d => decide (Counted M (r + q) d))).Sublist (CL M (r + q)) := by
      unfold CL; rw [hF, List.filter_comm]; exact List.filter_sublist
    have hdec := (cl_vals hC hG (show r + q < M.length by omega)).2
    exact (hdec.sublist (hsub.map _))
  · -- the last copy: the values of `M.take x`
    have hCLT : CL (M.take (r + L)) (r + q) = F.filter (fun d => decide (Counted M (r + q) d)) := by
      unfold CL
      rw [children_take, ← hF]
      apply List.filter_congr
      intro d hd
      obtain ⟨h0, _, h2⟩ := hFm d hd
      simp only [decide_eq_decide]
      exact cnt_same_B hlen hR0 hp (by omega) (by omega) h0 h2
    have hdec := (cl_vals hC' hGT (show r + q < (M.take (r + L)).length by
      rw [List.length_take]; omega)).2
    rw [hCLT] at hdec
    exact hdec

/-- **The decrease before `r`** at a column whose counted children are those of `M` (not the parent of
`r`, or `r` is a bump child of it): only the last counted child can be in `D`, and it drops. -/
theorem dec_pre0
    (hoffD : ∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    {i : Nat} (hi : i < r) (hb : par M 0 r = some i → col M r = bump M i) :
    ((CL (TRIO.gexp M r L 0 0 n) i).map σ.o).Pairwise (fun a b => b ≤ a) := by
  have hx : r + L + 1 = M.length := hlen
  have hiM : i < M.length := by omega
  rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hi hb]
  have hCLr : ∀ d ∈ CL M i, d < r := by
    intro d hd
    have hdc := cl_mem_children hd
    by_cases hig : par M 0 r = some i
    · have hle := children_g_le hlen hL hp hig hdc
      rcases Nat.lt_or_ge d r with h | h
      · exact h
      · have hdr : d = r := by omega
        subst hdr
        unfold CL at hd
        have := (List.mem_filter.mp hd).2
        simp only [decide_eq_true_eq] at this
        exact absurd (hb hig) this.1
    · exact children_lt_r hlen hL hp hi hig hdc
  apply pairwise_lower_last (P := fun d => DepX M (r + L) true d)
    (List.Pairwise.filter _ (children_sorted M i)) (cl_vals hC hG hiM).2
  · intro d hd hD e he hde
    have hecnt : Counted M i e := by
      have he' : e ∈ CL M i := he
      unfold CL at he'; simpa using (List.mem_filter.mp he').2
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) (cl_mem_children hd)
      (cl_mem_children he) hde hD hecnt
  · intro d hd hD; exact hoffD d (hCLr d hd) hD
  · intro d hd hD; exact hdl d (hCLr d hd) hD

/-- **The shape at the parent `g` of `r` when `r` counts there.** -/
theorem g0_shape {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hl : ρ'.o r < ρ.o r) :
    ∃ Lc Cm : List Nat, CL M g = Lc ++ [r] ∧ CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] ∧
      Lc.map σ.o = Lc.map ρ.o ∧ Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  -- the counted children in `M`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set Lc := F.filter (fun d => decide (Counted M g d)) with hLcdef
  have hclM : CL M g = Lc ++ [r] := by
    unfold CL; rw [hchM, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
    rfl
  -- the counted children in `N`
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hroots : [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) =
      (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
    have e1 : (List.range n).map f = [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [hfdef, Nat.add_sub_cancel]
    have e2 : (List.range n).map f = (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ, List.map_append]; simp [hfdef]
    rw [← e1, e2]
  set Cm := ((List.range (n - 1)).map f).filter
    (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) with hCmdef
  have hclN : CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] := by
    unfold CL
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
      List.filter_append]
    have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) = Lc := by
      apply List.filter_congr
      intro d hd
      have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
      simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hgr hdr]
    rw [hF', List.append_assoc]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hLast]
    rfl
  have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hLcv : Lc.map σ.o = Lc.map ρ.o := by
    apply List.map_congr_left
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  exact ⟨_, _, hclM, hclN, hLcv, hCmv⟩

/-- **The decrease at the parent `g` of `r` when `r` counts there**: the copy roots before the last are
`omid`, the last is `o′(r)`. -/
theorem dec_g0 {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hl : ρ'.o r < ρ.o r) :
    ((CL (TRIO.gexp M r L 0 0 n) g).map σ.o).Pairwise (fun a b => b ≤ a) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  -- the counted children in `M`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set Lc := F.filter (fun d => decide (Counted M g d)) with hLcdef
  have hclM : CL M g = Lc ++ [r] := by
    unfold CL; rw [hchM, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
    rfl
  -- the counted children in `N`
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hroots : [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) =
      (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
    have e1 : (List.range n).map f = [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [hfdef, Nat.add_sub_cancel]
    have e2 : (List.range n).map f = (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ, List.map_append]; simp [hfdef]
    rw [← e1, e2]
  set Cm := ((List.range (n - 1)).map f).filter
    (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) with hCmdef
  have hclN : CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] := by
    unfold CL
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
      List.filter_append]
    have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) = Lc := by
      apply List.filter_congr
      intro d hd
      have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
      simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hgr hdr]
    rw [hF', List.append_assoc]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hLast]
    rfl
  have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hLcv : Lc.map σ.o = Lc.map ρ.o := by
    apply List.map_congr_left
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  have hsN := cl_valsT hCN hGN (i := g)
  rw [hclM] at hsM hpM
  rw [hclN] at hsN
  simp only [List.map_append, List.map_singleton] at hsM hpM hsN
  rw [hLcv, hCmv, hσlast] at hsN
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  -- the decrease at `g` in `N`
  have hpN : (Lc.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r]).Pairwise
      (fun a b => b ≤ a) := by
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hlo : ρ'.o r ≤ omid M r L ρ := by
      obtain ⟨_, s', y', hs'⟩ := hsN (ρ'.o r) (by simp)
      have h := hl
      rw [hs', hor] at h
      rw [hs', hom]
      rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
      · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hp1.1,
      List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha b hb => ?_⟩, by simp, fun a ha b hb => ?_⟩
    · rw [(List.mem_replicate.mp hb).2]
      exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
    · simp at hb; rw [hb]
      rcases List.mem_append.mp ha with ha | ha
      · exact le_trans hlo (le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp)))
      · rw [(List.mem_replicate.mp ha).2]; exact hlo
  have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) g).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hclN]; simp only [List.map_append, List.map_singleton]; rw [hLcv, hCmv, hσlast]; exact hpN
  exact hpN0

omit hGN in
/-- `omid` is standard. -/
theorem isOT_omid : isOT (omid M r L ρ) = true := by
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  have hot := hG.ot_o r (by omega)
  rw [hor] at hot
  rw [hom]
  set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))
  rw [isOT_psi_iff] at hot ⊢
  obtain ⟨hv, hY, _, _, hc⟩ := hot
  refine ⟨hv, isOT_app_left hY, rfl, z_le _, fun g hg => ?_⟩
  have hg' : g ∈ comps (ρ.v r) (app Y0 one) := by rw [comps_app]; exact List.mem_append_left _ hg
  have hle : g ≤ Y0 := (lt_succ_iff (x := Y0)).mp (hc g hg')
  rcases (le_iff _ _).mp hle with h | h
  · exact h
  · exfalso; have := size_comps hg; rw [h] at this; exact Nat.lt_irrefl _ this

omit hGN in
/-- **`GoodOT` of `N`** from the standard values at the `D` columns before `r`. -/
theorem goodOT_N_t0 {ρ' : Valn} {rkN : Bool → Nat → Nat} (hRN : Rk (TRIO.gexp M r L 0 0 n) rkN)
    (hGT : Good3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hoffD : ∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i)
    (hOTD : ∀ i, i < r → DepX M (r + L) true i → isOT (σ.o i) = true) :
    GoodOT (TRIO.gexp M r L 0 0 n) σ := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have ho : ∀ i, i < (TRIO.gexp M r L 0 0 n).length → isOT (σ.o i) = true := by
    intro i hi
    rcases Nat.lt_or_ge i r with h | h
    · by_cases hd : DepX M (r + L) true i
      · exact hOTD i h hd
      · rw [hoffD i h hd]; exact hG.ot_o i (by omega)
    · rw [hσB i h hi]
      have hph : phi0 r L i < r + L := by
        unfold phi0; rw [if_neg (by omega)]; have := Nat.mod_lt (i - r) hL; omega
      unfold tauN
      simp only [if_neg (show ¬ i < r by omega)]
      split_ifs
      · exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN
      · exact hG.ot_o _ (by omega)
      · exact hGT.ot_o _ (by rw [List.length_take]; omega)
  exact ⟨ho, ot_v_of_o hCN hRN ho⟩

/-- **`Good3` of the valuation of `N = M[n]`** (`t = 0`) from its standard values. -/
theorem good3_N_t0 {ρ' : Valn} (hC' : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hoffD : ∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hl : ∀ g, par M 0 r = some g → Counted M g r → ρ'.o r < ρ.o r) :
    Good3 (TRIO.gexp M r L 0 0 n) σ := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  apply good3_of_OT hCN hGN
  intro i hi
  rcases Nat.lt_or_ge i r with hir | hir
  · by_cases hgc : par M 0 r = some i ∧ Counted M i r
    · exact dec_g0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hgc.1 hgc.2
        hoffD hσmid hσlast (hLast i hgc.1 hgc.2) (hl i hgc.1 hgc.2)
    · apply dec_pre0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hoffD hdl hir
      intro hig
      by_contra hb
      exact hgc ⟨hig, hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
  · have hk : (i - r) / L < n := by
      rw [hlN] at hi
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hq : (i - r) % L < L := Nat.mod_lt _ hL
    have hi' : i = r + ((i - r) / L * L + (i - r) % L) := by
      have := Nat.div_add_mod (i - r) L
      rw [Nat.mul_comm] at this; omega
    rw [hi']
    exact dec_copy0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hC' hGT hσB hk hq

end


end Ytosk
