/-
**3 行・t = 0: N = M[n] の枠の性質の一般形。**

枠の性質 Q(v(i), 数える子の前の値の並び, 数える子の値) が M と M.take x の枠で成り立てば、N の枠でも成り立つ。
ただし r より前の D の子の枠（`hFOD`）と、r が数えられる g の枠（`hFOg`）は別に仮定する。
`frameOT_N_t0` の一般化。
-/
import Ytosk.V3T0FO

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- Where an element sits in a concatenation. -/
theorem append_split_cons {α : Type} : ∀ (A D P Q : List α) (c : α), A ++ D = P ++ c :: Q →
    (∃ R0, A = P ++ c :: R0) ∨ (∃ P2, P = A ++ P2 ∧ D = P2 ++ c :: Q)
  | [], D, P, Q, c, h => Or.inr ⟨P, by simp, by simpa using h⟩
  | a :: A, D, [], Q, c, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨A, by rw [h.1]; rfl⟩
  | a :: A, D, p :: P, Q, c, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases append_split_cons A D P Q c h.2 with ⟨R0, hR⟩ | ⟨P2, hP, hD⟩
    · exact Or.inl ⟨R0, by rw [h.1, hR]; rfl⟩
    · exact Or.inr ⟨P2, by rw [h.1, hP]; rfl, hD⟩

/-- **A rewriting frame whose child drops keeps `FrameDom`**: the rewrite of the new child is a rewrite
of the old one, and `H` is monotone. -/
theorem frameDom_drop {a B s s' y y' : T} (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hle : psi s' y' z ≤ psi s y z) (hss : y' ≠ z → s' = s)
    (hM : lt B y = true ∧ lt (psi a z z) (psi s y z) = true → FrameDom a B s (H s y)) :
    lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true → FrameDom a B s' (H s' y') := by
  intro ht
  have hy0 : y' ≠ z := fun h => by rw [h] at ht; exact T.not_lt_z _ ht.1
  obtain rfl := hss hy0
  have hyy : y' ≤ y := by
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  have hMt : lt B y = true ∧ lt (psi a z z) (psi s' y z) = true :=
    ⟨lt_of_lt_of_le (show B < y' from ht.1) hyy, lt_of_lt_of_le (show psi a z z < psi s' y' z from ht.2) hle⟩
  exact (hM hMt).mono (H_mono hc' hc hyy)

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **A frame property of `N = M[n]`** (`t = 0`) from those of `M` and `M.take x`, the frames before `r`
whose child is in `D`, and the frames of `g` when `r` counts there. -/
theorem frameQ_N_t0 (Q : T → List T → T → Prop) {ρ' : Valn}
    (hFO : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      Q (ρ.v i) (Lc.map ρ.o) (ρ.o c))
    (hFOT : ∀ i, i < (M.take (r + L)).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (M.take (r + L)) i = Lc ++ c :: R → Q (ρ'.v i) (Lc.map ρ'.o) (ρ'.o c))
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hFOg : ∀ g, par M 0 r = some g → Counted M g r →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (TRIO.gexp M r L 0 0 n) g = Lc ++ c :: R →
        Q (σ.v g) (Lc.map σ.o) (σ.o c))
    (hFOD : ∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        Q (ρ.v i) (Lc.map ρ.o) (σ.o c)) :
    ∀ i, i < (TRIO.gexp M r L 0 0 n).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L 0 0 n) i = Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  intro i hi Lc c R hCL
  rcases Nat.lt_or_ge i r with hir | hir
  · by_cases hgc : par M 0 r = some i ∧ Counted M i r
    · exact hFOg i hgc.1 hgc.2 Lc c R hCL
    have hb : par M 0 r = some i → col M r = bump M i := by
      intro hig
      by_contra hb
      exact hgc ⟨hig, hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
    rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hir hb] at hCL
    have hiM : i < M.length := by omega
    -- the counted children before `c` are not in `D`
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hccnt : Counted M i c := by
      have := hcCL; unfold CL at this; simpa using (List.mem_filter.mp this).2
    have hsort : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ (children_sorted M i)
    rw [hCL] at hsort
    have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
      intro d hd
      have hdc : d < c := (List.pairwise_append.mp hsort).2.2 d hd c (by simp)
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdr : d < r := by
        have hdch := cl_mem_children hdCL
        by_cases hig : par M 0 r = some i
        · have hle := children_g_le hlen hL hp hig hdch
          have hcle := children_g_le hlen hL hp hig (cl_mem_children hcCL)
          omega
        · exact children_lt_r hlen hL hp hir hig hdch
      apply (hoffD d hdr).1
      intro hD
      exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) (cl_mem_children hdCL)
        (cl_mem_children hcCL) hdc hD hccnt
    have hv : σ.v i = ρ.v i := by
      apply (hoffD i hir).2
      intro hD
      exact uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hD (cl_mem_children hcCL) hccnt
    rw [hv, List.map_congr_left hLc]
    have hcr : c < r := by
      have hcch := cl_mem_children hcCL
      by_cases hig : par M 0 r = some i
      · have hle := children_g_le hlen hL hp hig hcch
        rcases Nat.lt_or_ge c r with h | h
        · exact h
        · exfalso; have hcr' : c = r := by omega
          rw [hcr'] at hccnt; exact hgc ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hir hig hcch
    by_cases hDc : DepX M (r + L) true c
    · exact hFOD i hir hgc Lc c R hCL hDc
    · rw [(hoffD c hcr).1 hDc]
      exact hFO i hiM Lc c R hCL
  · -- a copy column
    have hk0 : (i - r) / L < n := by
      rw [hlN] at hi
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hq0 : (i - r) % L < L := Nat.mod_lt _ hL
    have hi' : i = r + ((i - r) / L * L + (i - r) % L) := by
      have := Nat.div_add_mod (i - r) L
      rw [Nat.mul_comm] at this; omega
    obtain ⟨k, q, hk, hq, rfl⟩ : ∃ k q, k < n ∧ q < L ∧ i = r + (k * L + q) :=
      ⟨_, _, hk0, hq0, hi'⟩
    rw [cl_copy0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hk hq] at hCL
    obtain ⟨G, hGdef⟩ : ∃ G, G = ((children M (r + q)).filter (fun c => decide (c < r + L))).filter
      (fun d => decide (Counted M (r + q) d)) := ⟨_, rfl⟩
    rw [← hGdef] at hCL
    obtain ⟨Lc', T', hGs, hLc', hT'⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', rfl, hc', hR'⟩ := List.map_eq_cons_iff.mp hT'
    have hGm : ∀ d ∈ G, r + q < d ∧ d < r + L := fun d hd => by
      rw [hGdef] at hd
      have h := List.mem_filter.mp (List.mem_filter.mp hd).1
      exact ⟨(mem_children h.1).1, by simpa using h.2⟩
    have hval : ∀ d ∈ Lc', σ.o (shk r (k * L) d) = if k + 1 < n then ρ.o d else ρ'.o d := by
      intro d hd
      obtain ⟨h1, h2⟩ := hGm d (by rw [hGs]; simp [hd])
      obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
      have hkL : k * L + L ≤ n * L := by
        have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
      simp only [shk, if_pos (show r ≤ r + q' by omega)]
      rw [show r + q' + k * L = r + (k * L + q') by omega, (hσB _ (by omega) (by rw [hlN]; omega)).1]
      split
      · rename_i hkn; exact tau_o_mid hkn (by omega) (by omega)
      · have hk' : k = n - 1 := by omega
        rw [hk']
        exact tau_o_last (by omega)
    have hcval : σ.o (shk r (k * L) c') = if k + 1 < n then ρ.o c' else ρ'.o c' := by
      obtain ⟨h1, h2⟩ := hGm c' (by rw [hGs]; simp)
      obtain ⟨q', rfl⟩ : ∃ q', c' = r + q' := ⟨c' - r, by omega⟩
      have hkL : k * L + L ≤ n * L := by
        have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
      simp only [shk, if_pos (show r ≤ r + q' by omega)]
      rw [show r + q' + k * L = r + (k * L + q') by omega, (hσB _ (by omega) (by rw [hlN]; omega)).1]
      split
      · rename_i hkn; exact tau_o_mid hkn (by omega) (by omega)
      · have hk' : k = n - 1 := by omega
        rw [hk']
        exact tau_o_last (by omega)
    rw [← hc', hcval]
    rw [← hLc', List.map_map]
    have hLc'' : Lc'.map (σ.o ∘ shk r (k * L)) = Lc'.map (if k + 1 < n then ρ.o else ρ'.o) := by
      apply List.map_congr_left
      intro d hd
      simp only [Function.comp]
      rw [hval d hd]
      split <;> rfl
    rw [hLc'', (hσB _ (by omega) hi).2]
    by_cases hkn : k + 1 < n
    · rw [if_pos hkn, if_pos hkn, tau_v_mid hkn hq]
      -- the frame of `M` at `r + q`
      have hCLM : ∃ X, CL M (r + q) = G ++ X := by
        by_cases hxq : r + L ∈ children M (r + q)
        · refine ⟨((([r + L] : List Nat)).filter (fun d => decide (Counted M (r + q) d))), ?_⟩
          unfold CL
          rw [hGdef]
          conv_lhs => rw [children_split_x (x := r + L) hlen hxq]
          rw [List.filter_append]
        · refine ⟨[], ?_⟩
          unfold CL
          rw [hGdef, children_filter_x (x := r + L) hlen hxq, List.append_nil]
      obtain ⟨X, hX⟩ := hCLM
      exact hFO (r + q) (by omega) Lc' c' (R' ++ X) (by rw [hX, hGs]; simp)
    · rw [if_neg hkn, if_neg hkn]
      have hk' : k = n - 1 := by omega
      rw [show r + (k * L + q) = r + ((n - 1) * L + q) by rw [hk'], tau_v_last hq]
      exact hFOT (r + q) (by rw [List.length_take]; omega) Lc' c' R'
        (by rw [cl_take_B hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hq, ← hGdef, hGs])


/-- **The frames of `g`** (`t = 0`, `r` counts at `g`): before the copy roots they are frames of `M`;
at a copy root the earlier values are those of `M` and `j` middle values, and the child is the middle
value or `o′(r)`. -/
theorem g_frames_t0 (Q : T → List T → T → Prop) {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn}
    (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hQM : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M g = Lc ++ c :: R →
      Q (ρ.v g) (Lc.map ρ.o) (ρ.o c))
    (hQc : ∀ (Lc : List Nat) (j : Nat) (cv : T), CL M g = Lc ++ [r] →
      (cv = omid M r L ρ ∨ cv = ρ'.o r) → Q (ρ.v g) (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)) cv) :
    ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat), CL (TRIO.gexp M r L 0 0 n) g = Lc' ++ c :: R' →
      Q (σ.v g) (Lc'.map σ.o) (σ.o c) := by
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
  intro Lc' c R' hCL
  rw [hclN, hσvg] at *
  rw [hclN] at hCL
  rcases append_split_cons Lc (Cm ++ [r + (n - 1) * L]) Lc' R' c (by rw [← List.append_assoc]; exact hCL) with
    ⟨R0, hR0⟩ | ⟨P2, hP, hD⟩
  · -- a child before the copy roots: a frame of `M`
    have hσL : Lc'.map σ.o = Lc'.map ρ.o := by
      have := hLcv; rw [hR0, List.map_append, List.map_append] at this
      exact List.append_inj_left this (by simp)
    have hcσ : σ.o c = ρ.o c := by
      have := hLcv; rw [hR0, List.map_append, List.map_append] at this
      have h2 := List.append_inj_right this (by simp)
      simp only [List.map_cons, List.cons.injEq] at h2; exact h2.1
    rw [hσL, hcσ]
    exact hQM Lc' c (R0 ++ [r]) (by rw [hclM, hR0]; simp)
  · rcases append_split_cons Cm [r + (n - 1) * L] P2 R' c hD with ⟨R1, hR1⟩ | ⟨P3, hP3, hD3⟩
    · -- a middle copy root
      have hcm : c ∈ Cm := by rw [hR1]; simp
      have hcv : σ.o c = omid M r L ρ := by
        have := hCmv; rw [hR1] at this
        have hc' : σ.o c ∈ Cm.map σ.o := List.mem_map_of_mem (by rw [hR1]; simp)
        rw [hCmv] at hc'; exact (List.mem_replicate.mp hc').2
      have hP2v : P2.map σ.o = List.replicate P2.length (omid M r L ρ) := by
        rw [List.eq_replicate_iff]; refine ⟨by simp, fun b hb => ?_⟩
        have : b ∈ Cm.map σ.o := by rw [hR1]; simp only [List.map_append]; exact List.mem_append_left _ hb
        rw [hCmv] at this; exact (List.mem_replicate.mp this).2
      rw [hP, List.map_append, hLcv, hP2v, hcv]
      exact hQc Lc P2.length _ hclM (Or.inl rfl)
    · -- the last copy root
      have hP3n : P3 = [] := by
        cases P3 with
        | nil => rfl
        | cons a P3' => simp at hD3
      subst hP3n
      have hcl : c = r + (n - 1) * L := by simp at hD3; exact hD3.1.symm
      rw [List.append_nil] at hP3
      rw [hP, hP3, List.map_append, hLcv, hCmv, hcl, hσlast]
      exact hQc Lc Cm.length _ hclM (Or.inr rfl)


/-- The frame property of `FrameClosed`. -/
abbrev QFC (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    FrameDom a (spArg a z (sumN Lv)) s (H s y)

/-- **`FrameClosed` of `N = M[n]`** (`t = 0`): the frames of the copies are those of `M` and `M.take x`;
a frame before `r` whose child is in `D` keeps `FrameDom` because the child drops (`frameDom_drop`); at `g`
the first copy root is below `o(r)` and the later ones do not rewrite (`no_rw_after`). -/
theorem frameClosed_N_t0 {ρ' : Valn} (hF : FrameClosed M ρ) (hFT : FrameClosed (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hlr : ρ'.o r ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z) :
    FrameClosed (TRIO.gexp M r L 0 0 n) σ := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  -- `σ.o d = ψ_{s′}(y′)` with `y′ ≠ 0` keeps the subscript of `ρ.o d`
  have hsub : ∀ d, d < r → ∀ s y s' y', ρ.o d = psi s y z → σ.o d = psi s' y' z → y' ≠ z → s' = s := by
    intro d hd s y s' y' h h' hy
    obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show d < (TRIO.gexp M r L 0 0 n).length by rw [hlN]; omega)
    rw [h'] at hy0; simp only [psi.injEq] at hy0
    obtain ⟨y1, hy1⟩ := o_psi_sub hC (show d < M.length by omega)
    rw [h] at hy1; simp only [psi.injEq] at hy1
    rw [hy0.1, hy1.1, sf_ot (hGN.ot_v d (by rw [hlN]; omega)), sf_ot (hG.ot_v d (by omega))]
    by_contra hne
    have := hss d hd hne
    rw [h'] at this; simp only [psi.injEq] at this; exact hy this.2.1
  intro i hi Lc c R hCL
  apply frameQ_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN
    QFC (ρ' := ρ') hF hFT hσB hoffD
  · -- the frames of `g` when `r` counts there
    intro g hg hcnt
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := (hoffD g hgr).2 (fun hd =>
      uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hd hrc hcnt)
    apply g_frames_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN QFC hg hcnt
      (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast (hLast g hg hcnt)
      (fun Lc c R h => hF g (by omega) Lc c R h)
    intro Lc j cv hclM hcv s y hsy ht
    obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
    set v := ρ.v r with hv
    set a := ρ.v g with ha
    set Y0 := spArg v z (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))
      with hY0
    have hOot : isOT (psi v Y0 z) = true := by
      rw [← hom]; exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN
    have hXot : isOT (psi v (app Y0 one) z) = true := by rw [← hor]; exact hG.ot_o r (by omega)
    have hcv' : isOT cv = true := by
      rcases hcv with rfl | rfl
      · rw [hom]; exact hOot
      · exact hGT.ot_o r (by rw [List.length_take]; omega)
    have hcvle : cv ≤ psi v Y0 z := by
      rcases hcv with rfl | rfl
      · rw [hom]
      · rw [← hom]; exact hO'le
    have hcvss : y ≠ z → s = v := by
      intro hy
      rcases hcv with rfl | rfl
      · rw [hom] at hsy; simp only [psi.injEq] at hsy; exact hsy.1.symm
      · by_contra hne; exact hy (hy' s y hsy hne)
    -- the earlier values
    obtain ⟨hsM, hpM⟩ := cl_vals hC hG (show g < M.length by omega)
    rw [hclM] at hsM hpM
    simp only [List.map_append, List.map_singleton] at hsM hpM
    have hOr : psi v Y0 z < ρ.o r := by
      rw [hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
    have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
      (List.pairwise_append.mp hpM).1
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
    rw [hsum, spArg_app] at ht ⊢
    rcases Nat.eq_zero_or_pos j with hj | hj
    · -- the first copy root: below `o(r)`
      subst hj
      simp only [mulT] at ht ⊢
      rw [hsy] at hcv' hcvle
      have hle : psi s y z ≤ psi v (app Y0 one) z := by rw [← hor]; exact le_trans hcvle (le_of_lt hOr)
      exact frameDom_drop hXot hcv' hle hcvss
        (fun h => hF g (by omega) Lc r [] (by rw [hclM]) v (app Y0 one) hor h) ht
    · -- a later one does not rewrite
      exfalso
      have hnr := no_rw_after (a := a) (B := spArg a z (sumN (Lc.map ρ.o))) hOot hj
      apply hnr
      rw [hsy] at hcvle
      have hy0 : y ≠ z := fun h => by rw [h] at ht; exact T.not_lt_z _ ht.1
      obtain rfl := hcvss hy0
      have hyy : y ≤ Y0 := by
        rcases (le_iff _ _).mp hcvle with h | h
        · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · simp only [psi.injEq] at h; rw [h.2.1]
      exact ⟨lt_of_lt_of_le (show _ < y from ht.1) hyy, lt_of_lt_of_le (show _ < psi v y z from ht.2) hcvle⟩
  · -- a frame before `r` whose child is in `D`
    intro i' hi' hng Lc' c' R' hCL' hD s y hsy ht
    have hcM : c' ∈ children M i' := cl_mem_children (show c' ∈ CL M i' by rw [hCL']; simp)
    have hccnt : Counted M i' c' := by
      have : c' ∈ CL M i' := by rw [hCL']; simp
      unfold CL at this; simpa using (List.mem_filter.mp this).2
    have hcr : c' < r := by
      by_cases hig : par M 0 r = some i'
      · have hle := children_g_le hlen hL hp hig hcM
        rcases Nat.lt_or_ge c' r with h | h
        · exact h
        · exfalso; have : c' = r := by omega
          rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hi' hig hcM
    have hcMl : c' < M.length := by omega
    obtain ⟨s0, y0, hs0⟩ := (single_o hC hG hcMl).2
    have hc0 : isOT (psi s0 y0 z) = true := by rw [← hs0]; exact hG.ot_o c' hcMl
    have hc1 : isOT (psi s y z) = true := by
      rw [← hsy]; exact hGN.ot_o c' (by rw [hlN]; omega)
    have hle : psi s y z ≤ psi s0 y0 z := by rw [← hsy, ← hs0]; exact hdl c' hcr hD
    exact frameDom_drop hc0 hc1 hle (hsub c' hcr s0 y0 s y hs0 hsy)
      (hF i' (by omega) Lc' c' R' hCL' s0 y0 hs0) ht
  · exact hi
  · exact hCL

end

end Ytosk
