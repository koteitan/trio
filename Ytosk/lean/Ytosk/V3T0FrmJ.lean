/-
**3 行・t = 0: g の枠（`g_frames_t0` の写し）。最後の写しの根では、前の中間の写しの根の数 j が 0 なら、
中間の写しの根はどれも数えられないことも渡す（T0IVRes を使うため）。**
-/
import Ytosk.V3T0Frm

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **The frames of `g`** (`t = 0`, `r` counts at `g`): before the copy roots they are frames of `M`;
at a copy root the earlier values are those of `M` and `j` middle values, and the child is the middle
value or `o′(r)`. -/
theorem g_frames_t0J (Q : T → List T → T → Prop) {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn}
    (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hQM : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M g = Lc ++ c :: R →
      Q (ρ.v g) (Lc.map ρ.o) (ρ.o c))
    (hQc : ∀ (Lc : List Nat) (j : Nat) (cv : T), CL M g = Lc ++ [r] →
      (cv = omid M r L ρ ∨ (cv = ρ'.o r ∧
        (j = 0 → ∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)))) →
      Q (ρ.v g) (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)) cv) :
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
      refine hQc Lc Cm.length _ hclM (Or.inr ⟨rfl, fun h0 k hk hkc => ?_⟩)
      have hmem : r + k * L ∈ Cm := List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩, by simpa using hkc⟩
      rw [List.length_eq_zero_iff] at h0
      rw [h0] at hmem; simp at hmem

end

end Ytosk
