/-
**3 行・t = 0・n ≥ 2: 組み立て。**

- r に親 g があるとき: N と M の根はどちらも r より前の列だけ（`root_N_A`）。D の呼び出しは ◁ で真に下がり
  （`t0_dep_lhd`、種 `t0_S1`・`t0_S2`）、D の外は同じ値なので、根の和は真に下がる。
- r が根のとき: r より前は値が変わらず、M の根 r（値 ψ_v(Y0 + 1)）が N ではコピーの根
  ψ_v(Y0) × (n − 1) と M.take x での r の値に替わる（`root_N_B`）。
-/
import Ytosk.V3T0B

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

/-- **The root value when `r` has a parent**: only the columns before `r` are roots, in both. -/
theorem root_N_A (hR0 : R0P M) (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    {g : Nat} (hg : par M 0 r = some g) {ρ σ : Valn} (hG : Good3 M ρ)
    (hGN : Good3 (TRIO.gexp M r L 0 0 n) σ)
    (hle : ∀ i, i < r → σ.o i ≤ ρ.o i)
    (hstrict : ∀ R, R < r → Anc0 M R (r + L) → col M R = (0, 0, 0) → σ.o R < ρ.o R) :
    isOT (root (TRIO.gexp M r L 0 0 n) σ) = true ∧ root (TRIO.gexp M r L 0 0 n) σ < root M ρ := by
  classical
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have he0r : 0 < entry M 0 r := by have := hR0 r g hg; omega
  have he0x : entry M 0 (r + L) = entry M 0 r + 1 := hR0 _ _ hp
  set f' : Nat → T := fun i => if col M i = (0, 0, 0) then σ.o i else z with hf'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hcol0 : ∀ {N : Mat} {i : Nat}, entry N 0 i ≠ 0 → col N i ≠ (0, 0, 0) := by
    intro N i h hc
    rw [col_eq_entries] at hc
    simp only [Prod.mk.injEq] at hc
    exact h hc.1
  have hot' : ∀ i, i < r → isOT (f' i) = true := by
    intro i hi; simp only [hf']; split
    · exact hGN.ot_o i (by rw [hlN]; have : L ≤ n * L := Nat.le_mul_of_pos_left L hn; omega)
    · rfl
  have hot : ∀ i, i < r → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i (by omega)
    · rfl
  have hrootN : root (TRIO.gexp M r L 0 0 n) σ = sumN ((List.range r).map f') := by
    unfold root
    rw [hlN, List.range_add, List.map_append]
    rw [sumN_append_zeros (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hir := List.mem_range.mp hi
      split
      · exact hGN.ot_o i (by rw [hlN]; have : L ≤ n * L := Nat.le_mul_of_pos_left L hn; omega)
      · rfl)]
    · congr 1
      apply List.map_congr_left
      intro i hi
      rw [col_pre0 hlen hL hp hn (by have := List.mem_range.mp hi; omega)]
    · intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have hk' := List.mem_range.mp hk
      have := e0_copies_ge hlen hL hp hn (j := r + k) (by omega) (by omega)
      rw [if_neg (hcol0 (by omega))]
  have hrootM : root M ρ = sumN ((List.range r).map f) := by
    unfold root
    rw [← hlen]
    have hz : ∀ t ∈ (List.map (fun x => r + x) (List.range (L + 1))).map
        (fun i => if col M i = (0, 0, 0) then ρ.o i else z), t = z := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have hk' := List.mem_range.mp hk
      have he : entry M 0 (r + k) ≠ 0 := by
        rcases Nat.lt_or_ge k L with h | h
        · have := e0_B_ge hlen hL hp h; omega
        · rw [show r + k = r + L by omega, he0x]; omega
      rw [if_neg (hcol0 he)]
    rw [show r + L + 1 = r + (L + 1) by omega, List.range_add, List.map_append,
      sumN_append_zeros (fun t ht => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        have hir := List.mem_range.mp hi
        split
        · exact hG.ot_o i (by omega)
        · rfl) _ hz]
  rw [hrootN, hrootM]
  refine ⟨isOT_sumN _ (fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact hot' i (List.mem_range.mp hi)), ?_⟩
  obtain ⟨R, hRA, hR0c, hRl⟩ := root_t1 hR01 hR12 h00 (r + L)
  have he0R : entry M 0 R = 0 := by rw [col_eq_entries] at hR0c; simp only [Prod.mk.injEq] at hR0c; exact hR0c.1
  have hRr : R < r := by
    by_contra h
    have hRx := hRA.le
    rcases Nat.lt_or_ge R (r + L) with h' | h'
    · have := e0_B_ge hlen hL hp (q := R - r) (by omega); rw [show r + (R - r) = R by omega] at this; omega
    · rw [show R = r + L by omega, he0x] at he0R; omega
  apply sumN_range_lt f' f r hRr hot' hot
  · intro i hi; simp only [hf', hf]; split
    · exact hle i hi
    · exact le_refl _
  · simp only [hf', hf]; rw [if_pos hR0c, if_pos hR0c]; exact hstrict R hRr hRA hR0c
  · intro i h1 h2
    have hn' := hcol0 (hRl i h1 (by omega))
    simp only [hf', hf]; exact ⟨if_neg hn', if_neg hn'⟩

omit hlen hL hp hn in
theorem col0_ne {N : Mat} {i : Nat} (h : entry N 0 i ≠ 0) : col N i ≠ (0, 0, 0) := by
  intro hc
  rw [col_eq_entries] at hc
  simp only [Prod.mk.injEq] at hc
  exact h hc.1

/-- **A root `r`** has the zero column. -/
theorem col_r_root (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hrn : par M 0 r = none) :
    col M r = (0, 0, 0) := by
  obtain ⟨R, hRA, hR0c, _⟩ := root_t1 hR01 hR12 h00 r
  cases hRA with
  | refl => exact hR0c
  | step hq _ => rw [hrn] at hq; cases hq

/-- The roots of `M` when `r` is a root. -/
theorem roots_M_root (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hrn : par M 0 r = none) :
    roots M = (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) ++ [r] := by
  have hcr := col_r_root hlen hL hp hn hR01 hR12 h00 hrn
  unfold roots
  rw [← hlen, show r + L + 1 = r + (L + 1) by omega, List.range_add, List.filter_append,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  rw [List.filter_cons, if_pos (by simpa using hcr)]
  congr 1
  rw [List.filter_eq_nil_iff]
  intro i hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
  have hq' := List.mem_range.mp hq
  simp only [Function.comp, decide_eq_true_eq]
  exact col0_ne (show entry M 0 (r + (q + 1)) ≠ 0 by
    have := e0_B_gt hlen hL hp (q := q + 1) (by omega) (by omega); omega)

/-- The roots of `N` when `r` is a root: those before `r`, then the copy roots. -/
theorem roots_N_root (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hrn : par M 0 r = none) :
    roots (TRIO.gexp M r L 0 0 n) = (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) ++
      (List.range n).map (fun k => r + k * L) := by
  have hcr := col_r_root hlen hL hp hn hR01 hR12 h00 hrn
  have hlN := lenN0 hlen hn (M := M) (L := L)
  unfold roots
  rw [hlN, List.range_add, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [col_pre0 hlen hL hp hn (by have := List.mem_range.mp hi; omega)]
  · have hblk : ∀ k, k ≤ n → ((List.range (k * L)).map (fun x => r + x)).filter
        (fun i => decide (col (TRIO.gexp M r L 0 0 n) i = (0, 0, 0))) =
        (List.range k).map (fun j => r + j * L) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [Nat.succ_mul, List.range_add, List.map_append, List.filter_append, ih (by omega),
          List.range_succ, List.map_append]
        congr 1
        obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.filter_cons]
        have h0 : col (TRIO.gexp M r (L' + 1) 0 0 n) (r + (k * (L' + 1) + 0)) = (0, 0, 0) := by
          rw [col_copy0 hlen (by omega) (by omega), Nat.add_zero]; exact hcr
        rw [Nat.add_zero] at h0
        rw [if_pos (by simpa using h0)]
        simp only [List.map_singleton, List.cons.injEq]
        rw [List.filter_eq_nil_iff]
        refine ⟨by omega, fun i hi => ?_⟩
        rw [List.map_map, List.map_map] at hi
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        have hq' := List.mem_range.mp hq
        simp only [Function.comp, decide_eq_true_eq]
        have hc := col_copy0 hlen (k := k) (q := q + 1) (n := n) (by omega) (by omega)
        rw [show r + (k * (L' + 1) + (q + 1)) = r + (k * (L' + 1) + Nat.succ q) by rfl] at hc
        rw [hc]
        exact col0_ne (by have := e0_B_gt hlen hL hp (q := q + 1) (by omega) (by omega); omega)
    rw [Nat.mul_comm] at *
    simpa [Nat.mul_comm] using hblk n (le_refl _)

/-- **The root value when `r` is a root**: the root `r` of `M` (value `X`) becomes the copy roots
`O × (n − 1)` and `X′ ≤ O`, with `O · n < X`. -/
theorem root_N_B (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hrn : par M 0 r = none)
    (hn2 : 2 ≤ n) {ρ σ : Valn} {O X' : T}
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsN : ∀ i ∈ roots (TRIO.gexp M r L 0 0 n), Single (σ.o i))
    (hpN : ((roots (TRIO.gexp M r L 0 0 n)).map σ.o).Pairwise (fun a b => b ≤ a))
    (hσG : ∀ i, i < r → σ.o i = ρ.o i)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = O) (hσlast : σ.o (r + (n - 1) * L) = X')
    (hOX : mulT O n < ρ.o r) :
    isOT (root (TRIO.gexp M r L 0 0 n) σ) = true ∧ root (TRIO.gexp M r L 0 0 n) σ < root M ρ := by
  rw [root_eq_roots hsN hpN, root_eq_roots hsM hpM]
  refine ⟨isOT_sumN _ (fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact (hsN i hi).1), ?_⟩
  have hrM := roots_M_root hlen hL hp hn hR01 hR12 h00 hrn
  have hrN := roots_N_root hlen hL hp hn hR01 hR12 h00 hrn
  set RG := (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) with hRG
  have hRGv : RG.map σ.o = RG.map ρ.o := List.map_congr_left (fun i hi => by
    have := List.mem_range.mp (List.mem_filter.mp hi).1; exact hσG i this)
  have hcv : ((List.range n).map (fun k => r + k * L)).map σ.o = List.replicate (n - 1) O ++ [X'] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hσlast
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
      Nat.add_sub_cancel, hσlast]
    congr 1
    rw [List.map_map, List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hsN' : ∀ t ∈ RG.map ρ.o ++ (List.replicate (n - 1) O ++ [X']), Single t := by
    intro t ht
    have : t ∈ (RG ++ (List.range n).map (fun k => r + k * L)).map σ.o := by
      rw [List.map_append, hRGv, hcv]; exact ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp this
    exact hsN i (by rw [hrN]; exact hi)
  have hsM' : ∀ t ∈ RG.map ρ.o ++ [ρ.o r], Single t := by
    intro t ht
    have : t ∈ (RG ++ [r]).map ρ.o := by rw [List.map_append, List.map_singleton]; exact ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp this
    exact hsM i (by rw [hrM]; exact hi)
  rw [hrN, List.map_append, hRGv, hcv] at hpN ⊢
  rw [hrM, List.map_append, List.map_singleton] at hpM ⊢
  rw [sumN_append_dec hsN' hpN, sumN_append_dec hsM' hpM, sumN_singleton (hsM' _ (by simp))]
  apply app_lt_app_left
  have hp2 := (List.pairwise_append.mp hpN).2.1
  have hs2 : ∀ t ∈ List.replicate (n - 1) O ++ [X'], Single t := fun t ht => hsN' t (List.mem_append_right _ ht)
  have hO : Single O := hs2 O (List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
  rw [sumN_append_dec hs2 hp2, sumN_replicate hO, sumN_singleton (hs2 _ (by simp))]
  have hX'O : X' ≤ O := (List.pairwise_append.mp hp2).2.2 O
    (List.mem_replicate.mpr ⟨by omega, rfl⟩) X' (by simp)
  have hle : app (mulT O (n - 1)) X' ≤ mulT O n := by
    rw [show n = (n - 1) + 1 by omega, mulT_succ', Nat.add_sub_cancel]
    rcases (le_iff _ _).mp hX'O with h | h
    · exact le_of_lt (app_lt_app_left _ h)
    · rw [h]
  exact lt_of_le_of_lt hle hOX

end

end Ytosk
