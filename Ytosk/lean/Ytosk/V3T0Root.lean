/-
**3 行・t = 0: 展開 N = M[n] の評価の根の並び（RootP）。**

根の値の並びが減ること:
- r に親がある: N と M の根は同じ（r 以後の列は行 0 が正）。値が変わるのは x の祖先の根だけで、それは最後の根
  （x の祖先でない根は C に入らない: その部分木の次の列は根で、上げの的になれない `root_chg_anc`）。
- r が根: N の根は r より前の根とコピーの根。値は M の根、omid × (n − 1)、最後に o′(r)。
-/
import Ytosk.V3T0FO

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem col_ne0 {N : Mat} {i : Nat} (h : entry N 0 i ≠ 0) : col N i ≠ (0, 0, 0) := by
  intro hc
  rw [col_eq_entries] at hc
  simp only [Prod.mk.injEq] at hc
  exact h hc.1

/-- The column after the subtree of a root is a root. -/
theorem e0_zero_of_nextC {M : Mat} {R c' : Nat} (hR : entry M 0 R = 0) (hN : NextC M R c') :
    entry M 0 c' = 0 := by
  by_contra h
  obtain ⟨p, hp⟩ := par0_some_of (M := M) hN.1 (by omega)
  obtain ⟨hpc, _, hbet⟩ := (par0_spec M).mp hp
  rcases Nat.lt_or_ge p R with hpR | hpR
  · have := hbet R hpR hN.1; omega
  · exact hN.2.2 (Anc0.step hp (hN.2.1 p hpR hpc))

/-- **A changed root is an ancestor of `x − 1`.** -/
theorem root_chg_anc {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR01 : R01 M) (hR12 : R12 M) {R : Nat} (hRx : R < x) (hcol : col M R = (0, 0, 0))
    (hC : ChgX M x true R) : Anc0 M R (x - 1) := by
  by_contra hn
  obtain ⟨c', hN, _, hup, _⟩ := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).2 R hRx (Anc0.refl R) hn
  have he0R : entry M 0 R = 0 := by
    have : entry M 0 R = (col M R).1 := rfl
    rw [this, hcol]
  have he0 := e0_zero_of_nextC he0R hN
  have he2 := upg_target_e2 hup
  have := hR12 _ (hR01 _ he0)
  omega

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

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

/-- **The roots of `N` and `M` agree when `r` has a parent**: they are before `r`. -/
theorem roots_N_par (hR0 : R0P M) {g : Nat} (hg : par M 0 r = some g) :
    roots (TRIO.gexp M r L 0 0 n) = roots M := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have he0r : 0 < entry M 0 r := by have := hR0 r g hg; omega
  have hAx : Anc0 M r (r + L) := Anc0.step hp (Anc0.refl r)
  have hposM : ∀ q, q ≤ L → col M (r + q) ≠ (0, 0, 0) := by
    intro q hq
    apply col_ne0
    have hA := anc_between hAx (r + q) (by omega) (by omega)
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simpa using (by omega : entry M 0 r ≠ 0)
    · have := anc0_e0_lt hA (by omega); omega
  have hpre : ∀ i, i < r → col (TRIO.gexp M r L 0 0 n) i = col M i := fun i hi =>
    col_pre0 hlen hL hp hn (by omega)
  have eN : roots (TRIO.gexp M r L 0 0 n) = (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) := by
    unfold roots
    rw [hlN, List.range_add, List.filter_append]
    have h1 : ((List.range r).filter fun i => decide (col (TRIO.gexp M r L 0 0 n) i = (0, 0, 0))) =
        (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) :=
      List.filter_congr (fun i hi => by rw [hpre i (List.mem_range.mp hi)])
    have h2 : ((List.range (n * L)).map (fun x => r + x)).filter
        (fun i => decide (col (TRIO.gexp M r L 0 0 n) i = (0, 0, 0))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi
      have ht' := List.mem_range.mp ht
      have hk : t / L < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hq : t % L < L := Nat.mod_lt _ hL
      have ht2 : t = t / L * L + t % L := by
        have := Nat.div_add_mod t L; rw [Nat.mul_comm] at this; omega
      simp only [decide_eq_true_eq]
      rw [ht2, col_copy0 hlen hk hq]
      exact hposM _ (by omega)
    rw [h1, h2, List.append_nil]
  have eM : roots M = (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) := by
    unfold roots
    rw [show M.length = r + (L + 1) by omega, List.range_add, List.filter_append]
    have h2 : ((List.range (L + 1)).map (fun x => r + x)).filter
        (fun i => decide (col M i = (0, 0, 0))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
      simp only [decide_eq_true_eq]
      exact hposM q (by have := List.mem_range.mp hq; omega)
    rw [h2, List.append_nil]
  rw [eN, eM]

/-- **The root order of `N = M[n]`** (`t = 0`). -/
theorem rootP_N_t0 (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M) (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    {ρ σ ρ' : Valn} (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hoffD : ∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hσG0 : par M 0 r = none → ∀ i, i < r → σ.o i = ρ.o i)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hOX : omid M r L ρ ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ) :
    ((roots (TRIO.gexp M r L 0 0 n)).map σ.o).Pairwise (fun a b => b ≤ a) := by
  have hx : r + L + 1 = M.length := hlen
  have hAx : Anc0 M r (r + L) := Anc0.step hp (Anc0.refl r)
  cases hrg : par M 0 r with
  | some g =>
    rw [roots_N_par hlen hL hp hn hR0 hrg]
    have he0r : 0 < entry M 0 r := by have := hR0 r g hrg; omega
    have hroot : ∀ R ∈ roots M, R < M.length ∧ col M R = (0, 0, 0) := fun R hR => by
      unfold roots at hR
      have h := List.mem_filter.mp hR
      exact ⟨List.mem_range.mp h.1, by simpa using h.2⟩
    have he0 : ∀ R ∈ roots M, entry M 0 R = 0 := fun R hR => by
      have : entry M 0 R = (col M R).1 := rfl
      rw [this, (hroot R hR).2]
    have hRr : ∀ R ∈ roots M, R < r := by
      intro R hR
      by_contra h
      have hA := anc_between hAx R (by omega) (by have := (hroot R hR).1; omega)
      rcases Nat.eq_zero_or_pos (R - r) with h1 | h1
      · have : R = r := by omega
        subst this; have := he0 _ hR; omega
      · have := anc0_e0_lt hA (by omega); have := he0 R hR; omega
    apply pairwise_lower_last (P := fun R => DepX M (r + L) true R)
      (List.Pairwise.filter _ List.pairwise_lt_range) hpM
    · intro R hR hD R' hR' hRR'
      have hRx := hRr R hR
      have hanc := root_chg_anc hx hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 (by omega) (hroot R hR).2
        (depX_chgX hD)
      have hR'x : R' ≤ r + L - 1 := by have := hRr R' hR'; omega
      have hA' := anc_between hanc R' (by omega) hR'x
      have := anc0_e0_lt hA' (by omega)
      have := he0 R' hR'
      omega
    · intro R hR hD; exact hoffD R (hRr R hR) hD
    · intro R hR hD; exact hdl R (hRr R hR) hD
  | none =>
    rw [roots_N_root hlen hL hp hn hR01 hR12 h00 hrg, List.map_append]
    rw [roots_M_root hlen hL hp hn hR01 hR12 h00 hrg, List.map_append, List.map_singleton] at hpM
    set F := (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) with hF
    have hFv : F.map σ.o = F.map ρ.o := List.map_congr_left (fun i hi => by
      rw [hF, List.mem_filter, List.mem_range] at hi
      exact hσG0 hrg i hi.1)
    have hmapN : ((List.range n).map (fun k => r + k * L)).map σ.o =
        List.replicate (n - 1) (omid M r L ρ) ++ [ρ'.o r] := by
      have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
        rw [← List.range_succ]; congr 1; omega
      rw [hr, List.map_append, List.map_append]
      congr 1
      · rw [List.map_map, List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
        exact hσmid k (by have := List.mem_range.mp hk; omega)
      · simp only [List.map_cons, List.map_nil]; rw [hσlast]
    rw [hFv, hmapN]
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_append.mpr
      ⟨List.pairwise_replicate.mpr (Or.inr (le_refl _)), by simp, fun a ha b hb => ?_⟩,
      fun a ha b hb => ?_⟩
    · simp at hb; rw [hb, (List.mem_replicate.mp ha).2]; exact hO'le
    · have hra := hp1.2.2 a ha (ρ.o r) (by simp)
      rcases List.mem_append.mp hb with hb | hb
      · rw [(List.mem_replicate.mp hb).2]; exact le_trans hOX hra
      · simp at hb; rw [hb]; exact le_trans hO'le (le_trans hOX hra)

end

end Ytosk
