/-
**3 行・t = 0: T0IVRes を構造から証明する。**

g = P_0(r) が r を数え、N = M[n] で中間の写しの根がどれも数えられないとき（とくに k = 0 の r 自身）:
- N で r は数えられないので isUpg N r ∧ topped N r。UAT(N) で r への上げは直前の列 r − 1 から（upg M (r − 1) = r）。
- topped N r は M.take x で topped（topped_copy0）。r の行 2 は 1（上げの的）なので、M.take x での r の子は
  すべて bump（all_bump_of_last）で数えられない。よって M での r の数える子は x だけで o(r) = ψ_{v(r)}(1)。
- 次の列型の上げの的 r には、g の r より前の数える子がある（cnt_before_next_upg）ので状態 B ≠ 0。
- B ≥ 1 = y なので古い枠は r で書き換えない。
-/
import Ytosk.V3T0Res
import Ytosk.V3BumpDrop
import Ytosk.V3T0NoVB

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`T0IVRes` holds.** -/
theorem t0IVRes_holds : T0IVRes := by
  intro M ρ rk r L hM hS I R hlen hL hp he1 n hn2 g hg hcnt hno Lc0 hCL s y hy
  have hn : 1 ≤ n := by omega
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hgr : g < r := par_lt M 0 r g hg
  -- `r` is not counted at `g` in `N`
  have h0 := hno 0 (by omega)
  rw [Nat.zero_mul, Nat.add_zero] at h0
  have hUT : isUpg (TRIO.gexp M r L 0 0 n) r = true ∧ topped (TRIO.gexp M r L 0 0 n) r = true := by
    by_contra hne
    apply h0
    refine ⟨?_, hne⟩
    rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
    exact hcnt.1
  have hTT : topped (M.take (r + L)) r = true := by
    have h := topped_copy0 hlen hL hp hn (k := 0) (q := 0) (by omega) hL
    simp only [Nat.zero_mul, Nat.add_zero] at h
    rw [← h]; exact hUT.2
  -- the upgrade to `r` comes from `r − 1`
  have hSN : SInv (TRIO.gexp M r L 0 0 n) :=
    sInv_std (std_gexp_t0 hM I hlen hL hp he1 n) (ne_SRO_of_rk (rk_N0 hlen hL hp hn I.r0p I.z2 hx2 hn2 I.rank))
  have hU := hUT.1
  unfold isUpg at hU
  obtain ⟨j, _, hju⟩ := List.any_eq_true.mp hU
  have hju' : upg (TRIO.gexp M r L 0 0 n) j = some r := by simpa using hju
  have hj1 : j + 1 = r := by
    by_contra hne
    have := hSN.uat j r hju' (fun h => hne h.symm)
    rw [hUT.2] at this; exact absurd this (by simp)
  have hr0 : 0 < r := by omega
  have huM : upg M (r - 1) = some r := by
    rw [← upg_pre0 hlen hL hp hn (show r - 1 + 1 < r + L by omega), show r - 1 = j by omega]; exact hju'
  -- an earlier counted child of `g`: the state is nonzero
  obtain ⟨c, hcM, hcr, hcc⟩ := cnt_before_next_upg I.r0p I.z2 I.sd I.uat r hr0 huM g hg
  have hcLc : c ∈ Lc0 := by
    have hcCL : c ∈ CL M g := by
      unfold CL; exact List.mem_filter.mpr ⟨hcM, by simpa using hcc⟩
    rw [hCL] at hcCL
    rcases List.mem_append.mp hcCL with h | h
    · exact h
    · simp at h; omega
  have hgM : g < M.length := by omega
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hgM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hLs := sumN_dec (Lc0.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  have hB : spArg (ρ.v g) z (sumN (Lc0.map ρ.o)) ≠ z := by
    apply spArg_ne_z
    right
    intro hz
    have h := hLs.2
    rw [hz] at h
    have hmem : ρ.o c ∈ Lc0.map ρ.o := List.mem_map_of_mem hcLc
    rw [← h] at hmem
    simp [summands] at hmem
  -- the counted children of `r` in `M`: only `x`
  have he2r : entry M 2 r = 1 := by have := upg_target_e2 huM; have := I.z2 r; omega
  have hrL : r < r + L := by omega
  have hbT : ∀ d ∈ children (M.take (r + L)) r, col M d = bump M r := by
    intro d hd
    unfold topped at hTT
    cases hl : (children (M.take (r + L)) r).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hd; simp at hd
    | some ℓ =>
      rw [hl] at hTT
      simp only [decide_eq_true_eq] at hTT
      have hlast : children (M.take (r + L)) r = (children (M.take (r + L)) r).dropLast ++ [ℓ] := by
        rw [List.dropLast_append_getLast? _ hl]
      have hall := all_bump_of_last (R0P_take I.r0p (r + L)) (Z2_take I.z2 (r + L)) (SibDec_take I.sd (r + L))
        (Z1C_take I.z1 (r + L)) (by rw [entry_take M 2 hrL]; exact he2r) hlast hTT d hd
      have hdx := (mem_children_take hd).1
      rwa [col_take M hdx, bump_take M hrL] at hall
  have hCLr : CL M r = [] ++ [r + L] := by
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    have hsplit := split_last_max _ _ (children_sorted M r) hxr
      (fun d hd => by have := (mem_children hd).2; omega)
    unfold CL
    rw [hsplit, List.filter_append]
    have hxc : Counted M r (r + L) := by
      refine ⟨fun h => ?_, fun h => by rw [isUpg_x0 hlen hL hp hx2] at h; exact absurd h.1 (by simp)⟩
      have := congrArg (fun t => t.2.2) h
      simp [col_eq_entries, bump] at this; omega
    rw [List.filter_eq_nil_iff.mpr]
    · simp [hxc]
    · intro d hd hcd
      rw [List.mem_filter] at hd
      have hdx : d < r + L := by simpa using hd.2
      have hdT : d ∈ children (M.take (r + L)) r := by
        rw [children_take, List.mem_filter]; exact ⟨hd.1, by simpa using hdx⟩
      exact (of_decide_eq_true hcd).1 (hbT d hdT)
  have hrM : r < M.length := by omega
  have hox := o_x_one0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.cons I.good
  have hsMr : ∀ d ∈ CL M r, Single (ρ.o d) := fun d hd => single_o I.cons I.good
    (mem_children (cl_mem_children hd)).2
  have hor := o_last_form I.cons hrM (I.good.ot_v r hrM) hCLr hsMr (cl_vals I.cons I.good hrM).2
    (show ρ.o (r + L) = psi z z z from hox)
  have hst : step (ρ.v r) (spArg (ρ.v r) z (sumN (([] : List Nat).map ρ.o))) z z z = one := by
    show step (ρ.v r) z z z z = one
    unfold step; rw [if_neg (fun h => T.not_lt_z _ h.1)]; rfl
  rw [hst] at hor
  rw [hor] at hy
  simp only [psi.injEq] at hy
  rw [← hy.2.1]
  rintro ⟨h1, _⟩
  exact hB (lt_one_iff.mp h1)

end Ytosk
