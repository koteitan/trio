/-
**3 行・t = 0: 最後のコピーの根は数えられる（`counted_last0`）。**

N = gexp M r L 0 0 n（n ≥ 2）で、c = r + (n − 1)L は最後のコピーの根。M で r が数えられるなら N で c も数えられる。
- 列は r の写し、bump は M と同じなので、1 つ目の条件は M のまま。
- c が上げの的になるのは、前のコピーの最後の列 c − 1（M の x − 1 から r への上げ）か、最後のコピーの列 c + q
  （M の r + q から r への上げ）からだけ。
- どちらも M の B の列 r + q（0 < q < L）から r への上げになる。そのとき r の行 2 は 1 で、r + q の祖先である r の子 c1 は
  Z1C（行 1 ≤ r の行 1）と SibDec（M.take x の最後の子 = bump 以上）で bump になり、UAB に反する。
  したがって r は M.take x で topped でない（`upg_r_not_topped`）。
-/
import Ytosk.V3T0S

namespace Ytosk

open T

/-- **An upgrade from inside `B` to `r` makes `r` not topped in `M.take x`.** -/
theorem upg_r_not_topped {M : Mat} {r L q : Nat} (hlen : r + L + 1 = M.length)
    (hp : par M 0 (r + L) = some r) (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hUAB : UAB M) (hq0 : 0 < q) (hq : q < L) (hu : upg M (r + q) = some r) :
    topped (M.take (r + L)) r = false := by
  have he2r : entry M 2 r = 1 := le_antisymm (hZ2 r) (upg_target_e2 hu)
  have hA : Anc0 M r (r + q) :=
    anc_between (anc0_of_par M 0 r (r + L) hp) (r + q) (by omega) (by omega)
  obtain ⟨c1, hc1p, hc1A⟩ := anc0_child hA (by omega)
  have hc1le := hc1A.le
  have hc1M : c1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hc1p⟩
  have hc1T : c1 ∈ children (M.take (r + L)) r := by
    rw [children_take, List.mem_filter]; exact ⟨hc1M, by simp; omega⟩
  unfold topped
  cases hl : (children (M.take (r + L)) r).getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hc1T; simp at hc1T
  | some c0 =>
    simp only [decide_eq_false_iff_not]
    intro hcb
    have hc0T := List.mem_of_getLast? hl
    rw [children_take, List.mem_filter] at hc0T
    have hc0M := hc0T.1
    have hc0x : c0 < r + L := by simpa using hc0T.2
    rw [col_take M hc0x, bump_take M (by omega)] at hcb
    -- `c1 ≤ c0`: `c0` is the last child before `x`
    have hc1c0 : c1 ≤ c0 := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
      have hs := children_sorted (M.take (r + L)) r
      rw [hys] at hc1T hs
      rcases List.mem_append.mp hc1T with h | h
      · exact le_of_lt ((List.pairwise_append.mp hs).2.2 c1 h c0 (by simp))
      · simp at h; omega
    -- `c1` is a bump child of `r`
    have hcol1 : col M c1 = bump M r := by
      have he0 := hR0 c1 r hc1p
      have hz1 := hZ1 r c1 he2r hc1M
      have hz2 := hZ2 c1
      rcases Nat.lt_or_ge c1 c0 with hlt | hge
      · obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hc1M
        have hle : colLe (col M c0) (col M c1) := by
          apply sib_le hSD l₂ l₁ c1 hsplit c0
          have hs := children_sorted M r
          rw [hsplit] at hs hc0M
          rcases List.mem_append.mp hc0M with h' | h'
          · exfalso; have := (List.pairwise_append.mp hs).2.2 c0 h' c1 (by simp); omega
          · simp only [List.mem_cons] at h'
            rcases h' with h' | h'
            · omega
            · exact h'
        rw [hcb] at hle
        unfold colLe bump at hle
        simp only [col_eq_entries] at hle
        simp only [col_eq_entries, bump, Prod.mk.injEq]
        refine ⟨by omega, by omega, by omega⟩
      · have : c1 = c0 := by omega
        rw [this]; exact hcb
    exact hUAB (r + q) r hu (by omega) c1 hc1M hcol1 hc1A

/-- **The root of the last copy is counted** when `r` is counted in `M` (`t = 0`, `n ≥ 2`). -/
theorem counted_last0 {M : Mat} {r L n g : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) (hR0 : R0P M) (hZ2 : Z2 M)
    (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M) (hR12 : R12 M) (hn2 : 2 ≤ n)
    (hg : par M 0 r = some g) (hc : Counted M g r) :
    Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L) := by
  have he2 : entry M 2 (r + L) = 0 := hR12 _ he1
  have hn : 1 ≤ n := by omega
  have hgr : g < r := par_lt M 0 r g hg
  have hnL : (n - 1) * L + L = n * L := by
    rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  have hnL2 : (n - 2) * L + L = (n - 1) * L := by
    rw [← Nat.succ_mul, show (n - 2).succ = n - 1 by omega]
  have hLle : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hcN : col (TRIO.gexp M r L 0 0 n) (r + (n - 1) * L) = col M r := by
    have := col_copy0 hlen (k := n - 1) (q := 0) (by omega) hL (M := M) (n := n)
    simpa using this
  have hbN : bump (TRIO.gexp M r L 0 0 n) g = bump M g := bump_pre0 hlen hL hp hn (by omega)
  refine ⟨by rw [hcN, hbN]; exact hc.1, ?_⟩
  rintro ⟨hU, hT⟩
  have hT' : topped (TRIO.gexp M r L 0 0 n) (r + (n - 1) * L) = topped (M.take (r + L)) r := by
    have := topped_copy0 hlen hL hp hn (k := n - 1) (q := 0) (by omega) hL (M := M)
    simpa using this
  rw [hT'] at hT
  -- an upgrade from `B` to `r` would make `r` not topped
  have hno : ∀ q, 0 < q → q < L → upg M (r + q) ≠ some r := by
    intro q hq0 hq hu
    rw [upg_r_not_topped hlen hp hR0 hZ2 hSD hZ1 hUAB hq0 hq hu] at hT
    cases hT
  unfold isUpg at hU
  rw [List.any_eq_true] at hU
  obtain ⟨j, hj, hu⟩ := hU
  have hjN := List.mem_range.mp hj
  rw [hlN] at hjN
  have hu' : upg (TRIO.gexp M r L 0 0 n) j = some (r + (n - 1) * L) := by simpa using hu
  obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
  rcases hcase with hnext | ⟨_, hlt⟩
  · -- from the last column of the previous copy: `x − 1` upgrades to `r` in `M`
    have hj' : j = r + ((n - 2) * L + (L - 1)) := by omega
    rw [hj', upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 (k := n - 2) (by omega)] at hu'
    cases hU' : upg M (r + (L - 1)) with
    | none => rw [hU'] at hu'; cases hu'
    | some t =>
      rw [hU'] at hu'
      simp only [Option.map_some, Option.some.injEq] at hu'
      split at hu'
      · rename_i htr
        subst htr
        by_cases hL1 : L = 1
        · subst hL1
          obtain ⟨_, _, _, _, h⟩ := upg_spec hU'
          omega
        · exact hno (L - 1) (by omega) (by omega) hU'
      · -- `t` is a target of `x − 1`, so `t ≤ x − 1` (the next column `x` has row 2 equal to `0`)
        have ht2 := upg_target_e2 hU'
        obtain ⟨_, _, _, _, h⟩ := upg_spec hU'
        rcases h with h | ⟨_, h⟩
        · rw [show r + (L - 1) + 1 = r + L by omega] at h
          rw [h] at ht2; omega
        · omega
  · -- from inside the last copy
    have hj' : j = r + ((n - 1) * L + (j - (r + (n - 1) * L))) := by omega
    by_cases hq1 : j - (r + (n - 1) * L) + 1 < L
    · rw [hj', upg_copy0 hlen hL hp hn (k := n - 1) (by omega) hq1] at hu'
      cases hU' : upg M (r + (j - (r + (n - 1) * L))) with
      | none => rw [hU'] at hu'; cases hu'
      | some t =>
        rw [hU'] at hu'
        simp only [Option.map_some, Option.some.injEq] at hu'
        have htr : t = r := by unfold shk at hu'; split at hu' <;> omega
        rw [htr] at hU'
        exact hno _ (by omega) (by omega) hU'
    · have hjl : j = r + ((n - 1) * L + (L - 1)) := by omega
      rw [hjl, upg_none_last0 hlen hL hp hn] at hu'
      cases hu'

end Ytosk
