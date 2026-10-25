/-
**最初の写しの根は M[n] でも数える（2026-10-25、Bad2・t = 0 の r ≠ x − 1 用）。**

旧の `counted_first0` は r の行 2 = 0（r は上げの的にならない）を仮定していた。r の行 2 = 1 の場合も、r を上げ先にできる
列を調べると（`counted_last0` と同じ議論）、残るのは列 r − 1 からの上げ（上げ先 = r − 1 + 1）だけになる:
- bad part の中の列 r + q（0 < q < L）から r への上げは、r を `M.take x` で topped でなくする（`upg_r_not_topped`）。
- 後ろの写しの列の上げ先は写されて r にならない（`upg_copy0` の `shk`、`upg_copy_last0`）。
- 上げ先が自分自身になることはない（`upg_spec`）。
-/
import Ytosk.V3T0BadS2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The first copy root counts at `g` in `N`** when it does in `M`, unless `r − 1` upgrades to `r` while `r` is
topped in `M.take x`. -/
theorem counted_first0G {M : Mat} {r L n g : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (hn2 : 2 ≤ n) (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hUAB : UAB M) (he2 : entry M 2 (r + L) = 0)
    (hg : par M 0 r = some g) (hc : Counted M g r)
    (hT : topped (M.take (r + L)) r = true → upg M (r - 1) ≠ some r) :
    Counted (TRIO.gexp M r L 0 0 n) g r := by
  have hn : 1 ≤ n := by omega
  have hgr : g < r := par_lt M 0 r g hg
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hcN : col (TRIO.gexp M r L 0 0 n) r = col M r := by
    have := col_copy0 hlen (k := 0) (q := 0) (by omega) hL (M := M) (n := n)
    simpa using this
  have hbN : bump (TRIO.gexp M r L 0 0 n) g = bump M g := bump_pre0 hlen hL hp hn (by omega)
  refine ⟨by rw [hcN, hbN]; exact hc.1, ?_⟩
  rintro ⟨hU, hTN⟩
  have hTT : topped (M.take (r + L)) r = true := by
    have := topped_copy0 hlen hL hp hn (k := 0) (q := 0) (by omega) hL (M := M)
    simp only [Nat.zero_mul, Nat.add_zero] at this
    rw [← this]; exact hTN
  -- no upgrade from inside `B` to `r`
  have hno : ∀ q, 0 < q → q < L → upg M (r + q) ≠ some r := by
    intro q hq0 hq hu
    rw [upg_r_not_topped hlen hp hR0 hZ2 hSD hZ1 hUAB hq0 hq hu] at hTT
    cases hTT
  have hself : ∀ j, upg M j ≠ some j := by
    intro j hu
    obtain ⟨_, _, _, _, h⟩ := upg_spec hu
    omega
  unfold isUpg at hU
  obtain ⟨j, hj, hu⟩ := List.any_eq_true.mp hU
  have hjN := List.mem_range.mp hj
  rw [hlN] at hjN
  have hu' : upg (TRIO.gexp M r L 0 0 n) j = some r := by simpa using hu
  rcases Nat.lt_or_ge (j + 1) (r + L) with h | h
  · rw [upg_pre0 hlen hL hp hn h] at hu'
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
    rcases hcase with hnext | ⟨_, hlt⟩
    · exact hT hTT (by rw [show r - 1 = j by omega]; exact hu')
    · exact hno (j - r) (by omega) (by omega) (by rw [show r + (j - r) = j by omega]; exact hu')
  · obtain ⟨k, q, hk, hq, hjkq⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hjN
    by_cases hq1 : q + 1 < L
    · rw [hjkq, upg_copy0 hlen hL hp hn hk hq1] at hu'
      cases hUt : upg M (r + q) with
      | none => rw [hUt] at hu'; cases hu'
      | some t =>
        rw [hUt] at hu'
        simp only [Option.map_some, Option.some.injEq] at hu'
        unfold shk at hu'
        split at hu'
        · have hk0 : k * L = 0 := by omega
          have htr : t = r := by omega
          rw [htr] at hUt
          rcases Nat.eq_zero_or_pos q with hq0 | hq0
          · subst hq0; exact hself r (by simpa using hUt)
          · exact hno q hq0 (by omega) hUt
        · omega
    · have hqL : q = L - 1 := by omega
      rw [hqL] at hjkq
      by_cases hkn : k + 1 < n
      · rw [hjkq, upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 hkn] at hu'
        cases hUt : upg M (r + (L - 1)) with
        | none => rw [hUt] at hu'; cases hu'
        | some t =>
          rw [hUt] at hu'
          simp only [Option.map_some, Option.some.injEq] at hu'
          split at hu'
          · have : (k + 1) * L ≥ L := Nat.le_mul_of_pos_left L (by omega)
            omega
          · rename_i htne; exact htne hu'
      · have hk1 : k = n - 1 := by omega
        rw [hjkq, hk1, upg_none_last0 hlen hL hp hn] at hu'; cases hu'

/-- **Residual: the hard seeds of a `Bad2` matrix at `t = 0`, all at the `M` level** (2026-10-25): the two component
facts of `T0BadSeedsH6`, and for `r ≠ x − 1` with `r` counted at `g` and topped in `M.take x`: `r − 1` does not upgrade
to `r` (`counted_first0G`). -/
def T0BadSeedsH7 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ g pp, par M 0 r = some g → par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 →
      col M g = bump M pp →
      Lhd z ((drop1 M (r + L) rk).o r) (ρ.o r) ∨
        ∀ w', (drop1 M (r + L) rk).o r = psi w' z z →
          ∀ u, ¬ w' < u → ∀ e ∈ comps u w', ∃ d ∈ z :: comps u (ρ.v r), e ≤ d) ∧
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 →
      LhdE (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o)))
          (omega (sumN ((children (M.take (r + L)) r).map ρ.o))) ∨
        ∀ s b', omega (sumN ((children (M.take (r + L)) r).map ρ.o)) = psi s b' z →
          ∀ u, ∀ e ∈ comps u (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o))),
            ∃ d ∈ z :: b' :: (comps u b' ++ comps u s), e ≤ d) ∧
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → Counted M g r → topped (M.take (r + L)) r = true →
      upg M (r - 1) ≠ some r)

theorem t0BadSeedsH6_of (h7 : T0BadSeedsH7) : T0BadSeedsH6 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  obtain ⟨hS3, hS2, hup⟩ := h7 M ρ rk hM hS hB I r L hlen hL hp he1
  have S := sInv_std hM hS
  refine ⟨hS3, hS2, fun n hn2 σ _ g hg hrx hc => ?_⟩
  exact counted_first0G hlen hL hp hn2 S.r0p S.z2 S.sibDec S.z1c S.uab (S.r12 _ he1) hg hc (hup g hg hrx hc)

end Ytosk
