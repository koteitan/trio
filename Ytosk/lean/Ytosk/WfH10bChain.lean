/-
**H10 を最上位から外す（2026-10-29）。**

`T0BadSeedsH10Big`（r − 1 が r へ上げないこと）は標準形の Bad2 の行列で偽（WfH10Cex）。それを使っていたのは
`t0_S1N_cnt`（V3T0BadNode）の「r は M[n] でも g で数える」だけだった。`t0_S1N_cnt` を作り直したので
（v(r) > v(g) の枝は数える写しが 0 個でもよい `t0_S1AW_nodeHi`、v(r) ≤ v(g) の枝では r − 1 → r の上げが
起きない `v_par0_lt_of_upg_prev`）、`T0BadSeedsH6` の数える欄は `counted_first0G` で構造から出る。
ここでは `T0BadSeedsH6` の残りの 2 欄（`T0BadSeedsH7W`）を `HDropU` と `HUAC` だけから出す
（`t0BadSeedsH7_of`・`t0BadSeedsH8_of`・`t0BadSeedsH9_of` の第 3 欄以外の部分の写し）。
-/
import Ytosk.V3T0SeedSum

namespace Ytosk.WfH10b

open T

/-- **The component fields of the `t = 0` `Bad2` seeds from `HDropU` and `HUAC` alone** (no preceding-upgrade
residual). -/
theorem t0BadSeedsH7W_of (hDU : HDropU) (hU : HUAC) : T0BadSeedsH7W := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  have S := sInv_std hM hS
  obtain ⟨SX, SJ⟩ := sInvXJ_std hM hS
  obtain ⟨R, _⟩ := hDU M ρ rk hM hS (by intro h; subst h; simp at hlen) I
  have hx : (r + L) + 1 = M.length := hlen
  have hcnt := counted_take_last (M := M) (show 1 ≤ M.length by omega)
    S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hT := cons_of_rk hRT
  rw [show M.length - 1 = r + L by omega] at R
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV M ρ (drop1 M (r + L) rk) i :=
    drop_all_hardB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hT hRT I.vs R.vst I.fc I.fo
      R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hT hRT I.kd I.td R.ab R.ws) R.ua
  refine ⟨fun g pp hg hpp h1p h2p hgb => ?_, fun g hg hrx hrb h1g h2g => ?_⟩
  · by_cases hs : L = 1 ∧ ∃ k, upg M r = some k ∧ k < r
    · obtain ⟨hL1, k, hk, hkr⟩ := hs
      subst hL1
      right
      intro w' hw' u _ e he
      obtain ⟨_, ho⟩ := lost_upg_take hM hS I (x := r + 1) (by omega) rfl hk
      rw [ho] at hw'
      simp only [psi.injEq] at hw'
      rw [← hw'.1] at he
      rcases dom_add_one (hU M ρ rk hM hS I.cons I.rank I.good r k hk hkr) u e he with h | ⟨d, hd, hed⟩
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      · exact ⟨d, List.mem_cons_of_mem _ hd, hed⟩
    · left
      apply T0SeedOutside.seed_lhd_outside S SX.loc.2.2.2 SJ I.cons I.good hx hp hg hpp hgb he1 ?_ hT hRT hdrop
      rintro ⟨hr, k, hk, hkr⟩
      exact hs ⟨by omega, k, hk, hkr⟩
  · by_cases hs : children (M.take (r + L)) r = [r + L - 1] ∧ ∃ k, upg M (r + L - 1) = some k ∧ k < r + L - 1
    · obtain ⟨hch, k, hk, hkx⟩ := hs
      right
      have S := sInv_std hM hS
      obtain ⟨hv', ho'⟩ := lost_upg_take hM hS I (x := r + L) (r := r + L - 1) (by omega) (by omega) hk
      -- `x − 1` has no children in `M` (`x` is a child of `r ≠ x − 1`)
      have hchM : children M (r + L - 1) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc
        have hcl := mem_children hc
        have hcx : c = r + L := by omega
        have hpc := (mem_children_iff.mp hc).2
        rw [hcx, hp] at hpc
        exact hrx (Option.some.inj hpc)
      have hvot : isOT (ρ.v (r + L - 1)) = true := I.good.ot_v _ (by omega)
      have hoM := o_nochild I.cons (by omega) hchM hvot
      have hVot : isOT (add (vOpt ρ (par M 1 (r + L - 1))) one) = true :=
        isOT_add (vOpt_ot I.good (by omega)) isOT_one
      have hw0 : add (vOpt ρ (par M 1 (r + L - 1))) one ≠ z := by
        intro h
        have := congrArg last h
        rw [show one = psi z z z from rfl, last_add_W ⟨z, z, rfl⟩] at this
        cases this
      have hvz : ρ.v (r + L - 1) ≠ z := v_ne_z_of_e1 I.cons (by omega) (upg_e12 hk).1
      rw [hch]
      simp only [List.map_cons, List.map_nil]
      rw [sumN_singleton (single_o I.cons I.good (by omega)), hoM, omega_psi_zz hvz (isOT_psi_zz hvot)]
      intro s b' hsb u e he
      simp only [psi.injEq] at hsb
      obtain ⟨rfl, rfl, -⟩ := hsb
      rw [sumN_singleton ⟨by rw [ho']; exact isOT_psi_zz hVot, _, _, ho'⟩, ho',
        omega_psi_zz hw0 (isOT_psi_zz hVot)] at he
      rcases comps_psi_zz he with h | he
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      rcases dom_add_one (hU M ρ rk hM hS I.cons I.rank I.good (r + L - 1) k hk hkx) u e he with h | ⟨d, hd, hed⟩
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      · exact ⟨d, by simp [hd], hed⟩
    · left
      apply T0SeedSum.seed_sum_lhd hU hM hS I hx ?_ hrb h1g h2g ?_ hrx hs hT hRT hdrop
      · exact mem_children_iff.mpr ⟨by have := par_lt M 0 (r + L) r hp; omega, hg⟩
      · exact mem_children_iff.mpr ⟨by omega, hp⟩

end Ytosk.WfH10b
