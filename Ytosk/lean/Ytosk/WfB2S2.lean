/-
**B2StepAb を構造の残りと値の残りに分ける（2026-10-31, WfB2S）。**

`B2StepAb` の枠（Bad2、n = x − 1 が祖先 k < n へ上げる、m = P₀ k、v(m) のある加数 r < W = bumpW(k)、
j = 子を持つ最後の bump 子、c = j の最初の子、a = m の行 1 の鎖で行 1 が c と同じ列）。行 1 の親は 1 段ずつ（R1S）なので
鎖の a より上で m 以下の列 y は、e1 c + 1 ≥ e1 m なら y = m だけ（そのとき e1 c + 1 = e1 m）。
- `B2LevS`（構造だけ、値なし）: P₀ n が bump 子なら、bump 子の子がすべて行 1 = 0 か、e1 m ≤ e1 c + 1。
- `B2UpgV`（値）: e1 c + 1 = e1 m で m が t へ上げるなら W ≤ last v(t)。このとき v(m) = v(P₁ m) + last v(t) の
  加数はすべて last v(t) 以上なので、吸収（r < W）は起きない。
`b2StepAb_of : B2LevS → B2UpgV → WfB2S.B2StepAb`（StepDom の前件は矛盾になる）。

測定（tmp/wf/WfB2S/fr6.py、P₀ n が bump 子、Bad2 を仮定せず、すべての位置 n）: B2LevS・B2UpgV とも例外 0。
-/
import Ytosk.WfB2S

namespace Ytosk.WfB2S

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Every summand of `V + ψ_s(b)` is at least `ψ_s(b)`. -/
theorem summands_add_ge {s b : T} : ∀ (V : T), ∀ r ∈ summands (add V (psi s b z)), ¬ r < psi s b z
  | z, r, hr => by
    simp only [add, summands, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact lt_irrefl' _
  | psi a a' c, r, hr => by
    by_cases hlt : psi a a' z < psi s b z
    · have hadd : add (psi a a' c) (psi s b z) = psi s b z := by
        simp only [add, if_pos (show lt (psi a a' z) (psi s b z) = true from hlt)]
      rw [hadd] at hr
      simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact lt_irrefl' _
    · have hadd : add (psi a a' c) (psi s b z) = psi a a' (add c (psi s b z)) := by
        simp only [add, if_neg (show ¬ lt (psi a a' z) (psi s b z) = true from hlt)]
      rw [hadd] at hr
      simp only [summands, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hlt
      · exact summands_add_ge c r hr

/-- The last summand is `0` or a single term. -/
theorem last_form : ∀ X : T, last X = z ∨ ∃ a b, last X = psi a b z
  | z => Or.inl rfl
  | psi a b z => Or.inr ⟨a, b, rfl⟩
  | psi _ _ (psi c d e) => last_form (psi c d e)

/-- **Structural residual** (no values): at `n = x − 1` upgrading to an ancestor `k` (`m = P₀ k`) with the row-0
parent of `n` a bump child, either every child of a bump child of `k` has row 1 equal to `0`, or the last bump child
`j` of `k` with children has a first child `c` with `e1 m ≤ e1 c + 1` (the level of `c` on the chain of `m` is `m`
or `P₁ m`). -/
def B2LevS : Prop :=
  ∀ M, Std M → M ≠ SRO → ∀ n, n + 2 = M.length → ∀ k m p g, upg M n = some k → k < n →
    par M 0 k = some m → par M 0 n = some p → par M 0 p = some g → col M p = bump M g →
    (∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, entry M 1 c = 0) ∨
    ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧
      (∀ d ∈ R, col M d = bump M k → children M d = []) ∧ children M j = c :: C ∧
      entry M 1 m ≤ entry M 1 c + 1

/-- **Value residual**: in that frame, when `c` sits one level below `m` and `m` upgrades to `t`, the bump term of `k`
is at most the increment `last v(t)` (measured: equal or smaller in every frame). -/
def B2UpgV : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ n, n + 2 = M.length → ∀ k m, upg M n = some k →
    k < n → par M 0 k = some m →
    ∀ L j R c C, children M k = L ++ j :: R → col M j = bump M k →
      (∀ d ∈ R, col M d = bump M k → children M d = []) → children M j = c :: C →
      entry M 1 c + 1 = entry M 1 m → ∀ t, upg M m = some t → bumpW M ρ k ≤ last (ρ.v t)

theorem b2StepAb_of (hS : B2LevS) (hV : B2UpgV) : B2StepAb := by
  intro M ρ rk hM hS' hB I n hn k m hu hk hkm hab
  have S := sInv_std hM hS'
  have hnN : n < M.length := by omega
  obtain ⟨p, g, hp, hg, hpg, _⟩ := hB.2
  have hn2 : M.length - 2 = n := by omega
  rw [hn2] at hp
  rcases hS M hM hS' n hn k m p g hu hk hkm hp hg hpg with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hCc, hle⟩
  · exact Or.inl (WfH7W2.lev_bumpW_zero I.cons I.good h0)
  refine Or.inr ⟨L, j, R, c, C, hL, hjb, hR, hCc, ?_⟩
  intro a ha hae y h1 h2 hne t ht
  exfalso
  have hya : entry M 1 a < entry M 1 y :=
    WfHUACDeep.up1_hi h1 y (WfHUACDeep.up1_anc0 h1) (Anc0.refl y) hne
  have hym : entry M 1 y ≤ entry M 1 m := WfHUACDeep.up1_e1_le h2
  have hy : y = m := by
    by_contra hym'
    have := WfHUACDeep.up1_hi h2 m (WfHUACDeep.up1_anc0 h2) (Anc0.refl m) (Ne.symm hym')
    omega
  subst hy
  have hcm : entry M 1 c + 1 = entry M 1 y := by omega
  have hWL := hV M ρ rk hM hS' hB I n hn k y hu hk hkm L j R c C hL hjb hR hCc hcm t ht
  obtain ⟨r, hr, hrW⟩ := hab
  -- the value of `y = m`
  have hkN := upg_lt hnN hu
  have hyN : y < M.length := by have := par_lt M 0 k y hkm; omega
  obtain ⟨h1y, h2y'⟩ := upg_e12 ht
  have h2y : entry M 2 y = 0 := by have := S.z2 y; omega
  have htN := upg_lt hyN ht
  have hVot := vOpt_ot I.good hyN
  obtain ⟨s, b, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
  have hbW : bumpW M ρ k = psi s b z := hW
  rw [hbW] at hWL hrW
  rcases last_form (ρ.v t) with hl | ⟨a', b', hl⟩
  · rw [hl] at hWL
    rcases hWL with h | h
    · exact not_lt_z _ h
    · cases h
  rw [hl] at hWL
  have hvy : ρ.v y = add (vOpt ρ (par M 1 y)) (psi a' b' z) := by
    rw [(I.cons y hyN).2]
    unfold vRhs
    rw [if_neg h1y, if_pos h2y, ht]
    simp only
    rw [hl]
    exact sf_ot (isOT_add hVot (by rw [← hl]; exact isOT_last (I.good.ot_v t htN)))
  rw [hvy] at hr
  have hge := summands_add_ge _ r hr
  rcases hWL with h | h
  · exact hge (lt_trans' hrW h)
  · rw [h] at hrW; exact hge hrW

#print axioms b2StepAb_of

end Ytosk.WfB2S
