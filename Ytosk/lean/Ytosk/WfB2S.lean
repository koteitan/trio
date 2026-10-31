/-
**B2Step を吸収のある枠に限る（2026-10-31, WfB2S）。**

HUACB2 の枠（Bad2、n = x − 1 が祖先 k < n へ上げる、m = P₀ k = P₁ n、W = bumpW(k)）で
v(n) = v(k) = v(m) + W（標準形の和）。
- v(m) の加数がどれも W 未満でない（吸収がない）なら v(m) の成分はそのまま v(n) の成分（`dom_add_noabs`）。
  HUACB2 はこの場合 Bad2 も StepDom もなしで成り立つ（`huacB2_noabs`）。
- 吸収がある（v(m) のある加数 r < W）場合だけ B2Step が要る: 残り `B2StepAb`。
  `huacB2_of_ab : B2StepAb → WfH7W.HUACB2`、`b2StepAb_of_step : B2Step → B2StepAb`（弱めであること）。

測定（tmp/wf/WfB2S/notes.md）: P₀ n が bump 子の枠（Bad2 を仮定しない、すべての位置 n）で、吸収があるなら
鎖の段 a より上に上げる列はない（StepDom は空）。吸収がない枠では m が上げ（a = P₁ m）、StepDom は偽になりうる
（graft2 で 1232 枠）。B2Step が Bad2 を要したのは、Bad2（UpgAbsX の破れ）が吸収を強いるためだけだった。
-/
import Ytosk.WfH7W2Ret

namespace Ytosk.WfB2S

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **No summand absorbed**: when no summand of `A` is below the single term `ψ_s(b)`, the components of `A` are
components of `A + ψ_s(b)`. -/
theorem dom_add_noabs {s b : T} :
    ∀ (A : T), (∀ r ∈ summands A, ¬ r < psi s b z) →
      ∀ u, Dom (comps u A) (comps u (add A (psi s b z)) ++ [z])
  | z, _ => by intro u g hg; simp [comps] at hg
  | psi a a' c, h => by
    intro u g hg
    have hlt : ¬ psi a a' z < psi s b z := h _ (by simp [summands])
    have hadd : add (psi a a' c) (psi s b z) = psi a a' (add c (psi s b z)) := by
      simp only [add, if_neg (show ¬ lt (psi a a' z) (psi s b z) = true from hlt)]
    rw [hadd]
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
      simp only [comps, List.mem_append]
      exact Or.inl hg
    · obtain ⟨d, hd, hgd⟩ := dom_add_noabs c (fun r hr => h r (by simp [summands, hr])) u g hg
      refine ⟨d, ?_, hgd⟩
      rcases List.mem_append.mp hd with hd | hd
      · exact List.mem_append_left _ (by simp only [comps, List.mem_append]; exact Or.inr hd)
      · exact List.mem_append_right _ hd

/-- **HUAC without absorption** (every upgrade `n → k`, no `Bad2`, no `StepDom`): if no summand of `v(P₁ n)` is
below `bumpW(k)`, the components of `v(P₁ n)` are components of `v(n)`. -/
theorem huacB2_noabs {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {n k : Nat} (hn : n < M.length) (hu : upg M n = some k)
    (hno : ∀ r ∈ summands (vOpt ρ (par M 1 n)), ¬ r < bumpW M ρ k) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  obtain ⟨h1n, h2n'⟩ := upg_e12 hu
  have h2n : entry M 2 n = 0 := by have := S.z2 n; omega
  have hkN := upg_lt hn hu
  obtain ⟨m, hmn, hmk, hcol, _⟩ := upg_spec hu
  have h1k : entry M 1 k ≠ 0 := by have := e1_of_col hcol; omega
  have h2k : entry M 2 k ≠ 0 := by have := e2_of_col hcol; omega
  have hVot := vOpt_ot hG (show n < M.length by omega)
  have hnv := v_upg_eq hC hn h1n h2n hu hVot
    (fun _ _ _ d hd => hG.ot_o d (mem_children hd).2)
  obtain ⟨s, b, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
  have hbW : bumpW M ρ k = psi s b z := hW
  have hkv : ρ.v k = add (vOpt ρ (par M 1 n)) (psi s b z) := by
    rw [(hC k hkN).2]
    unfold vRhs
    rw [if_neg h1k, if_neg h2k, hW, hmk, hmn]
    exact sf_ot (isOT_add (by simpa only [hmn] using hVot) (by rw [← hW]; exact isOT_omega (isOT_bumpP hG k)))
  rw [hnv, hkv]
  rw [hbW] at hno
  exact dom_add_noabs _ hno

/-- **Residual (`B2Step` only with absorption)**: the frame of `WfH7W2.B2Step` with the extra premise that some
summand of `v(m)` (`m = P₀ k = P₁ n`) is below `bumpW(k)`. Measured without `Bad2` at every position `n` whose row-0
parent is a bump child: with absorption the row-1 chain of `m` has no upgrade above the level of `c`. -/
def B2StepAb : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ n, n + 2 = M.length → ∀ k m, upg M n = some k →
    k < n → par M 0 k = some m → (∃ r ∈ summands (ρ.v m), r < bumpW M ρ k) →
    lev (bumpW M ρ k) = z ∨
    ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧ (∀ d ∈ R, col M d ≠ bump M k) ∧
      children M j = c :: C ∧
      ∀ a, WfHUACDeep.Up1 M a m → entry M 1 a = entry M 1 c → WfHUACDeep.StepDom M ρ a m

theorem b2StepAb_of_step (h : WfH7W2.B2Step) : B2StepAb :=
  fun M ρ rk hM hS hB I n hn k m hu hk hkm _ => h M ρ rk hM hS hB I n hn k m hu hk hkm

/-- **`HUACB2` from `B2StepAb`**: without absorption by `huacB2_noabs`, with absorption by the deep return
(`WfH7W2.huacB2_of_step` restricted). -/
theorem huacB2_of_ab (h : B2StepAb) : WfH7W.HUACB2 := by
  intro M ρ rk hM hS hB I n hn k hu hk u
  have S := sInv_std hM hS
  obtain ⟨m, hmn, hkm⟩ := upg_target_par0 S.r0p hu
  have hnN : n < M.length := by omega
  by_cases hab : ∃ r ∈ summands (ρ.v m), r < bumpW M ρ k
  · rcases h M ρ rk hM hS hB I n hn k m hu hk hkm hab with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hCc, hst⟩
    · exact HUACZero.dom_of_zero S I.cons I.good hnN hu h0 u
    · have hj : j ∈ children M k := by rw [hL]; simp
      obtain ⟨hcn, hc2, a, ha, hae⟩ := WfHUAC2Canon.canon_struct hM hS hu hk hkm hL hjb hCc
      exact WfHUACDeep.dom_of_deep S I.cons I.good hnN hu hk hkm
        ⟨L, j, R, c, a, hL, hjb, hR, by rw [hCc]; simp,
          WfHUAC2Canon.first_kid_survives hM hS I.cons I.good hj hjb hCc, hcn, ha, hae.symm, hc2,
          hst a ha hae⟩ u
  · refine huacB2_noabs S I.cons I.good hnN hu ?_ u
    rw [hmn]
    intro r hr hlt
    exact hab ⟨r, hr, hlt⟩

end Ytosk.WfB2S
