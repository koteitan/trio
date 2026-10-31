/-
**3 行・t = 2・Bad2: 列の値の上界 o(c) < B(V) を子に下げる（2026-10-31、WfSrcC2）。**

o(c) = ψ_{v(c)}(spArg_{v(c)}(0, X))、X = Σ（数える子 d の o(d)）。
- v(c) < V なら o(c) < B(V)。
- v(c) = V で X < B(V) なら、sp の各段は Ω_{V+1} 未満にとどまる（引き金の段は添字 V・引数 Ω_{V+1} 未満の項で、
  その H は Ω_{V+1} 未満、`spArg_lt_om`）。よって o(c) < B(V)（`o_lt_bnd_of_children`）。
X < B(V) は数える子ごとの o(d) < B(V) から（`WfSrcC2.sumN_lt_single`）。
-/
import Ytosk.WfSrcC2a

namespace Ytosk.WfSrcC2

open T WfT2Abs

set_option linter.unusedSectionVars false

/-- **`sp` stays below `Ω_{a+1}`** when started below it and fed a standard term below `B(a)`. -/
theorem spArg_lt_om {a : T} (ha : isOT a = true) :
    ∀ (c b : T), isOT c = true → c < Bnd a → b < psi (add a one) z z →
      spArg a b c < psi (add a one) z z
  | z, b, _, _, hb => hb
  | psi s y c, b, hc, hlt, hb => by
    rw [spArg_cons]
    have hsy : s < a ∨ (s = a ∧ y < psi (add a one) z z) := psi_lt_psi_z_iff.mp hlt
    have haa : a < add a one := by rw [add_one_eq_succ ha]; exact lt_succ_self a
    have hsa1 : s < add a one := by
      rcases hsy with h | ⟨rfl, _⟩
      · exact lt_trans h haa
      · exact haa
    have hc' : c < Bnd a := by
      cases c with
      | z => exact T.z_lt_psi _ _ _
      | psi s' y' c' =>
        have hhd : psi s' y' z ≤ psi s y z := (isOT_psi_iff.mp hc).2.2.2.1
        exact lt_single_rest (lt_of_le_of_lt hhd (lt_single_rest hlt))
    apply spArg_lt_om ha c _ (isOT_rest hc) hc'
    unfold step
    split
    · rename_i htr
      have hns := not_lt_of_trig htr.2
      have hs : s = a := by
        rcases hsy with h | ⟨h, _⟩
        · exact absurd h hns
        · exact h
      subst hs
      have hy : y < psi (add s one) z z := by
        rcases hsy with h | ⟨_, h⟩
        · exact absurd h hns
        · exact h
      have hyOT : isOT y = true := isOT_arg hc
      unfold H
      have hcut : cut (add s one) y = z := by
        rw [cut_eq_split _ hyOT]
        exact split_fst_of_head_lt (lt_of_le_of_lt (WfT2Exp.head_le_self y) hy)
      rw [hcut]
      simp only [add, sub]
      split
      · exact psi_lt_psi_z_iff.mpr (Or.inl haa)
      · exact T.z_lt_psi _ _ _
    · exact add_lt_single hb (psi_lt_psi_z_iff.mpr (Or.inl hsa1))

/-- **`o(c) < B(V)` from the children**: `v(c) < V`, or `v(c) = V` and every counted child has `o < B(V)`. -/
theorem o_lt_bnd_of_children {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {c : Nat}
    (hc : c < M.length) {V : T}
    (h : ρ.v c < V ∨ (ρ.v c = V ∧ ∀ d ∈ children M c, Counted M c d → ρ.o d < Bnd V)) :
    ρ.o c < Bnd V := by
  classical
  have hv := hG.ot_v c hc
  have hcs : ∀ t ∈ (children M c).map (cnt M ρ c), isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact isOT_cnt hG (mem_children hd).2
  have ho : ρ.o c = psi (ρ.v c) (spArg (ρ.v c) z (sumN ((children M c).map (cnt M ρ c)))) z := by
    rw [(hC c hc).1]
    unfold oRhs
    show add (sp (sf (ρ.v c)) z (sf (sumN ((children M c).map (cnt M ρ c))))) (sf z) = _
    rw [sp_eq_spArg, sf_ot hv, sf_ot (isOT_sumN _ hcs)]
    rfl
  rw [ho]
  unfold Bnd
  rcases h with hlt | ⟨rfl, hd⟩
  · exact psi_lt_psi_z_iff.mpr (Or.inl hlt)
  · apply psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, ?_⟩)
    apply spArg_lt_om hv _ z (isOT_sumN _ hcs) _ (T.z_lt_psi _ _ _)
    apply sumN_lt_single hcs
    intro t ht
    obtain ⟨d, hdc, rfl⟩ := List.mem_map.mp ht
    rw [cnt_eq_ite]
    split
    · rename_i hcd
      exact hd d hdc hcd
    · exact T.z_lt_psi _ _ _

/-- **Small below `B(V)` by `v` alone**: `v(c) < V`, or `v(c) = V` and every counted child is small. -/
inductive SmallB (M : Mat) (ρ : Valn) (V : T) : Nat → Prop
  | lo {c : Nat} : ρ.v c < V → SmallB M ρ V c
  | eq {c : Nat} : ρ.v c = V → (∀ d ∈ children M c, Counted M c d → SmallB M ρ V d) → SmallB M ρ V c

/-- `SmallB` gives `o(c) < B(V)`. -/
theorem o_lt_bnd_of_small {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {V : T} {c : Nat}
    (hc : c < M.length) (h : SmallB M ρ V c) : ρ.o c < Bnd V := by
  induction h with
  | lo hlt => exact o_lt_bnd_of_children hC hG hc (Or.inl hlt)
  | @eq c hv _ ih =>
    exact o_lt_bnd_of_children hC hG hc
      (Or.inr ⟨hv, fun d hd hcd => ih d hd hcd (mem_children hd).2⟩)

/-- **Residual (c), by `v` alone**: as `SrcC2Res`, with `SmallB (v(r))` for every child of a bump child of the
origin target `k`. -/
def SrcC3Res : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → par M 0 (r + 1) = some r → par M 1 (r + 1) = some r →
      ∀ τ, Cons (M.take (r + 1)) τ →
      ∀ p i, par M 0 r = some p → par M 0 p = some i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        WfT2Abs.DropFail M ρ τ (r + 1) i → WfT2Src.SrcFacts M ρ τ (r + 1) i →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
          ¬ Lhd z s (bumpW M ρ i) →
          ∀ m b k, par M 1 i = some m → WfHUACDeep.Up1 M b m → upg M b = some k → s = bumpW M ρ k →
            ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, SmallB M ρ (ρ.v r) c

/-- **Bridge**: `SrcC2Res` from `SrcC3Res`. -/
theorem c2_of_c3 (h : SrcC3Res) : SrcC2Res := by
  intro M ρ rk C hB2 hz hs r hlen hr h0 h1x τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl m b k hm hb hu
    hk j hj hjb c hc
  exact o_lt_bnd_of_small C.I.cons C.I.good (mem_children hc).2
    (h M ρ rk C hB2 hz hs r hlen hr h0 h1x τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl m b k hm hb hu hk
      j hj hjb c hc)

/-- **`SmallB` from a bound on the whole subtree**: if every column of the row-0 subtree of `c` has `v ≤ V`. -/
theorem smallB_of_sub {M : Mat} {ρ : Valn} {V : T} {c : Nat}
    (h : ∀ e, Anc0 M c e → e < M.length → ρ.v e ≤ V) : c < M.length → SmallB M ρ V c := by
  suffices key : ∀ n e, M.length - e = n → Anc0 M c e → e < M.length → SmallB M ρ V e from
    fun hc => key _ c rfl (Anc0.refl c) hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e hn hce heN
    by_cases hlt : ρ.v e < V
    · exact SmallB.lo hlt
    · have hv : ρ.v e = V := le_antisymm (h e hce heN) (not_lt.mp hlt)
      refine SmallB.eq hv ?_
      intro d hd _
      have hed := mem_children hd
      have hpd := (mem_children_iff.mp hd).2
      exact ih (M.length - d) (by omega) d rfl (hce.trans (anc0_of_par M 0 e d hpd)) hed.2

/-- **Residual (c), as a subtree bound on `v`**: as `SrcC3Res`, with `v(e) ≤ v(r)` for every column `e` of the
row-0 subtree of each child `c` of a bump child of the origin target `k`. -/
def SrcC4Res : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → par M 0 (r + 1) = some r → par M 1 (r + 1) = some r →
      ∀ τ, Cons (M.take (r + 1)) τ →
      ∀ p i, par M 0 r = some p → par M 0 p = some i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        WfT2Abs.DropFail M ρ τ (r + 1) i → WfT2Src.SrcFacts M ρ τ (r + 1) i →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
          ¬ Lhd z s (bumpW M ρ i) →
          ∀ m b k, par M 1 i = some m → WfHUACDeep.Up1 M b m → upg M b = some k → s = bumpW M ρ k →
            ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j,
              ∀ e, Anc0 M c e → e < M.length → ρ.v e ≤ ρ.v r

/-- **Bridge**: `SrcC3Res` from `SrcC4Res`. -/
theorem c3_of_c4 (h : SrcC4Res) : SrcC3Res := by
  intro M ρ rk C hB2 hz hs r hlen hr h0 h1x τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl m b k hm hb hu
    hk j hj hjb c hc
  exact smallB_of_sub
    (h M ρ rk C hB2 hz hs r hlen hr h0 h1x τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl m b k hm hb hu hk
      j hj hjb c hc) (mem_children hc).2

/-- **Bridge**: `WfSrcB.SrcC` from `SrcC4Res`. -/
theorem srcC_of_c4 (h : SrcC4Res) : WfSrcB.SrcC := srcC_of_c2 (c2_of_c3 (c3_of_c4 h))

end Ytosk.WfSrcC2
