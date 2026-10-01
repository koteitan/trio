/-
**3 行: 2 つの行列の割り当てが一致する範囲。**

M' の呼び出しの集合 E の外で、M' の等式が（同じ値を読めば）M の等式と同じで、読む呼び出しも E の外なら、
M' の割り当ては E の外で M の割り当てと一致する（`agree_off`、M' の順位についての帰納法）。
先頭部分 M.take x（展開 n = 1）の値で、x にも x − 1 の上げにも依存しない列の値が変わらないことに使う。
-/
import Ytosk.V3Take

namespace Ytosk

open T

/-- **Agreement outside a set of calls.** -/
theorem agree_off {M M' : Mat} {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (E : Bool → Nat → Prop)
    (hC : Cons M ρ) (hC' : Cons M' ρ') (hR' : Rk M' rk') (hlen : M'.length ≤ M.length)
    (ho : ∀ i, i < M'.length → ¬ E true i → ∀ σ : Valn, oRhs M' σ i = oRhs M σ i)
    (hv : ∀ i, i < M'.length → ¬ E false i → ∀ σ : Valn, vRhs M' σ i = vRhs M σ i)
    (hdo : ∀ i, i < M'.length → ¬ E true i →
      ¬ E false i ∧ ∀ c ∈ children M' i, Counted M' i c → ¬ E true c)
    (hdv : ∀ i, i < M'.length → ¬ E false i → entry M' 1 i ≠ 0 →
      (∀ m, par M' 1 i = some m → ¬ E false m) ∧
      (entry M' 2 i = 0 → ∀ k, upg M' i = some k → ¬ E false k) ∧
      (entry M' 2 i ≠ 0 → ∀ j ∈ children M' i, col M' j = bump M' i → ∀ k ∈ children M' j,
        ¬ E true k)) :
    ∀ i, i < M'.length → (¬ E true i → ρ'.o i = ρ.o i) ∧ (¬ E false i → ρ'.v i = ρ.v i) := by
  have key : ∀ N, ∀ i, i < M'.length → (rk' true i ≤ N → ¬ E true i → ρ'.o i = ρ.o i) ∧
      (rk' false i ≤ N → ¬ E false i → ρ'.v i = ρ.v i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hvv : ∀ i, i < M'.length → rk' false i ≤ N → ¬ E false i → ρ'.v i = ρ.v i := by
        intro i hi hN hE
        obtain ⟨_, _, hR⟩ := hR' i hi
        rw [(hC' i hi).2, (hC i (by omega)).2, ← hv i hi hE ρ]
        apply vRhs_congr
        · intro m h1 hm
          have hlt := (hR h1).1 m hm
          exact (ih _ (by omega) m (by have := par_lt M' 1 i m hm; omega)).2 (Nat.le_refl _)
            ((hdv i hi hE h1).1 m hm)
        · intro k h1 h2 hk
          have hlt := (hR h1).2.1 h2 k hk
          exact (ih _ (by omega) k (upg_lt hi hk)).2 (Nat.le_refl _) ((hdv i hi hE h1).2.1 h2 k hk)
        · intro j hj h1 h2 hb k hk
          have hlt := (hR h1).2.2 h2 j hj hb k hk
          exact (ih _ (by omega) k (mem_children hk).2).1 (Nat.le_refl _)
            ((hdv i hi hE h1).2.2 h2 j hj hb k hk)
      refine fun i hi => ⟨fun hN hE => ?_, hvv i hi⟩
      obtain ⟨hvo, hc, _⟩ := hR' i hi
      obtain ⟨hEv, hEc⟩ := hdo i hi hE
      rw [(hC' i hi).1, (hC i (by omega)).1, ← ho i hi hE ρ]
      apply oRhs_congr
      · exact hvv i hi (by omega) hEv
      · intro c hcm hbc huc
        have hlt := hc c hcm hbc huc
        exact (ih _ (by omega) c (mem_children hcm).2).1 (Nat.le_refl _) (hEc c hcm ⟨hbc, huc⟩)
  intro i hi
  exact ⟨fun hE => (key _ i hi).1 (Nat.le_refl _) hE, fun hE => (key _ i hi).2 (Nat.le_refl _) hE⟩

end Ytosk
