/-
**WfQrL6 (2026-11-01): the glue with given `D` values is good** (`good3_N_t1Q`, copy of `good3_N_t1` with
`glueQ`; the `D` values are data: standard, at most the old value, nonzero).
-/
import Ytosk.WfQrL5
import Ytosk.V3Good3N

namespace Ytosk.WfQrL6
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The glued valuation of `M[n]` is good**, with given `D` values (copy of `good3_N_t1`). -/
theorem good3_N_t1Q (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {oq vq : Nat → T} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hGP : Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hoto : ∀ i, i < r + L → DepX M (r + L) true i → isOT (oq i) = true)
    (hotv : ∀ i, i < r + L → DepX M (r + L) false i → isOT (vq i) = true)
    (hle : ∀ c, c < r + L → DepX M (r + L) true c → oq c ≤ ρ.o c ∧ oq c ≠ z)
    (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z) :
    Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) := by
  set σ := glueQ M (r + L) ρ (shiftV ρP L) oq vq with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  -- values from `x` on
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueQ_o_ge (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueQ_v_ge (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  -- the value of a `D` child at or below `x`
  have hσD : ∀ c, c ≤ r + L → DepX M (r + L) true c → σ.o c ≤ ρ.o c ∧ σ.o c ≠ z := by
    intro c hc hd
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [hσ, glueQ_o_dep h hd]; exact hle c h hd
    · have : c = r + L := by omega
      subst this
      have := hσo 0
      simp only [Nat.add_zero] at this
      rw [this]; exact hlex
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.lt_or_ge i (r + L) with h | h
    · by_cases hd : DepX M (r + L) true i
      · rw [hσ, glueQ_o_dep h hd]; exact hoto i h hd
      · rw [hσ, glueQ_o_lt h hd]; exact hG.ot_o i (by omega)
    · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
      rw [hσo]; exact hGP.ot_o _ (by omega)
  · intro i hi
    rcases Nat.lt_or_ge i (r + L) with h | h
    · by_cases hd : DepX M (r + L) false i
      · rw [hσ, glueQ_v_dep h hd]; exact hotv i h hd
      · rw [hσ, glueQ_v_lt h hd]; exact hG.ot_v i (by omega)
    · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
      rw [hσv]; exact hGP.ot_v _ (by omega)
  · intro i hi
    rcases Nat.lt_or_ge i (r + L) with h | h
    · -- the structure is that of `M`
      have hS := hSA i h
      have hcv : cvals (TRIO.gexp M r L d0 0 n) σ i = cvals M σ i := by
        unfold cvals; rw [hS.ch]
        congr 1
        exact List.map_congr_left (fun c hc => hS.cnt c hc σ)
      rw [hcv]
      have hiM : i < M.length := by omega
      by_cases hd : DepX M (r + L) true i
      · rcases hOS i h hd with ⟨_, hnc⟩ | ⟨hv, Lc, c, R, hch, hcb, hcu, hR, hLnd⟩
        · have : cvals M σ i = [] := by
            unfold cvals
            exact nzs_zeros _ (fun t ht => by
              obtain ⟨d, hd', rfl⟩ := List.mem_map.mp ht; exact cnt_unc σ (hnc d hd'))
          rw [this]; exact List.Pairwise.nil
        · have hcmem : c ∈ children M i := by rw [hch]; exact List.mem_append_right _ List.mem_cons_self
          have hcm := mem_children hcmem
          have hdc : DepX M (r + L) true c := by
            cases hd with
            | leaf => omega
            | @ochild _ c' hc' hb' hu' hd' =>
              have : c' = c := by
                rw [hch] at hc'
                rcases List.mem_append.mp hc' with h' | h'
                · exact absurd hd' (hLnd c' h' ⟨hb', hu'⟩)
                · rcases List.mem_cons.mp h' with h' | h'
                  · exact h'
                  · rcases hR c' h' with h'' | h''
                    · exact absurd h'' hb'
                    · exact absurd h'' hu'
              rw [← this]; exact hd'
            | ov hv' => exact absurd hv' hv
          obtain ⟨hcle, hcz⟩ := hσD c (by omega) hdc
          have hsplitσ := cvals_split hch hcb hcu hR (ρ := σ) hcz
          have hsplitρ := cvals_split hch hcb hcu hR (ρ := ρ) (single_ne_z (single_o hC hG hcm.2))
          have hL' : nzs (Lc.map (cnt M σ i)) = nzs (Lc.map (cnt M ρ i)) := by
            congr 1
            apply List.map_congr_left
            intro d hdL
            by_cases hcd : Counted M i d
            · rw [cnt_cnt _ hcd.1 hcd.2, cnt_cnt _ hcd.1 hcd.2]
              have hdc' : d < c := by
                have hsort := children_sorted M i
                rw [hch] at hsort
                exact (List.pairwise_append.mp hsort).2.2 d hdL c List.mem_cons_self
              rw [hσ, glueQ_o_lt (by omega) (hLnd d hdL hcd)]
            · have : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
                by_cases h1 : col M d = bump M i
                · exact Or.inl h1
                · right; by_contra h2; exact hcd ⟨h1, h2⟩
              rw [cnt_unc _ this, cnt_unc _ this]
          rw [hsplitσ, hL']
          have hdec := hG.dec i hiM
          rw [hsplitρ] at hdec
          exact pairwise_snoc_lower hdec hcle
      · -- no counted child is in `D`: the values are those of `M`
        have : cvals M σ i = cvals M ρ i := by
          unfold cvals
          congr 1
          apply List.map_congr_left
          intro c hc
          have hcm := mem_children hc
          by_cases hcd : Counted M i c
          · rw [cnt_cnt _ hcd.1 hcd.2, cnt_cnt _ hcd.1 hcd.2]
            have hdc : ¬ DepX M (r + L) true c := fun h' => hd (DepX.ochild hc hcd.1 hcd.2 h')
            have hcx : c < r + L := by
              rcases Nat.lt_or_ge c (r + L) with h' | h'
              · exact h'
              · exfalso
                have : c = r + L := by omega
                rw [this] at hdc; exact hdc DepX.leaf
            rw [hσ, glueQ_o_lt hcx hdc]
          · have : col M c = bump M i ∨ (isUpg M c = true ∧ topped M c = true) := by
              by_cases h1 : col M c = bump M i
              · exact Or.inl h1
              · right; by_contra h2; exact hcd ⟨h1, h2⟩
            rw [cnt_unc _ this, cnt_unc _ this]
        rw [this]; exact hG.dec i hiM
    · -- a copy column: the counted values of the shifted column of `M[n − 1]`
      obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
      have ha : a < (n - 1) * L := by omega
      have hcv : cvals (TRIO.gexp M r L d0 0 n) σ (r + L + a) =
          cvals (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a) := by
        unfold cvals
        rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.map_map]
        congr 1
        apply List.map_congr_left
        intro d hd
        rw [hσ, glueQ_eq_glueZ M (r + L) ρ (shiftV ρP L) oq vq (fun _ => z)]
        exact cnt_copy hlen hL hA hd0e hn hpath hz2 ha hd
      rw [hcv]; exact hGP.dec _ (by omega)

end

end Ytosk.WfQrL6
