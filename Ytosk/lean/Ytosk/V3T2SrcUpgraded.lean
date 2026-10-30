/- Source windows through a quiet prefix followed by an actual upgrade.
The scalar bound on the old bump term is an explicit local premise, not
a new global residual. The split cutoff is retained throughout. -/
import Ytosk.V3T2SrcQuiet

namespace Ytosk.T2SrcUpgraded
open T
open T2SrcQuiet

/-- Until the first upgrade, parent steps add only copies of one. -/
theorem quiet_support {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {a m : Nat}
    (h : QuietParents M a m) (hm : m < M.length) (hm2 : entry M 2 m = 0) :
    HUACSupport.Support (ρ.v m) (ρ.v a) := by
  induction h with
  | refl => exact fun q hq => Or.inr hq
  | @step m p a hp hu tail ih =>
    have hpN : p < M.length := Nat.lt_trans (par_lt M 1 m p hp) hm
    have hp2 : entry M 2 p = 0 := by
      by_contra hn
      exact no_par1_of_e2 S.z1c hm (by have := S.z2 p; omega) hp
    apply HUACSupport.support_value_of_inputs hC hG hm hm2
    · simpa only [hp, vOpt] using ih hpN hp2
    · intro k hk
      rw [hu] at hk
      cases hk

/-- All summands of an upgraded value are at least its principal increment. -/
theorem upgraded_summand_ge {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {b k : Nat}
    (hb : b < M.length) (hu : upg M b = some k) {q : T}
    (hq : q ∈ summands (ρ.v b)) : bumpW M ρ k ≤ q := by
  have hv := HUACSupport.value_at_target S hC hG hb hu
  obtain ⟨s, y, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
  change bumpW M ρ k = psi s y z at hW
  rw [hv, hW] at hq
  rcases summands_add_single _ q hq with he | ⟨_, hn⟩
  · rw [he, hW]
  · rw [hW]
    exact le_of_not_gt hn

/-- The omega^2 cutoff discards the copies of one from the quiet prefix. -/
theorem large_summand_ge_target {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {a m k : Nat}
    (h : QuietParents M a m) (hm : m < M.length) (hm2 : entry M 2 m = 0)
    (hu : upg M a = some k) {q : T} (hq : q ∈ summands (ρ.v m))
    (hq2 : ¬ q < psi z two z) : bumpW M ρ k ≤ q := by
  rcases quiet_support S hC hG h hm hm2 q hq with he | hqa
  · exact False.elim (hq2 (he ▸ (by decide : one < psi z two z)))
  · have ham := WfHUACDeep.up1_le (quiet_up1 h)
    exact upgraded_summand_ge S hC hG (by omega) hu hqa

/-- If the threshold is below the upgraded increment, the low split
contains no summand at or above omega^2. -/
theorem head_small_of_increment_bound {A W B : T} (hA : isOT A = true)
    (hW : W ≤ B) (hB : ∀ q ∈ summands A, ¬ q < psi z two z → B ≤ q) :
    head (split A W).2 < psi z two z := by
  have hh : ∀ q ∈ summands A, ¬ q < psi z two z → q < W → q < psi z two z := by
    intro q hq hq2 hqw
    exact False.elim ((not_lt_of_ge (le_trans hW (hB q hq hq2))) hqw)
  rcases (T2SrcWindow.window_iff_head hA (z_lt_psi z two z)).mp hh with h | h
  · exact h
  · exact h

/-- A quiet prefix ending at an upgrade has an empty source window when
the old bump term is bounded by the target's bump term. No assumption on
the dropped valuation is needed for this empty-window case. -/
theorem not_dropFail_of_quiet_upgrade_bound {M : Mat} {ρ τ : Valn}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x i m a k : Nat}
    (hi : i < M.length) (hm1 : par M 1 i = some m)
    (h : QuietParents M a m) (hu : upg M a = some k)
    (hW : bumpW M ρ i ≤ bumpW M ρ k) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  have hmN : m < M.length := Nat.lt_trans (par_lt M 1 i m hm1) hi
  have hm2 : entry M 2 m = 0 := by
    by_contra hn
    exact no_par1_of_e2 S.z1c hi (by have := S.z2 m; omega) hm1
  apply T2SrcWindow.not_dropFail_of_head (vOpt_ot hG hi)
  left
  rw [hm1]
  exact head_small_of_increment_bound (hG.ot_v m hmN) hW
    (fun q hq hq2 => large_summand_ge_target S hC hG h hmN hm2 hu hq hq2)

/-- Pick the first upgrade, keeping the quiet prefix before it. -/
theorem first_upgrade_or_quiet {M : Mat} {a m : Nat} (h : WfHUACDeep.Up1 M a m) :
    QuietParents M a m ∨ ∃ b, QuietParents M b m ∧
      entry M 1 a < entry M 1 b ∧ upg M b ≠ none := by
  induction h with
  | refl => exact Or.inl (.refl _)
  | @step m p hp tail ih =>
    by_cases hu : upg M m = none
    · rcases ih with hq | ⟨b, hbm, hrow, hb⟩
      · exact Or.inl (.step hp hu hq)
      · exact Or.inr ⟨b, .step hp hu hbm, hrow, hb⟩
    · have hrow := par1_entry_lt hp
      have hle := WfHUACDeep.up1_e1_le tail
      exact Or.inr ⟨m, .refl _, by omega, hu⟩


/-- In a failed lost-return window, the first upgraded parent's increment
must be strictly below the old bump term. Otherwise every large summand
would remain above the split threshold, as proved above. -/
theorem failed_lost_first_increment_lt {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {x m i j : Nat} (hx : x + 1 = M.length) (hx2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    (hT : Cons (M.take x) τ) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : x - 1 ∈ children M j)
    (hrow : entry M 1 (x - 1) ≤ entry M 1 m)
    (hf : WfT2Abs.DropFail M ρ τ x i) :
    ∃ b k, QuietParents M b m ∧ entry M 1 (x - 1) < entry M 1 b ∧
      upg M b = some k ∧ bumpW M ρ k < bumpW M ρ i := by
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  obtain ⟨a, hA, har⟩ := parent_at_row hX hrow
  rcases first_upgrade_or_quiet hA with hq | ⟨b, hbm, hbl, hbu⟩
  · exact False.elim (not_dropFail_of_lost_quiet_return C hB hx hx2 ha hT hGT
      hmi hm1 hj hb hc hq har.symm hf)
  · cases hu : upg M b with
    | none => exact False.elim (hbu hu)
    | some k =>
      refine ⟨b, k, hbm, by omega, hu, ?_⟩
      by_contra hn
      have hiM : i < M.length := Nat.lt_trans (mem_children hj).1 (mem_children hj).2
      exact not_dropFail_of_quiet_upgrade_bound C.S C.I.cons C.I.good hiM hm1 hbm hu
        (le_of_not_gt hn) hf

/-- For a returned value it suffices to preserve support, rather than
comparison of the entire parent value. Copies of one are below the cutoff. -/
theorem not_dropFail_of_child_support {M : Mat} {ρ τ : Valn} {x i j c : Nat}
    (hT : Cons (M.take x) τ) (hGT : Good3 (M.take x) τ)
    (hj : j ∈ children (M.take x) i) (hb : col (M.take x) j = bump (M.take x) i)
    (hc : c ∈ children (M.take x) j)
    (hs : HUACSupport.Support (vOpt ρ (par M 1 i)) (τ.v c)) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  obtain ⟨y, hy⟩ := o_psi_sub hT (mem_children hc).2
  rw [sf_ot (hGT.ot_v c (mem_children hc).2)] at hy
  have hco : τ.v c < τ.o c := by rw [hy]; exact sub_lt _ _ _
  have hGo : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2
  have hsum := T2SrcLeaf.mem_le_sumN hGo (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hW := le_trans hsum (T2SrcLeaf.child_sum_le_bumpW hGT hj hb)
  intro hf
  apply hf
  intro q hq hq2 hnT _
  rcases hs q hq with he | hqv
  · exact False.elim (hq2 (he ▸ (by decide : one < psi z two z)))
  · have hqle := le_trans (summands_le_head (hGT.ot_v c (mem_children hc).2) q hqv) (head_le_self _)
    exact False.elim (hnT (lt_of_le_of_lt hqle (lt_of_lt_of_le hco hW)))

end Ytosk.T2SrcUpgraded
