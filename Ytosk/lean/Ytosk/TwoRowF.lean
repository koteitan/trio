/-
**2 行の経路の枠の交換の条件を、2 つの条件から導く。**

枠（h、経路の子 p）で fsD と正規化が交換する条件 `FrameD` のうち、書き換えない場合・非零・後続でないことは構造から出る。
残るのは、書き換えが起きる枠での (W) b < y⟨ζ⟩ と (L) 低い部分の有無の保存だけ。
-/
import Ytosk.TwoRowS

namespace Ytosk

open T

/-- Every summand of the `sp` state stays at least `c` when all inputs do. -/
theorem spArg_summands_ge {a c : T} (hc : ∃ s y, c = psi s y z) :
    ∀ (L st : T), isOT L = true → (∀ q ∈ summands L, c ≤ q) → (∀ q ∈ summands st, c ≤ q) →
      ∀ q ∈ summands (spArg a st L), c ≤ q
  | z, st, _, _, hst => by simpa [spArg] using hst
  | psi s y L', st, hL, hLq, hst => by
    rw [spArg_cons]
    have hsy : c ≤ psi s y z := hLq _ (by simp [summands])
    have hyot : isOT (psi s y z) = true := by
      obtain ⟨h1, h2, _, _, h5⟩ := isOT_psi_iff.mp hL
      exact isOT_psi_iff.mpr ⟨h1, h2, rfl, z_le _, h5⟩
    apply spArg_summands_ge hc L' _ (isOT_rest hL) (fun q hq => hLq q (by simp [summands, hq]))
    intro q hq
    unfold step at hq
    split at hq
    · exact le_trans hsy (H_summands_ge hyot q hq)
    · exact le_trans hsy (add_summands_ge st q hq)

/-- Adding a summand below every summand is concatenation. -/
theorem add_eq_app_of_ge {c : T} (hc : ∃ s y, c = psi s y z) :
    ∀ b : T, (∀ q ∈ summands b, c ≤ q) → add b c = app b c
  | z, _ => by simp
  | psi a1 b1 c1, h => by
    obtain ⟨s, y, rfl⟩ := hc
    rw [add_psi_psi]
    have h1 : ¬ psi a1 b1 z < psi s y z := fun hl =>
      lt_irrefl' _ (lt_of_lt_of_le hl (h _ (by simp [summands])))
    rw [if_neg h1, add_eq_app_of_ge ⟨s, y, rfl⟩ c1 (fun q hq => h q (by simp [summands, hq]))]
    rfl

theorem bst_summands_ge {M : Mat} {x : Nat} (hG : Good2 M) (hx : x + 1 = M.length) {h p : Nat}
    (hpA : Anc0 M p x) (hp : par M 0 p = some h) : ∀ q ∈ summands (bst M h p), o2r M p ≤ q := by
  have hle := children_le_of_anc_last hpA hx hp
  have hcmem : p ∈ children M h := mem_children_iff.mpr ⟨by have := hpA.le; omega, hp⟩
  have hsplit := split_last_max _ p (children_sorted M h) hcmem hle
  set C := (children M h).filter (fun d => decide (d < p)) with hCdef
  have hdM := hG.dec h
  simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
  have hp' := List.pairwise_append.mp hdM
  obtain ⟨hS, hsum⟩ := sumN_dec (C.map (o2r M)) (fun t ht => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i) hp'.1
  unfold bst
  rw [← hCdef]
  apply spArg_summands_ge (o2r_psi_form M p) _ z hS
  · intro q hq; rw [hsum] at hq; exact hp'.2.2 q hq _ (List.mem_singleton_self _)
  · intro q hq; simp [summands] at hq

theorem not_trig_cases {a s y : T} (h : ¬ lt (psi a z z) (psi s y z) = true) : s < a ∨ y = z := by
  rcases lt_trichotomy' a s with h1 | h1 | h1
  · exact absurd (show psi a z z < psi s y z by rw [psi_lt_psi_z_iff]; exact Or.inl h1) h
  · subst h1
    by_cases hy : y = z
    · exact Or.inr hy
    · exfalso; apply h
      show psi a z z < psi a y z
      rw [psi_lt_psi_z_iff]; right; refine ⟨rfl, ?_⟩
      cases y with
      | z => exact absurd rfl hy
      | psi => exact T.z_lt_psi _ _ _
  · exact Or.inl h1

/-- **The frame condition from (W) and (L).** -/
theorem frameD_path {M : Mat} {x h p : Nat} {ζ : T} (hG : Good2 M) (hx : x + 1 = M.length)
    (hpA : Anc0 M p x) (hp : par M 0 p = some h)
    (hok : isOT (fsD (o2r M p) ζ) = true ∧ fsD (o2r M p) ζ < o2r M p)
    (hcns : isSucc (o2r M p) = false)
    (hns : ∀ s y, o2r M p = psi s y z → y ≠ z → isSucc y = false)
    (hleaf : ∀ s, o2r M p = psi s z z →
      ∀ s' y', psi s' y' z ∈ summands (fsD (o2r M p) ζ) → y' ≤ bst M h p ∨ s' < vr M h)
    (hW : ∀ s y, o2r M p = psi s y z → lt (bst M h p) y = true →
      lt (psi (vr M h) z z) (psi s y z) = true → lt (bst M h p) (fsD y ζ) = true)
    (hL : ∀ s y, o2r M p = psi s y z → lt (bst M h p) y = true →
      lt (psi (vr M h) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z)) :
    FrameD (vr M h) (bst M h p) (o2r M p) ζ := by
  obtain ⟨s, y, hc⟩ := o2r_psi_form M p
  have hcot : isOT (psi s y z) = true := by rw [← hc]; exact hG.ot p
  rw [hc] at hok hcns ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [spArg_single]
    rcases step_cases (a := vr M h) (b := bst M h p) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
    · rw [hB]; intro h'; exact absurd (app_eq_z h').2 (by simp)
    · rw [h1]; exact h3
  · rw [spArg_single]
    rcases step_cases (a := vr M h) (b := bst M h p) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
    · rw [hB, isSucc_app B (by simp)]; exact hcns
    · rw [h1]; exact hns s y hc h3
  · by_cases htr : lt (bst M h p) y = true ∧ lt (psi (vr M h) z z) (psi s y z) = true
    · have hy : y ≠ z := by rintro rfl; simp [lt] at htr
      have hys := hns s y hc hy
      by_cases hlo : (split y (psi (succ s) z z)).2 = z
      · exact frame_fsD_trig0' hcot hys hok htr hlo ((hL s y hc htr.1 htr.2).2 hlo)
          (hW s y hc htr.1 htr.2)
      · exact frame_fsD_trig' hcot hys hok htr hlo ((hL s y hc htr.1 htr.2).1 hlo)
          (hW s y hc htr.1 htr.2)
    · have hno : y ≤ bst M h p ∨ s < vr M h := by
        by_cases h1 : lt (bst M h p) y = true
        · have h2 : ¬ lt (psi (vr M h) z z) (psi s y z) = true := fun h2 => htr ⟨h1, h2⟩
          rcases not_trig_cases h2 with h3 | h3
          · exact Or.inr h3
          · left; rw [h3]; exact z_le _
        · left
          rcases lt_trichotomy' y (bst M h p) with h3 | h3 | h3
          · exact Or.inl h3
          · exact Or.inr h3
          · exact absurd h3 h1
      have hge := bst_summands_ge hG hx hpA hp
      rw [hc] at hge
      have hbc : isOT (app (bst M h p) (psi s y z)) = true := by
        have hoh := hG.ot h
        rw [o2r_frame hG hx hpA hp, hc, spArg_single] at hoh
        unfold step at hoh
        rw [if_neg htr, add_eq_app_of_ge ⟨s, y, rfl⟩ _ hge] at hoh
        exact isOT_arg hoh
      apply frame_fsD_notrig' hok hno hbc
      intro s' y' hq
      by_cases hy : y = z
      · subst hy; exact hleaf s hc s' y' (by rw [hc]; exact hq)
      · have hys := hns s y hc hy
        rw [fsD_psi hy hys] at hq hok
        simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
        obtain ⟨rfl, rfl, _⟩ := hq
        have hylt : fsD y ζ < y := by
          have := hok.2; rw [psi_lt_psi_z_iff] at this
          rcases this with h' | ⟨_, h'⟩
          · exact absurd h' (lt_irrefl' _)
          · exact h'
        rcases hno with h' | h'
        · left; exact le_of_lt (lt_of_lt_of_le hylt h')
        · right; exact h'

end Ytosk
