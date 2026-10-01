/-
**コピーの根の鎖（2 行、q = r のとき）。**

b を状態、B を b の Ω_{a+1} 以上の部分とし、y_0 = b、y_{k+1} = step(a, b, a, y_k) とおく（コピーの根 r⁽ᵏ⁾ の値の引数）。
k ≥ 0 で y_{k+1} = B ++ ψ_a(y_k)、ψ_a(y_{k+1}) は標準形、y_k < y_{k+1}。
したがって ψ_a(y_{k+1}) が状態 b で書き換えるときの状態 H は B ++ ψ_a(y_{k+1}) で、b + Ω_{a+1} = B ++ Ω_{a+1} より
（どんな続きでも）小さい（`SB`）。これが `spArg_frame_diff` の条件 (ii) になる。
-/
import Ytosk.SP

namespace Ytosk

open T

/-- Adding a principal `c` to `B ++ lo` drops `lo` when every summand of `B` is at least `c` and `lo` is
below `c`. -/
theorem add_app_drop {s y : T} : ∀ {B lo : T}, (∀ q ∈ summands B, ¬ q < psi s y z) →
    (lo = z ∨ head lo < psi s y z) → add (app B lo) (psi s y z) = app B (psi s y z)
  | z, lo, _, hlo => by
    rcases hlo with rfl | h
    · simp
    · cases lo with
      | z => simp
      | psi a1 b1 c1 => simp only [app_z]; rw [add_psi_psi, if_pos (by simpa [head] using h)]
  | psi a1 b1 B', lo, hB, hlo => by
    simp only [app_psi]
    rw [add_psi_psi, if_neg (hB _ (by simp [summands]))]
    rw [add_app_drop (fun q hq => hB q (by simp [summands, hq])) hlo]

theorem split_app_of {t : T} : ∀ {B X : T}, (∀ q ∈ summands B, ¬ q < t) → (X = z ∨ head X < t) →
    split (app B X) t = (B, X)
  | z, X, _, hX => by
    rcases hX with rfl | h
    · rfl
    · cases X with
      | z => rfl
      | psi a1 b1 c1 =>
        simp only [app_z, split]; rw [if_pos (show lt (psi a1 b1 z) t = true from h)]
  | psi a1 b1 B', X, hB, hX => by
    simp only [app_psi, split]
    rw [if_neg (show ¬ lt (psi a1 b1 z) t = true from hB _ (by simp [summands]))]
    rw [split_app_of (fun q hq => hB q (by simp [summands, hq])) hX]

/-- The chain of arguments of the copies of the bad root. -/
def chain (a b : T) : Nat → T
  | 0 => b
  | k + 1 => step a b a (chain a b k) z

section
variable {a b : T}

theorem head_lt_of_lt_principal {lo s y : T} (h : lo < psi s y z) : lo = z ∨ head lo < psi s y z := by
  cases lo with
  | z => exact Or.inl rfl
  | psi a1 b1 c1 =>
    right
    have h1 := head_le_of_lt h
    simp only [head] at h1 ⊢
    rcases (le_iff _ _).mp h1 with h2 | h2
    · exact h2
    · exfalso
      simp only [psi.injEq, and_true] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact not_lt_of_ge (psi_le_psi_rest (z_le c1)) h

/-- The facts about the split of the state `b`. -/
theorem chain_split (hb : isOT (psi a b z) = true) :
    app (split b (psi (succ a) z z)).1 (split b (psi (succ a) z z)).2 = b ∧
    (∀ q ∈ summands (split b (psi (succ a) z z)).1, ¬ q < psi (succ a) z z) ∧
    (split b (psi (succ a) z z)).2 < psi a b z := by
  refine ⟨split_app _ b, split_fst_ge _ b, ?_⟩
  by_cases hlo : (split b (psi (succ a) z z)).2 = z
  · rw [hlo]; exact T.z_lt_psi _ _ _
  · exact split_lo_lt hb hlo

theorem Om_succ_gt (a y : T) : psi a y z < psi (succ a) z z := by
  rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self a)

/-- One more copy keeps the form `B ++ ψ_a(y)` standard. -/
theorem chain_ot {B lo y : T} (hb : isOT (psi a b z) = true) (hbpl : app B lo = b)
    (hB : ∀ q ∈ summands B, ¬ q < psi (succ a) z z) (hlo : lo < psi a b z)
    (hy : isOT (psi a y z) = true) (hby : b ≤ y) (hyl : y < app B (psi a y z)) :
    isOT (psi a (app B (psi a y z)) z) = true := by
  have hBot : isOT B = true := by
    have := isOT_arg hb; rw [← hbpl] at this; exact isOT_app_left this
  have hge : ∀ q ∈ summands B, head (psi a y z) ≤ q := fun q hq =>
    le_of_lt (lt_of_lt_of_le (Om_succ_gt a y) (le_of_not_gt (hB q hq)))
  have happ : isOT (app B (psi a y z)) = true := isOT_app_of hBot hy hge
  have hloy : lo < psi a y z := by
    apply lt_of_lt_of_le hlo
    rw [le_iff]
    rcases (le_iff _ _).mp hby with h | rfl
    · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩
    · right; rfl
  have hbl : b < app B (psi a y z) := by rw [← hbpl]; exact app_lt_app_left B hloy
  rw [isOT_psi_iff]
  refine ⟨isOT_sub hb, happ, rfl, z_le _, ?_⟩
  intro g hg
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · have : g ∈ comps a b := by rw [← hbpl, comps_app]; exact List.mem_append_left _ hg
    exact lt_trans (comps_lt hb g this) hbl
  · have hss : lt a a = false := Bool.eq_false_iff.mpr (lt_irrefl' a)
    simp only [comps, hss, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact hyl
    · exact lt_trans (comps_lt hy g hg) hyl
    · rw [comps_self_nil (isOT_sub hb)] at hg; simp at hg
    · simp [comps] at hg

/-- **The chain lemma.** -/
theorem chain_succ (hb : isOT (psi a b z) = true) : ∀ k : Nat,
    chain a b (k + 1) = app (split b (psi (succ a) z z)).1 (psi a (chain a b k) z) ∧
    isOT (psi a (chain a b (k + 1)) z) = true ∧ chain a b k < chain a b (k + 1) ∧ b ≤ chain a b k
  | 0 => by
    obtain ⟨hbpl, hB, hlo⟩ := chain_split hb
    have h1 : chain a b 1 = app (split b (psi (succ a) z z)).1 (psi a b z) := by
      show step a b a b z = _
      unfold step
      rw [if_neg (by simp [show lt b b = false from Bool.eq_false_iff.mpr (lt_irrefl' b)])]
      rw [show add b (psi a b z) = add (app (split b (psi (succ a) z z)).1 (split b (psi (succ a) z z)).2)
        (psi a b z) by rw [hbpl]]
      apply add_app_drop
      · intro q hq hlt; exact hB q hq (lt_trans hlt (Om_succ_gt a b))
      · exact head_lt_of_lt_principal hlo
    have hyl : b < app (split b (psi (succ a) z z)).1 (psi a b z) := by
      conv => lhs; rw [← hbpl]
      exact app_lt_app_left _ hlo
    refine ⟨h1, ?_, ?_, le_refl _⟩
    · rw [h1]; exact chain_ot hb hbpl hB hlo hb (le_refl _) hyl
    · show b < chain a b 1; rw [h1]; exact hyl
  | k + 1 => by
    obtain ⟨hbpl, hB, hlo⟩ := chain_split hb
    obtain ⟨hk, hot, hlt, hle⟩ := chain_succ hb k
    have hby : b ≤ (chain a b (k + 1)) := le_trans hle (le_of_lt hlt)
    have hloy : (split b (psi (succ a) z z)).2 < psi a (chain a b k) z := by
      apply lt_of_lt_of_le hlo
      rw [le_iff]
      rcases (le_iff _ _).mp hle with h | h
      · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩
      · right; exact congrArg (fun t => psi a t z) h
    have hbyl : b < (chain a b (k + 1)) := by
      rw [hk]; conv => lhs; rw [← hbpl]
      exact app_lt_app_left _ hloy
    have hyne : (chain a b (k + 1)) ≠ z := by intro h; rw [h] at hbyl; exact T.not_lt_z _ hbyl
    have h2 : chain a b (k + 2) = app (split b (psi (succ a) z z)).1 (psi a (chain a b (k + 1)) z) := by
      show step a b a (chain a b (k + 1)) z = _
      unfold step
      have htrig : lt b (chain a b (k + 1)) = true ∧ lt (psi a z z) (psi a (chain a b (k + 1)) z) = true := by
        refine ⟨hbyl, ?_⟩
        show psi a z z < psi a (chain a b (k + 1)) z
        rw [psi_lt_psi_z_iff]
        exact Or.inr ⟨rfl, lt_of_le_of_lt (z_le b) hbyl⟩
      rw [if_pos htrig, H_eq hot]
      have hsp : split (chain a b (k + 1)) (psi (succ a) z z) = ((split b (psi (succ a) z z)).1, psi a (chain a b k) z) := by
        rw [hk]
        apply split_app_of hB
        right; exact Om_succ_gt a _
      rw [hsp]
      simp
    have hyl : (chain a b (k + 1)) < app (split b (psi (succ a) z z)).1 (psi a (chain a b (k + 1)) z) := by
      conv => lhs; rw [hk]
      exact app_lt_app_left (split b (psi (succ a) z z)).1 (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩)
    refine ⟨h2, ?_, ?_, hby⟩
    · rw [h2]; exact chain_ot hb hbpl hB hlo hot hby hyl
    · show (chain a b (k + 1)) < chain a b (k + 2); rw [h2]; exact hyl

/-- The state when a copy of the bad root rewrites is below `b + Ω_{a+1}` inside itself. -/
theorem chain_SB (hb : isOT (psi a b z) = true) (k : Nat) :
    SB (H a (chain a b (k + 1))) (add b (psi (succ a) z z)) := by
  obtain ⟨hbpl, hB, hlo⟩ := chain_split hb
  obtain ⟨hk, hot, hlt, _⟩ := chain_succ hb k
  have hH : H a (chain a b (k + 1)) = app (split b (psi (succ a) z z)).1 (psi a (chain a b (k + 1)) z) := by
    rw [H_eq hot]
    have hsp : split (chain a b (k + 1)) (psi (succ a) z z) =
        ((split b (psi (succ a) z z)).1, psi a (chain a b k) z) := by
      rw [hk]; exact split_app_of hB (Or.inr (Om_succ_gt a _))
    rw [hsp]; simp
  have hW : add b (psi (succ a) z z) = app (split b (psi (succ a) z z)).1 (psi (succ a) z z) := by
    conv => lhs; rw [← hbpl]
    apply add_app_drop hB
    exact head_lt_of_lt_principal (lt_trans hlo (Om_succ_gt a b))
  rw [hH, hW]
  intro R
  rw [app_assoc]
  apply app_lt_app_left
  simp only [app_psi, app_z]
  exact lt_of_head_lt (Om_succ_gt a _)

end

end Ytosk
