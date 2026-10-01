/-
**最上位の仮定 `HInvE` を、標準形についての帰納法に分ける。**

`Std` は SRO から展開で作られる。SRO 自身は除かれる（評価の循環）ので、基底は SRO[n]。
各段 `M → M[n]` は、n ≤ 1（と最後の列が 0、親がない場合）は接頭辞 `M.take j`、n ≥ 2 は型ごとの展開。
したがって残りの仕事は 3 つの仮定:
- `hBase`: SRO[n] の評価と不変条件。
- `hTake`: 接頭辞に移る（`Inv3 ∧ Res3A` が `M.take j` へ）。
- `hExp`: n ≥ 2 の展開（最後の列が 0 でない）。
-/
import Ytosk.V3TopC

namespace Ytosk

open T

/-- `M[0]` is a proper prefix. -/
theorem expand_zero_take {M : Mat} (hM : M ≠ []) : ∃ j, j < M.length ∧ expand M 0 = M.take j := by
  cases M with
  | nil => exact absurd rfl hM
  | cons c M' =>
    unfold expand
    simp only
    split_ifs with h
    · exact ⟨_, by simp, rfl⟩
    all_goals first
      | (split
         · exact ⟨_, by simp, rfl⟩
         · rename_i r hr
           have := par_lt _ _ _ _ hr
           refine ⟨r, by simp at this ⊢; omega, ?_⟩
           simp)

/-- **`HInvE` by induction on `Std`.** -/
theorem hInvE_of_step
    (hBase : ∀ n, expand SRO n ≠ [] → ∃ ρ rk, Inv3 (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk)
    (hStep : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ n, expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3 (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN) :
    HInvE := by
  intro M hM
  induction hM with
  | sro => intro h; exact absurd rfl h
  | @exp M n hM ih =>
    intro hS hE
    by_cases hMS : M = SRO
    · subst hMS; exact hBase n hE
    by_cases hME : M = []
    · subst hME; exact absurd rfl hE
    obtain ⟨ρ, rk, I, R⟩ := ih hMS hME
    exact hStep M ρ rk hM hMS hME I R n hS hE

/-- **The step from the prefix step and the expansion step.** -/
theorem hStep_of_parts
    (hTake : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
        ∃ ρ' rk', Inv3 (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3 (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ n, expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3 (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R n hNS hNE
  have hlen : 0 < M.length := by
    cases M with
    | nil => exact absurd rfl hE
    | cons _ _ => simp
  by_cases hz : col M (M.length - 1) = (0, 0, 0)
  · have he := expand_zero_last hE hz n
    rw [he] at hNS hNE ⊢
    exact hTake M ρ rk hM hS hE I R _ (by omega) hNS hNE
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rcases Nat.lt_or_ge n 1 with hn0 | hn1
    · obtain rfl : n = 0 := by omega
      obtain ⟨j, hj, he⟩ := expand_zero_take hE
      rw [he] at hNS hNE ⊢
      exact hTake M ρ rk hM hS hE I R j hj hNS hNE
    · obtain rfl : n = 1 := by omega
      rw [expand_one] at hNS hNE ⊢
      exact hTake M ρ rk hM hS hE I R _ (by omega) hNS hNE
  · exact hExp M ρ rk hM hS hE I R hz n hn hNS hNE

/-- **Termination from the three parts of the induction** and the case `t = 2` of the descent. -/
theorem trio_terminates_ind
    (hBase : ∀ n, expand SRO n ≠ [] → ∃ ρ rk, Inv3 (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk)
    (hTake : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
        ∃ ρ' rk', Inv3 (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3 (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN)
    (hT2 : HInvE → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' :=
  trio_terminatesE (hInvE_of_step hBase (hStep_of_parts hTake hExp)) hT2

end Ytosk
