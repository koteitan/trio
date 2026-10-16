/-
**1 列落としで動かない部分木（2026-10-16、t2）。**

`chg_free_sub`: x − 1 が上げず（upg(x − 1) = none）、列 k の部分木が x を含まず、部分木の出口
（部分木の最後の列 i の次の列 i + 1）へ i から上げがないなら、k の部分木のどの呼び出しも
M.take x で変わらない（ChgX に入らない）。ChgX の帰納法:
- 根の変化（x、x − 1 の上げ、x を子に持つ列、数え方の変化）は部分木の外（`cnt_change`）。
- P_1 で読む v、上げの先の v が部分木の外で変わるなら、その列は TopC（`chg_struct`）なので、
  P_1 の子はなく（TopC の定義）、祖先型の上げもない（`no_anc_upg`）。次の列への上げは出口の仮定で除く。
-/
import Ytosk.V3ChgS

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- The subtree of `k` does not contain `x`, so it lies before `x`. -/
theorem sub_lt_x {k d : Nat} (hk : k < x) (hkx : ¬ Anc0 M k x) (hA : Anc0 M k d) : d < x := by
  by_contra h
  by_cases hkd : k = d
  · omega
  · have := anc0_lt_len hA hkd
    have hdx : d = x := by omega
    exact hkx (hdx ▸ hA)

/-- **Nothing in a region changes** under the drop of `x`: the region lies before `x`, is closed under taking
children, and no column of it upgrades to the next column outside it. -/
theorem chg_free_reg (hun : upg M (x - 1) = none) {Reg : Nat → Prop} (hRx : ∀ d, Reg d → d < x)
    (hRch : ∀ i c, Reg i → c ∈ children M i → Reg c)
    (hexit : ∀ i, Reg i → ¬ Reg (i + 1) → upg M i ≠ some (i + 1)) :
    ∀ b d, ChgX M x b d → ¬ Reg d := by
  intro b d h
  induction h with
  | leaf => exact fun h => by have := hRx _ h; omega
  | supg hne => exact absurd hun hne
  | @scnt i c hc hcx hch =>
    intro hA
    have hix : i < x := hRx i hA
    rcases cnt_change hx hix hcx hch with hxc | hu
    · have := hRx _ (hRch c x (hRch i c hA hc) hxc); omega
    · rw [hun] at hu; cases hu
  | @snb i _ _ hxi _ =>
    intro hA
    have := hRx _ (hRch i x hA hxi); omega
  | @ochild i c hc _ _ _ ih =>
    intro hA
    exact ih (hRch i c hA hc)
  | ov _ ih => exact ih
  | @vpar i m _ hm hCm ih =>
    intro hA
    have hix := hRx i hA
    by_cases hkm : Reg m
    · exact ih hkm
    · have hmx : m < x := by have := par_lt M 1 i m hm; omega
      have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl hmx
      exact hT.2.2 i hix hm
  | @vupg i k' _ _ hu hCk ih =>
    intro hA
    have hix := hRx i hA
    by_cases hkk : Reg k'
    · exact ih hkk
    · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
      rcases hcase with hk1 | ⟨hAk, hki⟩
      · subst hk1; exact hexit i hA hkk hu
      · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl (by omega)
        exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT (by omega) hu hAk hki
  | @vbump i j k'' _ _ hj _ hk'' _ ih =>
    intro hA
    exact ih (hRch j k'' (hRch i j hA hj) hk'')

/-- **Nothing in the subtree of `k` changes** under the drop of `x`. -/
theorem chg_free_sub (hun : upg M (x - 1) = none) {k : Nat} (hk : k < x) (hkx : ¬ Anc0 M k x)
    (hexit : ∀ i, Anc0 M k i → ¬ Anc0 M k (i + 1) → upg M i ≠ some (i + 1)) :
    ∀ b d, ChgX M x b d → ¬ Anc0 M k d :=
  chg_free_reg hx hR0 hZ2 hSD hZ1 hUAT hUAB hun (Reg := fun d => Anc0 M k d)
    (fun d hd => sub_lt_x hx hR0 hZ2 hSD hZ1 hUAT hUAB hk hkx hd)
    (fun i c hi hc => Anc0.trans hi (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl i))) hexit

end

end Ytosk
