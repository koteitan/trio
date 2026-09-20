/-
RFlc1.lean: LC1_farword（nested 遠い語頭を LC1 content に入れる）への還元。
LC1_farword base (H=fun_=>0) は PVF_snoc で RLF(nested 頭) に還元できる（green）。
残余 = RLF ((1,b+τ,1)::shiftr01 1 0 Z) = R_farword（RLC=∀ LC1_farword の mutual recursion）。
-/
import GzD

namespace TRIO
namespace RFlc1

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-- **LC1_farword base (H=fun_=>0) ⟸ RLF(nested 頭)**（PVF_snoc、green）。
    LC1 の外頭 (1,b+liftOff+1,1) を PVF_snoc で足す。内容 = nested 頭 + Z は RLF が供給。
    ∴ 残余は RLF ((1,b+τ,1)::shiftr01 1 0 Z) = R_farword。 -/
theorem LC1_farword_base_of_rlf {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {b τ : ℕ} {Z : TrioSeq}
    (hrlf : RLF A o b (((1, b + τ, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Z)) :
    LC1 A o (fun _ => 0) b (((1, b + τ, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Z) := by
  intro W hW hPV
  have h := PVF_snoc hA (⟨hPV, hW⟩ : PVF A o b W) hrlf
  rw [liftOff_zeroF]
  exact h.1

end RFlc1
end TRIO
