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

/-
CONCRETE Lean error for the direct PVF_snoc-mirror at general f (via `hY.1 f b le_rfl`):
  `hL W hW h` fails — `h : PVP A o f b W` but hL expects
  `PVP A (o + addF (fun x => 0) f o) (addF (fun x => 0) f) b W`.
∴ RLC の LC1 は offset **o + f·o**（≠ o、state = addF(0)f = f）で content は reliftX'd。
PVF_snoc は g=fun_=>0 で f·o=0 → offset o、content Y だったから通った。general-f では offset がずれる。
∴ PVP_snoc_gen は hY.1 直接適用でなく GpT_snocz_core の塔（PVP の ∀t が per-level の shift を供給、
hY.1 を per-t の g で使う）が必須。= GpT_snocz_core(120行)に content Y を通す construction。
-/

end RFlc1
end TRIO
