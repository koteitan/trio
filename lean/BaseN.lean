/-
BaseN.lean: 素の遠い語の頭コピー塔 base(n) = (0,0,0)(1,1,1)(2,1,1)^n ∈ W 0。
route(B) の残余 crux。base(1) = R1317（遠い語ゼロ）。base(n≥2) は「多頭」の
z の字（行 2 の親が頭、行 2 = 1）を中身に持つ語で、GTall_zlet で扱う。
-/
import GzE

namespace TRIO
namespace BaseN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzE

/-- base(2) の中身の z の字語 `[(1,1,1)] ++ [(1,1,1)]` の coneV。 -/
theorem base2_hcone :
    coneV ([((1, 1, 1) : ℕ × ℕ × ℕ)] ++ [((1, 0 + 1, 1) : ℕ × ℕ × ℕ)]) 0
      [((1, 1, 1) : ℕ × ℕ × ℕ)].length := by
  intro y hy
  have hy1 : y ≤ 1 := rtg0_le hy
  rcases Nat.lt_or_ge y 1 with h | h
  · obtain rfl : y = 0 := by omega
    decide
  · obtain rfl : y = 1 := by omega
    decide

/-
残余 crux（route(B) の新 crux = 多頭 Dzf / z の字の荷閉包）。

base(2) は GTall_zlet で以下 2 つの GT1 義務に還元される（Subst1 不使用）:

  base2_hload0 w :
    GT1 w [(1,w+1,1)]                              -- 遠い字 1 個（荷ゼロ）
  base2_hload w R :
    GT1 w ([(1,w+1,1)] ++ shiftr01 1 0 ((0,w+1,0)::R))   -- 遠い字 + 段 w+1 の荷

いずれも「z の字（行 2 = 1）が段 v→v+1 を開き、その下に段 v+1 の Wg 荷を吊るす」
閉包。GT1 を展開すると

  (0,w,0) :: (rword 0 w L ++ [(1,w+1,1)]) ++ [(2,w+1,1)]  （hload0）

の形で、oper_zcone により塔 flatMap_k shiftr01(2k) 0 ((0,w+k,0) :: mlift P w k) に落ちる。
各段は (0,w+k,0) :: rword 0 (w+k) (L↑k ++ [[]]) ∈ Wg（BwT_snocz + BwT_lift、無条件）だが、
塔全体の組み立ては段間が **shift 2 の z-drop** で継がれるため hang_Wg / hangv（荷頭 ≤ 1
が必要）では閉じない。単頭の遠い語では tower_Wg / tower_GPF（空アンカーの GpT、無条件）が
これを処理している（GzD, GzF）。base(n) はこれを対角（任意接頭辞 L・段増加）へ一般化した
GpT 式の塔閉包を要する。SlotAx / SCF には z の字ケースが無く、GTall_zlet は未使用（新規）。

結論: base(2) の還元は Subst1 を使わない。残余は無条件（GpT 塔閉包の一般化）だが、
既存インフラに無い新規補題群を要する。
-/

/-- hload0: 遠い字 1 個の GT1（荷ゼロ）。多頭 Dzf 塔閉包の crux。 -/
theorem base2_hload0 (w : ℕ) : GT1 w [((1, w + 1, 1) : ℕ × ℕ × ℕ)] := by
  sorry

/-- hload: 遠い字 1 個 + 段 w+1 の荷 Z の GT1。多頭 Dzf 塔閉包の crux。 -/
theorem base2_hload (w : ℕ) (R : TrioSeq) (hR : argOK R)
    (hRW : (((0, w + 1, 0) : ℕ × ℕ × ℕ) :: R) ∈ Wg (2 * (w + 1))) :
    GT1 w ([((1, w + 1, 1) : ℕ × ℕ × ℕ)] ++ shiftr01 1 0 (((0, w + 1, 0) : ℕ × ℕ × ℕ) :: R)) := by
  sorry

/-- base(2) の中身の語 `[(1,1,1),(1,1,1)]` の GTall 0。 -/
theorem base2_word_GTall : GTall 0 ([((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ)]) := by
  have h := GTall_zlet (v := 0) (K := [((1, 1, 1) : ℕ × ℕ × ℕ)]) (x := 1)
    (hK := by intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega)
    (hx := by omega)
    (hcone := base2_hcone)
    (hload0 := by
      intro w _; rw [Nat.sub_zero, mlift_one_letter 0 w, show 0 + 1 + w = w + 1 from by omega]
      exact base2_hload0 w)
    (hload := by
      intro w _ R hR hRW
      rw [Nat.sub_zero, mlift_one_letter 0 w, show 0 + 1 + w = w + 1 from by omega]
      exact base2_hload w R hR hRW)
  simpa using h

/-- ★ base(2) = (0,0,0)(1,1,1)(2,1,1)(2,1,1) ∈ W 0。 -/
theorem base2_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0)
    (WordsG_consT (v := 0) ⟨base2_word_GTall,
      by intro y hy; simp at hy; rcases hy with rfl | rfl <;> exact Nat.le_refl 1⟩
      (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

end BaseN
end TRIO
