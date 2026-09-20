/-
RFpvf.lean: 遠い語頭が Wg-load を子として包む PVF（marker-free, PVF_snoc + RLF_load）。
childLoad / R_farword の GpT 世界の部品。RLF_load が Wg-load を RLF に吸収、PVF_snoc が遠い語頭を足す。
注: この構成の頭は行1 = b+2（o=1, 内容は頭より深い）。childLoad/Trc4 の load は頭と同段
(Y∈Wg(2(v+1)) = 頭段) なので ch-Z/okLowS(low-load) が対応（別ルート）。本補題は深い load 用。
-/
import GzD

namespace TRIO
namespace RFpvf

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-- 遠い語頭 (1,b+2,1) が Wg-load Z（∈Wg(2b) based）を子として包む PVF（marker-free）。 -/
theorem PVF_farhead_load (b : ℕ) (Z : TrioSeq) (hZ : Z ∈ Wg (2 * b)) (hb : based Z) :
    PVF [] 1 b (((1, b + 1 + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Z) := by
  have hrlf : RLF [] 1 b (shiftr01 1 0 Z) := by
    have := RLF_load (A := []) (o := 1) (by simp) (by simp) le_rfl
      (RLF_nil (A := []) (o := 1) (by simp) (by simp) le_rfl b) hZ hb
    simpa using this
  have h := PVF_snoc (A := []) (o := 1) (by simp) (PVF_nil1 b) hrlf
  rw [shiftr01_add0] at h
  simpa using h

end RFpvf
end TRIO
