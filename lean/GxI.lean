/-
GxI.lean: シート行 476, 477, 484, 489〜518。

先頭にタイの中身の字がある段 v の語（GxG.BwP）を `hang_Wg` で段 0〜3 につなぐ。
-/
import GxH

namespace TRIO
namespace GxI

open Wset
open Small
open GwS
open Gw
open GwU
open GwV
open GwZ
open GxD
open GxG
open GxH

theorem hangLv {v m : ℕ} {l : List TrioSeq} (h : BwP v m l) {Z : TrioSeq}
    (hZ : (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: Z) ∈ Wg (2 * (v + 1))) :
    (((0, v, 0) : ℕ × ℕ × ℕ) :: (rword 0 v (pre v m ++ l) ++
      shiftr01 1 0 (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: Z))) ∈ Wg (2 * v) :=
  hangv (star_of_BwP h le_rfl) (fun x hx => rword_ge 0 v _ x hx) (Wg_shift hZ 1)
    (shift1_ge _) (by simp [shiftr01, entry]) (2 * v) le_rfl

theorem rowL {m : ℕ} {l : List TrioSeq} (h : BwP 0 m l) {Z : TrioSeq}
    (hZ : (((0, 1, 0) : ℕ × ℕ × ℕ) :: Z) ∈ Wg (2 * 1)) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: (rword 0 0 (pre 0 m ++ l) ++
      shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: Z))) ∈ W 0 :=
  GxB.Wg0_sub_W0 (hangLv h hZ)

theorem Bn : ∀ n, BwP 0 n []
  | 0 => BwP_nil 0
  | (n + 1) => BwP_pre_succ (Bn n)

theorem B3 : BwP 0 3 [] := Bn 3
theorem B4 : BwP 0 4 [] := Bn 4
theorem B5 : BwP 0 5 [] := Bn 5
theorem C3 : BwP 1 3 [] := BwP_pre_succ C2
theorem D1 : BwP 2 1 [] := BwP_pre_succ (BwP_nil 2)
theorem D2 : BwP 2 2 [] := BwP_pre_succ D1
theorem D3 : BwP 2 3 [] := BwP_pre_succ D2
theorem E2 : BwP 3 2 [] := BwP_pre_succ (BwP_pre_succ (BwP_nil 3))

theorem snz {v0 m : ℕ} (h : BwP v0 m []) : BwP v0 m [[]] := by
  simpa using Bw_snoczP (WOk_nil v0) h

theorem WOk_z (v0 : ℕ) : WOkWv v0 [[]] := WOkWv_singleton (RawWv_nil v0)

theorem WOk_zz (v0 : ℕ) : WOkWv v0 [[], []] := WOkWv_append (WOk_z v0) (WOk_z v0)

theorem D_110 : BwP 2 1 [[((1, 1, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 2) (Wg_mono (show 2 ≤ 2 * 2 by omega) Wg2_110) (by decide) (WOk_nil 2) D1

theorem W2_1121 : [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ Wg (2 * 1) := by
  have hA : ([] : TrioSeq) ∈ Wstarv 1 := fun _ a ha => by simpa using Wg_mono ha (Om_mem_Wg 1)
  have h := GxE.dead_snoc 1 le_rfl hA (by simp) 2 le_rfl
  simpa [shiftr01] using Wg_shift h 1

theorem C_1121 : BwP 1 1 [[((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 1) W2_1121 (by decide) (WOk_nil 1) C1

theorem D1z : BwP 2 1 [[]] := snz D1
theorem D2z : BwP 2 2 [[]] := snz D2

theorem D_120 : BwP 2 1 [[((1, 2, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 2) Wg4_120 (by decide) (WOk_nil 2) D1

theorem D_120_z : BwP 2 1 [[((1, 2, 0) : ℕ × ℕ × ℕ)], []] := by
  simpa using Bw_snoczP (WOkWv_singleton raw120) D_120

theorem D_1212 : BwP 2 1 [[((1, 2, 0) : ℕ × ℕ × ℕ), ((1, 2, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 2) Wg4_1212 (by decide) (WOk_nil 2) D1

theorem B2z : BwP 0 2 [[]] := snz B2

theorem B2zz : BwP 0 2 [[], []] := by
  simpa using Bw_snoczP (WOk_z 0) B2z

theorem B2zzz : BwP 0 2 [[], [], []] := by
  simpa using Bw_snoczP (WOk_zz 0) B2zz

theorem B2_100 : BwP 0 2 [[((1, 0, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 0) W100 (by decide) (WOk_nil 0) B2

theorem B2_1011 : BwP 0 2 [shiftr01 1 0 (((0, 0, 0) : ℕ × ℕ × ℕ) :: rword 0 0 (pre 0 0 ++ [[]]))] := by
  simpa using BwC (v0 := 0) (Wg_shift (Wg_of_BwP Gz0 le_rfl) 1) (shift1_ge _) (WOk_nil 0) B2

theorem C2z : BwP 1 2 [[]] := snz C2

theorem C2_110 : BwP 1 2 [[((1, 1, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 1) Wg2_110 (by decide) (WOk_nil 1) C2

theorem C2_110_z : BwP 1 2 [[((1, 1, 0) : ℕ × ℕ × ℕ)], []] := by
  simpa using Bw_snoczP (WOkWv_singleton raw1_110) C2_110

theorem C2_110110 : BwP 1 2 [[((1, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 1) Wg2_110_110 (by decide) (WOk_nil 1) C2

theorem B3z : BwP 0 3 [[]] := snz B3

theorem B3zz : BwP 0 3 [[], []] := by
  simpa using Bw_snoczP (WOk_z 0) B3z

theorem B4z : BwP 0 4 [[]] := snz B4
theorem B5z : BwP 0 5 [[]] := snz B5

/-- ★ シート行 476。 -/
theorem R476_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 1, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C_110 (Wg_of_BwP D_110 le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 477。 -/
theorem R477_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 1, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 1, 0), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have hZ2 := tower_snoc 2 (star_of_BwP D_110 le_rfl) (fun x hx => rword_ge 0 2 _ x hx) 4 le_rfl
  have hZ := hangLv C_110 hZ2
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 484。 -/
theorem R484_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B2 (Wg_of_BwP C_1121 le_rfl)

/-- ★ シート行 489。 -/
theorem R489_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C2 (Wg_of_BwP D1z le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 490。 -/
theorem R490_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C2 (Wg_of_BwP D_120 le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 491。 -/
theorem R491_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 2, 0), (3, 3, 1)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C2 (Wg_of_BwP D_120_z le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 492。 -/
theorem R492_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C2 (Wg_of_BwP D_1212 le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 493。 -/
theorem R493_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C2 (Wg_of_BwP D2 le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 494。 -/
theorem R494_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 3, 0), (3, 3, 0), (4, 4, 1), (5, 4, 0), (4, 4, 1), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have hZ2 := hangLv D2 (Wg_of_BwP E2 le_rfl)
  have hZ := hangLv C2 hZ2
  simpa [pre, rword, rcol, shiftr01] using rowL B2 hZ

/-- ★ シート行 495。 -/
theorem R495_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B2z

/-- ★ シート行 496。 -/
theorem R496_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_hang B2z Wg2_110 (by decide) (by simp [entry])

/-- ★ シート行 497。 -/
theorem R497_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01, GxC.L4] using W0_hang B2z L4_Wg L4_ge (by simp [entry, GxC.L4])

/-- ★ シート行 498。 -/
theorem R498_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B2z (Wg_of_BwP C2 le_rfl)

/-- ★ シート行 499。 -/
theorem R499_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B2z (Wg_of_BwP C2z le_rfl)

/-- ★ シート行 500。 -/
theorem R500_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have hZ := tower_snoc 1 (star_of_BwP C2z le_rfl) (fun x hx => rword_ge 0 1 _ x hx) 2 le_rfl
  simpa [pre, rword, rcol, shiftr01] using rowL B2z hZ

/-- ★ シート行 501。 -/
theorem R501_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have hZ2 := tower_snoc 2 (star_of_BwP D2z le_rfl) (fun x hx => rword_ge 0 2 _ x hx) 4 le_rfl
  have hZ := hangLv C2z hZ2
  simpa [pre, rword, rcol, shiftr01] using rowL B2z hZ

/-- ★ シート行 502。 -/
theorem R502_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B2zz

/-- ★ シート行 503。 -/
theorem R503_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B2zzz

/-- ★ シート行 504。 -/
theorem R504_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B2_100

/-- ★ シート行 505。 -/
theorem R505_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B2_1011

/-- ★ シート行 506。 -/
theorem R506_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B3

/-- ★ シート行 507。 -/
theorem R507_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B3 (Wg_of_BwP C2z le_rfl)

/-- ★ シート行 508。 -/
theorem R508_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B3 (Wg_of_BwP C2_110 le_rfl)

/-- ★ シート行 509。 -/
theorem R509_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B3 (Wg_of_BwP C2_110_z le_rfl)

/-- ★ シート行 510。 -/
theorem R510_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B3 (Wg_of_BwP C2_110110 le_rfl)

/-- ★ シート行 511。 -/
theorem R511_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowL B3 (Wg_of_BwP C3 le_rfl)

/-- ★ シート行 512。 -/
theorem R512_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have hZ := hangLv C3 (Wg_of_BwP D3 le_rfl)
  simpa [pre, rword, rcol, shiftr01] using rowL B3 hZ

/-- ★ シート行 513。 -/
theorem R513_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B3z

/-- ★ シート行 514。 -/
theorem R514_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B3zz

/-- ★ シート行 515。 -/
theorem R515_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B4

/-- ★ シート行 516。 -/
theorem R516_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B4z

/-- ★ シート行 517。 -/
theorem R517_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B5z

/-- ★ シート行 518 `(0,0,0)(1,1,1)(2,1,0)(2,0,0)`。 -/
theorem R518_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  have e : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0)] : TrioSeq) = [((0, 0, 0) : ℕ × ℕ × ℕ)] ++
      [((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)] ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := rfl
  rw [e, oper_snoc00'' _ (M := [((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)]) (d := 2)
    (by simp) (by simp [entry]) (by
      intro r hr1 hr2
      simp at hr2
      have : r = 1 := by omega
      subst this; simp [entry]) n]
  have h := W0_of_BwP (Bn n)
  rw [List.append_nil, rword_pre] at h
  simpa using h

#print axioms R476_mem
#print axioms R512_mem
#print axioms R518_mem

end GxI
end TRIO
