/-
RFsnoc.lean: PVP_snoc_gen — general-f 遠い語頭+内容 append（PVF_snoc の general-f 版）。
GpT_snocz_core(GyG:93, bare頭, general-f) の塔に内容 Y を通す手術。
PVP_snoc_gen の ∀t wrapper は完成（hPV' を mlift_mlift で埋め、PVP_snocz に倣う）。
残余 = GpT_snocz_content（塔+内容の core）+ RLC level-shift（hY'）。
-/
import GzD

namespace TRIO
namespace RFsnoc

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-- GpT レベルの 遠い語頭+内容（general f）。GpT_snocz_core に内容 Y を通す（core surgery）。 -/
theorem GpT_snocz_content {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) {f : ℕ → ℕ} {b : ℕ} {W Y : TrioSeq} (hW : Fr W) (hYfr : Fr Y)
    (hPV : ∀ t, GpT A (o + t) f b (mlift W (b + liftOff f A o) t))
    (hY : RLC A o (fun _ => 0) b Y) :
    GpT A o f b (W ++ ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
  sorry

/-- RLC の段シフト（o → o+t、Y → mlift Y u t）。wrapper が o+t で GpT_snocz_content を使うため。 -/
theorem RLC_levelshift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {Y : TrioSeq}
    (hY : RLC A o (fun _ => 0) b Y) (t : ℕ) :
    RLC A (o + t) (fun _ => 0) b (mlift Y (b + liftOff f A o) t) := by
  sorry

/-- **PVP_snoc_gen**: general-f の PVF_snoc。∀t で GpT_snocz_content を回す（PVP_snocz に倣う、wrapper 完成）。 -/
theorem PVP_snoc_gen {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {b : ℕ} {W Y : TrioSeq} (hW : Fr W) (hYfr : Fr Y)
    (h : PVP A o f b W) (hY : RLC A o (fun _ => 0) b Y) :
    PVP A o f b (W ++ ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
  intro t
  set u := b + liftOff f A o with hu
  have eML : mlift (W ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) u t
      = mlift W u t ++ ((1, u + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y u t) := by
    rw [mlift_app hW (Hd_letter _ _), mlift_letter (show u < u + 1 by omega) hYfr t]
  rw [eML]
  have ehead : u + 1 + t = b + liftOff f A (o + t) + 1 := by rw [hu, liftOff_add_t hA]; omega
  rw [ehead]
  have huteq : b + liftOff f A (o + t) = u + t := by rw [hu, liftOff_add_t hA]; omega
  refine GpT_snocz_content (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    (Fr_mlift hW _ _) (Fr_mlift hYfr _ _) (fun t' => ?_) ?_
  · -- hPV': GpT A (o+t+t') f b (mlift (mlift W u t) (b+liftOff f A (o+t)) t')
    rw [huteq, mlift_mlift W u t t']
    have := h (t + t')
    rwa [show o + (t + t') = o + t + t' by omega, ← hu] at this
  · -- hY': RLC A (o+t) (fun_=>0) b (mlift Y u t)  = RLC_levelshift
    rw [hu]; exact RLC_levelshift hA hY t

end RFsnoc
end TRIO
