/-
GzY.lean: 錨なし・段 o の節点の子の並びで、遠い字と低い列（okWk o）のあとの、行 1 が字と同じ b+o+1 の空の節点（F）。

FarP_GpT_lt（s = o+1 > o）。h2 の子の段は τ ≤ o なので GzW.okWkF_node（k = o）で出る。
F は t の持ち上げで字と同じだけ動くので、中身が全ての k ≥ o で okWk k なら語の述語（PVF）になる。
-/
import GzP
import GzW

namespace TRIO
namespace GzY

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW

/-- ★ 錨なし・段 o の子の並びで、遠い字と低い列のあとの F。 -/
theorem GPF_farW_Fr {o b u : ℕ} (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : OkWsk o b ws) {X : TrioSeq} (hX : okWkF o u X) :
    GPF [] o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + o + 1, 0) : ℕ × ℕ × ℕ)]) := by
  have hFP := FarP_GpT_lt (A := []) (o := o) (by simp) ho (f := fun _ => 0) (s := o + 1)
    (by simp [liftOff, stepSum])
  have hP : Fr (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) :=
    Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
  have hlo : ∀ h : ℕ → ℕ, liftOff h [] o = o := fun h => by simp [liftOff, stepSum]
  have eP : ∀ b', b ≤ b' → mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b)
      = farW b' (b' + o + 1) (ws ++ [(u, X)]) := by
    intro b' hb'
    have hRu : RawWsk o b (ws ++ [(u, X)]) := (OkWsk_snoc hub hX hws).1
    have := mlift_farW_basek (show b < b + o + 1 by omega) (b' - b) (ws ++ [(u, X)]) hRu
    rw [farW_snoc] at this
    rw [show b + (b' - b) = b' by omega, show b + o + 1 + (b' - b) = b' + o + 1 by omega] at this
    exact this
  have hGw : ∀ (h : ℕ → ℕ) b' (ws' : List (ℕ × TrioSeq)), OkWsk o b' ws' →
      GpT [] o h b' (farW b' (b' + o + 1) ws') := by
    intro h b' ws' hs
    have := GpT_farWsk (A := []) (o := o) (by simp) (by simp) ho (by simp) le_rfl hs h
    rwa [hlo] at this
  have hbot : BotGe (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) (1 + 1) (b + (o + 1)) := by
    unfold fwW
    exact BotGe_node (Fr_farW _ _ _) (by omega) (BotGe_top (Fr_FLW (Fr_mlift hX.1 _ _)) _)
  refine ⟨?_, Fr_append hP (Fr_single (by omega) _ _)⟩
  suffices h : GpT [] o (fun _ => 0) b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + (o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (o + 1) = b + o + 1 by omega] at h
  refine hFP b _ 2 hP (by omega) hbot (fun g b' hb' => ?_) (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
  · rw [reliftX_nilA, eP b' hb']
    exact hGw _ b' _ (OkWsk_snoc (le_trans hub hb') hX (OkWsk_mono hb' hws))
  · have hτo : τ ≤ o := by
      have : reOff (fun _ => 0) g [] (o + 1) = o + 1 := by simp [reOff, reStep]
      omega
    rw [reliftX_nilA, eP b' hb']
    have hGL' : GpT [] τ (addF (fun _ => 0) g) b' L := by
      simpa [GC, lowP, sumOn] using hGL
    have hGF : GPF [] τ b' L := ⟨GpT_congr (by simp) (fun a ha => by simp at ha) hGL', hL⟩
    have hX' := okWkF_node ho hτo (okWkF_lift ho (le_trans hub hb') hX) hGF
    have hs := OkWsk_snoc le_rfl hX' (OkWsk_mono hb' hws)
    have e : farW b' (b' + o + 1) (ws ++ [(u, X)]) ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = farW b' (b' + o + 1) (ws ++ [(b', mlift X u (b' - u) ++
            ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      rw [farW_snoc, farW_snoc, List.append_assoc]
      congr 1
      show fwW b' (b' + o + 1) u X ++ _ = fwW b' (b' + o + 1) b' _
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    rw [e]
    exact hGw _ b' _ hs

/-- ★ 中身が全ての k ≥ o で okWk k なら、F の語は語の述語（PVF）。 -/
theorem PVF_farW_Fr {o b u : ℕ} (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : ∀ k, o ≤ k → OkWsk k b ws) {X : TrioSeq} (hX : ∀ k, o ≤ k → okWkF k u X) :
    PVF [] o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + o + 1, 0) : ℕ × ℕ × ℕ)]) := by
  have hG := GPF_farW_Fr ho hub (hws o le_rfl) (hX o le_rfl)
  refine ⟨fun t => ?_, hG.2⟩
  rw [liftOff_zeroF [] o]
  have hRu : RawWsk o b (ws ++ [(u, X)]) := (OkWsk_snoc hub (hX o le_rfl) (hws o le_rfl)).1
  have hbot : BotGe (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) 2 (b + o + 1) := by
    unfold fwW
    exact BotGe_node (Fr_farW _ _ _) le_rfl (BotGe_top (Fr_FLW (Fr_mlift (hX o le_rfl).1 _ _)) _)
  have em : mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
        [((2, b + o + 1, 0) : ℕ × ℕ × ℕ)]) (b + o) t
      = farW b (b + (o + t) + 1) ws ++ fwW b (b + (o + t) + 1) u X ++
        [((2, b + (o + t) + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone _ _ (coneV_of_BotGe hbot (show b + o < b + o + 1 by omega))]
    show mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) (b + o) t ++
      [((2, b + o + 1 + t, 0) : ℕ × ℕ × ℕ)] = _
    have := mlift_farW_highk (show b + o ≤ b + o by omega) (show b + o < b + o + 1 by omega) t
      (ws ++ [(u, X)]) hRu
    rw [farW_snoc, farW_snoc] at this
    rw [this, show b + o + 1 + t = b + (o + t) + 1 by omega]
  rw [em]
  exact (GPF_farW_Fr (o := o + t) (by omega) hub (hws (o + t) (by omega)) (hX (o + t) (by omega))).1

end GzY
end TRIO
