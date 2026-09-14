/-
GzS.lean: 錨が全て 2 以上の節点の子の並びで、遠い字と低い列のあとの行 1 が b+2 の空の節点（行 1462 の F の子の形）。

錨が 2 以上なら、再持ち上げは段 b+2 を動かさず（reOff 2 = 2）、τ = 1 の級は錨なし（lowP A 1 = []）。
よって GzP の GPF_farW_bot2 と同じく、FarP_GpT_ge / lt の h2 は子つきのタイだけで出る。
-/
import GzP

namespace TRIO
namespace GzS

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM GzN GzP

theorem lowP_ge2 {f : ℕ → ℕ} {A : List ℕ} (hA2 : ∀ a ∈ A, 2 ≤ a) : lowP f A 1 = [] := by
  unfold lowP
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  have h1 : a ≤ liftVal f A a := by unfold liftVal; omega
  have h2 := hA2 a ha
  simp only [decide_eq_true_eq]
  omega

theorem reOff_two {f g : ℕ → ℕ} {A : List ℕ} (hA2 : ∀ a ∈ A, 2 ≤ a) : reOff f g A 2 = 2 := by
  unfold reOff
  have key : ∀ A' : List ℕ, (∀ a ∈ A', 2 ≤ a) → reStep 0 f g A A' 2 = 0 := by
    intro A' hA'
    induction A' with
    | nil => rfl
    | cons a A' ih =>
        simp only [reStep]
        have h1 := hA' a (by simp)
        have h2 : a ≤ liftVal f A a := by unfold liftVal; omega
        rw [if_neg (by omega), ih (fun x hx => hA' x (List.mem_cons_of_mem a hx))]
  rw [key A hA2]

theorem GpT_farWsA {A : List ℕ} {o b : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {ws : List (ℕ × TrioSeq)} (hs : OkWs b ws) (f : ℕ → ℕ) :
    GpT A o f b (farW b (b + liftOff f A o + 1) ws) :=
  FarCW_of b ws hs.2 A o f b le_rfl hs.1 hA hA1 ho

/-- ★ 錨が全て 2 以上の節点の子の並びで、遠い字と低い列のあとの行 1 が b+2 の空の節点。 -/
theorem GPF_farW_bot2A {A : List ℕ} {o b u : ℕ} (hA : ∀ a ∈ A, a < o) (hA2 : ∀ a ∈ A, 2 ≤ a)
    (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)} (hws : OkWs b ws) {X : TrioSeq}
    (hX : okWF u X) :
    GPF A o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)]) := by
  have hA1 : ∀ a ∈ A, 1 ≤ a := fun a ha => by have := hA2 a ha; omega
  have hlo : liftOff (fun _ => 0) A o = o := liftOff_zeroF A o
  have hFP : FarP (GC A) (fun h => GpT A o h) A (fun _ => 0) 2 := by
    rcases Nat.lt_or_ge o 2 with h | h
    · exact FarP_GpT_lt hA ho (by rw [hlo]; omega)
    · exact FarP_GpT_ge hA hA1 ho le_rfl (by rw [hlo]; omega)
  have hP : Fr (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) :=
    Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
  have eP : ∀ b', b ≤ b' → mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b)
      = farW b' (b' + o + 1) (ws ++ [(u, X)]) := by
    intro b' hb'
    have hRu : RawWs b (ws ++ [(u, X)]) := (OkWs_snoc hub hX hws).1
    have := mlift_farW_base (show b < b + o + 1 by omega) (b' - b) (ws ++ [(u, X)]) hRu
    rw [farW_snoc] at this
    rw [show b + (b' - b) = b' by omega, show b + o + 1 + (b' - b) = b' + o + 1 by omega] at this
    exact this
  refine ⟨?_, Fr_append hP (Fr_single (by omega) _ _)⟩
  refine hFP b _ 2 hP (by omega) ?_ (fun g b' hb' => ?_) (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
  · exact BotGe_node (Fr_farW _ _ _) (by omega) (BotGe_top (Fr_FLW (Fr_mlift hX.1 _ _)) (b + 2))
  · have hs := OkWs_snoc (le_trans hub hb') hX (OkWs_mono hb' hws)
    rw [eP b' hb']
    have e := reliftX_farW hA hA1 b' (fun _ => 0) g (ws ++ [(u, X)]) hs.1
    rw [hlo] at e
    rw [e]
    exact GpT_farWsA hA hA1 ho hs _
  · have hτ1 : τ = 1 := by
      have := reOff_two (f := fun _ => 0) (g := g) hA2
      omega
    subst hτ1
    have hs0 := OkWs_snoc (le_trans hub hb') hX (OkWs_mono hb' hws)
    rw [eP b' hb']
    have e := reliftX_farW hA hA1 b' (fun _ => 0) g (ws ++ [(u, X)]) hs0.1
    rw [hlo] at e
    rw [e]
    have hGL' : GpT [] 1 (addF (fun _ => 0) g) b' L := by
      simpa [GC, lowP_ge2 hA2, sumOn] using hGL
    have hGF : GF 1 b' L := ⟨(Gof_one_iff b' L).mpr (GTs_of_GpT hGL'), hL⟩
    have hX' : okWF b' (mlift X u (b' - u) ++ ((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      okWF_tie (okWF_lift (le_trans hub hb') hX) hGF
    have hs := OkWs_snoc le_rfl hX' (OkWs_mono hb' hws)
    have e2 : farW b' (b' + liftOff (addF (fun _ => 0) g) A o + 1) (ws ++ [(u, X)]) ++
        shiftr01 (2 - 1) 0 (((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = farW b' (b' + liftOff (addF (fun _ => 0) g) A o + 1) (ws ++ [(b', mlift X u (b' - u) ++
            ((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      rw [farW_snoc, farW_snoc, List.append_assoc]
      congr 1
      show fwW b' _ u X ++ _ = fwW b' _ b' _
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    rw [e2]
    exact GpT_farWsA hA hA1 ho hs _

/-- ★ o ≥ 2 なら語の述語（PVF）。 -/
theorem PVF_farW_bot2A {A : List ℕ} {o b u : ℕ} (hA : ∀ a ∈ A, a < o) (hA2 : ∀ a ∈ A, 2 ≤ a)
    (ho : 2 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)} (hws : OkWs b ws) {X : TrioSeq}
    (hX : okWF u X) :
    PVF A o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)]) := by
  have hFr := (GPF_farW_bot2A hA hA2 (by omega) hub hws hX).2
  refine ⟨fun t => ?_, hFr⟩
  have hRu : RawWs b (ws ++ [(u, X)]) := (OkWs_snoc hub hX hws).1
  rw [liftOff_zeroF A o]
  have em : mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)])
      (b + o) t = farW b (b + (o + t) + 1) ws ++ fwW b (b + (o + t) + 1) u X ++
        [((2, b + 2, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_low _ _ (show ((2, b + 2, 0) : ℕ × ℕ × ℕ).2.1 ≤ b + o by show b + 2 ≤ b + o; omega)]
    have := mlift_farW_high (show b + 1 ≤ b + o by omega) (show b + o < b + o + 1 by omega) t
      (ws ++ [(u, X)]) hRu
    rw [farW_snoc, farW_snoc] at this
    rw [this, show b + o + 1 + t = b + (o + t) + 1 by omega]
  rw [em]
  exact (GPF_farW_bot2A (o := o + t) (fun a ha => by have := hA a ha; omega) hA2 (by omega) hub hws hX).1

end GzS
end TRIO
