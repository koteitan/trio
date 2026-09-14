/-
GzP.lean: タイの子の並び（錨なし、段 1）で、遠い字と低い列のあとに空の F が来る遠い語（行 1454 の形）。

    GPF_farW_F : OkWs b ws → okWF u X →
      GPF [] 1 b (farW b (b+2) ws ++ fwW b (b+2) u X ++ [(2, b+2, 0)])

F（行 1 が b+2、深さ 2）の根はタイの節点そのもの。FarP_GpT_lt を ([], 1) で使い、
h1 は F のない並び（PVF_farWs）、h2 は τ = 1（子つきのタイ、okWF_tie）だけで出る。
-/
import GzN

namespace TRIO
namespace GzP

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM GzN

theorem OkWs_snoc {b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okWF u X) :
    ∀ {ws : List (ℕ × TrioSeq)}, OkWs b ws → OkWs b (ws ++ [(u, X)])
  | [], _ => OkWs_cons hub h (OkWs_nil b)
  | w :: ws, hs => by
      have hw : RawW b w := hs.1 w (by simp)
      have hwo : okW w.1 w.2 := hs.2 w (by simp)
      have hs' : OkWs b ws :=
        ⟨fun w' h' => hs.1 w' (List.mem_cons_of_mem _ h'), fun w' h' => hs.2 w' (List.mem_cons_of_mem _ h')⟩
      have ih := OkWs_snoc hub h hs'
      refine ⟨fun w' h' => ?_, fun w' h' => ?_⟩
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact hw
        · exact ih.1 w' h'
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact hwo
        · exact ih.2 w' h'

theorem OkWs_mono {b b' : ℕ} (h : b ≤ b') {ws : List (ℕ × TrioSeq)} (hs : OkWs b ws) : OkWs b' ws :=
  ⟨RawWs_mono h hs.1, hs.2⟩

theorem reliftX_nilA (b : ℕ) (f g : ℕ → ℕ) (X : TrioSeq) : reliftX b f g [] X = X := by
  unfold reliftX
  have : reStair b f g [] = fun m => m := by funext m; simp [reStair, reStep]
  rw [this]; exact slift_id X

theorem okWF_lift {u u' : ℕ} (hu : u ≤ u') {X : TrioSeq} (h : okWF u X) : okWF u' (mlift X u (u' - u)) :=
  ⟨Fr_mlift h.1 _ _, okW_ax.lift u X h.1 h.2 u' hu⟩

/-- 錨なし・段 1 の遠い語の並びの GpT（任意の状態）。 -/
theorem GpT_farWs1 {b : ℕ} {ws : List (ℕ × TrioSeq)} (hs : OkWs b ws) (f : ℕ → ℕ) :
    GpT [] 1 f b (farW b (b + 2) ws) := by
  have := PVP_to_GpT (PVF_farWs (A := []) (o := 1) (by simp) (by simp) le_rfl b ws hs).1
  exact GpT_congr (by simp) (fun a ha => by simp at ha) this

/-- ★ 遠い字と低い列のあとの空の F（タイの子の並び）。 -/
theorem GPF_farW_F {b u : ℕ} (hub : u ≤ b) {ws : List (ℕ × TrioSeq)} (hws : OkWs b ws)
    {X : TrioSeq} (hX : okWF u X) :
    GPF [] 1 b (farW b (b + 2) ws ++ fwW b (b + 2) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)]) := by
  have hFP := FarP_GpT_lt (A := []) (o := 1) (by simp) le_rfl (f := fun _ => 0) (s := 2)
    (by simp [liftOff, stepSum])
  have hP : Fr (farW b (b + 2) ws ++ fwW b (b + 2) u X) := Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
  have hHX : Hd X := hX.2.1
  -- 持ち上げた並びの形
  have eP : ∀ b', b ≤ b' → mlift (farW b (b + 2) ws ++ fwW b (b + 2) u X) b (b' - b)
      = farW b' (b' + 2) (ws ++ [(u, X)]) := by
    intro b' hb'
    have hRu : RawWs b (ws ++ [(u, X)]) := (OkWs_snoc hub hX hws).1
    have := mlift_farW_base (show b < b + 2 by omega) (b' - b) (ws ++ [(u, X)]) hRu
    rw [farW_snoc] at this
    rw [show b + (b' - b) = b' by omega, show b + 2 + (b' - b) = b' + 2 by omega] at this
    exact this
  refine ⟨?_, Fr_append hP (Fr_single (by omega) _ _)⟩
  refine hFP b _ 2 hP (by omega) ?_ (fun g b' hb' => ?_) (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
  · have hbot : BotGe (farW b (b + 2) ws ++ ((1, b + 2, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (((1, b + 2, 1) : ℕ × ℕ × ℕ) :: mlift X u (b - u))) (1 + 1) (b + 2) :=
      BotGe_node (Fr_farW _ _ _) le_rfl (BotGe_top (Fr_FLW (Fr_mlift hX.1 _ _)) (b + 2))
    exact hbot
  · rw [reliftX_nilA, eP b' hb']
    exact GpT_farWs1 (OkWs_snoc (le_trans hub hb') hX (OkWs_mono hb' hws)) _
  · have hτ1 : τ = 1 := by
      have : reOff (fun _ => 0) g [] 2 = 2 := by simp [reOff, reStep]
      omega
    subst hτ1
    rw [reliftX_nilA, eP b' hb']
    have hGL' : GpT [] 1 (addF (fun _ => 0) g) b' L := by
      simpa [GC, lowP, sumOn] using hGL
    have hGF : GF 1 b' L := ⟨(Gof_one_iff b' L).mpr (GTs_of_GpT hGL'), hL⟩
    have hX' : okWF b' (mlift X u (b' - u) ++ ((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      okWF_tie (okWF_lift (le_trans hub hb') hX) hGF
    have hs := OkWs_snoc le_rfl hX' (OkWs_mono hb' hws)
    have e : farW b' (b' + 2) (ws ++ [(u, X)]) ++
        shiftr01 (2 - 1) 0 (((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = farW b' (b' + 2) (ws ++ [(b', mlift X u (b' - u) ++
            ((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      rw [farW_snoc, farW_snoc, List.append_assoc]
      congr 1
      show fwW b' (b' + 2) u X ++ _ = fwW b' (b' + 2) b' _
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    rw [e]
    exact GpT_farWs1 hs _

/-! ## 一般の段 o（錨なし）: 遠い字と低い列のあとの、行 1 が b+2 の空の節点 -/

theorem GpT_farWs {o b : ℕ} (ho : 1 ≤ o) {ws : List (ℕ × TrioSeq)} (hs : OkWs b ws) (f : ℕ → ℕ) :
    GpT [] o f b (farW b (b + o + 1) ws) := by
  have := PVP_to_GpT (PVF_farWs (A := []) (o := o) (by simp) (by simp) ho b ws hs).1
  exact GpT_congr (by simp) (fun a ha => by simp at ha) this

/-- ★ 錨なし・段 o の節点の子の並びで、遠い字と低い列のあとの行 1 が b+2 の空の節点。
o = 1 なら F（FarP_GpT_lt）、o ≥ 2 なら節点以下の段（FarP_GpT_ge）。h2 は τ = 1（子つきのタイ）だけ。 -/
theorem GPF_farW_bot2 {o b u : ℕ} (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : OkWs b ws) {X : TrioSeq} (hX : okWF u X) :
    GPF [] o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)]) := by
  have hFP : FarP (GC []) (fun h => GpT [] o h) [] (fun _ => 0) 2 := by
    rcases Nat.lt_or_ge o 2 with h | h
    · exact FarP_GpT_lt (A := []) (o := o) (by simp) ho (by simp [liftOff, stepSum]; omega)
    · exact FarP_GpT_ge (A := []) (o := o) (by simp) (by simp) ho le_rfl
        (by simp [liftOff, stepSum]; omega)
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
  · rw [reliftX_nilA, eP b' hb']
    exact GpT_farWs ho (OkWs_snoc (le_trans hub hb') hX (OkWs_mono hb' hws)) _
  · have hτ1 : τ = 1 := by
      have : reOff (fun _ => 0) g [] 2 = 2 := by simp [reOff, reStep]
      omega
    subst hτ1
    rw [reliftX_nilA, eP b' hb']
    have hGL' : GpT [] 1 (addF (fun _ => 0) g) b' L := by
      simpa [GC, lowP, sumOn] using hGL
    have hGF : GF 1 b' L := ⟨(Gof_one_iff b' L).mpr (GTs_of_GpT hGL'), hL⟩
    have hX' : okWF b' (mlift X u (b' - u) ++ ((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      okWF_tie (okWF_lift (le_trans hub hb') hX) hGF
    have hs := OkWs_snoc le_rfl hX' (OkWs_mono hb' hws)
    have e : farW b' (b' + o + 1) (ws ++ [(u, X)]) ++
        shiftr01 (2 - 1) 0 (((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = farW b' (b' + o + 1) (ws ++ [(b', mlift X u (b' - u) ++
            ((1, b' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      rw [farW_snoc, farW_snoc, List.append_assoc]
      congr 1
      show fwW b' (b' + o + 1) u X ++ _ = fwW b' (b' + o + 1) b' _
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    rw [e]
    exact GpT_farWs ho hs _

/-- ★ o ≥ 2 なら、行 1 が b+2 の空の節点は節点の段以下なので t の持ち上げで動かず、語の述語（PVF）になる。 -/
theorem PVF_farW_bot2 {o b u : ℕ} (ho : 2 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : OkWs b ws) {X : TrioSeq} (hX : okWF u X) :
    PVF [] o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)]) := by
  have hFr := (GPF_farW_bot2 (o := o) (by omega) hub hws hX).2
  refine ⟨fun t => ?_, hFr⟩
  have hRu : RawWs b (ws ++ [(u, X)]) := (OkWs_snoc hub hX hws).1
  have e1 : liftOff (fun _ => 0) [] o = o := by simp [liftOff, stepSum]
  rw [e1]
  have hP : Fr (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) :=
    Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
  have em : mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++ [((2, b + 2, 0) : ℕ × ℕ × ℕ)])
      (b + o) t = farW b (b + (o + t) + 1) ws ++ fwW b (b + (o + t) + 1) u X ++
        [((2, b + 2, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_low _ _ (show ((2, b + 2, 0) : ℕ × ℕ × ℕ).2.1 ≤ b + o by show b + 2 ≤ b + o; omega)]
    have := mlift_farW_high (show b + 1 ≤ b + o by omega) (show b + o < b + o + 1 by omega) t
      (ws ++ [(u, X)]) hRu
    rw [farW_snoc, farW_snoc] at this
    rw [this, show b + o + 1 + t = b + (o + t) + 1 by omega]
  rw [em]
  exact (GPF_farW_bot2 (o := o + t) (by omega) hub hws hX).1

end GzP
end TRIO
