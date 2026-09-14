/-
HaG.lean: 錨の列 A0・段 o の級の遠い語（中身は RA A0 o 0）の生成器の部品。

- okRA A0 o u X := Fr X ∧ RA A0 o 0 u X。荷（slot_load）と、段 u+τ（1 ≤ τ ≤ o）の節点（RA_node、子は GPF (A0 の τ 未満) τ）。
- PVF_farWA: 遠い語の並びは節点の子の並び（語の述語）。
- GPF_farWA_F / PVF_farWA_F: 遠い字と中身のあとの、行 1 が字と同じ b+o+1 の空の節点（F）。
  FarP_GpT_lt（s = o+1）。h2 の τ ≤ liftOff g A0 o の子は、状態 g に持ち上げた中身に RA_node で置く。
-/
import HaF

namespace TRIO
namespace HaG

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF

/-! ## 中身と並び -/

def okRA (A0 : List ℕ) (o u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ RA A0 o (fun _ => 0) u X

theorem okRA_nil (A0 : List ℕ) (o u : ℕ) : okRA A0 o u [] := ⟨Fr_nil, RA_nil A0 o _ u⟩

theorem okRA_load {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRA A0 o u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRA A0 o u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RA_ax hA01 ho _) h.1 h.2 Z hZ hb⟩

theorem okRA_node {A0 : List ℕ} {o u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRA A0 o u X) (hL : GPF A' τ u L) :
    okRA A0 o u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _), RA_node hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

def OkWsA (A0 : List ℕ) (o b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, w.1 ≤ b ∧ okRA A0 o w.1 w.2

theorem OkWsA_nil (A0 : List ℕ) (o b : ℕ) : OkWsA A0 o b [] := fun _ h => by simp at h

theorem OkWsA_cons {A0 : List ℕ} {o b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okRA A0 o u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsA A0 o b ws) : OkWsA A0 o b ((u, X) :: ws) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨hub, h⟩
  · exact hs w hw

theorem OkWsA_snoc {A0 : List ℕ} {o b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okRA A0 o u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsA A0 o b ws) : OkWsA A0 o b (ws ++ [(u, X)]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hs w hw
  · simp at hw; subst hw; exact ⟨hub, h⟩

theorem OkWsA_mono {A0 : List ℕ} {o b b' : ℕ} (hbb : b ≤ b') {ws : List (ℕ × TrioSeq)}
    (hs : OkWsA A0 o b ws) : OkWsA A0 o b' ws :=
  fun w hw => ⟨le_trans (hs w hw).1 hbb, (hs w hw).2⟩

theorem RawWsA_of_OkWsA {A0 : List ℕ} {o b : ℕ} {ws : List (ℕ × TrioSeq)} (h : OkWsA A0 o b ws) :
    RawWsA A0 o (fun _ => 0) b ws := fun w hw => by
  have hok := RA_okWA (h w hw).2.2
  exact ⟨(h w hw).1, (h w hw).2.1, hok.1, hok.2.1⟩

theorem FarCA_ofA {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} (b0 : ℕ) :
    ∀ ws : List (ℕ × TrioSeq), (∀ w ∈ ws, okWA A0 k0 H w.1 w.2) → FarCA A0 k0 H b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact FarCA_nil A0 k0 H b0
  | append_singleton ws w ih =>
      intro hok
      have hw := hok w (List.mem_append_right _ (List.mem_singleton_self _))
      exact hw.2.2 b0 ws (ih (fun w' h' => hok w' (List.mem_append_left _ h')))

theorem FarCA_of_OkWsA {A0 : List ℕ} {o b : ℕ} {ws : List (ℕ × TrioSeq)} (h : OkWsA A0 o b ws)
    (b0 : ℕ) : FarCA A0 o (fun _ => 0) b0 ws :=
  FarCA_ofA b0 ws (fun w hw => RA_okWA (h w hw).2.2)

theorem reOff_zz (A0 : List ℕ) (o : ℕ) :
    reOff (fun _ => 0) (addF (fun _ => 0) (fun _ => 0)) A0 o = o := by
  have e : addF (fun _ => (0 : ℕ)) (fun _ => 0) = (fun _ => 0) := by funext a; simp [addF]
  rw [e]; unfold reOff; rw [reStep_zeroG]; omega

/-- ★ 遠い語の並び（中身は okRA）は節点の子の並び（語の述語）。 -/
theorem PVF_farWA {A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ A0, a < o) (hA1 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (b : ℕ) (ws : List (ℕ × TrioSeq)) (h : OkWsA A0 o b ws) :
    PVF A0 o b (farW b (b + o + 1) ws) := by
  have := farWA_PVP (FarCA_of_OkWsA h b) (fun _ => 0) (S := []) (o := o) (f := fun _ => 0)
    (fun a _ => by simp [addF]) le_rfl (RawWsA_of_OkWsA h) (by simp) (by simpa using hA)
    (by simpa using hA1) ho (by simp) (by rw [reOff_zz]; simp [liftOff_zeroF])
  simp only [List.nil_append, liftOff_zeroF, relWs_zero] at this
  exact ⟨this, Fr_farW _ _ _⟩

/-! ## 字と同じ行 1 の F -/

/-- ★ 錨の列 A0・段 o の子の並びで、遠い字と中身のあとの F。 -/
theorem GPF_farWA_F {A0 : List ℕ} {o b u : ℕ} (hA : ∀ a ∈ A0, a < o) (hA1 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)} (hws : OkWsA A0 o b ws) {X : TrioSeq}
    (hX : okRA A0 o u X) :
    GPF A0 o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + o + 1, 0) : ℕ × ℕ × ℕ)]) := by
  have hlo : liftOff (fun _ => 0) A0 o = o := liftOff_zeroF A0 o
  have hFP := FarP_GpT_lt (A := A0) (o := o) hA ho (f := fun _ => 0) (s := o + 1)
    (by rw [hlo]; omega)
  have hP : Fr (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) :=
    Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
  have hs1 : ∀ b', b ≤ b' → OkWsA A0 o b' (ws ++ [(u, X)]) := fun b' hb' =>
    OkWsA_snoc (le_trans hub hb') hX (OkWsA_mono hb' hws)
  have hRk : RawWsk o b (ws ++ [(u, X)]) := by
    have := RawWsk_relWs (RawWsA_of_OkWsA (hs1 b le_rfl)) (fun _ => 0)
    rwa [reOff_zz, relWs_zero] at this
  have eP : ∀ b', b ≤ b' → mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b)
      = farW b' (b' + o + 1) (ws ++ [(u, X)]) := by
    intro b' hb'
    have := mlift_farW_basek (show b < b + o + 1 by omega) (b' - b) (ws ++ [(u, X)]) hRk
    rw [farW_snoc] at this
    rw [show b + (b' - b) = b' by omega, show b + o + 1 + (b' - b) = b' + o + 1 by omega] at this
    exact this
  have eR : ∀ (g : ℕ → ℕ) b', b ≤ b' →
      reliftX b' (fun _ => 0) g A0 (mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b))
        = farW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1)
          (relWs A0 (fun _ => 0) g (ws ++ [(u, X)])) := by
    intro g b' hb'
    rw [eP b' hb']
    have := reliftX_farWA (S := []) (o := o) (by simpa using hA) (by simp) b' (k0 := o)
      (h := fun _ => 0) (g := fun _ => 0) (f := fun _ => 0) (fun a _ => by simp [addF]) g (by simp)
      (ws ++ [(u, X)]) (RawWsA_of_OkWsA (hs1 b' hb'))
    simp only [List.nil_append, hlo, relWs_zero] at this
    have e00 : addF (fun _ => (0 : ℕ)) g = g := by funext a; simp [addF]
    rw [this]
    rw [e00]
  have hCg : ∀ (g : ℕ → ℕ) b', b ≤ b' →
      GpT A0 o (addF (fun _ => 0) g) b' (farW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1)
        (relWs A0 (fun _ => 0) g (ws ++ [(u, X)]))) := by
    intro g b' hb'
    have hK0 : reOff (fun _ => 0) (addF (fun _ => 0) g) A0 o ≤ liftOff (addF (fun _ => 0) g) A0 o := by
      rw [liftOff_eq_reOff0]
    have := FarCA_of_OkWsA (hs1 b' hb') b' g [] o (addF (fun _ => 0) g) b' (fun _ _ => rfl) le_rfl
      (RawWsA_of_OkWsA (hs1 b' hb')) (by simp) (by simpa using hA) (by simpa using hA1) ho (by simp)
      (by simpa using hK0)
    simpa using this
  have hbot : BotGe (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) (1 + 1) (b + (o + 1)) := by
    unfold fwW
    exact BotGe_node (Fr_farW _ _ _) (by omega) (BotGe_top (Fr_FLW (Fr_mlift hX.1 _ _)) _)
  refine ⟨?_, Fr_append hP (Fr_single (by omega) _ _)⟩
  suffices hG : GpT A0 o (fun _ => 0) b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + (o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (o + 1) = b + o + 1 by omega] at hG
  refine hFP b _ 2 hP (by omega) hbot (fun g b' hb' => ?_) (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
  · rw [eR g b' hb']
    exact hCg g b' hb'
  · rw [eR g b' hb']
    have hτo : τ ≤ liftOff (addF (fun _ => 0) g) A0 o := by
      have := reOff_above hA (fun _ => 0) g 1
      rw [hlo] at this
      omega
    -- 状態 g に持ち上げた最後の中身に節点を置く
    have hRX : RA A0 o (addF (fun _ => 0) g) b'
        (mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
          ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      have h1 := RA_lift hX.2 g
      have h2 := (RA_ax hA1 ho _).lift u _ (Fr_reliftX hX.1 _ _ _ _) h1 b' (le_trans hub hb')
      exact RA_node hA1 ho hA (Fr_mlift (Fr_reliftX hX.1 _ _ _ _) _ _) h2 hGL hτo
    have hokY := RA_okWA hRX
    have hRw : ∀ w ∈ ws, Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + reOff (fun _ => 0) (fun _ => 0) A0 o) w.2 :=
      fun w hw => (RawWsA_of_OkWsA hws w hw).2
    have hC3 := FarCA_relift (FarCA_of_OkWsA hws b') hRw g
    have hFrY : Fr (mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
        ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      Fr_append (Fr_mlift (Fr_reliftX hX.1 _ _ _ _) _ _) (Fr_node _ _)
    have hR3 := RawWsA_snoc (RawWsA_relWs (RawWsA_mono hb' (RawWsA_of_OkWsA hws)) g)
      (show RawWA A0 o (addF (fun _ => 0) g) b' (b', mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
        ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) from ⟨le_rfl, hFrY, hokY.1, hokY.2.1⟩)
    have hK0 : reOff (fun _ => 0) (addF (addF (fun _ => 0) g) (fun _ => 0)) A0 o
        ≤ liftOff (addF (fun _ => 0) g) A0 o := by
      rw [addF_zero, liftOff_eq_reOff0]
    have := hokY.2.2 b' _ hC3 (fun _ => 0) [] o (addF (fun _ => 0) g) b'
      (fun a _ => by rw [addF_zero]) le_rfl hR3 (by simp) (by simpa using hA) (by simpa using hA1) ho
      (by simp) (by simpa using hK0)
    simp only [List.nil_append, relWs_zero, farW_snoc] at this
    rw [relWs_snoc, farW_snoc, List.append_assoc]
    have e : fwW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1) u (reliftX u (fun _ => 0) g A0 X) ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = fwW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1) b'
          (mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
            ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    rw [e]
    exact this

/-- ★ 中身が全ての k ≥ o で okRA A0 k なら、F の語は語の述語（PVF）。 -/
theorem PVF_farWA_F {A0 : List ℕ} {o b u : ℕ} (hA : ∀ a ∈ A0, a < o) (hA1 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)} (hws : ∀ k, o ≤ k → OkWsA A0 k b ws)
    {X : TrioSeq} (hX : ∀ k, o ≤ k → okRA A0 k u X) :
    PVF A0 o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + o + 1, 0) : ℕ × ℕ × ℕ)]) := by
  have hG := GPF_farWA_F hA hA1 ho hub (hws o le_rfl) (hX o le_rfl)
  refine ⟨fun t => ?_, hG.2⟩
  rw [liftOff_zeroF A0 o]
  have hRk : RawWsk o b (ws ++ [(u, X)]) := by
    have := RawWsk_relWs (RawWsA_of_OkWsA (OkWsA_snoc hub (hX o le_rfl) (hws o le_rfl))) (fun _ => 0)
    rwa [reOff_zz, relWs_zero] at this
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
      (ws ++ [(u, X)]) hRk
    rw [farW_snoc, farW_snoc] at this
    rw [this, show b + o + 1 + t = b + (o + t) + 1 by omega]
  rw [em]
  exact (GPF_farWA_F (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega) hub
    (hws (o + t) (by omega)) (hX (o + t) (by omega))).1

end HaG
end TRIO
