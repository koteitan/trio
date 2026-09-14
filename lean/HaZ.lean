/-
HaZ.lean: 接頭辞 Q つきの錨つきの族の生成器の部品（HaG の写し）と、F の語を足しても TowP。

- okRAQ Q A0 o u X := Fr X ∧ RAQ Q A0 o 0 u X。荷と節点の規則。
- GPF_farWAQ_F: Q r ++ 遠い語 ++ 遠い字と中身 ++ F（行 1 が字と同じ r）。FarP_GpT_lt（s = o+1）。
- TowP_QP: TowP Q なら TowP (Q ++ Pf)（F の語を足す）。空の接頭辞 QNil も TowP。
- PVF_TowP: TowP の接頭辞は節点の子の並び（語の述語）。
-/
import HaY

namespace TRIO
namespace HaZ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HaI HaN HaW HaX HaY

variable {Q : ℕ → TrioSeq}

/-! ## 中身と並び -/

def okRAQ (Q : ℕ → TrioSeq) (A0 : List ℕ) (o u : ℕ) (X : TrioSeq) : Prop :=
  Fr X ∧ RAQ Q A0 o (fun _ => 0) u X

theorem okRAQ_nil (hQ : TowP Q) (A0 : List ℕ) (o u : ℕ) : okRAQ Q A0 o u [] :=
  ⟨Fr_nil, RAQ_nil hQ A0 o _ u⟩

theorem okRAQ_load (hQ : TowP Q) {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    {X : TrioSeq} (h : okRAQ Q A0 o u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRAQ Q A0 o u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RAQ_ax hQ hA01 ho _) h.1 h.2 Z hZ hb⟩

theorem okRAQ_node (hQ : TowP Q) {A0 : List ℕ} {o u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRAQ Q A0 o u X) (hL : GPF A' τ u L) :
    okRAQ Q A0 o u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _),
    RAQ_node hQ hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

def OkWsAQ (Q : ℕ → TrioSeq) (A0 : List ℕ) (o b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, w.1 ≤ b ∧ okRAQ Q A0 o w.1 w.2

theorem OkWsAQ_nil (Q : ℕ → TrioSeq) (A0 : List ℕ) (o b : ℕ) : OkWsAQ Q A0 o b [] :=
  fun _ h => by simp at h

theorem OkWsAQ_cons {A0 : List ℕ} {o b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okRAQ Q A0 o u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsAQ Q A0 o b ws) : OkWsAQ Q A0 o b ((u, X) :: ws) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨hub, h⟩
  · exact hs w hw

theorem OkWsAQ_snoc {A0 : List ℕ} {o b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okRAQ Q A0 o u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsAQ Q A0 o b ws) : OkWsAQ Q A0 o b (ws ++ [(u, X)]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hs w hw
  · simp at hw; subst hw; exact ⟨hub, h⟩

theorem OkWsAQ_mono {A0 : List ℕ} {o b b' : ℕ} (hbb : b ≤ b') {ws : List (ℕ × TrioSeq)}
    (hs : OkWsAQ Q A0 o b ws) : OkWsAQ Q A0 o b' ws :=
  fun w hw => ⟨le_trans (hs w hw).1 hbb, (hs w hw).2⟩

theorem RawWsA_of_OkWsAQ {A0 : List ℕ} {o b : ℕ} {ws : List (ℕ × TrioSeq)}
    (h : OkWsAQ Q A0 o b ws) : RawWsA A0 o (fun _ => 0) b ws := fun w hw => by
  have hok := RAQ_okWA (h w hw).2.2
  exact ⟨(h w hw).1, (h w hw).2.1, hok.1, hok.2.1⟩

theorem FarCAQ_ofA (hQ : TowP Q) {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} (b0 : ℕ) :
    ∀ ws : List (ℕ × TrioSeq), (∀ w ∈ ws, okWAQ Q A0 k0 H w.1 w.2) → FarCAQ Q A0 k0 H b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact FarCAQ_nil hQ A0 k0 H b0
  | append_singleton ws w ih =>
      intro hok
      have hw := hok w (List.mem_append_right _ (List.mem_singleton_self _))
      exact hw.2.2 b0 ws (ih (fun w' h' => hok w' (List.mem_append_left _ h')))

theorem FarCAQ_of_OkWsAQ (hQ : TowP Q) {A0 : List ℕ} {o b : ℕ} {ws : List (ℕ × TrioSeq)}
    (h : OkWsAQ Q A0 o b ws) (b0 : ℕ) : FarCAQ Q A0 o (fun _ => 0) b0 ws :=
  FarCAQ_ofA hQ b0 ws (fun w hw => RAQ_okWA (h w hw).2.2)

/-! ## 字と同じ行 1 の F -/

/-- ★ 接頭辞 Q と遠い語のあと、遠い字と中身のあとの F。 -/
theorem GPF_farWAQ_F (hQ : TowP Q) {A0 : List ℕ} {o b u : ℕ} (hA : ∀ a ∈ A0, a < o)
    (hA1 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : OkWsAQ Q A0 o b ws) {X : TrioSeq} (hX : okRAQ Q A0 o u X) :
    GPF A0 o b (Q (b + o + 1) ++ farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + o + 1, 0) : ℕ × ℕ × ℕ)]) := by
  have hlo : liftOff (fun _ => 0) A0 o = o := liftOff_zeroF A0 o
  have hFP := FarP_GpT_lt (A := A0) (o := o) hA ho (f := fun _ => 0) (s := o + 1)
    (by rw [hlo]; omega)
  have hP : Fr (Q (b + o + 1) ++ farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) :=
    Fr_append (Fr_QW hQ _ _ _) (Fr_fwW _ _ _ _)
  have hs1 : ∀ b', b ≤ b' → OkWsAQ Q A0 o b' (ws ++ [(u, X)]) := fun b' hb' =>
    OkWsAQ_snoc (le_trans hub hb') hX (OkWsAQ_mono hb' hws)
  have hRk : RawWsk o b (ws ++ [(u, X)]) := by
    have := RawWsk_relWs (RawWsA_of_OkWsAQ (hs1 b le_rfl)) (fun _ => 0)
    rwa [reOff_zz, relWs_zero] at this
  have eP : ∀ b', b ≤ b' →
      mlift (Q (b + o + 1) ++ farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b)
        = Q (b' + o + 1) ++ farW b' (b' + o + 1) (ws ++ [(u, X)]) := by
    intro b' hb'
    have := mlift_QW_base hQ (show b < b + o + 1 by omega) (b' - b) hRk
    rw [farW_snoc, ← List.append_assoc] at this
    rw [show b + (b' - b) = b' by omega, show b + o + 1 + (b' - b) = b' + o + 1 by omega] at this
    exact this
  have eR : ∀ (g : ℕ → ℕ) b', b ≤ b' →
      reliftX b' (fun _ => 0) g A0
          (mlift (Q (b + o + 1) ++ farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b))
        = Q (b' + liftOff (addF (fun _ => 0) g) A0 o + 1) ++
          farW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1)
            (relWs A0 (fun _ => 0) g (ws ++ [(u, X)])) := by
    intro g b' hb'
    rw [eP b' hb']
    have := reliftX_QWA hQ (S := []) (o := o) (by simpa using hA) (by simp) b' (k0 := o)
      (h := fun _ => 0) (g := fun _ => 0) (f := fun _ => 0) (fun a _ => by simp [addF]) g (by simp)
      (ws ++ [(u, X)]) (RawWsA_of_OkWsAQ (hs1 b' hb'))
    simp only [List.nil_append, hlo, relWs_zero] at this
    have e00 : addF (fun _ => (0 : ℕ)) g = g := by funext a; simp [addF]
    rw [this]
    rw [e00]
  have hCg : ∀ (g : ℕ → ℕ) b', b ≤ b' →
      GpT A0 o (addF (fun _ => 0) g) b' (Q (b' + liftOff (addF (fun _ => 0) g) A0 o + 1) ++
        farW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1)
          (relWs A0 (fun _ => 0) g (ws ++ [(u, X)]))) := by
    intro g b' hb'
    have hK0 : reOff (fun _ => 0) (addF (fun _ => 0) g) A0 o ≤ liftOff (addF (fun _ => 0) g) A0 o := by
      rw [liftOff_eq_reOff0]
    have := FarCAQ_of_OkWsAQ hQ (hs1 b' hb') b' g [] o (addF (fun _ => 0) g) b' (fun _ _ => rfl)
      le_rfl (RawWsA_of_OkWsAQ (hs1 b' hb')) (by simp) (by simpa using hA) (by simpa using hA1) ho
      (by simp) (by simpa using hK0)
    simpa using this
  have hbot : BotGe (Q (b + o + 1) ++ farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) (1 + 1)
      (b + (o + 1)) := by
    unfold fwW
    exact BotGe_node (Fr_QW hQ _ _ _) (by omega) (BotGe_top (Fr_FLW (Fr_mlift hX.1 _ _)) _)
  refine ⟨?_, Fr_append hP (GzF.Fr_single (by omega) _ _)⟩
  suffices hG : GpT A0 o (fun _ => 0) b (Q (b + o + 1) ++ farW b (b + o + 1) ws ++
      fwW b (b + o + 1) u X ++ [((2, b + (o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (o + 1) = b + o + 1 by omega] at hG
  refine hFP b _ 2 hP (by omega) hbot (fun g b' hb' => ?_) (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
  · rw [eR g b' hb']
    exact hCg g b' hb'
  · rw [eR g b' hb']
    have hτo : τ ≤ liftOff (addF (fun _ => 0) g) A0 o := by
      have := reOff_above hA (fun _ => 0) g 1
      rw [hlo] at this
      omega
    have hRX : RAQ Q A0 o (addF (fun _ => 0) g) b'
        (mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
          ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      have h1 := RAQ_lift hX.2 g
      have h2 := (RAQ_ax hQ hA1 ho _).lift u _ (Fr_reliftX hX.1 _ _ _ _) h1 b' (le_trans hub hb')
      exact RAQ_node hQ hA1 ho hA (Fr_mlift (Fr_reliftX hX.1 _ _ _ _) _ _) h2 hGL hτo
    have hokY := RAQ_okWA hRX
    have hRw : ∀ w ∈ ws, Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + reOff (fun _ => 0) (fun _ => 0) A0 o) w.2 :=
      fun w hw => (RawWsA_of_OkWsAQ hws w hw).2
    have hC3 := FarCAQ_relift (FarCAQ_of_OkWsAQ hQ hws b') hRw g
    have hFrY : Fr (mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
        ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      Fr_append (Fr_mlift (Fr_reliftX hX.1 _ _ _ _) _ _) (Fr_node _ _)
    have hR3 := RawWsA_snoc (RawWsA_relWs (RawWsA_mono hb' (RawWsA_of_OkWsAQ hws)) g)
      (show RawWA A0 o (addF (fun _ => 0) g) b' (b', mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
        ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) from ⟨le_rfl, hFrY, hokY.1, hokY.2.1⟩)
    have hK0 : reOff (fun _ => 0) (addF (addF (fun _ => 0) g) (fun _ => 0)) A0 o
        ≤ liftOff (addF (fun _ => 0) g) A0 o := by
      rw [addF_zero, liftOff_eq_reOff0]
    have := hokY.2.2 b' _ hC3 (fun _ => 0) [] o (addF (fun _ => 0) g) b'
      (fun a _ => by rw [addF_zero]) le_rfl hR3 (by simp) (by simpa using hA) (by simpa using hA1) ho
      (by simp) (by simpa using hK0)
    simp only [List.nil_append, relWs_zero, farW_snoc] at this
    rw [relWs_snoc, farW_snoc]
    have e : fwW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1) u (reliftX u (fun _ => 0) g A0 X) ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = fwW b' (b' + liftOff (addF (fun _ => 0) g) A0 o + 1) b'
          (mlift (reliftX u (fun _ => 0) g A0 X) u (b' - u) ++
            ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    simp only [List.append_assoc] at this ⊢
    rw [e]
    exact this

/-! ## F の語を足しても TowP -/

def QNil : ℕ → TrioSeq := fun _ => []

theorem TowP_nil : TowP QNil := by
  refine ⟨fun _ => Fr_nil, fun v r t _ => by simp [QNil, mlift_nil], fun A o _ b f g => ?_,
    fun A o f b hA hA1 ho => ?_⟩
  · show reliftX b f g A [] = []
    unfold reliftX; exact slift_nil _
  · show GpT A o f b []
    rcases Nat.lt_or_ge o 2 with h2 | h2
    · have ho1 : o = 1 := by omega
      subst ho1
      have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.mpr
        (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
      subst hA0
      exact GpT_nil1 f b
    · exact GpT_nil hA h2 f b

def QP (Q : ℕ → TrioSeq) (r : ℕ) : TrioSeq := Q r ++ Pf r

theorem QP_eq (Q : ℕ → TrioSeq) (b r : ℕ) :
    Q r ++ farW b r [] ++ fwW b r b [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] = QP Q r := by
  rw [QP, ← Pf_eq b r]; simp only [List.append_assoc]

/-- ★ TowP の接頭辞に F の語を足しても TowP。 -/
theorem TowP_QP (hQ : TowP Q) : TowP (QP Q) := by
  have hfr : ∀ r, Fr (QP Q r) := fun r => Fr_append (hQ.fr r) (Fr_Pf r)
  have hml : ∀ v r t, v < r → mlift (QP Q r) v t = QP Q (r + t) := by
    intro v r t h
    rw [QP, QP, mlift_app (hQ.fr r) (fun _ => rfl), hQ.lift v r t h, mlift_Pf h t]
  have hrel : ∀ (A : List ℕ) (o : ℕ), (∀ a ∈ A, a < o) → ∀ (b : ℕ) (f g : ℕ → ℕ),
      reliftX b f g A (QP Q (b + liftOff f A o + 1)) = QP Q (b + liftOff (addF f g) A o + 1) := by
    intro A o hA b f g
    rw [QP, QP, reliftX_app (hQ.fr _) (fun _ => rfl), hQ.relift A o hA b f g, reliftX_Pf hA b f g]
  refine ⟨hfr, hml, hrel, fun A o f b hA hA1 ho => ?_⟩
  have h0 := GPF_farWAQ_F hQ hA hA1 ho (le_refl b) (OkWsAQ_nil Q A o b) (okRAQ_nil hQ A o b)
  rw [QP_eq Q b (b + o + 1)] at h0
  have h1 := GpT_lift hA h0.1 f
  have e := hrel A o hA b (fun _ => 0) f
  rw [liftOff_zeroF] at e
  rw [e] at h1
  have e0 : addF (fun _ => (0 : ℕ)) f = f := by funext a; simp [addF]
  rwa [e0] at h1

/-- ★ TowP の接頭辞は節点の子の並び（語の述語）。 -/
theorem PVF_TowP (hQ : TowP Q) {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (b : ℕ) : PVF A o b (Q (b + o + 1)) := by
  have := hQ.pvp hA hA1 ho (fun _ => 0) b
  rw [liftOff_zeroF] at this
  exact ⟨this, hQ.fr _⟩

end HaZ
end TRIO
