/-
GyJ.lean: 字の中身の文脈の族 RLC の遠い塔の公理 FarP_RLC と、字の中身の F の規則 RLC_F。

字の持ち上げ t は、錨 o の持ち上げ（upF o t G）に吸収させて GpT の族の公理 CtxP_GpT に帰着させる。
-/
import GyI

namespace TRIO
namespace GyJ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI

/-! ## 階段の交換 -/

theorem reStair_high_comm {A : List ℕ} {O : ℕ} (hA : ∀ a ∈ A, a < O) (b : ℕ) (H G : ℕ → ℕ)
    (t m : ℕ) :
    reStair b H G A (m + (if b + liftOff H A O < m then t else 0))
      = reStair b H G A m + (if b + liftOff (addF H G) A O < reStair b H G A m then t else 0) := by
  have hall : ∀ m', liftOff H A O ≤ m' → reStep 0 H G A A m' = sumOn G A := by
    intro m' hm'
    rw [reStep_lowP, lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := H) hA ha; omega)]
  have hk := liftOff_addF hA H G
  unfold reStair
  by_cases h : b + liftOff H A O < m
  · obtain ⟨m', rfl⟩ : ∃ m', m = b + m' := ⟨m - b, by omega⟩
    rw [if_pos h, show b + m' + t = b + (m' + t) by omega, reStep_base, reStep_base,
      hall (m' + t) (by omega), hall m' (by omega),
      if_pos (show b + liftOff (addF H G) A O < b + m' + sumOn G A by omega)]
    omega
  · rw [if_neg h, Nat.add_zero]
    have hmono : reStep b H G A A m ≤ reStep b H G A A (b + liftOff H A O) :=
      reStep_mono b H G A (by omega) A
    rw [reStep_base, hall _ le_rfl] at hmono
    rw [if_neg (by omega)]
    omega

theorem liftVal_cons_low {H : ℕ → ℕ} {A : List ℕ} {o a : ℕ} (hA : ∀ x ∈ A, x < o) (ha : a ∈ A) :
    liftVal H (o :: A) a = liftVal H A a := by
  unfold liftVal
  simp only [stepSum]
  rw [if_neg (by have := hA a ha; omega), Nat.zero_add]

theorem liftVal_cons_top {H : ℕ → ℕ} {A : List ℕ} {o : ℕ} (hA : ∀ x ∈ A, x < o) :
    liftVal H (o :: A) o = liftOff H A (o + H o) := by
  unfold liftVal
  simp only [stepSum]
  rw [if_pos (by omega), stepSum_all 0 (o + 1) H (fun x hx => by have := hA x hx; omega),
    sumOn_liftOff (fun x hx => by have := hA x hx; omega)]
  omega

theorem reStair_cons_top {A : List ℕ} {o : ℕ} (hA : ∀ x ∈ A, x < o) (b : ℕ) (H G G2 : ℕ → ℕ)
    (hG2 : ∀ a ∈ A, G2 a = G a) (m : ℕ) :
    reStair b H G2 (o :: A) m
      = reStair b H G A m +
        (if b + liftOff (addF H G) A (o + H o) < reStair b H G A m then G2 o else 0) := by
  have hA' : ∀ x ∈ A, x < o + H o := fun x hx => by have := hA x hx; omega
  have hall : ∀ m', liftOff H A (o + H o) ≤ m' → reStep 0 H G A A m' = sumOn G A := by
    intro m' hm'
    rw [reStep_lowP, lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := H) hA' ha; omega)]
  have hk := liftOff_addF hA' H G
  have etail : reStep b H G2 (o :: A) A m = reStep b H G A A m :=
    reStep_congr2 b m (fun x hx => liftVal_cons_low hA hx) (fun x hx => hG2 x hx)
  unfold reStair
  simp only [reStep]
  rw [etail, liftVal_cons_top hA]
  by_cases h : b + liftOff H A (o + H o) < m
  · obtain ⟨m', rfl⟩ : ∃ m', m = b + m' := ⟨m - b, by omega⟩
    rw [if_pos h, reStep_base, hall m' (by omega),
      if_pos (show b + liftOff (addF H G) A (o + H o) < b + m' + sumOn G A by omega)]
    omega
  · rw [if_neg h]
    have hmono : reStep b H G A A m ≤ reStep b H G A A (b + liftOff H A (o + H o)) :=
      reStep_mono b H G A (by omega) A
    rw [reStep_base, hall _ le_rfl] at hmono
    rw [if_neg (by omega)]
    omega

theorem reliftX_cons_top {A : List ℕ} {o : ℕ} (hA : ∀ x ∈ A, x < o) (b : ℕ) (H G G2 : ℕ → ℕ)
    (hG2 : ∀ a ∈ A, G2 a = G a) (X : TrioSeq) :
    reliftX b H G2 (o :: A) X
      = mlift (reliftX b H G A X) (b + liftOff (addF H G) A (o + H o)) (G2 o) := by
  unfold reliftX
  rw [mlift_eq_slift, slift_slift (reStair_stair b H G A) (stair_step _ _)]
  congr 1
  funext m
  exact reStair_cons_top hA b H G G2 hG2 m

theorem reOff_high_comm {A : List ℕ} {O : ℕ} (hA : ∀ a ∈ A, a < O) (H G : ℕ → ℕ) (t m : ℕ) :
    reOff H G A (m + (if liftOff H A O < m then t else 0))
      = reOff H G A m + (if liftOff (addF H G) A O < reOff H G A m then t else 0) := by
  have := reStair_high_comm hA 0 H G t m
  simpa [reStair, reOff] using this

theorem reOff_cons_top {A : List ℕ} {o : ℕ} (hA : ∀ x ∈ A, x < o) (H G G2 : ℕ → ℕ)
    (hG2 : ∀ a ∈ A, G2 a = G a) (m : ℕ) :
    reOff H G2 (o :: A) m
      = reOff H G A m + (if liftOff (addF H G) A (o + H o) < reOff H G A m then G2 o else 0) := by
  have := reStair_cons_top hA 0 H G G2 hG2 m
  simpa [reStair, reOff] using this

/-! ## 語と級の部品 -/

theorem PVP_shift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVP A o H b W) (t : ℕ) : PVP A (o + t) H b (mlift W (b + liftOff H A o) t) := by
  intro t'
  have := h (t + t')
  rw [show o + (t + t') = o + t + t' by omega] at this
  rw [liftOff_add_t hA, show b + (liftOff H A o + t) = b + liftOff H A o + t by omega, mlift_mlift]
  exact this

theorem PVP_relift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVP A o H b W) (G : ℕ → ℕ) : PVP A o (addF H G) b (reliftX b H G A W) := by
  intro t
  have := GpT_lift (fun a ha => by have := hA a ha; omega) (h t) G
  rwa [mlift_reliftX_high hA] at this

theorem GC_congr {A : List ℕ} {F1 F2 : ℕ → ℕ} (hF : ∀ a ∈ A, F1 a = F2 a) {τ b : ℕ} {L : TrioSeq}
    (h : GC A F1 τ b L) : GC A F2 τ b L := by
  have hlv : ∀ a, liftVal F1 A a = liftVal F2 A a := fun a => by
    unfold liftVal; rw [stepSum_congr 0 (a + 1) hF]
  have hl : lowP F1 A τ = lowP F2 A τ := by unfold lowP; simp only [hlv]
  unfold GC at h ⊢
  rw [← hl]
  have hs : sumOn F1 (lowP F1 A τ) = sumOn F2 (lowP F1 A τ) :=
    sumOn_congr (fun x hx => hF x (mem_lowP_iff.mp hx).1)
  rw [← hs]
  exact GpT_congr (fun x hx => (lowP_lt_o1 x hx).1) (fun x hx => hF x (mem_lowP_iff.mp hx).1) h

theorem lowP_cons_low {H : ℕ → ℕ} {A : List ℕ} {o τ : ℕ} (hA : ∀ x ∈ A, x < o)
    (hτ : τ ≤ liftVal H (o :: A) o) : lowP H (o :: A) τ = lowP H A τ := by
  unfold lowP
  rw [List.filter_cons, if_neg (by simpa using hτ)]
  exact List.filter_congr (fun x hx => by rw [liftVal_cons_low hA hx])

theorem GC_cons_low {H : ℕ → ℕ} {A : List ℕ} {o τ : ℕ} (hA : ∀ x ∈ A, x < o)
    (hτ : τ ≤ liftVal H (o :: A) o) {b : ℕ} {L : TrioSeq} (h : GC A H τ b L) :
    GC (o :: A) H τ b L := by
  unfold GC at h ⊢
  rw [lowP_cons_low hA hτ]; exact h

theorem mlift_snoc_bottom {Q : TrioSeq} {d v : ℕ} (hbot : BotGe Q d v) (a t : ℕ) :
    mlift (Q ++ [((d, v, 0) : ℕ × ℕ × ℕ)]) a t
      = mlift Q a t ++ [((d, v + (if a < v then t else 0), 0) : ℕ × ℕ × ℕ)] := by
  rw [mlift_eq_slift, mlift_eq_slift, slift_snoc, amin_snoc_bottom hbot]
  simp

def upF (o t : ℕ) (G : ℕ → ℕ) : ℕ → ℕ := fun a => if a = o then t else G a

theorem upF_low {A : List ℕ} {o : ℕ} (hA : ∀ x ∈ A, x < o) (t : ℕ) (G : ℕ → ℕ) :
    ∀ a ∈ A, upF o t G a = G a := fun a ha => by
  have := hA a ha
  simp [upF, show a ≠ o by omega]

theorem addF_upF_low {A : List ℕ} {o : ℕ} (hA : ∀ x ∈ A, x < o) (F : ℕ → ℕ) (t : ℕ) (G : ℕ → ℕ) :
    ∀ a ∈ A, addF F (upF o t G) a = addF F G a := fun a ha => by
  unfold addF; rw [upF_low hA t G a ha]

/-! ## 字の中身の族の遠い塔の公理 -/

theorem FarP_RLC {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {s : ℕ} (hs2 : 2 ≤ s) (hs : s ≤ liftOff H (o :: A) (o + 1)) :
    FarP (GC (o :: A)) (RLC A o) (o :: A) H s := by
  intro b P d hP hd hbot h1 h2 g b' hb'
  have hbotb : BotGe (mlift P b (b' - b)) d (b' + s) := by
    have := BotGe_slift hbot (stair_step b (b' - b))
    rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b' - b) = b' + s by omega] at this
    exact this
  have eB1 : mlift (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]) b (b' - b)
      = mlift P b (b' - b) ++ [((d, b' + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbot, if_pos (by omega), show b + s + (b' - b) = b' + s by omega]
  rw [eB1, reliftX_snoc_bottom hd b' hbotb H g (o :: A)]
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = reliftX b' H g (o :: A) (mlift P b (b' - b)) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = reOff H g (o :: A) s := ⟨_, rfl⟩
  rw [← hP1, ← hs1]
  have hP1Fr : Fr P1 := by rw [hP1]; exact Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
  have hbotP1 : BotGe P1 d (b' + s1) := by
    have := BotGe_slift hbotb (reStair_stair b' H g (o :: A))
    change BotGe (reliftX b' H g (o :: A) (mlift P b (b' - b))) d _ at this
    rwa [reStair_base, ← hP1, ← hs1] at this
  have hAO : ∀ a ∈ A, a < o + addF H g o := fun a ha => by have := hA a ha; omega
  have hs1ge : 2 ≤ s1 := by rw [hs1]; unfold reOff; omega
  have hs1k : s1 ≤ liftOff (addF H g) A (o + addF H g o) + 1 := by
    rw [hs1, ← liftVal_cons_top hA]
    have e1 := reOff_liftOff H g (o :: A) (o + 1)
    have e2 : liftOff (addF H g) (o :: A) (o + 1) = liftVal (addF H g) (o :: A) o + 1 := by
      unfold liftOff liftVal; omega
    have := reOff_mono H g (o :: A) hs
    omega
  intro W hW hPVW t
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff (addF H g) A (o + addF H g o) := ⟨_, rfl⟩
  rw [← hk] at hs1k ⊢
  have hFrB : Fr (P1 ++ [((d, b' + s1, 0) : ℕ × ℕ × ℕ)]) :=
    Fr_append hP1Fr (fun y hy => by simp at hy; subst hy; show 1 ≤ d; omega)
  rw [mlift_letterU hW hFrB (show b' + k < b' + k + 1 by omega), mlift_snoc_bottom hbotP1]
  obtain ⟨s2, hs2def⟩ : ∃ s2, s2 = s1 + (if k < s1 then t else 0) := ⟨_, rfl⟩
  have es2 : b' + s1 + (if b' + k < b' + s1 then t else 0) = b' + s2 := by
    rw [hs2def]; by_cases hc : k < s1 <;> simp [hc] <;> omega
  rw [es2]
  have hs2le : s2 ≤ k + 1 + t := by rw [hs2def]; split_ifs <;> omega
  have hs2ge : 2 ≤ s2 := by rw [hs2def]; split_ifs <;> omega
  have hbotP2 : BotGe (mlift P1 (b' + k) t) d (b' + s2) := by
    have := BotGe_slift hbotP1 (stair_step (b' + k) t)
    rw [← mlift_eq_slift] at this
    rwa [es2] at this
  have eQ : mlift W (b' + k) t ++ ((1, b' + k + 1 + t, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (mlift P1 (b' + k) t ++ [((d, b' + s2, 0) : ℕ × ℕ × ℕ)])
      = (mlift W (b' + k) t ++ ((1, b' + k + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift P1 (b' + k) t)) ++ [((d + 1, b' + s2, 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01, List.append_assoc]
  rw [eQ]
  have hAOt : ∀ a ∈ A, a < o + addF H g o + t := fun a ha => by have := hA a ha; omega
  -- 段 b3、持ち上げ G での接頭辞の形
  have eQ3 : ∀ G b3, b' ≤ b3 →
      reliftX b3 (addF H g) G A (mlift (mlift W (b' + k) t ++ ((1, b' + k + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift P1 (b' + k) t)) b' (b3 - b'))
      = mlift (reliftX b3 (addF H g) G A (mlift W b' (b3 - b')))
            (b3 + liftOff (addF (addF H g) G) A (o + addF H g o)) t ++
          ((1, b3 + liftOff (addF (addF H g) G) A (o + addF H g o) + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (reliftX b3 H (addF g (upF o t G)) (o :: A) (mlift P b (b3 - b))) := by
    intro G b3 hb3
    rw [mlift_letterU (Fr_mlift hW _ _) (Fr_mlift hP1Fr _ _) (show b' < b' + k + 1 + t by omega),
      reliftX_app (Fr_mlift (Fr_mlift hW _ _) _ _) (Hd_letter _ _),
      show b' + k + 1 + t + (b3 - b') = b3 + (k + 1 + t) by omega,
      reliftX_node (Fr_mlift (Fr_mlift hP1Fr _ _) _ _) b3 (k + 1 + t) 1 (addF H g) G A]
    have hlowA : lowP (addF H g) A (k + 1 + t) = A := lowP_all (fun a ha => by
      have := liftVal_lt_liftOff (f := addF H g) hAO ha; omega)
    have hro : reOff (addF H g) G A (k + 1 + t)
        = liftOff (addF (addF H g) G) A (o + addF H g o) + 1 + t := by
      have := reOff_above hAO (addF H g) G (1 + t)
      rw [← hk] at this
      rw [show k + 1 + t = k + (1 + t) by omega, this]; omega
    rw [hlowA, hro]
    have eW : reliftX b3 (addF H g) G A (mlift (mlift W (b' + k) t) b' (b3 - b'))
        = mlift (reliftX b3 (addF H g) G A (mlift W b' (b3 - b')))
            (b3 + liftOff (addF (addF H g) G) A (o + addF H g o)) t := by
      rw [mlift_commk, show b' + k + (b3 - b') = b3 + liftOff (addF H g) A (o + addF H g o) by omega,
        mlift_reliftX_high hAO]
    have eP : reliftX b3 (addF H g) G A (mlift (mlift P1 (b' + k) t) b' (b3 - b'))
        = reliftX b3 H (addF g (upF o t G)) (o :: A) (mlift P b (b3 - b)) := by
      rw [mlift_commk, show b' + k + (b3 - b') = b3 + liftOff (addF H g) A (o + addF H g o) by omega,
        mlift_reliftX_high hAO]
      have eP1 : mlift P1 b' (b3 - b') = reliftX b3 H g (o :: A) (mlift P b (b3 - b)) := by
        rw [hP1, mlift_reliftX, show b' + (b3 - b') = b3 by omega]
        have e := mlift_mlift P b (b' - b) (b3 - b')
        rw [show b + (b' - b) = b' by omega, show b' - b + (b3 - b') = b3 - b by omega] at e
        rw [e]
      rw [eP1]
      have ect := reliftX_cons_top hA b3 (addF H g) G (upF o t G) (upF_low hA t G)
        (reliftX b3 H g (o :: A) (mlift P b (b3 - b)))
      have eupo : upF o t G o = t := by simp [upF]
      rw [eupo] at ect
      rw [← ect, reliftX_comp]
    rw [eW, eP, show b3 + (liftOff (addF (addF H g) G) A (o + addF H g o) + 1 + t)
      = b3 + liftOff (addF (addF H g) G) A (o + addF H g o) + 1 + t by omega]
  -- 語の良さ
  have hPV3 : ∀ G b3, b' ≤ b3 →
      PVP A (o + addF H g o + t) (addF (addF H g) (upF o t G)) b3
        (mlift (reliftX b3 (addF H g) G A (mlift W b' (b3 - b')))
          (b3 + liftOff (addF (addF H g) G) A (o + addF H g o)) t) := by
    intro G b3 hb3
    have p1 := PVP_lift hAO hA1 (by omega) hW hPVW hb3
    have p2 := PVP_relift hAO p1 G
    have p3 := PVP_shift hAO p2 t
    exact PVP_congr hAOt (fun a ha => (addF_upF_low hA (addF H g) t G a ha).symm) p3
  have eO : ∀ G, addF (addF H g) (upF o t G) o = addF H g o + t := fun G => by simp [addF, upF]
  have eL1 : ∀ G, liftOff (addF (addF H g) (upF o t G)) A (o + addF H g o + t)
      = liftOff (addF (addF H g) G) A (o + addF H g o) + t := by
    intro G
    rw [liftOff_add_t hAO]
    congr 1
    unfold liftOff
    rw [stepSum_congr 0 _ (fun a ha => addF_upF_low hA (addF H g) t G a ha)]
  have hFP := ((CtxP_GpT hAOt hA1 (by omega) (o + addF H g o + t + s2)) (addF H g)).2.2.2 s2
    hs2ge (by unfold liftOff; omega)
  refine hFP b' _ (d + 1) (Fr_append (Fr_mlift hW _ _) (Fr_letter _ _)) (by omega)
    (BotGe_node (Fr_mlift hW _ _) (show b' + s2 ≤ b' + k + 1 + t by omega) hbotP2)
    (fun G b3 hb3 => ?_) (fun G b3 hb3 τ L h1τ hτ hL hGL => ?_)
  · rw [eQ3 G b3 hb3]
    have hR := h1 (addF g (upF o t G)) b3 (by omega) (fun _ => 0) b3 le_rfl
    rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, ← addF_assoc, eO G, ← Nat.add_assoc] at hR
    have hL := hR _ (Fr_mlift (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) _ _) (hPV3 G b3 hb3) 0
    rw [Nat.add_zero, mlift_zero, eL1 G,
      show b3 + (liftOff (addF (addF H g) G) A (o + addF H g o) + t) + 1
        = b3 + liftOff (addF (addF H g) G) A (o + addF H g o) + 1 + t by omega] at hL
    exact GpT_congr hAOt (fun a ha => addF_upF_low hA (addF H g) t G a ha) hL
  · rw [eQ3 G b3 hb3, show d + 1 - 1 = d by omega]
    have hτ' : τ < reOff H (addF g (upF o t G)) (o :: A) s := by
      rw [← reOff_comp, ← hs1,
        reOff_cons_top hA (addF H g) G (upF o t G) (upF_low hA t G) s1]
      have e2 := reOff_high_comm hAO (addF H g) G t s1
      rw [← hk, ← hs2def] at e2
      have eupo : upF o t G o = t := by simp [upF]
      rw [eupo, ← e2]
      exact hτ
    have hGL' : GC (o :: A) (addF H (addF g (upF o t G))) τ b3 L := by
      rw [← addF_assoc]
      have hc1 := GC_congr (A := A) (F2 := addF (addF H g) (upF o t G))
        (fun a ha => (addF_upF_low hA (addF H g) t G a ha).symm) hGL
      refine GC_cons_low hA ?_ hc1
      rw [liftVal_cons_top hA, eO G, ← Nat.add_assoc, eL1 G]
      have h3 := reOff_mono (addF H g) G A hs2le
      have h4 := reOff_above hAO (addF H g) G (1 + t)
      rw [← hk, show k + (1 + t) = k + 1 + t by omega] at h4
      omega
    have hR := h2 (addF g (upF o t G)) b3 (by omega) τ L h1τ hτ' hL hGL' (fun _ => 0) b3 le_rfl
    rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, ← addF_assoc, eO G, ← Nat.add_assoc] at hR
    have hL2 := hR _ (Fr_mlift (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) _ _) (hPV3 G b3 hb3) 0
    rw [Nat.add_zero, mlift_zero, eL1 G,
      show b3 + (liftOff (addF (addF H g) G) A (o + addF H g o) + t) + 1
        = b3 + liftOff (addF (addF H g) G) A (o + addF H g o) + 1 + t by omega] at hL2
    have eS : ∀ (X Y U : TrioSeq) (c : ℕ × ℕ × ℕ),
        X ++ c :: shiftr01 1 0 (Y ++ shiftr01 (d - 1) 0 U) = (X ++ c :: shiftr01 1 0 Y) ++ shiftr01 d 0 U := by
      intro X Y U c
      rw [shiftr01_append0, shiftr01_add0, show d - 1 + 1 = d by omega]
      simp [List.append_assoc]
    rw [eS] at hL2
    exact GpT_congr hAOt (fun a ha => addF_upF_low hA (addF H g) t G a ha) hL2

/-- ★ 字の中身の族は、F の級（錨の列 o :: A、行 1 の差 o+1）の文脈の公理を満たす。 -/
theorem CtxP_RLC {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) :
    CtxP (GC (o :: A)) (o :: A) (o + 1) (RLC A o) := fun H =>
  ⟨RLC_ax hA hA1 ho H, fun H2 b X hH hX => RLC_congr hA hH hX, fun g b X _ hX => RLC_lift hX g,
    fun s hs2 hs => FarP_RLC hA hA1 ho hs2 hs⟩

/-- ★ 字の中身の F（行 1 が節点 + 1）と、その子の並び。 -/
theorem RLC_F {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {K E : TrioSeq} (hK : Fr K) (hRK : RLC A o H b K)
    (hE : GpT (o :: A) (o + 1) H b E) :
    RLC A o H b (K ++ ((1, b + liftOff H (o :: A) (o + 1), 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  have := GpT_elim0 hE (CtxP_RLC hA hA1 ho) b le_rfl K hK hRK
  rwa [Nat.sub_self, mlift_zero] at this

end GyJ
end TRIO
