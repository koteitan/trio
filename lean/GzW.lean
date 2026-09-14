/-
GzW.lean: okWk は錨なし・段 k の文脈の族（CtxP (GC []) [] k）。
よって遠い字の中身に、子の級 GpT [] τ の並びを持つ節点（1 ≤ τ ≤ k）を足せる（R_child）。

FarP の場（段 b+s の子のない節点、2 ≤ s ≤ k）: 遠い語の中では FarP_GpT_ge を使う。
錨が k 以上なので再持ち上げは段 s を動かさず（reOff_k）、h2 の子の級は錨なし（lowP_k）。
h1 / h2 は外側の FarP の h1 / h2 が与える okWk の続きの族から出る。
-/
import GzP
import GzV

namespace TRIO
namespace GzW

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM GzN GzP GzU GzV

theorem BotGe_cons {Q : TrioSeq} {d v r z : ℕ} (hvr : v ≤ r) (hbot : BotGe Q d v) :
    BotGe (((1, r, z) : ℕ × ℕ × ℕ) :: Q) d v := by
  intro c y hc hy hr
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · show v ≤ r; exact hvr
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    rw [List.cons_append] at hr
    have h2 := rtg0_cons_unlift (by omega) hr Q.length (by rw [List.length_cons]; omega)
    rw [entry_cons]
    simp only [List.length_cons] at hy
    exact hbot c y' hc (by omega) (by simpa using h2)

theorem reOff_k {f g : ℕ → ℕ} {A : List ℕ} {k s : ℕ} (hAk : ∀ a ∈ A, k ≤ liftVal f A a) (hs : s ≤ k) :
    reOff f g A s = s :=
  reStair_k 0 f g hAk (m := s) (by omega)

theorem lowP_k {f : ℕ → ℕ} {A : List ℕ} {k τ : ℕ} (hAk : ∀ a ∈ A, k ≤ liftVal f A a) (hτ : τ ≤ k) :
    lowP f A τ = [] := by
  unfold lowP
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  have h2 := hAk a ha
  simp only [decide_eq_true_eq]
  omega

/-- ★ okWk は錨なし・段 k の文脈の族。 -/
theorem okWk_ctx {k : ℕ} (hk1 : 1 ≤ k) : CtxP (GC []) [] k (fun _ => okWk k) := by
  intro f
  refine ⟨okWk_ax hk1, fun f' b X _ h => h, fun g b X _ h => by rw [reliftX_nilA]; exact h, ?_⟩
  intro s hs2 hsk
  have hsk' : s ≤ k := by simpa [liftOff, stepSum] using hsk
  intro b P d hP hd hbot h1 h2
  show okWk k b (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)])
  have hP0 : okWk k b P := by
    have := h1 (fun _ => 0) b le_rfl
    simp only [reliftX_nilA, Nat.sub_self, mlift_zero] at this
    exact this
  have h2' : ∀ (h : ℕ → ℕ) b', b ≤ b' → ∀ τ L, 1 ≤ τ → τ < s → Fr L → GpT [] τ h b' L →
      okWk k b' (mlift P b (b' - b) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
    intro h b' hb' τ L h1τ hτ hL hGL
    have hGC : GC [] (addF f (fun _ => 0)) τ b' L := by
      unfold GC
      simpa [lowP, sumOn] using
        GpT_congr (A := []) (o := τ) (f' := addF f (fun _ => 0)) (by simp) (fun a ha => by simp at ha) hGL
    have := h2 (fun _ => 0) b' hb' τ L h1τ (by simpa [reOff, reStep] using hτ) hL hGC
    simp only [reliftX_nilA] at this
    exact this
  refine ⟨?_, LowC_snoc hP0.2.1 _ (by show b + s ≤ b + k; omega),
    fun b0 ws hC A o f' bb hb hR hA hA1 ho hAk hko => ?_⟩
  · -- 先頭
    have hH := (h2' (fun _ => 0) b le_rfl 1 [] le_rfl (by omega) Fr_nil (GpT_nil1 _ b)).1
    rw [Nat.sub_self, mlift_zero] at hH
    intro _
    have h0 := hH (by simp [shiftr01])
    rcases P with _ | ⟨x, P⟩
    · simp [shiftr01, entry] at h0 ⊢; omega
    · exact h0
  · -- 遠い語の中
    have hwb : b ≤ bb := (hR _ (List.mem_append_right _ (List.mem_singleton_self _))).1
    have hR0 : RawWsk k bb ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have hso : s ≤ liftOff f' A o := le_trans hsk' hko
    have hGk : ∀ g : ℕ → ℕ, (∀ a ∈ A, k ≤ liftVal (addF f' g) A a) ∧ k ≤ liftOff (addF f' g) A o :=
      fun g => ⟨liftVal_ge_addF hAk g, liftOff_ge_addF hA hko g⟩
    have hbotP : BotGe (mlift P b (bb - b)) d (bb + s) := by
      have := BotGe_slift hbot (stair_step b (bb - b))
      rw [← mlift_eq_slift] at this
      rwa [if_pos (by omega), show b + s + (bb - b) = bb + s by omega] at this
    have eL : mlift (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]) b (bb - b)
        = mlift P b (bb - b) ++ [((d, bb + s, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone _ _ (coneV_of_BotGe hbot (by omega))]
      show _ ++ [((d, b + s + (bb - b), 0) : ℕ × ℕ × ℕ)] = _
      rw [show b + s + (bb - b) = bb + s by omega]
    obtain ⟨r, hr⟩ : ∃ r, r = bb + liftOff f' A o + 1 := ⟨_, rfl⟩
    rw [← hr, farW_snoc]
    change GpT A o f' bb (farW bb r ws ++ fwW bb r b (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]))
    have eF : fwW bb r b (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)])
        = fwW bb r b P ++ [((d + 1, bb + s, 0) : ℕ × ℕ × ℕ)] := by
      unfold fwW; rw [eL]; simp [shiftr01]
    rw [eF, ← List.append_assoc]
    have hFP := FarP_GpT_ge hA hA1 ho (f := f') hs2 hso
    have hQ : Fr (farW bb r ws ++ fwW bb r b P) := Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
    have hRP : ∀ b', bb ≤ b' → RawWsk k b' (ws ++ [(b, P)]) := fun b' hb' =>
      RawWsk_snoc (RawWsk_mono hb' hR0) ⟨by omega, hP, hP0.1, hP0.2.1⟩
    have eP : ∀ b', bb ≤ b' → mlift (farW bb r ws ++ fwW bb r b P) bb (b' - bb)
        = farW b' (b' + liftOff f' A o + 1) (ws ++ [(b, P)]) := by
      intro b' hb'
      have := mlift_farW_basek (show bb < r by omega) (b' - bb) (ws ++ [(b, P)]) (hRP bb le_rfl)
      rw [farW_snoc] at this
      rw [show bb + (b' - bb) = b' by omega, show r + (b' - bb) = b' + liftOff f' A o + 1 by omega]
        at this
      exact this
    refine hFP bb _ (d + 1) hQ (by omega) ?_ (fun g b' hb' => ?_)
      (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
    · unfold fwW
      exact BotGe_node (Fr_farW _ _ _) (by omega) (BotGe_cons (by omega) hbotP)
    · rw [eP b' hb', reliftX_farWk hA b' f' g hAk _ (hRP b' hb')]
      exact hP0.2.2 b0 ws hC A o (addF f' g) b' (by omega) (hRP b' hb') hA hA1 ho (hGk g).1 (hGk g).2
    · rw [eP b' hb', reliftX_farWk hA b' f' g hAk _ (hRP b' hb')]
      have hτs : τ < s := by rw [reOff_k hAk hsk'] at hτ; exact hτ
      have hGL' : GpT [] τ (addF f' g) b' L := by
        simpa [GC, lowP_k (hGk g).1 (show τ ≤ k by omega), sumOn] using hGL
      obtain ⟨Y2, hY2⟩ : ∃ Y2 : TrioSeq, Y2 = mlift P b (b' - b) ++
          shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := ⟨_, rfl⟩
      have hY : okWk k b' Y2 := by rw [hY2]; exact h2' _ b' (by omega) τ L h1τ hτs hL hGL'
      have hFrY : Fr Y2 := by rw [hY2]; exact Fr_append (Fr_mlift hP _ _) (Fr_shift_node _ _ _)
      have hs2' : RawWsk k b' (ws ++ [(b', Y2)]) :=
        RawWsk_snoc (RawWsk_mono (by omega) hR0) ⟨le_rfl, hFrY, hY.1, hY.2.1⟩
      have := hY.2.2 b0 ws hC A o (addF f' g) b' (by omega) hs2' hA hA1 ho (hGk g).1 (hGk g).2
      rw [farW_snoc] at this
      dsimp only at this
      have eY : fwW b' (b' + liftOff (addF f' g) A o + 1) b' Y2
          = fwW b' (b' + liftOff (addF f' g) A o + 1) b P ++
            shiftr01 d 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
        unfold fwW
        rw [hY2, Nat.sub_self, mlift_zero, ← List.cons_append, shiftr01_append0, shiftr01_add0,
          show d - 1 + 1 = d by omega, List.cons_append]
      rw [eY] at this
      rw [farW_snoc, List.append_assoc, show d + 1 - 1 = d by omega]
      exact this

/-- ★ 遠い字の中身に、子の級 GpT [] τ の並びを持つ節点（1 ≤ τ ≤ k）を足す。 -/
theorem okWkF_node {k u τ : ℕ} (hk1 : 1 ≤ k) (hτk : τ ≤ k) {X L : TrioSeq} (h : okWkF k u X)
    (hL : GPF [] τ u L) : okWkF k u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _), ?_⟩
  have hGC : GC [] (fun _ => 0) τ u L := by simpa [GC, lowP, sumOn] using hL.1
  exact R_child (okWk_ctx hk1) (by simp) h.1 h.2 hGC (by simpa [liftOff, stepSum] using hτk)

end GzW
end TRIO
