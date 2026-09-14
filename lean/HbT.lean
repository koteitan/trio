/-
HbT.lean: 荷の子を持つ F のタイつきの語に、空の F のタイを足す規則（HbI の写し）。

- FarCA0_embed: 族 (A0, k0) の並びは、条件を満たす級 (S ++ A0, o)（状態 f）の族に埋め込める。
- GTWA0_Fsucc: 全ての族で頭 Lds の空の語が良ければ、頭 Lds ++ [[]]（空の F のタイを足した語）も良い。
  F のタイは FarP_GpT_lt（s = liftOff + 1）。h1 は頭 Lds の空の語。h2 の節点は級 (S ++ A0, o) の族に埋め込み、RA0_node で置く。
-/
import HbS

namespace TRIO
namespace HbT

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HbD HbM HbP HbQ HbR HbS

/-- ★ 族の埋め込み。 -/
theorem FarCA0_embed {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hC : FarCA0 A0 k0 h b0 ws) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (hb : b0 ≤ b) (hR : RawWsA0 A0 k0 h b ws)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    FarCA0 (S ++ A0) o f b (relWs0 A0 h g ws) := by
  intro g2 S2 o2 f2 b2 hf2 hb2 _ hSA2 hA2 hA12 ho2 hK2 hKo2
  have eW : relWs0 (S ++ A0) f g2 (relWs0 A0 h g ws) = relWs0 A0 h (addF g g2) ws := by
    unfold relWs0
    rw [List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    have hw0 := hR w hw
    have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
      have := LowC_reliftX hw0.2.2.2.2 h g A0
      rwa [reOff_zero_comp] at this
    show (w.1, w.2.1, reliftX w.2.1 f g2 (S ++ A0) (reliftX w.2.1 h g A0 w.2.2))
      = (w.1, w.2.1, reliftX w.2.1 h (addF g g2) A0 w.2.2)
    rw [reliftX_ins_low hSA hf w.2.1 g2 hK hL, reliftX_comp]
  obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g2
  have hf' : ∀ a ∈ A0, f2 a = addF h (addF g g2) a := fun a ha => by
    have h1 := hf2 a (List.mem_append_right _ ha)
    have h2 := hf a ha
    simp only [addF] at h1 h2 ⊢; omega
  have hSA' : ∀ s ∈ S2 ++ S, ∀ a ∈ A0, a < s := by
    intro s hs a ha
    rcases List.mem_append.mp hs with hs | hs
    · exact hSA2 s hs a (List.mem_append_right _ ha)
    · exact hSA s hs a ha
  have hA' : ∀ a ∈ (S2 ++ S) ++ A0, a < o2 := by rw [List.append_assoc]; exact hA2
  have hA1' : ∀ a ∈ (S2 ++ S) ++ A0, 1 ≤ a := by rw [List.append_assoc]; exact hA12
  have eLo : liftOff (addF f g2) (S ++ A0) o = reOff (fun _ => 0) (addF f g2) (S ++ A0) o :=
    liftOff_eq_reOff0 _ _ _
  have hK' : ∀ s ∈ S2 ++ S, reOff (fun _ => 0) (addF h (addF g g2)) A0 k0
      ≤ liftVal f2 ((S2 ++ S) ++ A0) s := by
    intro s hs
    rw [List.append_assoc]
    rcases List.mem_append.mp hs with hs | hs
    · have := hK2 s hs
      omega
    · have e : liftVal f2 (S2 ++ (S ++ A0)) s = liftVal (addF f g2) (S ++ A0) s := by
        unfold liftVal
        rw [stepSum_append, stepSum_none 0 f2 (s + 1) S2
          (fun s2 hs2 => by have := hSA2 s2 hs2 s (List.mem_append_left _ hs); omega),
          Nat.zero_add, stepSum_congr 0 (s + 1) hf2]
      rw [e]; exact hKG s hs
  have hKo' : reOff (fun _ => 0) (addF h (addF g g2)) A0 k0 ≤ liftOff f2 ((S2 ++ S) ++ A0) o2 := by
    rw [List.append_assoc]; omega
  have := hC (addF g g2) (S2 ++ S) o2 f2 b2 hf' (le_trans hb hb2) (RawWsA0_mono hb2 hR) hSA' hA'
    hA1' ho2 hK' hKo'
  rw [List.append_assoc] at this
  rw [eW]
  exact this

/-- ★ 空の F のタイを足す規則。 -/
theorem GTWA0_Fsucc {Lds : List TrioSeq}
    (hnil : ∀ (A0 : List ℕ) (k0 : ℕ), (∀ a ∈ A0, 1 ≤ a) → 1 ≤ k0 →
      ∀ (H : ℕ → ℕ) (b0 c0 : ℕ), GTWA0 A0 k0 H b0 Lds c0 [])
    {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) (b0 c0 : ℕ) :
    GTWA0 A0 k0 H b0 (Lds ++ [[]]) c0 [] := by
  intro ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hR0 : RawWsA0 A0 k0 H b ws := fun w hw => hR w (List.mem_append_left _ hw)
  have hw1 := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hc0 : c0 ≤ b := hw1.1
  have hLds : ∀ Ld ∈ Lds, Fr Ld ∧ LowC b Ld := fun Ld hLd => hw1.2.1 Ld (List.mem_append_left _ hLd)
  have e0 : ∀ c (G : ℕ → ℕ), reliftX c H G A0 ([] : TrioSeq) = [] := fun c G => by
    unfold reliftX; exact slift_nil _
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A0) o + 1 := ⟨_, rfl⟩
  simp only [relWs0_snoc, farW0_snoc]
  rw [e0 c0 g, ← hr]
  have eF : fwH b r (FTL0 r (Lds ++ [[]])) c0 [] = fwH b r (FTL0 r Lds) c0 [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwH, FTL0_snoc, shiftr01, mlift_nil]
  rw [eF, ← List.append_assoc]
  have hRn : RawWsA0 A0 k0 H b (ws ++ [(Lds, c0, [])]) :=
    RawWsA0_snoc hR0 ⟨hc0, hLds, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  have hCn := hnil A0 k0 hA01 hk1 H b0 c0 ws hC
  have eP0 : farW0 b r (relWs0 A0 H g ws) ++ fwH b r (FTL0 r Lds) c0 []
      = farW0 b r (relWs0 A0 H g (ws ++ [(Lds, c0, [])])) := by
    simp only [relWs0_snoc, farW0_snoc]
    rw [e0 c0 g]
  have eR : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A0) (mlift (farW0 b r (relWs0 A0 H g ws) ++ fwH b r (FTL0 r Lds) c0 []) b (b' - b))
        = farW0 b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
          (relWs0 A0 H (addF g g') (ws ++ [(Lds, c0, [])])) := by
    intro g' b' hb'
    rw [eP0, mlift_farW0_basek (show b < r by omega) (b' - b) _ (RawWsk0_relWs0 hRn g),
      show b + (b' - b) = b' by omega, show r + (b' - b) = b' + liftOff f (S ++ A0) o + 1 by omega,
      reliftX_farW0A hA hSA b' hf g' hK _ (RawWsA0_mono hb' hRn)]
  have hFP := FarP_GpT_lt (A := S ++ A0) (o := o) hA ho (f := f) (s := liftOff f (S ++ A0) o + 1)
    (by omega)
  have hP : Fr (farW0 b r (relWs0 A0 H g ws) ++ fwH b r (FTL0 r Lds) c0 []) :=
    Fr_append (Fr_farW0 _ _ _) (Fr_fwH _ _ _ _ _)
  have hbot : BotGe (farW0 b r (relWs0 A0 H g ws) ++ fwH b r (FTL0 r Lds) c0 []) 2
      (b + (liftOff f (S ++ A0) o + 1)) := by
    unfold fwH
    exact BotGe_node (Fr_farW0 _ _ _) (by omega) (BotGe_one (Fr_FTL0Y (Fr_mlift Fr_nil _ _)) _)
  suffices hG : GpT (S ++ A0) o f b ((farW0 b r (relWs0 A0 H g ws) ++ fwH b r (FTL0 r Lds) c0 []) ++
      [((2, b + (liftOff f (S ++ A0) o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (liftOff f (S ++ A0) o + 1) = r by omega] at hG
  refine hFP b _ 2 hP (by omega) hbot (fun g' b' hb' => ?_) (fun g' b' hb' τ L h1τ hτ hL hGL => ?_)
  · -- h1: 頭 Lds の空の語
    rw [eR g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    exact hCn (addF g g') S o (addF f g') b' hfG (by omega) (RawWsA0_mono hb' hRn) hSA hA hA1 ho
      hKG hKoG
  · -- h2: 級 (S ++ A0, o) の族に埋め込んで節点を置く
    rw [eR g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    have hτo : τ ≤ liftOff (addF f g') (S ++ A0) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hE := FarCA0_embed hC (g := addF g g') (S := S) (o := o) (f := addF f g') (b := b') hfG
      (by omega) (RawWsA0_mono hb' hR0) hSA hA hKG hKoG
    have hRX : RA0 (S ++ A0) o (addF f g') Lds b'
        ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      RA0_node hA1 ho hA Fr_nil (RA0_nil (hnil (S ++ A0) o hA1 ho) (addF f g') b') hGL hτo
    have hokY := RA0_okWA hRX
    have hC4 := hokY.2.2 b' (relWs0 A0 H (addF g g') ws) hE
    have hRw := RawWsA0_relWs0 (RawWsA0_mono hb' hR0) (addF g g')
    have hle : reOff (fun _ => 0) (addF H (addF g g')) A0 k0
        ≤ reOff (fun _ => 0) (addF f g') (S ++ A0) o := by
      rw [← liftOff_eq_reOff0 (addF f g') (S ++ A0) o]; exact hKoG
    have hR4 : RawWsA0 (S ++ A0) o (addF f g') b'
        (relWs0 A0 H (addF g g') ws ++
          [(Lds, b', [] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      refine RawWsA0_snoc (fun w hw => ?_)
        ⟨le_rfl, fun Ld hLd => ⟨(hLds Ld hLd).1, LowC_mono (by omega) (hLds Ld hLd).2⟩,
          Fr_append Fr_nil (Fr_node _ _), hokY.1, hokY.2.1⟩
      have := hRw w hw
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, LowC_mono (by omega) this.2.2.2.2⟩
    have := hC4 (fun _ => 0) [] o (addF f g') b' (fun a _ => by rw [addF_zero]) le_rfl hR4
      (by simp) (by simpa using hA) (by simpa using hA1) ho (by simp)
      (by simp only [List.nil_append, addF_zero, liftOff_eq_reOff0]; exact le_rfl)
    simp only [List.nil_append, relWs0_zero, farW0_snoc] at this
    simp only [relWs0_snoc, farW0_snoc]
    rw [e0 c0 (addF g g')]
    have efw : fwH b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
          (FTL0 (b' + liftOff (addF f g') (S ++ A0) o + 1) Lds) c0 [] ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = fwH b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
            (FTL0 (b' + liftOff (addF f g') (S ++ A0) o + 1) Lds) b'
            (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      simp [fwH, shiftr01, mlift_nil, mlift_zero]
    rw [List.append_assoc, efw]
    exact this

end HbT
end TRIO
