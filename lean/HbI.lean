/-
HbI.lean: F のタイの規則（本数 n の空の語から本数 n+1 の空の語へ）。

- FarCAn_embed: 族 (A0, k0) の並びは、条件を満たす級 (S ++ A0, o)（状態 f）の族に埋め込める。
- GTWAn_nil_succ: F のタイは FarP_GpT_lt（s = liftOff + 1）。
  h1 は本数 n の空の語。h2 の節点（τ ≤ 級の差）は、並びを級 (S ++ A0, o) の族に埋め込み、その族の中身に RAn_node で置く。
- GTWAn_nil: 全ての n（帰納。本数 0 は潰れ）。
-/
import HbH

namespace TRIO
namespace HbI

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HbD HbE HbF HbG HbH

/-- ★ 族の埋め込み。 -/
theorem FarCAn_embed {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    (hC : FarCAn A0 k0 h b0 ws) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (hb : b0 ≤ b) (hR : RawWsAn A0 k0 h b ws)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    FarCAn (S ++ A0) o f b (relWsn A0 h g ws) := by
  intro g2 S2 o2 f2 b2 hf2 hb2 _ hSA2 hA2 hA12 ho2 hK2 hKo2
  have eW : relWsn (S ++ A0) f g2 (relWsn A0 h g ws) = relWsn A0 h (addF g g2) ws := by
    unfold relWsn
    rw [List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    have hw0 := hR w hw
    have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
      have := LowC_reliftX hw0.2.2.2 h g A0
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
  have := hC (addF g g2) (S2 ++ S) o2 f2 b2 hf' (le_trans hb hb2) (RawWsAn_mono hb2 hR) hSA' hA'
    hA1' ho2 hK' hKo'
  rw [List.append_assoc] at this
  rw [eW]
  exact this

/-- ★ F のタイの規則。 -/
theorem GTWAn_nil_succ {n : ℕ}
    (hnil : ∀ (A0 : List ℕ) (k0 : ℕ), (∀ a ∈ A0, 1 ≤ a) → 1 ≤ k0 →
      ∀ (H : ℕ → ℕ) (b0 c0 : ℕ), GTWAn A0 k0 H b0 n c0 [])
    {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) (b0 c0 : ℕ) :
    GTWAn A0 k0 H b0 (n + 1) c0 [] := by
  intro ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hR0 : RawWsAn A0 k0 H b ws := fun w hw => hR w (List.mem_append_left _ hw)
  have hc0 : c0 ≤ b := (hR _ (List.mem_append_right _ (List.mem_singleton_self _))).1
  have e0 : ∀ c (G : ℕ → ℕ), reliftX c H G A0 ([] : TrioSeq) = [] := fun c G => by
    unfold reliftX; exact slift_nil _
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A0) o + 1 := ⟨_, rfl⟩
  simp only [relWsn_snoc, farWn_snoc]
  rw [e0 c0 g, ← hr]
  have eF : fwWn b r (n + 1) c0 [] = fwWn b r n c0 [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwWn, FT_succ, shiftr01, mlift_nil]
  rw [eF, ← List.append_assoc]
  have hRn : RawWsAn A0 k0 H b (ws ++ [(n, c0, [])]) :=
    RawWsAn_snoc hR0 ⟨hc0, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  have hCn := hnil A0 k0 hA01 hk1 H b0 c0 ws hC
  have eP0 : farWn b r (relWsn A0 H g ws) ++ fwWn b r n c0 []
      = farWn b r (relWsn A0 H g (ws ++ [(n, c0, [])])) := by
    simp only [relWsn_snoc, farWn_snoc]
    rw [e0 c0 g]
  have eR : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A0) (mlift (farWn b r (relWsn A0 H g ws) ++ fwWn b r n c0 []) b (b' - b))
        = farWn b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
          (relWsn A0 H (addF g g') (ws ++ [(n, c0, [])])) := by
    intro g' b' hb'
    rw [eP0, mlift_farWn_basek (show b < r by omega) (b' - b) _ (RawWskn_relWsn hRn g),
      show b + (b' - b) = b' by omega, show r + (b' - b) = b' + liftOff f (S ++ A0) o + 1 by omega,
      reliftX_farWnA hA hSA b' hf g' hK _ (RawWsAn_mono hb' hRn)]
  have hFP := FarP_GpT_lt (A := S ++ A0) (o := o) hA ho (f := f) (s := liftOff f (S ++ A0) o + 1)
    (by omega)
  have hP : Fr (farWn b r (relWsn A0 H g ws) ++ fwWn b r n c0 []) :=
    Fr_append (Fr_farWn _ _ _) (Fr_fwWn _ _ _ _ _)
  have hbot : BotGe (farWn b r (relWsn A0 H g ws) ++ fwWn b r n c0 []) 2
      (b + (liftOff f (S ++ A0) o + 1)) := by
    unfold fwWn
    exact BotGe_node (Fr_farWn _ _ _) (by omega) (BotGe_top (Fr_FTY (Fr_mlift Fr_nil _ _)) _)
  suffices hG : GpT (S ++ A0) o f b ((farWn b r (relWsn A0 H g ws) ++ fwWn b r n c0 []) ++
      [((2, b + (liftOff f (S ++ A0) o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (liftOff f (S ++ A0) o + 1) = r by omega] at hG
  refine hFP b _ 2 hP (by omega) hbot (fun g' b' hb' => ?_) (fun g' b' hb' τ L h1τ hτ hL hGL => ?_)
  · -- h1: 本数 n の空の語
    rw [eR g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    exact hCn (addF g g') S o (addF f g') b' hfG (by omega) (RawWsAn_mono hb' hRn) hSA hA hA1 ho
      hKG hKoG
  · -- h2: 級 (S ++ A0, o) の族に埋め込んで節点を置く
    rw [eR g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    have hτo : τ ≤ liftOff (addF f g') (S ++ A0) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hE := FarCAn_embed hC (g := addF g g') (S := S) (o := o) (f := addF f g') (b := b') hfG
      (by omega) (RawWsAn_mono hb' hR0) hSA hA hKG hKoG
    have hRX : RAn (S ++ A0) o (addF f g') n b'
        ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      RAn_node hA1 ho hA Fr_nil (RAn_nil (hnil (S ++ A0) o hA1 ho) (addF f g') b') hGL hτo
    have hokY := RAn_okWA hRX
    have hC4 := hokY.2.2 b' (relWsn A0 H (addF g g') ws) hE
    have hRw := RawWsAn_relWsn (RawWsAn_mono hb' hR0) (addF g g')
    have hle : reOff (fun _ => 0) (addF H (addF g g')) A0 k0 ≤ reOff (fun _ => 0) (addF f g') (S ++ A0) o := by
      rw [← liftOff_eq_reOff0 (addF f g') (S ++ A0) o]; exact hKoG
    have hR4 : RawWsAn (S ++ A0) o (addF f g') b'
        (relWsn A0 H (addF g g') ws ++ [(n, b', [] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      refine RawWsAn_snoc (fun w hw => ?_) ⟨le_rfl, Fr_append Fr_nil (Fr_node _ _), hokY.1, hokY.2.1⟩
      have := hRw w hw
      exact ⟨this.1, this.2.1, this.2.2.1, LowC_mono (by omega) this.2.2.2⟩
    have := hC4 (fun _ => 0) [] o (addF f g') b' (fun a _ => by rw [addF_zero]) le_rfl hR4
      (by simp) (by simpa using hA) (by simpa using hA1) ho (by simp)
      (by simp only [List.nil_append, addF_zero, liftOff_eq_reOff0]; exact le_rfl)
    simp only [List.nil_append, relWsn_zero, farWn_snoc] at this
    simp only [relWsn_snoc, farWn_snoc]
    rw [e0 c0 (addF g g')]
    have efw : fwWn b' (b' + liftOff (addF f g') (S ++ A0) o + 1) n c0 [] ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = fwWn b' (b' + liftOff (addF f g') (S ++ A0) o + 1) n b'
          (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      simp [fwWn, shiftr01, mlift_nil, mlift_zero]
    rw [List.append_assoc, efw]
    exact this

/-- ★ 全ての本数 n で、空の語の規則。 -/
theorem GTWAn_nil : ∀ (n : ℕ) (A0 : List ℕ) (k0 : ℕ), (∀ a ∈ A0, 1 ≤ a) → 1 ≤ k0 →
    ∀ (H : ℕ → ℕ) (b0 c0 : ℕ), GTWAn A0 k0 H b0 n c0 []
  | 0 => fun A0 k0 _ _ H b0 c0 => GTWAn_nil0 A0 k0 H b0 c0
  | n + 1 => fun _ _ hA01 hk1 H b0 c0 => GTWAn_nil_succ (GTWAn_nil n) hA01 hk1 H b0 c0

end HbI
end TRIO
