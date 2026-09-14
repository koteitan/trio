/-
HcE.lean: 子が段 c+1 以下の列（荷と単位のタイ）の F のタイの語に、空の F のタイを足す規則（HbT の写し）。

    GoodLc v Lds := 子は Fr で LowC (v+1) ∧ ∀ A0 k0, 条件 → ∀ H b0, GTWAc A0 k0 H b0 Lds v []

- 子が LowC (c+1) なら、錨 ≥ 1 の再持ち上げで動かない（reliftX_tie_inv）。
- FarCAc_embed: 族 (A0, k0) の並びは級 (S ++ A0, o) の族に埋め込める（子と中身は reliftX_ins_low）。
- GoodLc_Fsucc: GoodLc v Lds → GoodLc v (Lds ++ [[]])。F のタイは FarP_GpT_lt（s = liftOff + 1）。
  h1 は頭 Lds の語、h2 の節点は級 (S ++ A0, o) の族に埋め込んで HcD.RAc_node で置く。
-/
import HcD

namespace TRIO
namespace HcE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcB HcC HcD

theorem reliftX_tie_inv {A0 : List ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) {c : ℕ} {D : TrioSeq}
    (hD : LowC (c + 1) D) (H g : ℕ → ℕ) : reliftX c H g A0 D = D := by
  have := slift_append_low (A := []) hD (φ := reStair c H g A0)
    (fun m hm => reStair_tie c H g hA01 hm)
  simpa [slift_nil] using this

def GoodLc (v : ℕ) (Lds : List TrioSeq) : Prop :=
  (∀ D ∈ Lds, Fr D ∧ LowC (v + 1) D) ∧
    ∀ (A0 : List ℕ) (k0 : ℕ), (∀ a ∈ A0, 1 ≤ a) → 1 ≤ k0 → ∀ (H : ℕ → ℕ) (b0 : ℕ),
      GTWAc A0 k0 H b0 Lds v []

theorem map_tie_inv {A0 : List ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) {c : ℕ} {L : List TrioSeq}
    (hL : ∀ D ∈ L, LowC (c + 1) D) (H g : ℕ → ℕ) : L.map (reliftX c H g A0) = L := by
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left (fun D hD => reliftX_tie_inv hA01 (hL D hD) H g)

theorem GoodLc_GoodCh {v : ℕ} {Lds : List TrioSeq} (h : GoodLc v Lds) {A0 : List ℕ} {k0 : ℕ}
    (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) : GoodCh A0 k0 H v Lds := by
  have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
  refine ⟨fun D hD => ⟨(h.1 D hD).1, LowC_mono (show v + 1 ≤ v + reOff (fun _ => 0) H A0 k0 by omega) (h.1 D hD).2⟩, fun g b0 => ?_⟩
  rw [map_tie_inv hA01 (fun D hD => (h.1 D hD).2) H g]
  exact h.2 A0 k0 hA01 hk1 (addF H g) b0

theorem GoodLc_lift {v : ℕ} {Lds : List TrioSeq} (h : GoodLc v Lds) {u : ℕ} (hv : v ≤ u) :
    GoodLc u (Lds.map (fun D => mlift D v (u - v))) := by
  have hraw : ∀ D ∈ Lds.map (fun D => mlift D v (u - v)), Fr D ∧ LowC (u + 1) D := by
    intro D hD
    simp only [List.mem_map] at hD
    obtain ⟨D0, hD0, rfl⟩ := hD
    refine ⟨Fr_mlift (h.1 D0 hD0).1 _ _, ?_⟩
    have := LowC_mliftk (h.1 D0 hD0).2 (u - v)
    rwa [show v + 1 + (u - v) = u + 1 by omega] at this
  refine ⟨hraw, fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hub : u ≤ b := hw.1
  have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
  have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
  have := h.2 A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb
    (RawWsAc_snoc hR0 ⟨show v ≤ b by omega,
      fun D hD => ⟨(h.1 D hD).1, LowC_mono (show v + 1 ≤ v + reOff (fun _ => 0) H A0 k0 by omega) (h.1 D hD).2⟩,
      Fr_nil, fun h => absurd rfl h, LowC_nil _⟩) hSA hA hA1 ho hK hKo
  have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
    unfold reliftX; exact slift_nil _
  simp only [relWsc_snoc, farWc_snoc] at this ⊢
  rw [e0, map_tie_inv hA01 (fun D hD => (h.1 D hD).2) H g] at this
  rw [e0, map_tie_inv hA01 (fun D hD => (hraw D hD).2) H g, FTLc_rebase hv hub]
  simpa [fwH, mlift_nil] using this

/-! ## 族の埋め込み -/

theorem FarCAc_embed {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hC : FarCAc A0 k0 h b0 ws) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (hb : b0 ≤ b) (hR : RawWsAc A0 k0 h b ws)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    FarCAc (S ++ A0) o f b (relWsc A0 h g ws) := by
  intro g2 S2 o2 f2 b2 hf2 hb2 _ hSA2 hA2 hA12 ho2 hK2 hKo2
  have eW : relWsc (S ++ A0) f g2 (relWsc A0 h g ws) = relWsc A0 h (addF g g2) ws := by
    unfold relWsc
    rw [List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    have hw0 := hR w hw
    have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
      have := LowC_reliftX hw0.2.2.2.2 h g A0
      rwa [reOff_zero_comp] at this
    have hLD : ∀ D ∈ w.1, reliftX w.2.1 f g2 (S ++ A0) (reliftX w.2.1 h g A0 D)
        = reliftX w.2.1 h (addF g g2) A0 D := by
      intro D hD
      have hLD0 : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 D) := by
        have := LowC_reliftX (hw0.2.1 D hD).2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_ins_low hSA hf w.2.1 g2 hK hLD0, reliftX_comp]
    show ((w.1.map (reliftX w.2.1 h g A0)).map (reliftX w.2.1 f g2 (S ++ A0)), w.2.1,
        reliftX w.2.1 f g2 (S ++ A0) (reliftX w.2.1 h g A0 w.2.2))
      = (w.1.map (reliftX w.2.1 h (addF g g2) A0), w.2.1, reliftX w.2.1 h (addF g g2) A0 w.2.2)
    rw [reliftX_ins_low hSA hf w.2.1 g2 hK hL, reliftX_comp, List.map_map]
    congr 1
    exact List.map_congr_left (fun D hD => hLD D hD)
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
  have := hC (addF g g2) (S2 ++ S) o2 f2 b2 hf' (le_trans hb hb2) (RawWsAc_mono hb2 hR) hSA' hA'
    hA1' ho2 hK' hKo'
  rw [List.append_assoc] at this
  rw [eW]
  exact this

/-! ## 空の F のタイ -/

/-- ★ 空の F のタイを足す規則。 -/
theorem GoodLc_Fsucc {v : ℕ} {Lds : List TrioSeq} (hL : GoodLc v Lds) : GoodLc v (Lds ++ [[]]) := by
  have hraw : ∀ D ∈ Lds ++ [[]], Fr D ∧ LowC (v + 1) D := by
    intro D hD
    rcases List.mem_append.mp hD with hD | hD
    · exact hL.1 D hD
    · rw [List.mem_singleton] at hD; rw [hD]; exact ⟨Fr_nil, LowC_nil _⟩
  refine ⟨hraw, fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  have hR0 : RawWsAc A0 k0 H b ws := fun w hw => hR w (List.mem_append_left _ hw)
  have hw1 := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hvb : v ≤ b := hw1.1
  have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
  have hLds : ∀ D ∈ Lds, Fr D ∧ LowC (v + reOff (fun _ => 0) H A0 k0) D :=
    fun D hD => ⟨(hL.1 D hD).1, LowC_mono (by omega) (hL.1 D hD).2⟩
  have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
    unfold reliftX; exact slift_nil _
  have einv : ∀ (G K : ℕ → ℕ), Lds.map (reliftX v K G A0) = Lds :=
    fun G K => map_tie_inv hA01 (fun D hD => (hL.1 D hD).2) K G
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A0) o + 1 := ⟨_, rfl⟩
  simp only [relWsc_snoc, farWc_snoc, List.map_append, List.map_singleton]
  rw [e0 v H g, einv g H, ← hr]
  have eF : fwH b r (FTLc b r v (Lds ++ [[]])) v []
      = fwH b r (FTLc b r v Lds) v [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwH, FTLc_snoc, shiftr01, mlift_nil]
  rw [eF, ← List.append_assoc]
  have hRn : RawWsAc A0 k0 H b (ws ++ [(Lds, v, [])]) :=
    RawWsAc_snoc hR0 ⟨hvb, hLds, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  have hCn := hL.2 A0 k0 hA01 hk1 H b0 ws hC
  have eP0 : farWc b r (relWsc A0 H g ws) ++ fwH b r (FTLc b r v Lds) v []
      = farWc b r (relWsc A0 H g (ws ++ [(Lds, v, [])])) := by
    simp only [relWsc_snoc, farWc_snoc]
    rw [e0 v H g, einv g H]
  have eR : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A0) (mlift (farWc b r (relWsc A0 H g ws) ++ fwH b r (FTLc b r v Lds) v [])
          b (b' - b))
        = farWc b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
          (relWsc A0 H (addF g g') (ws ++ [(Lds, v, [])])) := by
    intro g' b' hb'
    rw [eP0, mlift_farWc_basek (show b < r by omega) (b' - b) _ (RawWskc_relWsc hRn g),
      show b + (b' - b) = b' by omega, show r + (b' - b) = b' + liftOff f (S ++ A0) o + 1 by omega,
      reliftX_farWcA hA hSA b' hf g' hK _ (RawWsAc_mono hb' hRn)]
  have hFP := FarP_GpT_lt (A := S ++ A0) (o := o) hA ho (f := f) (s := liftOff f (S ++ A0) o + 1)
    (by omega)
  have hP : Fr (farWc b r (relWsc A0 H g ws) ++ fwH b r (FTLc b r v Lds) v []) :=
    Fr_append (Fr_farWc _ _ _) (Fr_fwH _ _ _ _ _)
  have hbot : BotGe (farWc b r (relWsc A0 H g ws) ++ fwH b r (FTLc b r v Lds) v []) 2
      (b + (liftOff f (S ++ A0) o + 1)) := by
    unfold fwH
    exact BotGe_node (Fr_farWc _ _ _) (by omega)
      (BotGe_one (Fr_append (Fr_FTLc _ _ _ _) (Fr_mlift Fr_nil _ _)) _)
  suffices hG : GpT (S ++ A0) o f b ((farWc b r (relWsc A0 H g ws) ++ fwH b r (FTLc b r v Lds) v []) ++
      [((2, b + (liftOff f (S ++ A0) o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (liftOff f (S ++ A0) o + 1) = r by omega] at hG
  refine hFP b _ 2 hP (by omega) hbot (fun g' b' hb' => ?_) (fun g' b' hb' τ L h1τ hτ hL' hGL => ?_)
  · -- h1: 頭 Lds の空の語
    rw [eR g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    exact hCn (addF g g') S o (addF f g') b' hfG (by omega) (RawWsAc_mono hb' hRn) hSA hA hA1 ho
      hKG hKoG
  · -- h2: 級 (S ++ A0, o) の族に埋め込んで節点を置く
    rw [eR g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    have hτo : τ ≤ liftOff (addF f g') (S ++ A0) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hE := FarCAc_embed hC (g := addF g g') (S := S) (o := o) (f := addF f g') (b := b') hfG
      (by omega) (RawWsAc_mono hb' hR0) hSA hA hKG hKoG
    have hRX : RAc (S ++ A0) o (addF f g') b' ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      RAc_node hA1 ho hA Fr_nil (RAc_nil _ _ _ _) hGL hτo
    have hokY := RAc_okWA hRX
    have hGb : GoodLc b' (Lds.map (fun D => mlift D v (b' - v))) := GoodLc_lift hL (by omega)
    have hGch := GoodLc_GoodCh hGb hA1 ho (addF f g')
    have hC4 := hokY.2.2 b' le_rfl _ hGch b' (relWsc A0 H (addF g g') ws) hE
    have hRw := RawWsAc_relWsc (RawWsAc_mono hb' hR0) (addF g g')
    have hle : reOff (fun _ => 0) (addF H (addF g g')) A0 k0
        ≤ reOff (fun _ => 0) (addF f g') (S ++ A0) o := by
      rw [← liftOff_eq_reOff0 (addF f g') (S ++ A0) o]; exact hKoG
    have hR4 : RawWsAc (S ++ A0) o (addF f g') b'
        (relWsc A0 H (addF g g') ws ++
          [(Lds.map (fun D => mlift D v (b' - v)), b',
            mlift ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) b' (b' - b'))]) := by
      rw [Nat.sub_self, mlift_zero]
      refine RawWsAc_snoc (fun w hw => ?_)
        ⟨le_rfl, hGch.1, Fr_append Fr_nil (Fr_node _ _), hokY.1, hokY.2.1⟩
      have := hRw w hw
      exact ⟨this.1, fun D hD => ⟨(this.2.1 D hD).1, LowC_mono (by omega) (this.2.1 D hD).2⟩,
        this.2.2.1, this.2.2.2.1, LowC_mono (by omega) this.2.2.2.2⟩
    have := hC4 (fun _ => 0) [] o (addF f g') b' (fun a _ => by rw [addF_zero]) le_rfl hR4
      (by simp) (by simpa using hA) (by simpa using hA1) ho (by simp)
      (by simp only [List.nil_append, addF_zero, liftOff_eq_reOff0]; exact le_rfl)
    simp only [List.nil_append, relWsc_zero, farWc_snoc, Nat.sub_self, mlift_zero] at this
    rw [FTLc_rebase (show v ≤ b' by omega) le_rfl] at this
    simp only [relWsc_snoc, farWc_snoc]
    rw [e0 v H (addF g g'), einv (addF g g') H]
    have efw : fwH b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
          (FTLc b' (b' + liftOff (addF f g') (S ++ A0) o + 1) v Lds) v [] ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = fwH b' (b' + liftOff (addF f g') (S ++ A0) o + 1)
            (FTLc b' (b' + liftOff (addF f g') (S ++ A0) o + 1) v Lds) b'
            (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
      simp [fwH, shiftr01, mlift_nil, mlift_zero]
    rw [List.append_assoc, efw]
    exact this

end HcE
end TRIO
