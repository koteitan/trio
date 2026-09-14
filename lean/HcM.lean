/-
HcM.lean: 子を塊と F の位置のタイの並びにした遠い語の、埋め込みで閉じた子の並びの良さ GoodChuX。

    EmbU A k H g S o f := 族 (A, k, H) を再持ち上げ g で級 (S ++ A, o) の状態 f に埋め込む条件
    GoodChuX A k H u Lds := 塊が低い ∧ ∀ 埋め込み (g S o f) と段 b ≥ u、級 (S ++ A, o, f) の良い接頭辞 ws、
      GpT (S ++ A) o f b (farWu b r (ws ++ [(Lds を g で再持ち上げした並び, u, [])]))

- EmbU_comp: 埋め込みの合成。FarCAu_embed: 族の並びの埋め込み（HcE.FarCAc_embed の写し）。
- GoodChuX_emb（埋め込み）、GoodChuX_lift（段）、GoodChuX_GoodChu（HcK の GoodChu へ）、GoodChuX_nil。
- GoodChuX_Fsucc: 空の F のタイを足す規則（HcE.GoodLc_Fsucc の写し）。h2 の中身の節点は、埋め込み先の族で
  HcL.RAu_node と HcK の中身の族に、GoodChuX から出した GoodChu を渡して置く。
-/
import HcL

namespace TRIO
namespace HcM

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcJ HcK HcL

/-! ## 埋め込み -/

def EmbU (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ a ∈ A, f a = addF H g a) ∧ (∀ s ∈ S, ∀ a ∈ A, a < s) ∧ (∀ a ∈ S ++ A, a < o) ∧
    (∀ a ∈ S ++ A, 1 ≤ a) ∧ 1 ≤ o ∧
    (∀ s ∈ S, reOff (fun _ => 0) (addF H g) A k ≤ liftVal f (S ++ A) s) ∧
    reOff (fun _ => 0) (addF H g) A k ≤ liftOff f (S ++ A) o

theorem EmbU_comp {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) {g2 : ℕ → ℕ} {S2 : List ℕ} {o2 : ℕ} {f2 : ℕ → ℕ}
    (hE2 : EmbU (S ++ A) o f g2 S2 o2 f2) : EmbU A k H (addF g g2) (S2 ++ S) o2 f2 := by
  obtain ⟨hf, hSA, hA, hA1, ho, hK, hKo⟩ := hE
  obtain ⟨hf2, hSA2, hA2, hA12, ho2, hK2, hKo2⟩ := hE2
  obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g2
  have eLo : liftOff (addF f g2) (S ++ A) o = reOff (fun _ => 0) (addF f g2) (S ++ A) o :=
    liftOff_eq_reOff0 _ _ _
  refine ⟨fun a ha => ?_, fun s hs a ha => ?_, ?_, ?_, ho2, fun s hs => ?_, ?_⟩
  · have h1 := hf2 a (List.mem_append_right _ ha)
    have h2 := hf a ha
    simp only [addF] at h1 h2 ⊢; omega
  · rcases List.mem_append.mp hs with hs | hs
    · exact hSA2 s hs a (List.mem_append_right _ ha)
    · exact hSA s hs a ha
  · rw [List.append_assoc]; exact hA2
  · rw [List.append_assoc]; exact hA12
  · rw [List.append_assoc]
    rcases List.mem_append.mp hs with hs | hs
    · have := hK2 s hs
      omega
    · have e : liftVal f2 (S2 ++ (S ++ A)) s = liftVal (addF f g2) (S ++ A) s := by
        unfold liftVal
        rw [stepSum_append, stepSum_none 0 f2 (s + 1) S2
          (fun s2 hs2 => by have := hSA2 s2 hs2 s (List.mem_append_left _ hs); omega),
          Nat.zero_add, stepSum_congr 0 (s + 1) hf2]
      rw [e]; exact hKG s hs
  · rw [List.append_assoc]; omega

theorem EmbU_relift {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (g' : ℕ → ℕ) : EmbU A k H (addF g g') S o (addF f g') := by
  obtain ⟨hf, hSA, hA, hA1, ho, hK, hKo⟩ := hE
  obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
  exact ⟨hfG, hSA, hA, hA1, ho, hKG, hKoG⟩

theorem EmbU_triv {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (hA1 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k)
    (H : ℕ → ℕ) : EmbU A k H (fun _ => 0) [] k H := by
  refine ⟨fun a _ => by rw [addF_zero], by simp, by simpa using hAk, by simpa using hA1, hk, by simp, ?_⟩
  simp only [List.nil_append, addF_zero, liftOff_eq_reOff0]; exact le_rfl

theorem EmbU_reliftX {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (c : ℕ) (g2 : ℕ → ℕ) {X : TrioSeq}
    (hX : LowC (c + reOff (fun _ => 0) H A k) X) :
    reliftX c f g2 (S ++ A) (reliftX c H g A X) = reliftX c H (addF g g2) A X := by
  have hL : LowC (c + reOff (fun _ => 0) (addF H g) A k) (reliftX c H g A X) := by
    have := LowC_reliftX hX H g A
    rwa [reOff_zero_comp] at this
  rw [reliftX_ins_low hE.2.1 hE.1 c g2 hE.2.2.2.2.2.1 hL, reliftX_comp]

theorem EmbU_relLds {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (c : ℕ) (g2 : ℕ → ℕ) {Lds : List (List (Option TrioSeq))}
    (hL : ∀ us ∈ Lds, RawUc (c + reOff (fun _ => 0) H A k) us) :
    (Lds.map (fun us => us.map (Option.map (reliftX c H g A)))).map
        (fun us => us.map (Option.map (reliftX c f g2 (S ++ A))))
      = Lds.map (fun us => us.map (Option.map (reliftX c H (addF g g2) A))) := by
  simp only [List.map_map]
  refine List.map_congr_left (fun us hus => ?_)
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left (fun x hx => ?_)
  cases x with
  | none => rfl
  | some X =>
      simp only [Function.comp_apply, Option.map]
      rw [EmbU_reliftX hE c g2 (hL us hus X hx).2.2]

theorem RawLds_emb {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hL : ∀ us ∈ Lds, RawUc (u + reOff (fun _ => 0) H A k) us) :
    ∀ us ∈ Lds.map (fun us => us.map (Option.map (reliftX u H g A))),
      RawUc (u + reOff (fun _ => 0) f (S ++ A) o) us := by
  intro us hus
  have hKo := hE.2.2.2.2.2.2
  rw [liftOff_eq_reOff0] at hKo
  exact RawUc_mono (Nat.add_le_add_left hKo _) (RawLdsu_relift (k0 := k) hL g us hus)

theorem RawWsAu_emb {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) {b : ℕ} {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)}
    (hR : RawWsAu A k H b ws) : RawWsAu (S ++ A) o f b (relWsu A H g ws) := by
  have hR' := RawWsAu_relWsu hR g
  have hKo := hE.2.2.2.2.2.2
  rw [liftOff_eq_reOff0] at hKo
  intro w hw
  have h0 := hR' w hw
  exact ⟨h0.1, fun us hus => RawUc_mono (Nat.add_le_add_left hKo _) (h0.2.1 us hus), h0.2.2.1,
    h0.2.2.2.1, LowC_mono (Nat.add_le_add_left hKo _) h0.2.2.2.2⟩

/-! ## 族の並び -/

theorem FarCAu_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 b1 : ℕ} (hb : b0 ≤ b1)
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hC : FarCAu A0 k0 h b0 ws) :
    FarCAu A0 k0 h b1 ws := fun g S o f b hf hb1 => hC g S o f b hf (le_trans hb hb1)

theorem FarCAu_embed {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)}
    (hC : FarCAu A0 k0 h b0 ws) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ}
    (hE : EmbU A0 k0 h g S o f) (hb : b0 ≤ b) (hR : RawWsAu A0 k0 h b ws) :
    FarCAu (S ++ A0) o f b (relWsu A0 h g ws) := by
  intro g2 S2 o2 f2 b2 hf2 hb2 _ hSA2 hA2 hA12 ho2 hK2 hKo2
  have hE2 : EmbU (S ++ A0) o f g2 S2 o2 f2 := ⟨hf2, hSA2, hA2, hA12, ho2, hK2, hKo2⟩
  have eW : relWsu (S ++ A0) f g2 (relWsu A0 h g ws) = relWsu A0 h (addF g g2) ws := by
    unfold relWsu
    rw [List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    have hw0 := hR w hw
    show ((w.1.map (fun us => us.map (Option.map (reliftX w.2.1 h g A0)))).map
        (fun us => us.map (Option.map (reliftX w.2.1 f g2 (S ++ A0)))), w.2.1,
        reliftX w.2.1 f g2 (S ++ A0) (reliftX w.2.1 h g A0 w.2.2))
      = (w.1.map (fun us => us.map (Option.map (reliftX w.2.1 h (addF g g2) A0))), w.2.1,
        reliftX w.2.1 h (addF g g2) A0 w.2.2)
    rw [EmbU_reliftX hE w.2.1 g2 hw0.2.2.2.2, EmbU_relLds hE w.2.1 g2 hw0.2.1]
  obtain ⟨hf', hSA', hA', hA1', ho', hK', hKo'⟩ := EmbU_comp hE hE2
  have := hC (addF g g2) (S2 ++ S) o2 f2 b2 hf' (le_trans hb hb2) (RawWsAu_mono hb2 hR) hSA' hA'
    hA1' ho' hK' hKo'
  rw [List.append_assoc] at this
  rw [eW]
  exact this

theorem FarCAu_self {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hC : FarCAu A k H b0 ws) {b : ℕ}
    (hb : b0 ≤ b) (hR : RawWsAu A k H b ws) (hAk : ∀ a ∈ A, a < k) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (hk : 1 ≤ k) : GpT A k H b (farWu b (b + liftOff H A k + 1) ws) := by
  have := hC (fun _ => 0) [] k H b (fun a _ => by rw [addF_zero]) hb hR (by simp) (by simpa using hAk)
    (by simpa using hA1) hk (by simp)
    (by simp only [List.nil_append, addF_zero, liftOff_eq_reOff0]; exact le_rfl)
  simp only [List.nil_append, relWsu_zero] at this
  exact this

theorem RawWsku_of_RawWsAu {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsAu A k H b ws) :
    RawWsku (reOff (fun _ => 0) H A k) b ws := fun w hw => hR w hw

theorem mlift_farWu_self {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b K : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsAu A k H b ws) {b' : ℕ}
    (hb : b ≤ b') : mlift (farWu b (b + K + 1) ws) b (b' - b) = farWu b' (b' + K + 1) ws := by
  have := mlift_farWu_basek (show b < b + K + 1 by omega) (b' - b) ws (RawWsku_of_RawWsAu hR)
  rwa [show b + (b' - b) = b' by omega, show b + K + 1 + (b' - b) = b' + K + 1 by omega] at this

theorem reliftX_farWu_self {A : List ℕ} {k : ℕ} (hA : ∀ a ∈ A, a < k) {H : ℕ → ℕ} (b : ℕ)
    (g : ℕ → ℕ) {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsAu A k H b ws) :
    reliftX b H g A (farWu b (b + liftOff H A k + 1) ws)
      = farWu b (b + liftOff (addF H g) A k + 1) (relWsu A H g ws) := by
  have := reliftX_farWuA (S := []) (A0 := A) (o := k) (by simpa using hA) (by simp) b (k0 := k)
    (h := H) (g := fun _ => 0) (f := H) (fun a _ => by rw [addF_zero]) g (by simp) ws hR
  have e : addF (fun _ => 0) g = g := by funext a; simp [addF]
  simp only [List.nil_append, relWsu_zero, e] at this
  exact this

theorem fwH_nil_app (b r : ℕ) (H0 : TrioSeq) (c : ℕ) (Y : TrioSeq) :
    fwH b r H0 c [] ++ shiftr01 1 0 Y = fwH b r H0 b Y := by
  simp [fwH, shiftr01, mlift_nil, mlift_zero]

/-! ## 子の並びの良さ -/

def GoodChuX (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (u : ℕ) (Lds : List (List (Option TrioSeq))) : Prop :=
  (∀ us ∈ Lds, RawUc (u + reOff (fun _ => 0) H A k) us) ∧
    ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), EmbU A k H g S o f → u ≤ b →
      ∀ ws, FarCAu (S ++ A) o f b ws → RawWsAu (S ++ A) o f b ws →
        GpT (S ++ A) o f b (farWu b (b + liftOff f (S ++ A) o + 1)
          (ws ++ [(Lds.map (fun us => us.map (Option.map (reliftX u H g A))), u, [])]))

theorem GoodChuX_emb {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hG : GoodChuX A k H u Lds) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) :
    GoodChuX (S ++ A) o f u (Lds.map (fun us => us.map (Option.map (reliftX u H g A)))) := by
  refine ⟨RawLds_emb hE hG.1, fun g2 S2 o2 f2 b hE2 hub ws hC hR => ?_⟩
  have := hG.2 (addF g g2) (S2 ++ S) o2 f2 b (EmbU_comp hE hE2) hub ws
    (by rw [List.append_assoc]; exact hC) (by rw [List.append_assoc]; exact hR)
  rw [List.append_assoc] at this
  rw [EmbU_relLds hE u g2 hG.1]
  exact this

theorem GoodChuX_lift {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hG : GoodChuX A k H u Lds) {u' : ℕ} (hu : u ≤ u') :
    GoodChuX A k H u' (Lds.map (fun us => us.map (Option.map (fun X => mlift X u (u' - u))))) := by
  refine ⟨fun us hus => ?_, fun g S o f b hE hub ws hC hR => ?_⟩
  · simp only [List.mem_map] at hus
    obtain ⟨us0, hus0, rfl⟩ := hus
    exact RawUc_lift hu (hG.1 us0 hus0)
  · have := hG.2 g S o f b hE (by omega) ws hC hR
    rw [farWu_snoc] at this
    rw [mapu_relift_mlift A H g hu, farWu_snoc]
    dsimp only at this ⊢
    rw [FTLu_rebase hu hub]
    simpa [fwH, mlift_nil] using this

theorem GoodChuX_GoodChu {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hG : GoodChuX A k H u Lds) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) :
    GoodChu (S ++ A) o f u (Lds.map (fun us => us.map (Option.map (reliftX u H g A)))) := by
  refine ⟨RawLds_emb hE hG.1, fun g2 b0 ws hC g3 S3 o3 f3 b3 hf3 hb3 hR3 hSA3 hA3 hA13 ho3 hK3 hKo3 => ?_⟩
  have hE3 : EmbU (S ++ A) o (addF f g2) g3 S3 o3 f3 := ⟨hf3, hSA3, hA3, hA13, ho3, hK3, hKo3⟩
  have hE2 := EmbU_relift hE g2
  have hw := hR3 _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hR0 : RawWsAu (S ++ A) o (addF f g2) b3 ws := fun w' h' => hR3 w' (List.mem_append_left _ h')
  have := hG.2 (addF (addF g g2) g3) (S3 ++ S) o3 f3 b3 (EmbU_comp hE2 hE3) hw.1
    (relWsu (S ++ A) (addF f g2) g3 ws)
    (by rw [List.append_assoc]; exact FarCAu_embed hC hE3 hb3 hR0)
    (by rw [List.append_assoc]; exact RawWsAu_emb hE3 hR0)
  rw [List.append_assoc] at this
  have e0 : ∀ c (K G : ℕ → ℕ) (B : List ℕ), reliftX c K G B ([] : TrioSeq) = [] := fun c K G B => by
    unfold reliftX; exact slift_nil _
  rw [relWsu_snoc, e0, EmbU_relLds hE u g2 hG.1, EmbU_relLds hE2 u g3 hG.1]
  exact this

theorem GoodChuX_nil (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (u : ℕ) : GoodChuX A k H u [] := by
  refine ⟨fun _ h => by simp at h, fun g S o f b hE hub ws hC hR => ?_⟩
  have hC' := farWAu_collapse (c0 := u) hC
  have hR' : RawWsAu (S ++ A) o f b (ws ++ [([], u, [])]) :=
    RawWsAu_snoc hR ⟨hub, fun _ h => by simp at h, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  simp only [List.map_nil]
  exact FarCAu_self hC' le_rfl hR' hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1

/-! ## 空の F のタイ -/

/-- ★ 空の F のタイを足す規則。 -/
theorem GoodChuX_Fsucc {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hG : GoodChuX A k H u Lds) : GoodChuX A k H u (Lds ++ [[]]) := by
  have hraw : ∀ us ∈ Lds ++ [[]], RawUc (u + reOff (fun _ => 0) H A k) us := by
    intro us hus
    rcases List.mem_append.mp hus with hus | hus
    · exact hG.1 us hus
    · rw [List.mem_singleton] at hus; rw [hus]; intro X hX; simp at hX
  refine ⟨hraw, fun g S o f b hE hub ws hC hR => ?_⟩
  have hA : ∀ a ∈ S ++ A, a < o := hE.2.2.1
  have hA1 : ∀ a ∈ S ++ A, 1 ≤ a := hE.2.2.2.1
  have ho : 1 ≤ o := hE.2.2.2.2.1
  obtain ⟨L, hLdef⟩ : ∃ L, L = Lds.map (fun us => us.map (Option.map (reliftX u H g A))) := ⟨_, rfl⟩
  have eL : (Lds ++ [([] : List (Option TrioSeq))]).map (fun us => us.map (Option.map (reliftX u H g A)))
      = L ++ [[]] := by
    rw [hLdef]; simp
  rw [eL]
  have hRL : ∀ us ∈ L, RawUc (u + reOff (fun _ => 0) f (S ++ A) o) us := by
    rw [hLdef]; exact RawLds_emb hE hG.1
  have hRn : RawWsAu (S ++ A) o f b (ws ++ [(L, u, [])]) :=
    RawWsAu_snoc hR ⟨hub, hRL, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
  rw [← hr, farWu_snoc]
  dsimp only
  have eF : fwH b r (FTLu b r u (L ++ [[]])) u []
      = fwH b r (FTLu b r u L) u [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwH, FTLu_snoc, chF, shiftr01, mlift_nil]
  rw [eF, ← List.append_assoc]
  have eP0 : farWu b r ws ++ fwH b r (FTLu b r u L) u [] = farWu b r (ws ++ [(L, u, [])]) := by
    rw [farWu_snoc]
  have eR : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A) (mlift (farWu b r ws ++ fwH b r (FTLu b r u L) u []) b (b' - b))
        = farWu b' (b' + liftOff (addF f g') (S ++ A) o + 1)
            (relWsu (S ++ A) f g' (ws ++ [(L, u, [])])) := by
    intro g' b' hb'
    rw [eP0, hr, mlift_farWu_self hRn hb', reliftX_farWu_self hA b' g' (RawWsAu_mono hb' hRn)]
  have hFP := FarP_GpT_lt (A := S ++ A) (o := o) hA ho (f := f) (s := liftOff f (S ++ A) o + 1)
    (by omega)
  have hP : Fr (farWu b r ws ++ fwH b r (FTLu b r u L) u []) :=
    Fr_append (Fr_farWu _ _ _) (Fr_fwH _ _ _ _ _)
  have hbot : BotGe (farWu b r ws ++ fwH b r (FTLu b r u L) u []) 2
      (b + (liftOff f (S ++ A) o + 1)) := by
    unfold fwH
    exact BotGe_node (Fr_farWu _ _ _) (by omega)
      (BotGe_one (Fr_append (Fr_FTLu _ _ _ _) (Fr_mlift Fr_nil _ _)) _)
  suffices hG2 : GpT (S ++ A) o f b ((farWu b r ws ++ fwH b r (FTLu b r u L) u []) ++
      [((2, b + (liftOff f (S ++ A) o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (liftOff f (S ++ A) o + 1) = r by omega] at hG2
  have hR0w : ∀ w ∈ ws, (∀ us ∈ w.1, RawUc (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) us) ∧
      Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) w.2.2 :=
    fun w hw => (hR w hw).2
  have e0 : ∀ c (K G : ℕ → ℕ) (B : List ℕ), reliftX c K G B ([] : TrioSeq) = [] := fun c K G B => by
    unfold reliftX; exact slift_nil _
  refine hFP b _ 2 hP (by omega) hbot (fun g' b' hb' => ?_) (fun g' b' hb' τ L' h1τ hτ hL' hGL => ?_)
  · -- h1: 頭 Lds の空の語
    rw [eR g' b' hb', relWsu_snoc, e0, hLdef, EmbU_relLds hE u g' hG.1]
    exact hG.2 (addF g g') S o (addF f g') b' (EmbU_relift hE g') (by omega) _
      (FarCAu_mono hb' (FarCAu_relift hC hR0w g')) (RawWsAu_relWsu (RawWsAu_mono hb' hR) g')
  · -- h2: 埋め込み先の族で中身の節点を置く
    rw [eR g' b' hb', relWsu_snoc, e0, hLdef, EmbU_relLds hE u g' hG.1]
    have hE' := EmbU_relift hE g'
    have hτo : τ ≤ liftOff (addF f g') (S ++ A) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hRX : RAu (S ++ A) o (addF f g') b' ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L') :=
      RAu_node hA1 ho hA Fr_nil (RAu_nil _ _ _ _) hGL hτo
    have hokY := RAu_okWA hRX
    have hGX := GoodChuX_GoodChu (GoodChuX_lift hG (show u ≤ b' by omega)) hE'
    rw [mapu_relift_mlift A H (addF g g') (show u ≤ b' by omega)] at hGX
    have hC3 : FarCAu (S ++ A) o (addF f g') b' (relWsu (S ++ A) f g' ws) :=
      FarCAu_mono hb' (FarCAu_relift hC hR0w g')
    have hC4 := hokY.2.2 b' le_rfl _ hGX b' _ hC3
    rw [Nat.sub_self, mlift_zero] at hC4
    have hR4 : RawWsAu (S ++ A) o (addF f g') b' (relWsu (S ++ A) f g' ws ++
        [((Lds.map (fun us => us.map (Option.map (reliftX u H (addF g g') A)))).map
          (fun us => us.map (Option.map (fun X => mlift X u (b' - u)))), b',
          [] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L')]) :=
      RawWsAu_snoc (RawWsAu_relWsu (RawWsAu_mono hb' hR) g')
        ⟨le_rfl, hGX.1, Fr_append Fr_nil (Fr_node _ _), hokY.1, hokY.2.1⟩
    have := FarCAu_self hC4 le_rfl hR4 hA hA1 ho
    rw [farWu_snoc] at this
    dsimp only at this
    rw [FTLu_rebase (show u ≤ b' by omega) le_rfl] at this
    rw [farWu_snoc]
    dsimp only
    rw [List.append_assoc, show 2 - 1 = 1 by rfl, fwH_nil_app]
    exact this

end HcM
end TRIO
