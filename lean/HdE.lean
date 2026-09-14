/-
HdE.lean: 木の単位の子の並びにした遠い語の、埋め込みで閉じた子の並びの良さ GoodChtX。

    EmbU A k H g S o f := 族 (A, k, H) を再持ち上げ g で級 (S ++ A, o) の状態 f に埋め込む条件
    GoodChtX A k H u Lds := 塊が低い ∧ ∀ 埋め込み (g S o f) と段 b ≥ u、級 (S ++ A, o, f) の良い接頭辞 ws、
      GpT (S ++ A) o f b (farWt b r (ws ++ [(Lds を g で再持ち上げした並び, u, [])]))

- EmbU_comp: 埋め込みの合成。FarCAt_embed: 族の並びの埋め込み（HcE.FarCAc_embed の写し）。
- GoodChtX_emb（埋め込み）、GoodChtX_lift（段）、GoodChtX_GoodCht（HcK の GoodCht へ）、GoodChtX_nil。
- GoodChtX_Fsucc: 空の F のタイを足す規則（HcE.GoodLc_Fsucc の写し）。h2 の中身の節点は、埋め込み先の族で
  HcL.RAt_node と HcK の中身の族に、GoodChtX から出した GoodCht を渡して置く。
-/
import HdD

namespace TRIO
namespace HdE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD

/-! ## 埋め込み（EmbU は HcM） -/

mutual
theorem EmbU_relT {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (c : ℕ) (g2 : ℕ → ℕ) :
    ∀ x : UT, RawT (c + reOff (fun _ => 0) H A k) x →
      relT (S ++ A) f g2 c (relT A H g c x) = relT A H (addF g g2) c x
  | .ch X, h => by simp only [relT]; rw [EmbU_reliftX hE c g2 h.2.2]
  | .tie _ us, h => by simp only [relT]; rw [EmbU_relTs hE c g2 us h]
theorem EmbU_relTs {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (c : ℕ) (g2 : ℕ → ℕ) :
    ∀ us : List UT, RawTs (c + reOff (fun _ => 0) H A k) us →
      relTs (S ++ A) f g2 c (relTs A H g c us) = relTs A H (addF g g2) c us
  | [], _ => by simp [relTs]
  | x :: us, h => by simp only [relTs]; rw [EmbU_relT hE c g2 x h.1, EmbU_relTs hE c g2 us h.2]
end

theorem EmbU_relLdt {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (c : ℕ) (g2 : ℕ → ℕ) {Lds : List (List UT)}
    (hL : ∀ us ∈ Lds, RawTs (c + reOff (fun _ => 0) H A k) us) :
    (Lds.map (relTs A H g c)).map (relTs (S ++ A) f g2 c) = Lds.map (relTs A H (addF g g2) c) := by
  simp only [List.map_map]
  exact List.map_congr_left (fun us hus => EmbU_relTs hE c g2 us (hL us hus))

theorem RawLdt_emb {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) {u : ℕ} {Lds : List (List UT)}
    (hL : ∀ us ∈ Lds, RawTs (u + reOff (fun _ => 0) H A k) us) :
    ∀ us ∈ Lds.map (relTs A H g u),
      RawTs (u + reOff (fun _ => 0) f (S ++ A) o) us := by
  intro us hus
  have hKo := hE.2.2.2.2.2.2
  rw [liftOff_eq_reOff0] at hKo
  exact RawTs_mono' (Nat.add_le_add_left hKo _) (RawLdst_relift (k0 := k) hL g us hus)

theorem RawWsAt_emb {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) {b : ℕ} {ws : List (List (List UT) × ℕ × TrioSeq)}
    (hR : RawWsAt A k H b ws) : RawWsAt (S ++ A) o f b (relWst A H g ws) := by
  have hR' := RawWsAt_relWst hR g
  have hKo := hE.2.2.2.2.2.2
  rw [liftOff_eq_reOff0] at hKo
  intro w hw
  have h0 := hR' w hw
  exact ⟨h0.1, fun us hus => RawTs_mono' (Nat.add_le_add_left hKo _) (h0.2.1 us hus), h0.2.2.1,
    h0.2.2.2.1, LowC_mono (Nat.add_le_add_left hKo _) h0.2.2.2.2⟩

/-! ## 族の並び -/

theorem FarCAt_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 b1 : ℕ} (hb : b0 ≤ b1)
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hC : FarCAt A0 k0 h b0 ws) :
    FarCAt A0 k0 h b1 ws := fun g S o f b hf hb1 => hC g S o f b hf (le_trans hb hb1)

theorem FarCAt_embed {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)}
    (hC : FarCAt A0 k0 h b0 ws) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ}
    (hE : EmbU A0 k0 h g S o f) (hb : b0 ≤ b) (hR : RawWsAt A0 k0 h b ws) :
    FarCAt (S ++ A0) o f b (relWst A0 h g ws) := by
  intro g2 S2 o2 f2 b2 hf2 hb2 _ hSA2 hA2 hA12 ho2 hK2 hKo2
  have hE2 : EmbU (S ++ A0) o f g2 S2 o2 f2 := ⟨hf2, hSA2, hA2, hA12, ho2, hK2, hKo2⟩
  have eW : relWst (S ++ A0) f g2 (relWst A0 h g ws) = relWst A0 h (addF g g2) ws := by
    unfold relWst
    rw [List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    have hw0 := hR w hw
    show ((w.1.map (relTs A0 h g w.2.1)).map
        (relTs (S ++ A0) f g2 w.2.1), w.2.1,
        reliftX w.2.1 f g2 (S ++ A0) (reliftX w.2.1 h g A0 w.2.2))
      = (w.1.map (relTs A0 h (addF g g2) w.2.1), w.2.1,
        reliftX w.2.1 h (addF g g2) A0 w.2.2)
    rw [EmbU_reliftX hE w.2.1 g2 hw0.2.2.2.2, EmbU_relLdt hE w.2.1 g2 hw0.2.1]
  obtain ⟨hf', hSA', hA', hA1', ho', hK', hKo'⟩ := EmbU_comp hE hE2
  have := hC (addF g g2) (S2 ++ S) o2 f2 b2 hf' (le_trans hb hb2) (RawWsAt_mono hb2 hR) hSA' hA'
    hA1' ho' hK' hKo'
  rw [List.append_assoc] at this
  rw [eW]
  exact this

theorem FarCAt_self {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hC : FarCAt A k H b0 ws) {b : ℕ}
    (hb : b0 ≤ b) (hR : RawWsAt A k H b ws) (hAk : ∀ a ∈ A, a < k) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (hk : 1 ≤ k) : GpT A k H b (farWt b (b + liftOff H A k + 1) ws) := by
  have := hC (fun _ => 0) [] k H b (fun a _ => by rw [addF_zero]) hb hR (by simp) (by simpa using hAk)
    (by simpa using hA1) hk (by simp)
    (by simp only [List.nil_append, addF_zero, liftOff_eq_reOff0]; exact le_rfl)
  simp only [List.nil_append, relWst_zero] at this
  exact this

theorem RawWskt_of_RawWsAt {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWsAt A k H b ws) :
    RawWskt (reOff (fun _ => 0) H A k) b ws := fun w hw => hR w hw

theorem mlift_farWt_self {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b K : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWsAt A k H b ws) {b' : ℕ}
    (hb : b ≤ b') : mlift (farWt b (b + K + 1) ws) b (b' - b) = farWt b' (b' + K + 1) ws := by
  have := mlift_farWt_basek (show b < b + K + 1 by omega) (b' - b) ws (RawWskt_of_RawWsAt hR)
  rwa [show b + (b' - b) = b' by omega, show b + K + 1 + (b' - b) = b' + K + 1 by omega] at this

theorem reliftX_farWt_self {A : List ℕ} {k : ℕ} (hA : ∀ a ∈ A, a < k) {H : ℕ → ℕ} (b : ℕ)
    (g : ℕ → ℕ) {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWsAt A k H b ws) :
    reliftX b H g A (farWt b (b + liftOff H A k + 1) ws)
      = farWt b (b + liftOff (addF H g) A k + 1) (relWst A H g ws) := by
  have := reliftX_farWtA (S := []) (A0 := A) (o := k) (by simpa using hA) (by simp) b (k0 := k)
    (h := H) (g := fun _ => 0) (f := H) (fun a _ => by rw [addF_zero]) g (by simp) ws hR
  have e : addF (fun _ => 0) g = g := by funext a; simp [addF]
  simp only [List.nil_append, relWst_zero, e] at this
  exact this

/-! ## 子の並びの良さ -/

def GoodChtX (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (u : ℕ) (Lds : List (List UT)) : Prop :=
  (∀ us ∈ Lds, RawTs (u + reOff (fun _ => 0) H A k) us) ∧
    ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), EmbU A k H g S o f → u ≤ b →
      ∀ ws, FarCAt (S ++ A) o f b ws → RawWsAt (S ++ A) o f b ws →
        GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1)
          (ws ++ [(Lds.map (relTs A H g u), u, [])]))

theorem GoodChtX_emb {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List UT)}
    (hG : GoodChtX A k H u Lds) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) :
    GoodChtX (S ++ A) o f u (Lds.map (relTs A H g u)) := by
  refine ⟨RawLdt_emb hE hG.1, fun g2 S2 o2 f2 b hE2 hub ws hC hR => ?_⟩
  have := hG.2 (addF g g2) (S2 ++ S) o2 f2 b (EmbU_comp hE hE2) hub ws
    (by rw [List.append_assoc]; exact hC) (by rw [List.append_assoc]; exact hR)
  rw [List.append_assoc] at this
  rw [EmbU_relLdt hE u g2 hG.1]
  exact this

theorem GoodChtX_lift {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List UT)}
    (hG : GoodChtX A k H u Lds) {u' : ℕ} (hu : u ≤ u') :
    GoodChtX A k H u' (Lds.map (mlTs u (u' - u))) := by
  refine ⟨fun us hus => ?_, fun g S o f b hE hub ws hC hR => ?_⟩
  · simp only [List.mem_map] at hus
    obtain ⟨us0, hus0, rfl⟩ := hus
    exact RawTs_lift hu (hG.1 us0 hus0)
  · have := hG.2 g S o f b hE (by omega) ws hC hR
    rw [farWt_snoc] at this
    rw [mapt_relift_mlift A H g hu, farWt_snoc]
    dsimp only at this ⊢
    rw [FTLt_rebase hu hub]
    simpa [fwH, mlift_nil] using this

theorem GoodChtX_GoodCht {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List UT)}
    (hG : GoodChtX A k H u Lds) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) :
    GoodCht (S ++ A) o f u (Lds.map (relTs A H g u)) := by
  refine ⟨RawLdt_emb hE hG.1, fun g2 b0 ws hC g3 S3 o3 f3 b3 hf3 hb3 hR3 hSA3 hA3 hA13 ho3 hK3 hKo3 => ?_⟩
  have hE3 : EmbU (S ++ A) o (addF f g2) g3 S3 o3 f3 := ⟨hf3, hSA3, hA3, hA13, ho3, hK3, hKo3⟩
  have hE2 := EmbU_relift hE g2
  have hw := hR3 _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hR0 : RawWsAt (S ++ A) o (addF f g2) b3 ws := fun w' h' => hR3 w' (List.mem_append_left _ h')
  have := hG.2 (addF (addF g g2) g3) (S3 ++ S) o3 f3 b3 (EmbU_comp hE2 hE3) hw.1
    (relWst (S ++ A) (addF f g2) g3 ws)
    (by rw [List.append_assoc]; exact FarCAt_embed hC hE3 hb3 hR0)
    (by rw [List.append_assoc]; exact RawWsAt_emb hE3 hR0)
  rw [List.append_assoc] at this
  have e0 : ∀ c (K G : ℕ → ℕ) (B : List ℕ), reliftX c K G B ([] : TrioSeq) = [] := fun c K G B => by
    unfold reliftX; exact slift_nil _
  rw [relWst_snoc, e0, EmbU_relLdt hE u g2 hG.1, EmbU_relLdt hE2 u g3 hG.1]
  exact this

theorem GoodChtX_nil (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (u : ℕ) : GoodChtX A k H u [] := by
  refine ⟨fun _ h => by simp at h, fun g S o f b hE hub ws hC hR => ?_⟩
  have hC' := farWAt_collapse (c0 := u) hC
  have hR' : RawWsAt (S ++ A) o f b (ws ++ [([], u, [])]) :=
    RawWsAt_snoc hR ⟨hub, fun _ h => by simp at h, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  simp only [List.map_nil]
  exact FarCAt_self hC' le_rfl hR' hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1

/-! ## 空の F のタイ -/

/-- ★ 空の F のタイを足す規則。 -/
theorem GoodChtX_Fsucc {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List UT)}
    (hG : GoodChtX A k H u Lds) : GoodChtX A k H u (Lds ++ [[]]) := by
  have hraw : ∀ us ∈ Lds ++ [[]], RawTs (u + reOff (fun _ => 0) H A k) us := by
    intro us hus
    rcases List.mem_append.mp hus with hus | hus
    · exact hG.1 us hus
    · rw [List.mem_singleton] at hus; rw [hus]; simp [RawTs]
  refine ⟨hraw, fun g S o f b hE hub ws hC hR => ?_⟩
  have hA : ∀ a ∈ S ++ A, a < o := hE.2.2.1
  have hA1 : ∀ a ∈ S ++ A, 1 ≤ a := hE.2.2.2.1
  have ho : 1 ≤ o := hE.2.2.2.2.1
  obtain ⟨L, hLdef⟩ : ∃ L, L = Lds.map (relTs A H g u) := ⟨_, rfl⟩
  have eL : (Lds ++ [([] : List UT)]).map (relTs A H g u)
      = L ++ [[]] := by
    rw [hLdef]; simp [relTs]
  rw [eL]
  have hRL : ∀ us ∈ L, RawTs (u + reOff (fun _ => 0) f (S ++ A) o) us := by
    rw [hLdef]; exact RawLdt_emb hE hG.1
  have hRn : RawWsAt (S ++ A) o f b (ws ++ [(L, u, [])]) :=
    RawWsAt_snoc hR ⟨hub, hRL, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
  rw [← hr, farWt_snoc]
  dsimp only
  have eF : fwH b r (FTLt b r u (L ++ [[]])) u []
      = fwH b r (FTLt b r u L) u [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwH, FTLt_snoc, chT, shiftr01, mlift_nil]
  rw [eF, ← List.append_assoc]
  have eP0 : farWt b r ws ++ fwH b r (FTLt b r u L) u [] = farWt b r (ws ++ [(L, u, [])]) := by
    rw [farWt_snoc]
  have eR : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A) (mlift (farWt b r ws ++ fwH b r (FTLt b r u L) u []) b (b' - b))
        = farWt b' (b' + liftOff (addF f g') (S ++ A) o + 1)
            (relWst (S ++ A) f g' (ws ++ [(L, u, [])])) := by
    intro g' b' hb'
    rw [eP0, hr, mlift_farWt_self hRn hb', reliftX_farWt_self hA b' g' (RawWsAt_mono hb' hRn)]
  have hFP := FarP_GpT_lt (A := S ++ A) (o := o) hA ho (f := f) (s := liftOff f (S ++ A) o + 1)
    (by omega)
  have hP : Fr (farWt b r ws ++ fwH b r (FTLt b r u L) u []) :=
    Fr_append (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _)
  have hbot : BotGe (farWt b r ws ++ fwH b r (FTLt b r u L) u []) 2
      (b + (liftOff f (S ++ A) o + 1)) := by
    unfold fwH
    exact BotGe_node (Fr_farWt _ _ _) (by omega)
      (BotGe_one (Fr_append (Fr_FTLt _ _ _ _) (Fr_mlift Fr_nil _ _)) _)
  suffices hG2 : GpT (S ++ A) o f b ((farWt b r ws ++ fwH b r (FTLt b r u L) u []) ++
      [((2, b + (liftOff f (S ++ A) o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (liftOff f (S ++ A) o + 1) = r by omega] at hG2
  have hR0w : ∀ w ∈ ws, (∀ us ∈ w.1, RawTs (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) us) ∧
      Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) w.2.2 :=
    fun w hw => (hR w hw).2
  have e0 : ∀ c (K G : ℕ → ℕ) (B : List ℕ), reliftX c K G B ([] : TrioSeq) = [] := fun c K G B => by
    unfold reliftX; exact slift_nil _
  refine hFP b _ 2 hP (by omega) hbot (fun g' b' hb' => ?_) (fun g' b' hb' τ L' h1τ hτ hL' hGL => ?_)
  · -- h1: 頭 Lds の空の語
    rw [eR g' b' hb', relWst_snoc, e0, hLdef, EmbU_relLdt hE u g' hG.1]
    exact hG.2 (addF g g') S o (addF f g') b' (EmbU_relift hE g') (by omega) _
      (FarCAt_mono hb' (FarCAt_relift hC hR0w g')) (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
  · -- h2: 埋め込み先の族で中身の節点を置く
    rw [eR g' b' hb', relWst_snoc, e0, hLdef, EmbU_relLdt hE u g' hG.1]
    have hE' := EmbU_relift hE g'
    have hτo : τ ≤ liftOff (addF f g') (S ++ A) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hRX : RAt (S ++ A) o (addF f g') b' ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L') :=
      RAt_node hA1 ho hA Fr_nil (RAt_nil _ _ _ _) hGL hτo
    have hokY := RAt_okWA hRX
    have hGX := GoodChtX_GoodCht (GoodChtX_lift hG (show u ≤ b' by omega)) hE'
    rw [mapt_relift_mlift A H (addF g g') (show u ≤ b' by omega)] at hGX
    have hC3 : FarCAt (S ++ A) o (addF f g') b' (relWst (S ++ A) f g' ws) :=
      FarCAt_mono hb' (FarCAt_relift hC hR0w g')
    have hC4 := hokY.2.2 b' le_rfl _ hGX b' _ hC3
    rw [Nat.sub_self, mlift_zero] at hC4
    have hR4 : RawWsAt (S ++ A) o (addF f g') b' (relWst (S ++ A) f g' ws ++
        [((Lds.map (relTs A H (addF g g') u)).map
          (mlTs u (b' - u)), b',
          [] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L')]) :=
      RawWsAt_snoc (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
        ⟨le_rfl, hGX.1, Fr_append Fr_nil (Fr_node _ _), hokY.1, hokY.2.1⟩
    have := FarCAt_self hC4 le_rfl hR4 hA hA1 ho
    rw [farWt_snoc] at this
    dsimp only at this
    rw [FTLt_rebase (show u ≤ b' by omega) le_rfl] at this
    rw [farWt_snoc]
    dsimp only
    rw [List.append_assoc, show 2 - 1 = 1 by rfl, fwH_nil_app]
    exact this

end HdE
end TRIO
