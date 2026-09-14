/-
HaC.lean: 錨つきの中身の遠い語の族（notes 追記546）の第 1 部: 上に錨 S を足した級での中身の再持ち上げ。

中身 Z が段 b+K 以下で、K が S の錨の持ち上げ後の位置以下なら、
    reliftX b f g (S ++ A0) Z = reliftX b f0 g A0 Z     （f = f0 on A0、S の錨は A0 の錨より上）
また再持ち上げで低さの上限は b+K から b + reOff f g A K に移る。
-/
import GzA
import HaA

namespace TRIO
namespace HaC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY HaA

theorem entry1_sliftH {Z : TrioSeq} {k : ℕ} (hk : k < Z.length) (φ : ℕ → ℕ) :
    entry (slift Z φ) 1 k = entry Z 1 k + (φ (amin Z k) - amin Z k) := by
  rw [show entry (slift Z φ) 1 k = ((slift Z φ).getD k (0, 0, 0)).2.1 from rfl, slift_getD hk]

theorem LowC_reliftX {Z : TrioSeq} {b K : ℕ} (hZ : LowC (b + K) Z) (f g : ℕ → ℕ) (A : List ℕ) :
    LowC (b + reOff f g A K) (reliftX b f g A Z) := by
  intro i hi
  unfold reliftX at hi ⊢
  rw [slift_length] at hi
  obtain ⟨k, hk, hle⟩ := hZ i hi
  have hkZ : k < Z.length := lt_of_le_of_lt (rtg0_le hk) hi
  refine ⟨k, rtg0_slift'.mpr hk, ?_⟩
  rw [entry1_sliftH hkZ]
  have h1 := amin_self_le Z k
  have h2 := reStep_mono b f g A (show amin Z k ≤ b + K by omega) A
  have h3 : reStair b f g A (b + K) = b + reOff f g A K := reStair_base b K f g A
  unfold reStair at h3 ⊢
  omega

theorem reStair_ins_low {S A0 : List ℕ} (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) {f f0 : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = f0 a) (b : ℕ) (g : ℕ → ℕ) {K : ℕ}
    (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) {m : ℕ} (hm : m ≤ b + K) :
    reStair b f g (S ++ A0) m = reStair b f0 g A0 m := by
  unfold reStair
  rw [reStep_append]
  have hS0 : ∀ S' : List ℕ, (∀ s ∈ S', K ≤ liftVal f (S ++ A0) s) →
      reStep b f g (S ++ A0) S' m = 0 := by
    intro S' hS'
    induction S' with
    | nil => rfl
    | cons s S' ih =>
        simp only [reStep]
        have h1 := hS' s (by simp)
        rw [if_neg (by omega), ih (fun x hx => hS' x (List.mem_cons_of_mem s hx))]
  rw [hS0 S hK, Nat.zero_add]
  have hA0 : ∀ a ∈ A0, liftVal f (S ++ A0) a = liftVal f0 A0 a ∧ g a = g a := by
    intro a ha
    refine ⟨?_, rfl⟩
    unfold liftVal
    rw [stepSum_append, stepSum_none 0 f (a + 1) S (fun s hs => by have := hSA s hs a ha; omega),
      Nat.zero_add, stepSum_congr 0 (a + 1) hf]
  rw [reStep_congr_all b m A0 hA0]

theorem reliftX_ins_low {S A0 : List ℕ} (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) {f f0 : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = f0 a) (b : ℕ) (g : ℕ → ℕ) {K : ℕ}
    (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) {Z : TrioSeq} (hZ : LowC (b + K) Z) :
    reliftX b f g (S ++ A0) Z = reliftX b f0 g A0 Z := by
  unfold reliftX
  refine slift_congr_amin (fun j hj => ?_)
  obtain ⟨k, hk, hle⟩ := hZ j hj
  have := amin_le hk
  exact reStair_ins_low hSA hf b g hK (by omega)

theorem reOff_zero_comp (h g : ℕ → ℕ) (A : List ℕ) (m : ℕ) :
    reOff h g A (reOff (fun _ => 0) h A m) = reOff (fun _ => 0) (addF h g) A m := by
  have := reOff_comp (fun _ => 0) h g A m
  have e : addF (fun _ => 0) h = h := by funext a; simp [addF]
  rwa [e] at this

theorem reOff_zero_le_sum (h g' : ℕ → ℕ) (A0 : List ℕ) (k0 : ℕ) :
    reOff (fun _ => 0) (addF h g') A0 k0 ≤ reOff (fun _ => 0) h A0 k0 + sumOn g' A0 := by
  unfold reOff
  rw [reStep_zeroF, reStep_zeroF]
  have e : stepSum 0 (addF h g') A0 k0 = stepSum 0 h A0 k0 + stepSum 0 g' A0 k0 :=
    stepSum_add 0 k0 h g' A0
  have := stepSum_le_sumOn g' k0 A0
  omega

/-! ## 持ち上げた中身の並び -/

noncomputable def relWs (A0 : List ℕ) (h g : ℕ → ℕ) (ws : List (ℕ × TrioSeq)) :
    List (ℕ × TrioSeq) :=
  ws.map (fun w => (w.1, reliftX w.1 h g A0 w.2))

def RawWA (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : ℕ × TrioSeq) : Prop :=
  w.1 ≤ b ∧ Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + reOff (fun _ => 0) h A0 k0) w.2

def RawWsA (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWA A0 k0 h b w

theorem RawWsA_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (ℕ × TrioSeq)} (hR : RawWsA A0 k0 h b ws) : RawWsA A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb, (hR w hw).2⟩

theorem RawWsk_relWs {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ} {ws : List (ℕ × TrioSeq)}
    (hR : RawWsA A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWsk (reOff (fun _ => 0) (addF h g) A0 k0) b (relWs A0 h g ws) := by
  intro w hw
  simp only [relWs, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, Fr_reliftX h0.2.1 _ _ _ _, Hd_reliftX h0.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2 h g A0
  rwa [reOff_zero_comp] at this

theorem reliftX_fwWA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) {c : ℕ} (hcb : c ≤ b)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hL : LowC (c + K) Y) :
    reliftX b f g (S ++ A0) (fwW b (b + liftOff f (S ++ A0) o + 1) c Y)
      = fwW b (b + liftOff (addF f g) (S ++ A0) o + 1) c (reliftX c f0 g A0 Y) := by
  unfold fwW
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega,
    reliftX_node (Fr_FLW (Fr_mlift hY c (b - c))) b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)]
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  rw [hlow, reOff_above hA f g 1]
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hL (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  have e : reliftX b f g (S ++ A0)
        ([((1, b + (liftOff f (S ++ A0) o + 1), 1) : ℕ × ℕ × ℕ)] ++ mlift Y c (b - c))
      = reliftX b f g (S ++ A0) [((1, b + (liftOff f (S ++ A0) o + 1), 1) : ℕ × ℕ × ℕ)] ++
        reliftX b f0 g A0 (mlift Y c (b - c)) := by
    rw [reliftX_app (Fr_single le_rfl _ _) (Hd_mlift hH _ _), reliftX_ins_low hSA hf b g hK hL']
  simp only [List.singleton_append] at e
  rw [e]
  have e1 : reliftX b f g (S ++ A0) [((1, b + (liftOff f (S ++ A0) o + 1), 1) : ℕ × ℕ × ℕ)]
      = [((1, b + (liftOff (addF f g) (S ++ A0) o + 1), 1) : ℕ × ℕ × ℕ)] := by
    have := reliftX_node (V := []) Fr_nil b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)
    rw [hlow, reOff_above hA f g 1] at this
    simpa [shiftr01, reliftX, slift_nil] using this
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [e1, ← em]
  simp only [List.singleton_append, ← Nat.add_assoc]

theorem reliftX_farWA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsA A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g ws))
      = farW b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWs A0 h (addF g g') ws)
  | [] => fun _ => by simp [farW, relWs, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsA A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWs A0 h g (w :: ws) = (w.1, reliftX w.1 h g A0 w.2) :: relWs A0 h g ws from rfl,
        show relWs A0 h (addF g g') (w :: ws)
          = (w.1, reliftX w.1 h (addF g g') A0 w.2) :: relWs A0 h (addF g g') ws from rfl,
        farW_cons, farW_cons, reliftX_app (Fr_fwW _ _ _ _) (Hd_farW _ _ _)]
      have hL : LowC (w.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.1 h g A0 w.2) := by
        have := LowC_reliftX hw.2.2.2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_fwWA hA hSA b hf g' hK hw.1 (Fr_reliftX hw.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.1 _ _ _ _) hL,
        reliftX_comp, reliftX_farWA hA hSA b hf g' hK ws hR']

/-! ## 上に錨を足した全ての級（条件つき）で GpT -/

def FarCA (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b0 : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF h g a) →
    b0 ≤ b → RawWsA A0 k0 h b ws → (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) →
    (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
    (∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) →
    reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o →
    GpT (S ++ A0) o f b (farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g ws))

theorem FarCA_nil (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b0 : ℕ) : FarCA A0 k0 h b0 [] := by
  intro g S o f b _ _ _ _ hA hA1 ho _ _
  rw [show farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g []) = [] from rfl]
  rcases Nat.lt_or_ge o 2 with h2 | h2
  · have ho1 : o = 1 := by omega
    subst ho1
    have hA0 : S ++ A0 = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
    rw [hA0]
    exact GpT_nil1 f b
  · exact GpT_nil hA h2 f b

theorem farWA_PVP {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ} {ws : List (ℕ × TrioSeq)}
    (hC : FarCA A0 k0 h b0 ws) (g : ℕ → ℕ) {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) {b : ℕ} (hb : b0 ≤ b) (hR : RawWsA A0 k0 h b ws)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o) (hA1 : ∀ a ∈ S ++ A0, 1 ≤ a)
    (ho : 1 ≤ o) (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    PVP (S ++ A0) o f b (farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g ws)) := by
  intro t
  rw [mlift_farW_highk
    (show b + reOff (fun _ => 0) (addF h g) A0 k0 ≤ b + liftOff f (S ++ A0) o by omega)
    (show b + liftOff f (S ++ A0) o < b + liftOff f (S ++ A0) o + 1 by omega) t _
    (RawWsk_relWs hR g)]
  have := hC g S (o + t) f b hf hb hR hSA (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    hK (by rw [liftOff_add_t hA]; omega)
  rwa [liftOff_add_t hA,
    show b + (liftOff f (S ++ A0) o + t) + 1 = b + liftOff f (S ++ A0) o + 1 + t by omega] at this

/-! ## 潰れの塔 -/

theorem towWA_GpT {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ} {ws : List (ℕ × TrioSeq)}
    (hC : FarCA A0 k0 h b0 ws) (g : ℕ → ℕ) :
    ∀ (m : ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF h g a) →
    b0 ≤ b → RawWsA A0 k0 h b ws → (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) →
    (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
    (∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) →
    reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o →
    GpT (S ++ A0) o f b (towW b (relWs A0 h g ws) (b + liftOff f (S ++ A0) o + 1) m)
  | 0, S, o, f, b, hf, hb, hR, hSA, hA, hA1, ho, hK, hKo => by
      rw [towW]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_farW _ _ _)
        (farWA_PVP hC g hf hb hR hSA hA hA1 ho hK hKo))
  | m + 1, S, o, f, b, hf, hb, hR, hSA, hA, hA1, ho, hK, hKo => by
      have hAo' : ∀ a ∈ o :: (S ++ A0), a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hA1' : ∀ a ∈ o :: (S ++ A0), 1 ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ho
        · exact hA1 a ha
      obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ, H = upF o 0 f := ⟨_, rfl⟩
      have hHo : H o = 0 := by rw [hH]; simp [upF]
      have hHA : ∀ a ∈ S ++ A0, H a = f a := by rw [hH]; exact upF_low hA 0 f
      have e1 : liftOff H (o :: (S ++ A0)) (o + 1) = liftOff f (S ++ A0) o + 1 := by
        rw [sumOn_liftOff hAo', sumOn_liftOff hA]
        simp only [sumOn, hHo, sumOn_congr hHA]
        omega
      have eo : liftOff H (S ++ A0) o = liftOff f (S ++ A0) o := by
        rw [sumOn_liftOff hA, sumOn_liftOff hA, sumOn_congr hHA]
      have hSA' : ∀ s ∈ o :: S, ∀ a ∈ A0, a < s := by
        intro s hs a ha
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hA a (List.mem_append_right _ ha)
        · exact hSA s hs a ha
      have hf' : ∀ a ∈ A0, H a = addF h g a := fun a ha => by
        rw [hHA a (List.mem_append_right _ ha)]; exact hf a ha
      have hK' : ∀ s ∈ o :: S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal H ((o :: S) ++ A0) s := by
        intro s hs
        simp only [List.mem_cons] at hs
        rw [List.cons_append]
        rcases hs with hs | hs
        · rw [hs, liftVal_cons_top hA, hHo, Nat.add_zero, eo]; exact hKo
        · rw [liftVal_cons_low hA (List.mem_append_left _ hs)]
          have e : liftVal H (S ++ A0) s = liftVal f (S ++ A0) s := by
            unfold liftVal; rw [stepSum_congr 0 (s + 1) hHA]
          rw [e]; exact hK s hs
      have hL := towWA_GpT hC g m (o :: S) (o + 1) H b hf' hb hR hSA' hAo' hA1' (by omega) hK'
        (by rw [List.cons_append, e1]; omega)
      rw [List.cons_append, e1,
        show b + (liftOff f (S ++ A0) o + 1) + 1 = b + liftOff f (S ++ A0) o + 1 + 1 by omega] at hL
      have hGC : GC (o :: (S ++ A0)) H (liftOff f (S ++ A0) o + 1) b
          (towW b (relWs A0 h g ws) (b + liftOff f (S ++ A0) o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_farW _ _ _) (farWA_PVP hC g hf hb hR hSA hA hA1 ho hK hKo)
      rw [show b + (liftOff f (S ++ A0) o + 1) = b + liftOff f (S ++ A0) o + 1 by omega] at this
      rw [towW]
      exact PVP_to_GpT this

/-- ★ 遠い語（中身が遠い字だけ）の潰れ（錨つきの中身の版）。 -/
theorem farWA_collapse {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 c0 : ℕ} {ws : List (ℕ × TrioSeq)}
    (hC : FarCA A0 k0 h b0 ws) : FarCA A0 k0 h b0 (ws ++ [(c0, [])]) := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hR0 : RawWsA A0 k0 h b ws := fun w hw => hR w (List.mem_append_left _ hw)
  refine GpT_intro hA (fun R hR' g' => ?_)
  rw [reliftX_farWA hA hSA b hf g' hK _ hR]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g' := ⟨_, rfl⟩
  have hfF : ∀ a ∈ A0, F a = addF h (addF g g') a := fun a ha => by
    have := hf a ha
    rw [hF]; simp only [addF] at this ⊢; omega
  have hKg := reOff_zero_le_sum (addF h g) g' A0 k0
  have eaddF : addF (addF h g) g' = addF h (addF g g') := by funext a; simp [addF]; omega
  rw [eaddF] at hKg
  have hKF : ∀ s ∈ S, reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ liftVal F (S ++ A0) s := by
    intro s hs
    rw [hF, liftVal_add]
    have h1 := hK s hs
    have h2 : sumOn g' A0 ≤ stepSum 0 g' (S ++ A0) (s + 1) := by
      rw [stepSum_append, stepSum_all 0 (s + 1) g' (A := A0) (fun a ha => by have := hSA s hs a ha; omega)]
      omega
    omega
  have hKoF : reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ liftOff F (S ++ A0) o := by
    rw [hF, liftOff_addF hA, sumOn_append]; omega
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff F (S ++ A0) o := ⟨_, rfl⟩
  rw [← hF, ← hkk]
  have hk1 : o ≤ kk := by rw [hkk]; unfold liftOff; omega
  have hkkk : reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ kk := by rw [hkk]; exact hKoF
  intro u' hu X hX hRX
  have ers : relWs A0 h (addF g g') (ws ++ [(c0, [])]) = relWs A0 h (addF g g') ws ++ [(c0, [])] := by
    simp [relWs, reliftX, slift_nil]
  have hRk : RawWsk (reOff (fun _ => 0) (addF h (addF g g')) A0 k0) b
      (relWs A0 h (addF g g') ws ++ [(c0, [])]) := by
    have := RawWsk_relWs hR (addF g g'); rwa [ers] at this
  rw [ers]
  obtain ⟨ws', hws'⟩ : ∃ ws', ws' = relWs A0 h (addF g g') ws := ⟨_, rfl⟩
  rw [← hws'] at hRk ⊢
  rw [mlift_farW_basek (show b < b + kk + 1 by omega) (u' - b) _ hRk,
    show b + kk + 1 + (u' - b) = u' + kk + 1 by omega, show b + (u' - b) = u' by omega, farW_snoc]
  have hRu : RawWsk (reOff (fun _ => 0) (addF h (addF g g')) A0 k0) u' ws' := by
    rw [hws']; exact RawWsk_mono hu (RawWsk_relWs hR0 (addF g g'))
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farW_P u' c ws'
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      ((farW u' (c + 1) ws' ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (farW u' (c + 1) ws' ++ fwW u' (c + 1) c0 [])
      = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwW, mlift_nil]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h' | h'
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          (farW u' (c + 1) ws' ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h'
      unfold lev at h'
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((farW u' (c + 1) ws' ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: (farW u' (c + 1) ws' ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
          [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h'
      simp [entry] at h'
    · exact h'
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farWk_flat hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towW u' ws' (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW u' ws' (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towWA_GpT hC (addF g g') m' S o F u' hfF (by omega) (RawWsA_mono hu hR0) hSA hA hA1 ho
    hKF hKoF
  rw [← hkk, ← hc, ← hws'] at hD
  have h' := GpT_elim0 hD hR'
  rw [← hkk] at h'
  have := h' u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end HaC
end TRIO
