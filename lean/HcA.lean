/-
HcA.lean: F のタイの子を中身と同じ形（語の段で持ち、錨で再持ち上げ）にした遠い語の土台（HbP の写し）。

    FTLc b r c Lds := (1,r,1) :: Lds.flatMap (fun D => (1,r,0) :: (mlift D c (b − c))↑1)
    farWc b r ws  := ws.flatMap (fun w => fwH b r (FTLc b r w.2.1 w.1) w.2.1 w.2.2)
    relWsc A0 h g ws := 各語の子と中身を reliftX (語の段) h g A0 で持ち上げた並び

子 D は中身と同じく語の段 c で低い（LowC (c + K) D）。級の段 b へは mlift D c (b − c) で置く。
-/
import HbT

namespace TRIO
namespace HcA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP

/-! ## 頭 -/

noncomputable def FTLc (b r c : ℕ) (Lds : List TrioSeq) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) ::
    Lds.flatMap (fun D => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift D c (b - c)))

theorem FTLc_snoc (b r c : ℕ) (Lds : List TrioSeq) (D : TrioSeq) :
    FTLc b r c (Lds ++ [D])
      = FTLc b r c Lds ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift D c (b - c)) := by
  simp [FTLc, List.flatMap_append]

theorem Fr_FTLc (b r c : ℕ) (Lds : List TrioSeq) : Fr (FTLc b r c Lds) := by
  intro x hx
  simp only [FTLc, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨D, -, hx⟩
  · exact Nat.le_refl 1
  · rcases hx with rfl | hx
    · exact Nat.le_refl 1
    · simp only [shiftr01, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      dsimp only; omega

theorem mlift_FTLc_high {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List TrioSeq, (∀ D ∈ Lds, Fr D ∧ LowC (c + k) D) →
      mlift (FTLc b r c Lds) v t = FTLc b (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTLc] using mlift_one hvr t
  | append_singleton Lds D ih =>
      intro hL
      have hD := hL D (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTLc_snoc, FTLc_snoc, mlift_app (Fr_FTLc _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hvr (Fr_mlift hD.1 _ _)]
      have hLv : LowC v (mlift D c (b - c)) := LowC_mono (by omega) (LowC_mliftk hD.2 (b - c))
      have e := mlift_append_low (A := []) hLv t
      simp only [List.nil_append, mlift_nil] at e
      rw [e]

theorem mlift_FTLc_base {b r c : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List TrioSeq, (∀ D ∈ Lds, Fr D) →
      mlift (FTLc b r c Lds) b t = FTLc (b + t) (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTLc] using mlift_one hbr t
  | append_singleton Lds D ih =>
      intro hL
      have hD := hL D (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTLc_snoc, FTLc_snoc, mlift_app (Fr_FTLc _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hbr (Fr_mlift hD _ _)]
      have e2 := mlift_mlift D c (b - c) t
      rw [show c + (b - c) = b by omega] at e2
      rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_FTLcA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ Lds : List TrioSeq, (∀ D ∈ Lds, Fr D ∧ LowC (c + K) D) →
    reliftX b f g (S ++ A0) (FTLc b (b + liftOff f (S ++ A0) o + 1) c Lds)
      = FTLc b (b + liftOff (addF f g) (S ++ A0) o + 1) c (Lds.map (reliftX c f0 g A0)) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _
      have := reliftX_one b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)
      rw [reOff_above hA f g 1] at this
      simpa [FTLc, ← Nat.add_assoc] using this
  | append_singleton Lds D ih =>
      intro hL
      have hD := hL D (List.mem_append_right _ (List.mem_singleton_self _))
      have hL' : LowC (b + K) (mlift D c (b - c)) := by
        have := LowC_mliftk hD.2 (b - c)
        rwa [show c + K + (b - c) = b + K by omega] at this
      rw [List.map_append, List.map_singleton, FTLc_snoc, FTLc_snoc,
        reliftX_app (Fr_FTLc _ _ _ _) (Hd_node _ _),
        ih (fun L hL'' => hL L (List.mem_append_left _ hL'')),
        show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega,
        reliftX_node (Fr_mlift hD.1 _ _) b (liftOff f (S ++ A0) o + 1) 0 f g (S ++ A0), hlow,
        reOff_above hA f g 1, reliftX_ins_low hSA hf b g hK hL']
      have em := mlift_reliftX c (b - c) f0 g A0 D
      rw [show c + (b - c) = b by omega] at em
      rw [← em]
      simp only [← Nat.add_assoc]

/-! ## 語と並び -/

noncomputable def farWc (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : TrioSeq :=
  ws.flatMap (fun w => fwH b r (FTLc b r w.2.1 w.1) w.2.1 w.2.2)

theorem farWc_cons (b r : ℕ) (w : List TrioSeq × ℕ × TrioSeq)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    farWc b r (w :: ws) = fwH b r (FTLc b r w.2.1 w.1) w.2.1 w.2.2 ++ farWc b r ws := by
  simp [farWc]

theorem farWc_snoc (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (w : List TrioSeq × ℕ × TrioSeq) :
    farWc b r (ws ++ [w]) = farWc b r ws ++ fwH b r (FTLc b r w.2.1 w.1) w.2.1 w.2.2 := by
  simp [farWc, List.flatMap_append]

theorem Fr_farWc (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Fr (farWc b r ws) := by
  intro y hy
  simp only [farWc, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwH b r _ w.2.1 w.2.2 y hy

theorem Hd_farWc (b r : ℕ) : ∀ ws : List (List TrioSeq × ℕ × TrioSeq), Hd (farWc b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farWc_cons]; rfl

theorem farWc_rep (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (w : List TrioSeq × ℕ × TrioSeq) :
    ∀ m, farWc b r (ws ++ List.replicate m w)
      = farWc b r ws ++ (List.range m).flatMap (fun _ => fwH b r (FTLc b r w.2.1 w.1) w.2.1 w.2.2)
  | 0 => by simp [farWc]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farWc_snoc, farWc_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

theorem mlift_fwc_highk {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b)
    {Lds : List TrioSeq} (hL : ∀ D ∈ Lds, Fr D ∧ LowC (c + k) D)
    {Y : TrioSeq} (hY : Fr Y) (hLY : LowC (c + k) Y) (t : ℕ) :
    mlift (fwH b r (FTLc b r c Lds) c Y) v t = fwH b (r + t) (FTLc b (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hvr (Fr_append (Fr_FTLc _ _ _ _) (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hLY (b - c))
  rw [mlift_append_low (A := FTLc b r c Lds) hL' t, mlift_FTLc_high hv hvr hcb t Lds hL]

theorem mlift_fwc_base {b r c : ℕ} (hbr : b < r) (hcb : c ≤ b) {Lds : List TrioSeq}
    (hL : ∀ D ∈ Lds, Fr D) {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (t : ℕ) :
    mlift (fwH b r (FTLc b r c Lds) c Y) b t
      = fwH (b + t) (r + t) (FTLc (b + t) (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hbr (Fr_append (Fr_FTLc _ _ _ _) (Fr_mlift hY c (b - c))) t,
    mlift_app (Fr_FTLc _ _ _ _) (Hd_mlift hH c (b - c)) b t, mlift_FTLc_base hbr hcb t Lds hL]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_fwcA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b)
    {Lds : List TrioSeq} (hL : ∀ D ∈ Lds, Fr D ∧ LowC (c + K) D)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hLY : LowC (c + K) Y) :
    reliftX b f g (S ++ A0)
        (fwH b (b + liftOff f (S ++ A0) o + 1) (FTLc b (b + liftOff f (S ++ A0) o + 1) c Lds) c Y)
      = fwH b (b + liftOff (addF f g) (S ++ A0) o + 1)
          (FTLc b (b + liftOff (addF f g) (S ++ A0) o + 1) c (Lds.map (reliftX c f0 g A0))) c
          (reliftX c f0 g A0 Y) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hLY (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  have eH := reliftX_FTLcA hA hSA b hf g hK hcb Lds hL
  unfold fwH
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega] at eH ⊢
  rw [reliftX_node (Fr_append (Fr_FTLc _ _ _ _) (Fr_mlift hY c (b - c))) b
      (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0),
    hlow, reOff_above hA f g 1, reliftX_app (Fr_FTLc _ _ _ _) (Hd_mlift hH _ _), eH,
    reliftX_ins_low hSA hf b g hK hL']
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [← em]
  simp only [← Nat.add_assoc]

/-! ## 低さの条件 -/

def RawWkc (k b : ℕ) (w : List TrioSeq × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ D ∈ w.1, Fr D ∧ LowC (w.2.1 + k) D) ∧ Fr w.2.2 ∧ Hd w.2.2 ∧
    LowC (w.2.1 + k) w.2.2

def RawWskc (k b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop := ∀ w ∈ ws, RawWkc k b w

theorem RawWskc_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hR : RawWskc k b ws) : RawWskc k b' ws := fun w hw =>
  ⟨le_trans (hR w hw).1 h, (hR w hw).2⟩

theorem RawWskc_tail {k b : ℕ} {w : List TrioSeq × ℕ × TrioSeq}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWskc k b (w :: ws)) : RawWskc k b ws :=
  fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farWc_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWskc k b ws → mlift (farWc b r ws) v t = farWc b (r + t) ws
  | [] => fun _ => by simp [farWc, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWc_cons, farWc_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWc b r ws),
        mlift_fwc_highk hv hvr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2 t,
        mlift_farWc_highk hv hvr t ws (RawWskc_tail hR)]

theorem mlift_farWc_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWskc k b ws → mlift (farWc b r ws) b t = farWc (b + t) (r + t) ws
  | [] => fun _ => by simp [farWc, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWc_cons, farWc_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWc b r ws),
        mlift_fwc_base hbr hw.1 (fun D hD => (hw.2.1 D hD).1) hw.2.2.1 hw.2.2.2.1 t,
        mlift_farWc_basek hbr t ws (RawWskc_tail hR)]

/-! ## 持ち上げた子と中身の並び -/

noncomputable def relWsc (A0 : List ℕ) (h g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    List (List TrioSeq × ℕ × TrioSeq) :=
  ws.map (fun w => (w.1.map (reliftX w.2.1 h g A0), w.2.1, reliftX w.2.1 h g A0 w.2.2))

def RawWAc (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : List TrioSeq × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ D ∈ w.1, Fr D ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) D) ∧
    Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) w.2.2

def RawWsAc (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWAc A0 k0 h b w

theorem RawWsAc_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsAc A0 k0 h b ws) : RawWsAc A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb, (hR w hw).2⟩

theorem RawWsAc_snoc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} {w : List TrioSeq × ℕ × TrioSeq}
    (h : RawWsAc A0 k0 H b ws) (hw : RawWAc A0 k0 H b w) : RawWsAc A0 k0 H b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem RawLds_relift {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {c : ℕ} {Lds : List TrioSeq}
    (hL : ∀ D ∈ Lds, Fr D ∧ LowC (c + reOff (fun _ => 0) h A0 k0) D) (g : ℕ → ℕ) :
    ∀ D ∈ Lds.map (reliftX c h g A0), Fr D ∧ LowC (c + reOff (fun _ => 0) (addF h g) A0 k0) D := by
  intro D hD
  simp only [List.mem_map] at hD
  obtain ⟨D0, hD0, rfl⟩ := hD
  refine ⟨Fr_reliftX (hL D0 hD0).1 _ _ _ _, ?_⟩
  have := LowC_reliftX (hL D0 hD0).2 h g A0
  rwa [reOff_zero_comp] at this

theorem RawWskc_relWsc {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsAc A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWskc (reOff (fun _ => 0) (addF h g) A0 k0) b (relWsc A0 h g ws) := by
  intro w hw
  simp only [relWsc, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, RawLds_relift h0.2.1 g, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 h g A0
  rwa [reOff_zero_comp] at this

theorem RawWsAc_relWsc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsAc A0 k0 H b ws) (g : ℕ → ℕ) :
    RawWsAc A0 k0 (addF H g) b (relWsc A0 H g ws) := by
  intro w hw
  simp only [relWsc, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, RawLds_relift h0.2.1 g, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 H g A0
  rwa [reOff_zero_comp] at this

theorem relWsc_snoc (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (Lds : List TrioSeq) (u : ℕ) (X : TrioSeq) :
    relWsc A0 H g (ws ++ [(Lds, u, X)])
      = relWsc A0 H g ws ++ [(Lds.map (reliftX u H g A0), u, reliftX u H g A0 X)] := by
  simp [relWsc]

theorem relWsc_rep (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (Lds : List TrioSeq) (u : ℕ) (W : TrioSeq) (m : ℕ) :
    relWsc A0 H g (ws ++ List.replicate m (Lds, u, W))
      = relWsc A0 H g ws ++ List.replicate m (Lds.map (reliftX u H g A0), u, reliftX u H g A0 W) := by
  simp [relWsc, List.map_replicate]

theorem relWsc_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    relWsc A0 (addF H g) g' (relWsc A0 H g ws) = relWsc A0 H (addF g g') ws := by
  simp [relWsc, reliftX_comp, Function.comp_def]

theorem relWsc_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    relWsc A0 H (fun _ => 0) ws = ws := by
  have e : ∀ c, reliftX c H (fun _ => 0) A0 = id := fun c => by funext Z; simp [reliftX_zero]
  simp [relWsc, e]

theorem relWsc_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) : relWsc A0 H g ws = relWsc A0 H' g ws := by
  unfold relWsc
  refine List.map_congr_left (fun w _ => ?_)
  rw [reliftX_congr w.2.1 hH (fun _ _ => rfl) w.2.2]
  congr 1
  exact List.map_congr_left (fun D _ => reliftX_congr w.2.1 hH (fun _ _ => rfl) D)

theorem reliftX_farWcA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsAc A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farWc b (b + liftOff f (S ++ A0) o + 1) (relWsc A0 h g ws))
      = farWc b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWsc A0 h (addF g g') ws)
  | [] => fun _ => by simp [farWc, relWsc, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsAc A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWsc A0 h g (w :: ws)
          = (w.1.map (reliftX w.2.1 h g A0), w.2.1, reliftX w.2.1 h g A0 w.2.2) :: relWsc A0 h g ws
          from rfl,
        show relWsc A0 h (addF g g') (w :: ws)
          = (w.1.map (reliftX w.2.1 h (addF g g') A0), w.2.1, reliftX w.2.1 h (addF g g') A0 w.2.2) ::
            relWsc A0 h (addF g g') ws from rfl,
        farWc_cons, farWc_cons, reliftX_app (Fr_fwH _ _ _ _ _) (Hd_farWc _ _ _)]
      have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
        have := LowC_reliftX hw.2.2.2.2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_fwcA hA hSA b hf g' hK hw.1 (RawLds_relift hw.2.1 g) (Fr_reliftX hw.2.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.2.1 _ _ _ _) hL]
      simp only [List.map_map, Function.comp_def, reliftX_comp]
      rw [reliftX_farWcA hA hSA b hf g' hK ws hR']

end HcA
end TRIO
