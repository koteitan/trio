/-
HbN.lean: F のタイごとに低い子を持つ語の頭 FTL（行 1577 以降の土台）。

    FTL b r c Lds := (1,r,1) :: Lds.flatMap (fun Ld => (1,r,0) :: shiftr01 1 0 (mlift Ld c (b - c)))
    farWL b r ws := ws.flatMap (fun w => fwH b r (FTL b r w.2.1 w.1) w.2.1 w.2.2)     （w = (Lds, c, Y)）

F のタイの子 Ld は中身と同じく低い（段 c+k0 以下）。F のタイは字と一緒に持ち上がり、子は中身と同じに動く。
FTL b r c (none^n の子) = FT r n。
-/
import HbM

namespace TRIO
namespace HbN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM

/-! ## 頭 -/

noncomputable def FTL (b r c : ℕ) (Lds : List TrioSeq) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) ::
    Lds.flatMap (fun Ld => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Ld c (b - c)))

theorem FTL_snoc (b r c : ℕ) (Lds : List TrioSeq) (Ld : TrioSeq) :
    FTL b r c (Lds ++ [Ld])
      = FTL b r c Lds ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Ld c (b - c)) := by
  simp [FTL, List.flatMap_append]

theorem FTL_rep_nil (b r c : ℕ) : ∀ n, FTL b r c (List.replicate n []) = FT r n
  | 0 => by simp [FTL, FT]
  | n + 1 => by
      rw [List.replicate_succ', FTL_snoc, FTL_rep_nil b r c n, FT_succ]
      simp [mlift_nil, shiftr01]

theorem Fr_FTL (b r c : ℕ) (Lds : List TrioSeq) : Fr (FTL b r c Lds) := by
  intro x hx
  simp only [FTL, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨Ld, -, hx⟩
  · exact Nat.le_refl 1
  · rcases hx with rfl | hx
    · exact Nat.le_refl 1
    · simp only [shiftr01, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      dsimp only; omega

theorem mlift_FTL_high {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List TrioSeq, (∀ Ld ∈ Lds, Fr Ld ∧ LowC (c + k) Ld) →
    mlift (FTL b r c Lds) v t = FTL b (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTL] using mlift_one hvr t
  | append_singleton Lds Ld ih =>
      intro hL
      have hLd := hL Ld (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTL_snoc, FTL_snoc, mlift_app (Fr_FTL _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')),
        mlift_node hvr (Fr_mlift hLd.1 _ _)]
      have hL' : LowC v (mlift Ld c (b - c)) := LowC_mono (by omega) (LowC_mliftk hLd.2 (b - c))
      have e := mlift_append_low (A := []) hL' t
      simp only [List.nil_append, mlift_nil] at e
      rw [e]

theorem mlift_FTL_base {b r c : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List TrioSeq, (∀ Ld ∈ Lds, Fr Ld) →
    mlift (FTL b r c Lds) b t = FTL (b + t) (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTL] using mlift_one hbr t
  | append_singleton Lds Ld ih =>
      intro hL
      have hLd := hL Ld (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTL_snoc, FTL_snoc, mlift_app (Fr_FTL _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')),
        mlift_node hbr (Fr_mlift hLd _ _)]
      have e2 := mlift_mlift Ld c (b - c) t
      rw [show c + (b - c) = b by omega] at e2
      rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_FTLA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ Lds : List TrioSeq, (∀ Ld ∈ Lds, Fr Ld ∧ LowC (c + K) Ld) →
    reliftX b f g (S ++ A0) (FTL b (b + liftOff f (S ++ A0) o + 1) c Lds)
      = FTL b (b + liftOff (addF f g) (S ++ A0) o + 1) c (Lds.map (reliftX c f0 g A0)) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _
      have := reliftX_one b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)
      rw [reOff_above hA f g 1] at this
      simpa [FTL, ← Nat.add_assoc] using this
  | append_singleton Lds Ld ih =>
      intro hL
      have hLd := hL Ld (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton, FTL_snoc, FTL_snoc,
        reliftX_app (Fr_FTL _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')),
        show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega,
        reliftX_node (Fr_mlift hLd.1 _ _) b (liftOff f (S ++ A0) o + 1) 0 f g (S ++ A0)]
      have hL' : LowC (b + K) (mlift Ld c (b - c)) := by
        have := LowC_mliftk hLd.2 (b - c)
        rwa [show c + K + (b - c) = b + K by omega] at this
      rw [hlow, reOff_above hA f g 1, reliftX_ins_low hSA hf b g hK hL']
      have em := mlift_reliftX c (b - c) f0 g A0 Ld
      rw [show c + (b - c) = b by omega] at em
      rw [← em]
      simp only [← Nat.add_assoc]

/-! ## 語 -/

theorem Fr_FTLY {b r c : ℕ} {Lds : List TrioSeq} {Y : TrioSeq} (hY : Fr Y) : Fr (FTL b r c Lds ++ Y) :=
  Fr_append (Fr_FTL b r c Lds) hY

theorem mlift_fwL_highk {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b)
    {Lds : List TrioSeq} (hL : ∀ Ld ∈ Lds, Fr Ld ∧ LowC (c + k) Ld)
    {Y : TrioSeq} (hY : Fr Y) (hLY : LowC (c + k) Y) (t : ℕ) :
    mlift (fwH b r (FTL b r c Lds) c Y) v t = fwH b (r + t) (FTL b (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hvr (Fr_FTLY (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hLY (b - c))
  rw [mlift_append_low (A := FTL b r c Lds) hL' t, mlift_FTL_high hv hvr hcb t Lds hL]

theorem mlift_fwL_base {b r c : ℕ} (hbr : b < r) (hcb : c ≤ b) {Lds : List TrioSeq}
    (hL : ∀ Ld ∈ Lds, Fr Ld) {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (t : ℕ) :
    mlift (fwH b r (FTL b r c Lds) c Y) b t = fwH (b + t) (r + t) (FTL (b + t) (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hbr (Fr_FTLY (Fr_mlift hY c (b - c))) t,
    mlift_app (Fr_FTL _ _ _ _) (Hd_mlift hH c (b - c)) b t, mlift_FTL_base hbr hcb t Lds hL]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_fwLA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b)
    {Lds : List TrioSeq} (hL : ∀ Ld ∈ Lds, Fr Ld ∧ LowC (c + K) Ld)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hLY : LowC (c + K) Y) :
    reliftX b f g (S ++ A0) (fwH b (b + liftOff f (S ++ A0) o + 1)
        (FTL b (b + liftOff f (S ++ A0) o + 1) c Lds) c Y)
      = fwH b (b + liftOff (addF f g) (S ++ A0) o + 1)
          (FTL b (b + liftOff (addF f g) (S ++ A0) o + 1) c (Lds.map (reliftX c f0 g A0))) c
          (reliftX c f0 g A0 Y) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hLY (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  have eH := reliftX_FTLA hA hSA b hf g hK hcb Lds hL
  unfold fwH
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega] at eH ⊢
  rw [reliftX_node (Fr_FTLY (Fr_mlift hY c (b - c))) b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0),
    hlow, reOff_above hA f g 1, reliftX_app (Fr_FTL _ _ _ _) (Hd_mlift hH _ _), eH,
    reliftX_ins_low hSA hf b g hK hL']
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [← em]
  simp only [← Nat.add_assoc]

/-! ## 並び -/

noncomputable def farWL (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : TrioSeq :=
  ws.flatMap (fun w => fwH b r (FTL b r w.2.1 w.1) w.2.1 w.2.2)

theorem farWL_cons (b r : ℕ) (w : List TrioSeq × ℕ × TrioSeq) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    farWL b r (w :: ws) = fwH b r (FTL b r w.2.1 w.1) w.2.1 w.2.2 ++ farWL b r ws := by
  simp [farWL]

theorem farWL_snoc (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) (w : List TrioSeq × ℕ × TrioSeq) :
    farWL b r (ws ++ [w]) = farWL b r ws ++ fwH b r (FTL b r w.2.1 w.1) w.2.1 w.2.2 := by
  simp [farWL, List.flatMap_append]

theorem Fr_farWL (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Fr (farWL b r ws) := by
  intro y hy
  simp only [farWL, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwH b r _ w.2.1 w.2.2 y hy

theorem Hd_farWL (b r : ℕ) : ∀ ws : List (List TrioSeq × ℕ × TrioSeq), Hd (farWL b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farWL_cons]; rfl

theorem farWL_rep (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) (w : List TrioSeq × ℕ × TrioSeq) :
    ∀ m, farWL b r (ws ++ List.replicate m w)
      = farWL b r ws ++ (List.range m).flatMap (fun _ => fwH b r (FTL b r w.2.1 w.1) w.2.1 w.2.2)
  | 0 => by simp [farWL]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farWL_snoc, farWL_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

def RawWkL (k b : ℕ) (w : List TrioSeq × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ Ld ∈ w.1, Fr Ld ∧ LowC (w.2.1 + k) Ld) ∧ Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + k) w.2.2

def RawWskL (k b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop := ∀ w ∈ ws, RawWkL k b w

theorem RawWskL_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hR : RawWskL k b ws) : RawWskL k b' ws := fun w hw => ⟨le_trans (hR w hw).1 h, (hR w hw).2⟩

theorem RawWskL_tail {k b : ℕ} {w : List TrioSeq × ℕ × TrioSeq} {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hR : RawWskL k b (w :: ws)) : RawWskL k b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farWL_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWskL k b ws → mlift (farWL b r ws) v t = farWL b (r + t) ws
  | [] => fun _ => by simp [farWL, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWL_cons, farWL_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWL b r ws),
        mlift_fwL_highk hv hvr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2 t,
        mlift_farWL_highk hv hvr t ws (RawWskL_tail hR)]

theorem mlift_farWL_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWskL k b ws → mlift (farWL b r ws) b t = farWL (b + t) (r + t) ws
  | [] => fun _ => by simp [farWL, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWL_cons, farWL_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWL b r ws),
        mlift_fwL_base hbr hw.1 (fun Ld hLd => (hw.2.1 Ld hLd).1) hw.2.2.1 hw.2.2.2.1 t,
        mlift_farWL_basek hbr t ws (RawWskL_tail hR)]

/-! ## 持ち上げた中身の並び -/

noncomputable def relWsL (A0 : List ℕ) (h g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    List (List TrioSeq × ℕ × TrioSeq) :=
  ws.map (fun w => (w.1.map (reliftX w.2.1 h g A0), w.2.1, reliftX w.2.1 h g A0 w.2.2))

def RawWAL (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : List TrioSeq × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ Ld ∈ w.1, Fr Ld ∧ Hd Ld ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) Ld) ∧
    Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) w.2.2

def RawWsAL (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWAL A0 k0 h b w

theorem RawWsAL_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsAL A0 k0 h b ws) : RawWsAL A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb, (hR w hw).2⟩

theorem RawWsAL_snoc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} {w : List TrioSeq × ℕ × TrioSeq}
    (h : RawWsAL A0 k0 H b ws) (hw : RawWAL A0 k0 H b w) : RawWsAL A0 k0 H b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem RawWskL_relWsL {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsAL A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWskL (reOff (fun _ => 0) (addF h g) A0 k0) b (relWsL A0 h g ws) := by
  intro w hw
  simp only [relWsL, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, fun Ld hLd => ?_, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  · simp only [List.mem_map] at hLd
    obtain ⟨L0, hL0, rfl⟩ := hLd
    have hl := h0.2.1 L0 hL0
    refine ⟨Fr_reliftX hl.1 _ _ _ _, ?_⟩
    have := LowC_reliftX hl.2.2 h g A0
    rwa [reOff_zero_comp] at this
  · have := LowC_reliftX h0.2.2.2.2 h g A0
    rwa [reOff_zero_comp] at this

theorem RawWsAL_relWsL {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsAL A0 k0 H b ws) (g : ℕ → ℕ) :
    RawWsAL A0 k0 (addF H g) b (relWsL A0 H g ws) := by
  intro w hw
  simp only [relWsL, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, fun Ld hLd => ?_, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  · simp only [List.mem_map] at hLd
    obtain ⟨L0, hL0, rfl⟩ := hLd
    have hl := h0.2.1 L0 hL0
    refine ⟨Fr_reliftX hl.1 _ _ _ _, Hd_reliftX hl.2.1 _ _ _ _, ?_⟩
    have := LowC_reliftX hl.2.2 H g A0
    rwa [reOff_zero_comp] at this
  · have := LowC_reliftX h0.2.2.2.2 H g A0
    rwa [reOff_zero_comp] at this

theorem relWsL_snoc (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (Lds : List TrioSeq) (u : ℕ) (X : TrioSeq) :
    relWsL A0 H g (ws ++ [(Lds, u, X)])
      = relWsL A0 H g ws ++ [(Lds.map (reliftX u H g A0), u, reliftX u H g A0 X)] := by
  simp [relWsL]

theorem relWsL_rep (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (Lds : List TrioSeq) (u : ℕ) (W : TrioSeq) (m : ℕ) :
    relWsL A0 H g (ws ++ List.replicate m (Lds, u, W))
      = relWsL A0 H g ws ++ List.replicate m (Lds.map (reliftX u H g A0), u, reliftX u H g A0 W) := by
  simp [relWsL, List.map_replicate]

theorem relWsL_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    relWsL A0 (addF H g) g' (relWsL A0 H g ws) = relWsL A0 H (addF g g') ws := by
  simp [relWsL, reliftX_comp, List.map_map, Function.comp_def]

theorem relWsL_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    relWsL A0 H (fun _ => 0) ws = ws := by
  have e : ∀ c, reliftX c H (fun _ => 0) A0 = id := fun c => by funext Z; simp [reliftX_zero]
  simp [relWsL, e]

theorem relWsL_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) : relWsL A0 H g ws = relWsL A0 H' g ws := by
  unfold relWsL
  refine List.map_congr_left (fun w _ => ?_)
  have e : reliftX w.2.1 H g A0 = reliftX w.2.1 H' g A0 :=
    funext (fun Z => reliftX_congr w.2.1 hH (fun _ _ => rfl) Z)
  rw [e]

theorem reliftX_farWLA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsAL A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farWL b (b + liftOff f (S ++ A0) o + 1) (relWsL A0 h g ws))
      = farWL b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWsL A0 h (addF g g') ws)
  | [] => fun _ => by simp [farWL, relWsL, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsAL A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWsL A0 h g (w :: ws)
          = (w.1.map (reliftX w.2.1 h g A0), w.2.1, reliftX w.2.1 h g A0 w.2.2) :: relWsL A0 h g ws
          from rfl,
        show relWsL A0 h (addF g g') (w :: ws)
          = (w.1.map (reliftX w.2.1 h (addF g g') A0), w.2.1, reliftX w.2.1 h (addF g g') A0 w.2.2) ::
            relWsL A0 h (addF g g') ws from rfl,
        farWL_cons, farWL_cons, reliftX_app (Fr_fwH _ _ _ _ _) (Hd_farWL _ _ _)]
      have hLow : ∀ Z : TrioSeq, LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) Z →
          LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 Z) := by
        intro Z hZ
        have := LowC_reliftX hZ h g A0
        rwa [reOff_zero_comp] at this
      have hLs : ∀ Ld ∈ w.1.map (reliftX w.2.1 h g A0),
          Fr Ld ∧ LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) Ld := by
        intro Ld hLd
        simp only [List.mem_map] at hLd
        obtain ⟨L0, hL0, rfl⟩ := hLd
        exact ⟨Fr_reliftX (hw.2.1 L0 hL0).1 _ _ _ _, hLow _ (hw.2.1 L0 hL0).2.2⟩
      rw [reliftX_fwLA hA hSA b hf g' hK hw.1 hLs (Fr_reliftX hw.2.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.2.1 _ _ _ _) (hLow _ hw.2.2.2.2),
        List.map_map, reliftX_comp, reliftX_farWLA hA hSA b hf g' hK ws hR']
      have e : (reliftX w.2.1 (addF h g) g' A0 ∘ reliftX w.2.1 h g A0) = reliftX w.2.1 h (addF g g') A0 := by
        funext Z; exact reliftX_comp w.2.1 h g g' A0 Z
      rw [e]

end HbN
end TRIO
