/-
HbP.lean: F のタイごとに荷（級の段で低い列）の子を持つ遠い語の族の核（行 1577 以降、HbN・HbO の簡約）。

    FTL0 r Lds := (1,r,1) :: Lds.flatMap (fun Ld => (1,r,0) :: shiftr01 1 0 Ld)
    farW0 b r ws := ws.flatMap (fun w => fwH b r (FTL0 r w.1) w.2.1 w.2.2)        （w = (Lds, c, Y)）
    FarCA0 A0 k0 h b0 ws := ∀ g S o f b, 条件 → GpT (S ++ A0) o f b (farW0 b r (relWs0 A0 h g ws))

F のタイの子 Ld は級の段 b で低い（RawWA0 に LowC b Ld）ので、持ち上げ（段 b 以上）でも再持ち上げでも変わらない。
中身 Y は HbE と同じく語の段で持ち上がる。
-/
import HbM

namespace TRIO
namespace HbP

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM

/-! ## 頭 -/

def FTL0 (r : ℕ) (Lds : List TrioSeq) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) :: Lds.flatMap (fun Ld => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Ld)

theorem FTL0_snoc (r : ℕ) (Lds : List TrioSeq) (Ld : TrioSeq) :
    FTL0 r (Lds ++ [Ld]) = FTL0 r Lds ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Ld := by
  simp [FTL0, List.flatMap_append]

theorem FTL0_rep_nil (r : ℕ) : ∀ n, FTL0 r (List.replicate n []) = FT r n
  | 0 => by simp [FTL0, FT]
  | n + 1 => by
      rw [List.replicate_succ', FTL0_snoc, FTL0_rep_nil r n, FT_succ]
      simp [shiftr01]

theorem Fr_FTL0 (r : ℕ) (Lds : List TrioSeq) : Fr (FTL0 r Lds) := by
  intro x hx
  simp only [FTL0, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨Ld, -, hx⟩
  · exact Nat.le_refl 1
  · rcases hx with rfl | hx
    · exact Nat.le_refl 1
    · simp only [shiftr01, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      dsimp only; omega

theorem mlift_FTL0 {v r : ℕ} (hvr : v < r) (t : ℕ) :
    ∀ Lds : List TrioSeq, (∀ Ld ∈ Lds, Fr Ld ∧ LowC v Ld) → mlift (FTL0 r Lds) v t = FTL0 (r + t) Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTL0] using mlift_one hvr t
  | append_singleton Lds Ld ih =>
      intro hL
      have hLd := hL Ld (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTL0_snoc, FTL0_snoc, mlift_app (Fr_FTL0 _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hvr hLd.1]
      have e := mlift_append_low (A := []) hLd.2 t
      simp only [List.nil_append, mlift_nil] at e
      rw [e]

theorem reliftX_FTL0A {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ) :
    ∀ Lds : List TrioSeq, (∀ Ld ∈ Lds, Fr Ld ∧ LowC b Ld) →
    reliftX b f g A (FTL0 (b + liftOff f A o + 1) Lds) = FTL0 (b + liftOff (addF f g) A o + 1) Lds := by
  have hlow : lowP f A (liftOff f A o + 1) = A :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _
      have := reliftX_one b (liftOff f A o + 1) 1 f g A
      rw [reOff_above hA f g 1] at this
      simpa [FTL0, ← Nat.add_assoc] using this
  | append_singleton Lds Ld ih =>
      intro hL
      have hLd := hL Ld (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTL0_snoc, FTL0_snoc, reliftX_app (Fr_FTL0 _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')),
        show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega,
        reliftX_node hLd.1 b (liftOff f A o + 1) 0 f g A, hlow, reOff_above hA f g 1]
      have e : reliftX b f g A Ld = Ld := by
        have := slift_append_low (A := []) hLd.2 (φ := reStair b f g A)
          (fun m hm => reStair_low b f g A hm)
        simpa [slift_nil] using this
      rw [e]
      simp only [← Nat.add_assoc]

/-! ## 語と並び -/

theorem Fr_FTL0Y {r : ℕ} {Lds : List TrioSeq} {Y : TrioSeq} (hY : Fr Y) : Fr (FTL0 r Lds ++ Y) :=
  Fr_append (Fr_FTL0 r Lds) hY

noncomputable def farW0 (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : TrioSeq :=
  ws.flatMap (fun w => fwH b r (FTL0 r w.1) w.2.1 w.2.2)

theorem farW0_cons (b r : ℕ) (w : List TrioSeq × ℕ × TrioSeq) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    farW0 b r (w :: ws) = fwH b r (FTL0 r w.1) w.2.1 w.2.2 ++ farW0 b r ws := by simp [farW0]

theorem farW0_snoc (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) (w : List TrioSeq × ℕ × TrioSeq) :
    farW0 b r (ws ++ [w]) = farW0 b r ws ++ fwH b r (FTL0 r w.1) w.2.1 w.2.2 := by
  simp [farW0, List.flatMap_append]

theorem Fr_farW0 (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Fr (farW0 b r ws) := by
  intro y hy
  simp only [farW0, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwH b r _ w.2.1 w.2.2 y hy

theorem Hd_farW0 (b r : ℕ) : ∀ ws : List (List TrioSeq × ℕ × TrioSeq), Hd (farW0 b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farW0_cons]; rfl

theorem farW0_rep (b r : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) (w : List TrioSeq × ℕ × TrioSeq) :
    ∀ m, farW0 b r (ws ++ List.replicate m w)
      = farW0 b r ws ++ (List.range m).flatMap (fun _ => fwH b r (FTL0 r w.1) w.2.1 w.2.2)
  | 0 => by simp [farW0]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farW0_snoc, farW0_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

theorem mlift_fw0_highk {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b)
    {Lds : List TrioSeq} (hL : ∀ Ld ∈ Lds, Fr Ld ∧ LowC b Ld)
    {Y : TrioSeq} (hY : Fr Y) (hLY : LowC (c + k) Y) (t : ℕ) :
    mlift (fwH b r (FTL0 r Lds) c Y) v t = fwH b (r + t) (FTL0 (r + t) Lds) c Y := by
  unfold fwH
  rw [mlift_letter hvr (Fr_FTL0Y (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hLY (b - c))
  rw [mlift_append_low (A := FTL0 r Lds) hL' t,
    mlift_FTL0 hvr t Lds (fun Ld hLd => ⟨(hL Ld hLd).1, LowC_mono (by omega) (hL Ld hLd).2⟩)]

theorem mlift_fw0_base {b r c : ℕ} (hbr : b < r) (hcb : c ≤ b) {Lds : List TrioSeq}
    (hL : ∀ Ld ∈ Lds, Fr Ld ∧ LowC b Ld) {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (t : ℕ) :
    mlift (fwH b r (FTL0 r Lds) c Y) b t = fwH (b + t) (r + t) (FTL0 (r + t) Lds) c Y := by
  unfold fwH
  rw [mlift_letter hbr (Fr_FTL0Y (Fr_mlift hY c (b - c))) t,
    mlift_app (Fr_FTL0 _ _) (Hd_mlift hH c (b - c)) b t, mlift_FTL0 hbr t Lds hL]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_fw0A {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b)
    {Lds : List TrioSeq} (hL : ∀ Ld ∈ Lds, Fr Ld ∧ LowC b Ld)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hLY : LowC (c + K) Y) :
    reliftX b f g (S ++ A0) (fwH b (b + liftOff f (S ++ A0) o + 1) (FTL0 (b + liftOff f (S ++ A0) o + 1) Lds) c Y)
      = fwH b (b + liftOff (addF f g) (S ++ A0) o + 1) (FTL0 (b + liftOff (addF f g) (S ++ A0) o + 1) Lds) c
          (reliftX c f0 g A0 Y) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hLY (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  have eH := reliftX_FTL0A hA b f g Lds hL
  unfold fwH
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega] at eH ⊢
  rw [reliftX_node (Fr_FTL0Y (Fr_mlift hY c (b - c))) b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0),
    hlow, reOff_above hA f g 1, reliftX_app (Fr_FTL0 _ _) (Hd_mlift hH _ _), eH,
    reliftX_ins_low hSA hf b g hK hL']
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [← em]
  simp only [← Nat.add_assoc]

def RawWk0 (k b : ℕ) (w : List TrioSeq × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ Ld ∈ w.1, Fr Ld ∧ LowC b Ld) ∧ Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + k) w.2.2

def RawWsk0 (k b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop := ∀ w ∈ ws, RawWk0 k b w

theorem RawWsk0_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hR : RawWsk0 k b ws) : RawWsk0 k b' ws := fun w hw =>
  ⟨le_trans (hR w hw).1 h, fun Ld hLd => ⟨((hR w hw).2.1 Ld hLd).1, LowC_mono h ((hR w hw).2.1 Ld hLd).2⟩,
    (hR w hw).2.2⟩

theorem RawWsk0_tail {k b : ℕ} {w : List TrioSeq × ℕ × TrioSeq} {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hR : RawWsk0 k b (w :: ws)) : RawWsk0 k b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farW0_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWsk0 k b ws → mlift (farW0 b r ws) v t = farW0 b (r + t) ws
  | [] => fun _ => by simp [farW0, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW0_cons, farW0_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farW0 b r ws),
        mlift_fw0_highk hv hvr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2 t,
        mlift_farW0_highk hv hvr t ws (RawWsk0_tail hR)]

theorem mlift_farW0_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWsk0 k b ws → mlift (farW0 b r ws) b t = farW0 (b + t) (r + t) ws
  | [] => fun _ => by simp [farW0, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW0_cons, farW0_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farW0 b r ws),
        mlift_fw0_base hbr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 t,
        mlift_farW0_basek hbr t ws (RawWsk0_tail hR)]

/-! ## 持ち上げた中身の並び -/

noncomputable def relWs0 (A0 : List ℕ) (h g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    List (List TrioSeq × ℕ × TrioSeq) :=
  ws.map (fun w => (w.1, w.2.1, reliftX w.2.1 h g A0 w.2.2))

def RawWA0 (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : List TrioSeq × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ Ld ∈ w.1, Fr Ld ∧ LowC b Ld) ∧
    Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) w.2.2

def RawWsA0 (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWA0 A0 k0 h b w

theorem RawWsA0_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsA0 A0 k0 h b ws) : RawWsA0 A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb,
    fun Ld hLd => ⟨((hR w hw).2.1 Ld hLd).1, LowC_mono hbb ((hR w hw).2.1 Ld hLd).2⟩, (hR w hw).2.2⟩

theorem RawWsA0_snoc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} {w : List TrioSeq × ℕ × TrioSeq}
    (h : RawWsA0 A0 k0 H b ws) (hw : RawWA0 A0 k0 H b w) : RawWsA0 A0 k0 H b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem RawWsk0_relWs0 {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsA0 A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWsk0 (reOff (fun _ => 0) (addF h g) A0 k0) b (relWs0 A0 h g ws) := by
  intro w hw
  simp only [relWs0, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, h0.2.1, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 h g A0
  rwa [reOff_zero_comp] at this

theorem RawWsA0_relWs0 {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsA0 A0 k0 H b ws) (g : ℕ → ℕ) :
    RawWsA0 A0 k0 (addF H g) b (relWs0 A0 H g ws) := by
  intro w hw
  simp only [relWs0, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, h0.2.1, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 H g A0
  rwa [reOff_zero_comp] at this

theorem relWs0_snoc (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (Lds : List TrioSeq) (u : ℕ) (X : TrioSeq) :
    relWs0 A0 H g (ws ++ [(Lds, u, X)]) = relWs0 A0 H g ws ++ [(Lds, u, reliftX u H g A0 X)] := by
  simp [relWs0]

theorem relWs0_rep (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq))
    (Lds : List TrioSeq) (u : ℕ) (W : TrioSeq) (m : ℕ) :
    relWs0 A0 H g (ws ++ List.replicate m (Lds, u, W))
      = relWs0 A0 H g ws ++ List.replicate m (Lds, u, reliftX u H g A0 W) := by
  simp [relWs0, List.map_replicate]

theorem relWs0_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    relWs0 A0 (addF H g) g' (relWs0 A0 H g ws) = relWs0 A0 H (addF g g') ws := by
  simp [relWs0, reliftX_comp]

theorem relWs0_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    relWs0 A0 H (fun _ => 0) ws = ws := by
  simp [relWs0, reliftX_zero]

theorem relWs0_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) : relWs0 A0 H g ws = relWs0 A0 H' g ws := by
  unfold relWs0
  exact List.map_congr_left (fun w _ => by rw [reliftX_congr w.2.1 hH (fun _ _ => rfl) w.2.2])

theorem reliftX_farW0A {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsA0 A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farW0 b (b + liftOff f (S ++ A0) o + 1) (relWs0 A0 h g ws))
      = farW0 b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWs0 A0 h (addF g g') ws)
  | [] => fun _ => by simp [farW0, relWs0, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsA0 A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWs0 A0 h g (w :: ws) = (w.1, w.2.1, reliftX w.2.1 h g A0 w.2.2) :: relWs0 A0 h g ws
          from rfl,
        show relWs0 A0 h (addF g g') (w :: ws)
          = (w.1, w.2.1, reliftX w.2.1 h (addF g g') A0 w.2.2) :: relWs0 A0 h (addF g g') ws from rfl,
        farW0_cons, farW0_cons, reliftX_app (Fr_fwH _ _ _ _ _) (Hd_farW0 _ _ _)]
      have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
        have := LowC_reliftX hw.2.2.2.2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_fw0A hA hSA b hf g' hK hw.1 hw.2.1 (Fr_reliftX hw.2.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.2.1 _ _ _ _) hL,
        reliftX_comp, reliftX_farW0A hA hSA b hf g' hK ws hR']

end HbP
end TRIO
