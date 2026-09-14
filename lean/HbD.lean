/-
HbD.lean: F のタイの本数 n を持つ遠い語（行 1525 以降のタイの子の並び）の土台。

    FT r n := (1,r,1) :: (1,r,0)^n                          （遠い字と F のタイ。行 1 は字と同じ r）
    fwWn b r n c Y := (1,r,1) :: shiftr01 1 0 (FT r n ++ mlift Y c (b - c))
    farWn b r ws := ws.flatMap (fun w => fwWn b r w.1 w.2.1 w.2.2)     （w = (n, c, Y)）

fwWn b r 0 c Y = fwW b r c Y。F のタイは字と一緒に持ち上がる（mlift_FT、reliftX_FT）。
-/
import HaC

namespace TRIO
namespace HbD

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC

/-! ## 字と F のタイ -/

def FT (r n : ℕ) : TrioSeq := ((1, r, 1) : ℕ × ℕ × ℕ) :: List.replicate n ((1, r, 0) : ℕ × ℕ × ℕ)

theorem FT_succ (r n : ℕ) : FT r (n + 1) = FT r n ++ [((1, r, 0) : ℕ × ℕ × ℕ)] := by
  simp [FT, List.replicate_succ']

theorem Fr_FT (r n : ℕ) : Fr (FT r n) := by
  intro x hx
  simp only [FT, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨-, rfl⟩ <;> exact Nat.le_refl 1

theorem mlift_FT {v r : ℕ} (hvr : v < r) (t : ℕ) : ∀ n, mlift (FT r n) v t = FT (r + t) n
  | 0 => by simpa [FT] using mlift_one hvr t
  | n + 1 => by
      rw [FT_succ, mlift_snoc_cone _ _ (coneV_top' (Fr_FT r n) hvr) t, mlift_FT hvr t n, FT_succ]

theorem reliftX_one (b s z : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    reliftX b f g A [((1, b + s, z) : ℕ × ℕ × ℕ)] = [((1, b + reOff f g A s, z) : ℕ × ℕ × ℕ)] := by
  have := reliftX_node (V := []) Fr_nil b s z f g A
  simpa [shiftr01, reliftX, slift_nil] using this

theorem reliftX_FT (b s : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    ∀ n, reliftX b f g A (FT (b + s) n) = FT (b + reOff f g A s) n
  | 0 => by simpa [FT] using reliftX_one b s 1 f g A
  | n + 1 => by
      rw [FT_succ, reliftX_app (Fr_FT _ n) (fun _ => rfl), reliftX_FT b s f g A n,
        reliftX_one b s 0 f g A, FT_succ]

/-! ## 語 -/

noncomputable def fwWn (b r n c : ℕ) (Y : TrioSeq) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ mlift Y c (b - c))

theorem fwWn_zero (b r c : ℕ) (Y : TrioSeq) : fwWn b r 0 c Y = fwW b r c Y := rfl

theorem Fr_fwWn (b r n c : ℕ) (Y : TrioSeq) : Fr (fwWn b r n c Y) := Fr_letter _ _

theorem Hd_fwWn (b r n c : ℕ) (Y : TrioSeq) : Hd (fwWn b r n c Y) := Hd_letter _ _

theorem Fr_FTY {r n : ℕ} {Y : TrioSeq} (hY : Fr Y) : Fr (FT r n ++ Y) := Fr_append (Fr_FT r n) hY

theorem mlift_fwWn_highk {b v r n c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b)
    {Y : TrioSeq} (hY : Fr Y) (hL : LowC (c + k) Y) (t : ℕ) :
    mlift (fwWn b r n c Y) v t = fwWn b (r + t) n c Y := by
  unfold fwWn
  rw [mlift_letter hvr (Fr_FTY (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hL (b - c))
  rw [mlift_append_low (A := FT r n) hL' t, mlift_FT hvr t n]

theorem mlift_fwWn_base {b r n c : ℕ} (hbr : b < r) (hcb : c ≤ b) {Y : TrioSeq} (hY : Fr Y)
    (hH : Hd Y) (t : ℕ) : mlift (fwWn b r n c Y) b t = fwWn (b + t) (r + t) n c Y := by
  unfold fwWn
  rw [mlift_letter hbr (Fr_FTY (Fr_mlift hY c (b - c))) t,
    mlift_app (Fr_FT r n) (Hd_mlift hH c (b - c)) b t, mlift_FT hbr t n]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_fwWnA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) {n c : ℕ} (hcb : c ≤ b)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hL : LowC (c + K) Y) :
    reliftX b f g (S ++ A0) (fwWn b (b + liftOff f (S ++ A0) o + 1) n c Y)
      = fwWn b (b + liftOff (addF f g) (S ++ A0) o + 1) n c (reliftX c f0 g A0 Y) := by
  unfold fwWn
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega,
    reliftX_node (Fr_FTY (Fr_mlift hY c (b - c))) b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)]
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  rw [hlow, reOff_above hA f g 1]
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hL (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  rw [reliftX_app (Fr_FT _ n) (Hd_mlift hH _ _), reliftX_ins_low hSA hf b g hK hL',
    reliftX_FT b (liftOff f (S ++ A0) o + 1) f g (S ++ A0) n, reOff_above hA f g 1]
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [← em]
  simp only [← Nat.add_assoc]

theorem fwWn_lift_eq (b r n : ℕ) {u u' : ℕ} (hu : u ≤ u') (hub : u' ≤ b) (W : TrioSeq) :
    fwWn b r n u' (mlift W u (u' - u)) = fwWn b r n u W := by
  unfold fwWn
  have e2 := mlift_mlift W u (u' - u) (b - u')
  rw [show u + (u' - u) = u' by omega, show u' - u + (b - u') = b - u by omega] at e2
  rw [e2]

theorem fwWn_append (b r n c : ℕ) {W U : TrioSeq} (hW : Fr W) (hU : Hd U) :
    fwWn b r n c (W ++ U) = fwWn b r n c W ++ shiftr01 1 0 (mlift U c (b - c)) := by
  unfold fwWn
  rw [mlift_app hW hU]
  simp [shiftr01]

/-! ## 並び -/

noncomputable def farWn (b r : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) : TrioSeq :=
  ws.flatMap (fun w => fwWn b r w.1 w.2.1 w.2.2)

theorem farWn_cons (b r : ℕ) (w : ℕ × ℕ × TrioSeq) (ws : List (ℕ × ℕ × TrioSeq)) :
    farWn b r (w :: ws) = fwWn b r w.1 w.2.1 w.2.2 ++ farWn b r ws := by simp [farWn]

theorem farWn_snoc (b r : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) (w : ℕ × ℕ × TrioSeq) :
    farWn b r (ws ++ [w]) = farWn b r ws ++ fwWn b r w.1 w.2.1 w.2.2 := by
  simp [farWn, List.flatMap_append]

theorem Fr_farWn (b r : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) : Fr (farWn b r ws) := by
  intro y hy
  simp only [farWn, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwWn b r w.1 w.2.1 w.2.2 y hy

theorem Hd_farWn (b r : ℕ) : ∀ ws : List (ℕ × ℕ × TrioSeq), Hd (farWn b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farWn_cons]; rfl

theorem farWn_rep (b r : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) (w : ℕ × ℕ × TrioSeq) :
    ∀ m, farWn b r (ws ++ List.replicate m w)
      = farWn b r ws ++ (List.range m).flatMap (fun _ => fwWn b r w.1 w.2.1 w.2.2)
  | 0 => by simp [farWn]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farWn_snoc, farWn_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

def RawWkn (k b : ℕ) (w : ℕ × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + k) w.2.2

def RawWskn (k b : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) : Prop := ∀ w ∈ ws, RawWkn k b w

theorem RawWskn_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (ℕ × ℕ × TrioSeq)} (hR : RawWskn k b ws) :
    RawWskn k b' ws := fun w hw => ⟨le_trans (hR w hw).1 h, (hR w hw).2⟩

theorem RawWskn_tail {k b : ℕ} {w : ℕ × ℕ × TrioSeq} {ws : List (ℕ × ℕ × TrioSeq)}
    (hR : RawWskn k b (w :: ws)) : RawWskn k b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farWn_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWskn k b ws → mlift (farWn b r ws) v t = farWn b (r + t) ws
  | [] => fun _ => by simp [farWn, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWn_cons, farWn_cons, mlift_app (Fr_fwWn b r _ _ _) (Hd_farWn b r ws),
        mlift_fwWn_highk hv hvr hw.1 hw.2.1 hw.2.2.2 t,
        mlift_farWn_highk hv hvr t ws (RawWskn_tail hR)]

theorem mlift_farWn_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWskn k b ws → mlift (farWn b r ws) b t = farWn (b + t) (r + t) ws
  | [] => fun _ => by simp [farWn, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWn_cons, farWn_cons, mlift_app (Fr_fwWn b r _ _ _) (Hd_farWn b r ws),
        mlift_fwWn_base hbr hw.1 hw.2.1 hw.2.2.1 t, mlift_farWn_basek hbr t ws (RawWskn_tail hR)]

/-! ## 持ち上げた中身の並び -/

noncomputable def relWsn (A0 : List ℕ) (h g : ℕ → ℕ) (ws : List (ℕ × ℕ × TrioSeq)) :
    List (ℕ × ℕ × TrioSeq) :=
  ws.map (fun w => (w.1, w.2.1, reliftX w.2.1 h g A0 w.2.2))

def RawWAn (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : ℕ × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) w.2.2

def RawWsAn (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWAn A0 k0 h b w

theorem RawWsAn_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (ℕ × ℕ × TrioSeq)} (hR : RawWsAn A0 k0 h b ws) : RawWsAn A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb, (hR w hw).2⟩

theorem RawWsAn_snoc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    {w : ℕ × ℕ × TrioSeq} (h : RawWsAn A0 k0 H b ws) (hw : RawWAn A0 k0 H b w) :
    RawWsAn A0 k0 H b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem RawWskn_relWsn {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    (hR : RawWsAn A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWskn (reOff (fun _ => 0) (addF h g) A0 k0) b (relWsn A0 h g ws) := by
  intro w hw
  simp only [relWsn, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, Fr_reliftX h0.2.1 _ _ _ _, Hd_reliftX h0.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2 h g A0
  rwa [reOff_zero_comp] at this

theorem RawWsAn_relWsn {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    (hR : RawWsAn A0 k0 H b ws) (g : ℕ → ℕ) : RawWsAn A0 k0 (addF H g) b (relWsn A0 H g ws) := by
  intro w hw
  simp only [relWsn, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, Fr_reliftX h0.2.1 _ _ _ _, Hd_reliftX h0.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2 H g A0
  rwa [reOff_zero_comp] at this

theorem relWsn_snoc (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (ℕ × ℕ × TrioSeq)) (n u : ℕ)
    (X : TrioSeq) : relWsn A0 H g (ws ++ [(n, u, X)]) = relWsn A0 H g ws ++ [(n, u, reliftX u H g A0 X)] := by
  simp [relWsn]

theorem relWsn_rep (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (ℕ × ℕ × TrioSeq)) (n u : ℕ) (W : TrioSeq)
    (m : ℕ) : relWsn A0 H g (ws ++ List.replicate m (n, u, W))
      = relWsn A0 H g ws ++ List.replicate m (n, u, reliftX u H g A0 W) := by
  simp [relWsn, List.map_replicate]

theorem relWsn_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (ws : List (ℕ × ℕ × TrioSeq)) :
    relWsn A0 (addF H g) g' (relWsn A0 H g ws) = relWsn A0 H (addF g g') ws := by
  simp [relWsn, reliftX_comp]

theorem relWsn_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (ℕ × ℕ × TrioSeq)) :
    relWsn A0 H (fun _ => 0) ws = ws := by
  simp [relWsn, reliftX_zero]

theorem relWsn_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (ℕ × ℕ × TrioSeq)) : relWsn A0 H g ws = relWsn A0 H' g ws := by
  unfold relWsn
  exact List.map_congr_left (fun w _ => by rw [reliftX_congr w.2.1 hH (fun _ _ => rfl) w.2.2])

theorem reliftX_farWnA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsAn A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farWn b (b + liftOff f (S ++ A0) o + 1) (relWsn A0 h g ws))
      = farWn b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWsn A0 h (addF g g') ws)
  | [] => fun _ => by simp [farWn, relWsn, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsAn A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWsn A0 h g (w :: ws) = (w.1, w.2.1, reliftX w.2.1 h g A0 w.2.2) :: relWsn A0 h g ws
          from rfl,
        show relWsn A0 h (addF g g') (w :: ws)
          = (w.1, w.2.1, reliftX w.2.1 h (addF g g') A0 w.2.2) :: relWsn A0 h (addF g g') ws from rfl,
        farWn_cons, farWn_cons, reliftX_app (Fr_fwWn _ _ _ _ _) (Hd_farWn _ _ _)]
      have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
        have := LowC_reliftX hw.2.2.2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_fwWnA hA hSA b hf g' hK hw.1 (Fr_reliftX hw.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.1 _ _ _ _) hL,
        reliftX_comp, reliftX_farWnA hA hSA b hf g' hK ws hR']

end HbD
end TRIO
