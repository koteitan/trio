/-
GzU.lean: GzM の閾値を b+1 から b+k に上げた版（錨が全て k 以上、節点が k 以上の添字に限る）。

    RawWk k b w    := w.1 ≤ b ∧ Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + k) w.2
    FarCWk k b0 ws := ∀ A o f b, b0 ≤ b → RawWsk k b ws → A < o → 1 ≤ A → 1 ≤ o → k ≤ A → k ≤ o →
                        GpT A o f b (farW b (b + liftOff f A o + 1) ws)

錨が k 以上なら再持ち上げは段 b+k 以下を動かさず（reStair_k）、節点が k 以上なら t の持ち上げも動かさない。
潰れの塔の F の子の添字 (o :: A, o+1) も同じ条件を満たす。
-/
import GzM

namespace TRIO
namespace GzU

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM

theorem LowC_mliftk {c k : ℕ} {Y : TrioSeq} (hY : LowC (c + k) Y) (t : ℕ) :
    LowC (c + k + t) (mlift Y c t) := by
  intro i hi
  rw [mlift_length] at hi
  obtain ⟨j, hj, hle⟩ := hY i hi
  have hjY : j < Y.length := lt_of_le_of_lt (rtg0_le hj) hi
  refine ⟨j, ?_, ?_⟩
  · rw [mlift_eq_slift]; exact rtg0_slift'.mpr hj
  · rw [entry1_mlift hjY]; split_ifs <;> omega

theorem reStair_k (b : ℕ) (f g : ℕ → ℕ) {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, k ≤ a) {m : ℕ}
    (hm : m ≤ b + k) : reStair b f g A m = m := by
  have key : ∀ A' : List ℕ, (∀ a ∈ A', k ≤ a) → reStep b f g A A' m = 0 := by
    intro A' hA'
    induction A' with
    | nil => rfl
    | cons a A' ih =>
        simp only [reStep]
        have h1 := hA' a (by simp)
        have h2 : a ≤ liftVal f A a := by unfold liftVal; omega
        rw [if_neg (by omega), ih (fun x hx => hA' x (List.mem_cons_of_mem a hx))]
  simp [reStair, key A hAk]

theorem mlift_fwW_highk {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b) {Y : TrioSeq}
    (hY : Fr Y) (hL : LowC (c + k) Y) (t : ℕ) : mlift (fwW b r c Y) v t = fwW b (r + t) c Y := by
  unfold fwW
  rw [mlift_letter hvr (Fr_FLW (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hL (b - c))
  have e := mlift_append_low (A := [((1, r, 1) : ℕ × ℕ × ℕ)]) hL' t
  simp only [List.singleton_append] at e
  rw [e, mlift_one hvr]
  rfl

theorem reliftX_fwWk {A : List ℕ} {o k : ℕ} (hA : ∀ a ∈ A, a < o) (hAk : ∀ a ∈ A, k ≤ a)
    (b : ℕ) (f g : ℕ → ℕ) {c : ℕ} (hcb : c ≤ b) {Y : TrioSeq} (hY : Fr Y) (hL : LowC (c + k) Y) :
    reliftX b f g A (fwW b (b + liftOff f A o + 1) c Y)
      = fwW b (b + liftOff (addF f g) A o + 1) c Y := by
  unfold fwW
  rw [show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega,
    reliftX_node (Fr_FLW (Fr_mlift hY c (b - c))) b (liftOff f A o + 1) 1 f g A]
  have hlow : lowP f A (liftOff f A o + 1) = A :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  rw [hlow, reOff_above hA f g 1]
  have hL' : LowC (b + k) (mlift Y c (b - c)) := by
    have := LowC_mliftk hL (b - c)
    rwa [show c + k + (b - c) = b + k by omega] at this
  have e : reliftX b f g A ([((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)] ++ mlift Y c (b - c))
      = reliftX b f g A [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)] ++ mlift Y c (b - c) := by
    unfold reliftX
    exact slift_append_low hL' (fun m hm => reStair_k b f g hAk hm)
  simp only [List.singleton_append] at e
  rw [e]
  have e1 : reliftX b f g A [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)]
      = [((1, b + (liftOff (addF f g) A o + 1), 1) : ℕ × ℕ × ℕ)] := by
    have := reliftX_node (V := []) Fr_nil b (liftOff f A o + 1) 1 f g A
    rw [hlow, reOff_above hA f g 1] at this
    simpa [shiftr01, reliftX, slift_nil] using this
  rw [e1]
  simp only [List.singleton_append, ← Nat.add_assoc]

/-! ## 並び -/

def RawWk (k b : ℕ) (w : ℕ × TrioSeq) : Prop := w.1 ≤ b ∧ Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + k) w.2

def RawWsk (k b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop := ∀ w ∈ ws, RawWk k b w

theorem RawWk_mono {k b b' : ℕ} (h : b ≤ b') {w : ℕ × TrioSeq} (hw : RawWk k b w) : RawWk k b' w :=
  ⟨le_trans hw.1 h, hw.2.1, hw.2.2.1, hw.2.2.2⟩

theorem RawWsk_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    RawWsk k b' ws := fun w hw => RawWk_mono h (hR w hw)

theorem RawWsk_tail {k b : ℕ} {w : ℕ × TrioSeq} {ws : List (ℕ × TrioSeq)}
    (hR : RawWsk k b (w :: ws)) : RawWsk k b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farW_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWsk k b ws → mlift (farW b r ws) v t = farW b (r + t) ws
  | [] => fun _ => by simp [farW, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW_cons, farW_cons, mlift_app (Fr_fwW b r _ _) (Hd_farW b r ws),
        mlift_fwW_highk hv hvr hw.1 hw.2.1 hw.2.2.2 t, mlift_farW_highk hv hvr t ws (RawWsk_tail hR)]

theorem mlift_farW_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWsk k b ws → mlift (farW b r ws) b t = farW (b + t) (r + t) ws
  | [] => fun _ => by simp [farW, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW_cons, farW_cons, mlift_app (Fr_fwW b r _ _) (Hd_farW b r ws),
        mlift_fwW_base hbr hw.1 hw.2.1 hw.2.2.1 t, mlift_farW_basek hbr t ws (RawWsk_tail hR)]

theorem reliftX_farWk {A : List ℕ} {o k : ℕ} (hA : ∀ a ∈ A, a < o) (hAk : ∀ a ∈ A, k ≤ a)
    (b : ℕ) (f g : ℕ → ℕ) : ∀ ws, RawWsk k b ws →
    reliftX b f g A (farW b (b + liftOff f A o + 1) ws)
      = farW b (b + liftOff (addF f g) A o + 1) ws
  | [] => fun _ => by simp [farW, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW_cons, farW_cons, reliftX_app (Fr_fwW _ _ _ _) (Hd_farW _ _ ws),
        reliftX_fwWk hA hAk b f g hw.1 hw.2.1 hw.2.2.2, reliftX_farWk hA hAk b f g ws (RawWsk_tail hR)]

/-! ## 全ての錨の列（k 以上）で GpT -/

def FarCWk (k b0 : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawWsk k b ws → (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → (∀ a ∈ A, k ≤ a) → k ≤ o →
    GpT A o f b (farW b (b + liftOff f A o + 1) ws)

theorem FarCWk_nil (k b0 : ℕ) : FarCWk k b0 [] := by
  intro A o f b _ _ hA hA1 ho _ _
  rw [show farW b (b + liftOff f A o + 1) [] = [] from rfl]
  rcases Nat.lt_or_ge o 2 with h | h
  · have ho1 : o = 1 := by omega
    subst ho1
    have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
    subst hA0
    exact GpT_nil1 f b
  · exact GpT_nil hA h f b

theorem farWk_PVP {k b0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCWk k b0 ws) {A : List ℕ}
    {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (hAk : ∀ a ∈ A, k ≤ a)
    (hko : k ≤ o) (f : ℕ → ℕ) (b : ℕ) (hb : b0 ≤ b) (hR : RawWsk k b ws) :
    PVP A o f b (farW b (b + liftOff f A o + 1) ws) := by
  intro t
  have hk : o ≤ liftOff f A o := by unfold liftOff; omega
  rw [mlift_farW_highk (show b + k ≤ b + liftOff f A o by omega)
    (show b + liftOff f A o < b + liftOff f A o + 1 by omega) t ws hR]
  have := hC A (o + t) f b hb hR (fun a ha => by have := hA a ha; omega) hA1 (by omega) hAk
    (by omega)
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega]
    at this

/-! ## 潰れの塔 -/

theorem towWk_GpT {k b0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCWk k b0 ws) :
    ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawWsk k b ws →
    (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → (∀ a ∈ A, k ≤ a) → k ≤ o →
    GpT A o f b (towW b ws (b + liftOff f A o + 1) m)
  | 0, A, o, f, b, hb, hR, hA, hA1, ho, hAk, hko => by
      rw [towW]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_farW _ _ ws)
        (farWk_PVP hC hA hA1 ho hAk hko f b hb hR))
  | m + 1, A, o, f, b, hb, hR, hA, hA1, ho, hAk, hko => by
      have hAo' : ∀ a ∈ o :: A, a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hA1' : ∀ a ∈ o :: A, 1 ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ho
        · exact hA1 a ha
      have hAk' : ∀ a ∈ o :: A, k ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hko
        · exact hAk a ha
      obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ, H = upF o 0 f := ⟨_, rfl⟩
      have hHo : H o = 0 := by rw [hH]; simp [upF]
      have hHA : ∀ a ∈ A, H a = f a := by rw [hH]; exact upF_low hA 0 f
      have e1 : liftOff H (o :: A) (o + 1) = liftOff f A o + 1 := by
        rw [sumOn_liftOff hAo', sumOn_liftOff hA]
        simp only [sumOn, hHo, sumOn_congr hHA]
        omega
      have hL := towWk_GpT hC m (o :: A) (o + 1) H b hb hR hAo' hA1' (by omega) hAk' (by omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b
          (towW b ws (b + liftOff f A o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_farW _ _ ws) (farWk_PVP hC hA hA1 ho hAk hko f b hb hR)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towW]
      exact PVP_to_GpT this

theorem mlift_PWk {k b c : ℕ} (hbc : b + k ≤ c) {ws : List (ℕ × TrioSeq)}
    (hR : RawWsk k b ws) (j : ℕ) :
    mlift (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = farW b (c + 1 + j) ws ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_farW _ _ ws) (fun _ => rfl), mlift_farW_highk hbc (by omega) j ws hR,
    mlift_one (show c < c + 1 by omega)]

theorem farWk_flat {k b : ℕ} {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    ∀ m c, b + k ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1) m
  | 0, c, hc => by simp [mlift_PWk hc hR, towW]
  | m + 1, c, hc => by
      rw [flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farW b (c + 1 + 1) ws ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_PWk hc hR, mlift_PWk (c := c + 1) (by omega) hR, shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farW b (c + 1 + 1) ws ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farWk_flat hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW b ws (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1 + 1) m) from rfl,
          ← shift_shift]
        rfl
      rw [towW, eT]
      simp [mlift_PWk hc hR]

/-- ★ 遠い語（中身が遠い字だけ）の潰れ（閾値 k の版）。 -/
theorem farWk_collapse {k b0 c0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCWk k b0 ws) :
    FarCWk k b0 (ws ++ [(c0, [])]) := by
  intro A o f b hb hR hA hA1 ho hAk hko
  have hR0 : RawWsk k b ws := fun w h => hR w (List.mem_append_left _ h)
  refine GpT_intro hA (fun R hR' g => ?_)
  rw [reliftX_farWk hA hAk b f g _ hR]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff F A o := ⟨_, rfl⟩
  rw [← hF, ← hkk]
  have hk1 : o ≤ kk := by rw [hkk]; unfold liftOff; omega
  intro u' hu X hX hRX
  rw [mlift_farW_basek (show b < b + kk + 1 by omega) (u' - b) _ hR,
    show b + kk + 1 + (u' - b) = u' + kk + 1 by omega, show b + (u' - b) = u' by omega, farW_snoc]
  have hRu : RawWsk k u' ws := RawWsk_mono hu hR0
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + k ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farW_P u' c ws
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      ((farW u' (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (farW u' (c + 1) ws ++ fwW u' (c + 1) c0 [])
      = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwW, mlift_nil]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          (farW u' (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((farW u' (c + 1) ws ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: (farW u' (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
          [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farWk_flat hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towW u' ws (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW u' ws (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towWk_GpT hC m' A o F u' (by omega) hRu hA hA1 ho hAk hko
  rw [← hkk, ← hc] at hD
  have h := GpT_elim0 hD hR'
  rw [← hkk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end GzU
end TRIO
