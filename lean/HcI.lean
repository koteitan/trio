/-
HcI.lean: F のタイの子を「中身と同じ形の塊」と「F の位置のタイ」の並びにした遠い語の土台（HcA の一般化）。

    unitF b r c : none ↦ [(1, r, 0)]、some X ↦ mlift X c (b − c)
    chF b r c us := us.flatMap (unitF b r c)
    FTLu b r c Lds := (1,r,1) :: Lds.flatMap (fun us => (1,r,0) :: (chF b r c us)↑1)
    farWu b r ws := ws.flatMap (fun w => fwH b r (FTLu b r w.2.1 w.1) w.2.1 w.2.2)
    relWsu A0 h g ws := 塊と中身を reliftX (語の段) h g A0 で持ち上げた並び

塊 X は中身と同じく語の段 c で低い（LowC (c + K) X）。F の位置のタイは級の F の位置 r に置き、持ち上げ・再持ち上げで r と一緒に動く。
-/
import HcA

namespace TRIO
namespace HcI

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HcA

/-! ## 子の単位の並び -/

noncomputable def unitF (b r c : ℕ) : Option TrioSeq → TrioSeq
  | none => [((1, r, 0) : ℕ × ℕ × ℕ)]
  | some X => mlift X c (b - c)

noncomputable def chF (b r c : ℕ) (us : List (Option TrioSeq)) : TrioSeq := us.flatMap (unitF b r c)

theorem chF_snoc (b r c : ℕ) (us : List (Option TrioSeq)) (o : Option TrioSeq) :
    chF b r c (us ++ [o]) = chF b r c us ++ unitF b r c o := by
  simp [chF, List.flatMap_append]

def RawUc (k : ℕ) (us : List (Option TrioSeq)) : Prop :=
  ∀ X, some X ∈ us → Fr X ∧ Hd X ∧ LowC k X

theorem RawUc_prefix {k : ℕ} {us : List (Option TrioSeq)} {o : Option TrioSeq}
    (h : RawUc k (us ++ [o])) : RawUc k us := fun X hX => h X (List.mem_append_left _ hX)

theorem RawUc_last {k : ℕ} {us : List (Option TrioSeq)} {o : Option TrioSeq}
    (h : RawUc k (us ++ [o])) : ∀ X, o = some X → Fr X ∧ Hd X ∧ LowC k X :=
  fun X hX => h X (by rw [← hX]; simp)

theorem RawUc_mono {k k' : ℕ} (hk : k ≤ k') {us : List (Option TrioSeq)} (h : RawUc k us) :
    RawUc k' us := fun X hX => ⟨(h X hX).1, (h X hX).2.1, LowC_mono hk (h X hX).2.2⟩

theorem Fr_unitF (b r c : ℕ) {o : Option TrioSeq} (h : ∀ X, o = some X → Fr X) :
    Fr (unitF b r c o) := by
  cases o with
  | none => exact GzF.Fr_single le_rfl _ _
  | some X => exact Fr_mlift (h X rfl) _ _

theorem Hd_unitF (b r c : ℕ) {o : Option TrioSeq} (h : ∀ X, o = some X → Hd X) :
    Hd (unitF b r c o) := by
  cases o with
  | none => exact fun _ => rfl
  | some X => exact Hd_mlift (h X rfl) _ _

theorem Fr_chF (b r c : ℕ) {k : ℕ} : ∀ {us : List (Option TrioSeq)}, RawUc k us → Fr (chF b r c us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; exact Fr_nil
  | append_singleton us o ih =>
      intro hR
      rw [chF_snoc]
      exact Fr_append (ih (RawUc_prefix hR)) (Fr_unitF b r c (fun X hX => (RawUc_last hR X hX).1))

theorem mlift_leaf0 {v r : ℕ} (hvr : v < r) (t : ℕ) :
    mlift [((1, r, 0) : ℕ × ℕ × ℕ)] v t = [((1, r + t, 0) : ℕ × ℕ × ℕ)] := by
  have := mlift_node hvr (V := []) Fr_nil t
  simpa [shiftr01, mlift_nil] using this

theorem mlift_chF_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ us : List (Option TrioSeq), RawUc k us → mlift (chF b r c us) b t = chF (b + t) (r + t) c us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; simp [chF, mlift_nil]
  | append_singleton us o ih =>
      intro hR
      have ho := RawUc_last hR
      rw [chF_snoc, chF_snoc, mlift_app (Fr_chF b r c (RawUc_prefix hR))
        (Hd_unitF b r c (fun X hX => (ho X hX).2.1)), ih (RawUc_prefix hR)]
      congr 1
      cases o with
      | none => exact mlift_leaf0 hbr t
      | some X =>
          show mlift (mlift X c (b - c)) b t = mlift X c (b + t - c)
          have e2 := mlift_mlift X c (b - c) t
          rw [show c + (b - c) = b by omega] at e2
          rw [e2, show b - c + t = b + t - c by omega]

theorem mlift_chF_high {b v r c K : ℕ} (hv : b + K ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ us : List (Option TrioSeq), RawUc (c + K) us → mlift (chF b r c us) v t = chF b (r + t) c us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; simp [chF, mlift_nil]
  | append_singleton us o ih =>
      intro hR
      have ho := RawUc_last hR
      rw [chF_snoc, chF_snoc, mlift_app (Fr_chF b r c (RawUc_prefix hR))
        (Hd_unitF b r c (fun X hX => (ho X hX).2.1)), ih (RawUc_prefix hR)]
      congr 1
      cases o with
      | none => exact mlift_leaf0 hvr t
      | some X =>
          show mlift (mlift X c (b - c)) v t = mlift X c (b - c)
          have hLv : LowC v (mlift X c (b - c)) :=
            LowC_mono (by omega) (LowC_mliftk (ho X rfl).2.2 (b - c))
          have e := mlift_append_low (A := []) hLv t
          simpa [mlift_nil] using e

theorem reliftX_chFA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ us : List (Option TrioSeq), RawUc (c + K) us →
    reliftX b f g (S ++ A0) (chF b (b + liftOff f (S ++ A0) o + 1) c us)
      = chF b (b + liftOff (addF f g) (S ++ A0) o + 1) c (us.map (Option.map (reliftX c f0 g A0))) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; simp [chF, reliftX, slift_nil]
  | append_singleton us o' ih =>
      intro hR
      have ho := RawUc_last hR
      rw [List.map_append, List.map_singleton, chF_snoc, chF_snoc,
        reliftX_app (Fr_chF _ _ _ (RawUc_prefix hR)) (Hd_unitF _ _ _ (fun X hX => (ho X hX).2.1)),
        ih (RawUc_prefix hR)]
      congr 1
      cases o' with
      | none =>
          have := reliftX_one b (liftOff f (S ++ A0) o + 1) 0 f g (S ++ A0)
          rw [reOff_above hA f g 1] at this
          simpa [unitF, ← Nat.add_assoc] using this
      | some X =>
          show reliftX b f g (S ++ A0) (mlift X c (b - c)) = mlift (reliftX c f0 g A0 X) c (b - c)
          have hL' : LowC (b + K) (mlift X c (b - c)) := by
            have := LowC_mliftk (ho X rfl).2.2 (b - c)
            rwa [show c + K + (b - c) = b + K by omega] at this
          rw [reliftX_ins_low hSA hf b g hK hL']
          have em := mlift_reliftX c (b - c) f0 g A0 X
          rw [show c + (b - c) = b by omega] at em
          rw [em]

/-! ## 頭 -/

noncomputable def FTLu (b r c : ℕ) (Lds : List (List (Option TrioSeq))) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) ::
    Lds.flatMap (fun us => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chF b r c us))

theorem FTLu_snoc (b r c : ℕ) (Lds : List (List (Option TrioSeq))) (us : List (Option TrioSeq)) :
    FTLu b r c (Lds ++ [us]) = FTLu b r c Lds ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chF b r c us) := by
  simp [FTLu, List.flatMap_append]

theorem Fr_FTLu (b r c : ℕ) (Lds : List (List (Option TrioSeq))) : Fr (FTLu b r c Lds) := by
  intro x hx
  simp only [FTLu, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨us, -, hx⟩
  · exact Nat.le_refl 1
  · rcases hx with rfl | hx
    · exact Nat.le_refl 1
    · simp only [shiftr01, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      dsimp only; omega

theorem mlift_FTLu_high {b v r c K : ℕ} (hv : b + K ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List (List (Option TrioSeq)), (∀ us ∈ Lds, RawUc (c + K) us) →
      mlift (FTLu b r c Lds) v t = FTLu b (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTLu] using mlift_one hvr t
  | append_singleton Lds us ih =>
      intro hL
      have hus := hL us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTLu_snoc, FTLu_snoc, mlift_app (Fr_FTLu _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hvr (Fr_chF _ _ _ hus),
        mlift_chF_high hv hvr hcb t us hus]

theorem mlift_FTLu_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List (List (Option TrioSeq)), (∀ us ∈ Lds, RawUc k us) →
      mlift (FTLu b r c Lds) b t = FTLu (b + t) (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTLu] using mlift_one hbr t
  | append_singleton Lds us ih =>
      intro hL
      have hus := hL us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTLu_snoc, FTLu_snoc, mlift_app (Fr_FTLu _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hbr (Fr_chF _ _ _ hus),
        mlift_chF_base hbr hcb t us hus]

theorem reliftX_FTLuA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ Lds : List (List (Option TrioSeq)), (∀ us ∈ Lds, RawUc (c + K) us) →
    reliftX b f g (S ++ A0) (FTLu b (b + liftOff f (S ++ A0) o + 1) c Lds)
      = FTLu b (b + liftOff (addF f g) (S ++ A0) o + 1) c
          (Lds.map (fun us => us.map (Option.map (reliftX c f0 g A0)))) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _
      have := reliftX_one b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)
      rw [reOff_above hA f g 1] at this
      simpa [FTLu, ← Nat.add_assoc] using this
  | append_singleton Lds us ih =>
      intro hL
      have hus := hL us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton, FTLu_snoc, FTLu_snoc,
        reliftX_app (Fr_FTLu _ _ _ _) (Hd_node _ _),
        ih (fun L hL'' => hL L (List.mem_append_left _ hL'')),
        show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega,
        reliftX_node (Fr_chF _ _ _ hus) b (liftOff f (S ++ A0) o + 1) 0 f g (S ++ A0), hlow,
        reOff_above hA f g 1,
        show b + (liftOff f (S ++ A0) o + 1) = b + liftOff f (S ++ A0) o + 1 by omega,
        reliftX_chFA hA hSA b hf g hK hcb us hus]
      simp only [← Nat.add_assoc]

/-! ## 語と並び -/

noncomputable def farWu (b r : ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) : TrioSeq :=
  ws.flatMap (fun w => fwH b r (FTLu b r w.2.1 w.1) w.2.1 w.2.2)

theorem farWu_cons (b r : ℕ) (w : List (List (Option TrioSeq)) × ℕ × TrioSeq)
    (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) :
    farWu b r (w :: ws) = fwH b r (FTLu b r w.2.1 w.1) w.2.1 w.2.2 ++ farWu b r ws := by
  simp [farWu]

theorem farWu_snoc (b r : ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq))
    (w : List (List (Option TrioSeq)) × ℕ × TrioSeq) :
    farWu b r (ws ++ [w]) = farWu b r ws ++ fwH b r (FTLu b r w.2.1 w.1) w.2.1 w.2.2 := by
  simp [farWu, List.flatMap_append]

theorem Fr_farWu (b r : ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) :
    Fr (farWu b r ws) := by
  intro y hy
  simp only [farWu, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwH b r _ w.2.1 w.2.2 y hy

theorem Hd_farWu (b r : ℕ) :
    ∀ ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq), Hd (farWu b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farWu_cons]; rfl

theorem farWu_rep (b r : ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq))
    (w : List (List (Option TrioSeq)) × ℕ × TrioSeq) :
    ∀ m, farWu b r (ws ++ List.replicate m w)
      = farWu b r ws ++ (List.range m).flatMap (fun _ => fwH b r (FTLu b r w.2.1 w.1) w.2.1 w.2.2)
  | 0 => by simp [farWu]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farWu_snoc, farWu_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

theorem mlift_fwu_highk {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b)
    {Lds : List (List (Option TrioSeq))} (hL : ∀ us ∈ Lds, RawUc (c + k) us)
    {Y : TrioSeq} (hY : Fr Y) (hLY : LowC (c + k) Y) (t : ℕ) :
    mlift (fwH b r (FTLu b r c Lds) c Y) v t = fwH b (r + t) (FTLu b (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hvr (Fr_append (Fr_FTLu _ _ _ _) (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hLY (b - c))
  rw [mlift_append_low (A := FTLu b r c Lds) hL' t, mlift_FTLu_high hv hvr hcb t Lds hL]

theorem mlift_fwu_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) {Lds : List (List (Option TrioSeq))}
    (hL : ∀ us ∈ Lds, RawUc k us) {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (t : ℕ) :
    mlift (fwH b r (FTLu b r c Lds) c Y) b t
      = fwH (b + t) (r + t) (FTLu (b + t) (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hbr (Fr_append (Fr_FTLu _ _ _ _) (Fr_mlift hY c (b - c))) t,
    mlift_app (Fr_FTLu _ _ _ _) (Hd_mlift hH c (b - c)) b t, mlift_FTLu_base hbr hcb t Lds hL]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_fwuA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b)
    {Lds : List (List (Option TrioSeq))} (hL : ∀ us ∈ Lds, RawUc (c + K) us)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hLY : LowC (c + K) Y) :
    reliftX b f g (S ++ A0)
        (fwH b (b + liftOff f (S ++ A0) o + 1) (FTLu b (b + liftOff f (S ++ A0) o + 1) c Lds) c Y)
      = fwH b (b + liftOff (addF f g) (S ++ A0) o + 1)
          (FTLu b (b + liftOff (addF f g) (S ++ A0) o + 1) c
            (Lds.map (fun us => us.map (Option.map (reliftX c f0 g A0))))) c
          (reliftX c f0 g A0 Y) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hLY (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  have eH := reliftX_FTLuA hA hSA b hf g hK hcb Lds hL
  unfold fwH
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega] at eH ⊢
  rw [reliftX_node (Fr_append (Fr_FTLu _ _ _ _) (Fr_mlift hY c (b - c))) b
      (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0),
    hlow, reOff_above hA f g 1, reliftX_app (Fr_FTLu _ _ _ _) (Hd_mlift hH _ _), eH,
    reliftX_ins_low hSA hf b g hK hL']
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [← em]
  simp only [← Nat.add_assoc]

/-! ## 低さの条件 -/

def RawWku (k b : ℕ) (w : List (List (Option TrioSeq)) × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ us ∈ w.1, RawUc (w.2.1 + k) us) ∧ Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + k) w.2.2

def RawWsku (k b : ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWku k b w

theorem RawWsku_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)}
    (hR : RawWsku k b ws) : RawWsku k b' ws := fun w hw =>
  ⟨le_trans (hR w hw).1 h, (hR w hw).2⟩

theorem RawWsku_tail {k b : ℕ} {w : List (List (Option TrioSeq)) × ℕ × TrioSeq}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsku k b (w :: ws)) :
    RawWsku k b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farWu_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWsku k b ws → mlift (farWu b r ws) v t = farWu b (r + t) ws
  | [] => fun _ => by simp [farWu, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWu_cons, farWu_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWu b r ws),
        mlift_fwu_highk hv hvr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2 t,
        mlift_farWu_highk hv hvr t ws (RawWsku_tail hR)]

theorem mlift_farWu_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWsku k b ws → mlift (farWu b r ws) b t = farWu (b + t) (r + t) ws
  | [] => fun _ => by simp [farWu, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWu_cons, farWu_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWu b r ws),
        mlift_fwu_base hbr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 t,
        mlift_farWu_basek hbr t ws (RawWsku_tail hR)]

/-! ## 持ち上げた子と中身の並び -/

noncomputable def relWsu (A0 : List ℕ) (h g : ℕ → ℕ)
    (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) :
    List (List (List (Option TrioSeq)) × ℕ × TrioSeq) :=
  ws.map (fun w => (w.1.map (fun us => us.map (Option.map (reliftX w.2.1 h g A0))), w.2.1,
    reliftX w.2.1 h g A0 w.2.2))

def RawWAu (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : List (List (Option TrioSeq)) × ℕ × TrioSeq) :
    Prop :=
  w.2.1 ≤ b ∧ (∀ us ∈ w.1, RawUc (w.2.1 + reOff (fun _ => 0) h A0 k0) us) ∧
    Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) w.2.2

def RawWsAu (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ)
    (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWAu A0 k0 h b w

theorem RawWsAu_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsAu A0 k0 h b ws) :
    RawWsAu A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb, (hR w hw).2⟩

theorem RawWsAu_snoc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} {w : List (List (Option TrioSeq)) × ℕ × TrioSeq}
    (h : RawWsAu A0 k0 H b ws) (hw : RawWAu A0 k0 H b w) : RawWsAu A0 k0 H b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem RawUc_relift {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {c : ℕ} {us : List (Option TrioSeq)}
    (hR : RawUc (c + reOff (fun _ => 0) h A0 k0) us) (g : ℕ → ℕ) :
    RawUc (c + reOff (fun _ => 0) (addF h g) A0 k0) (us.map (Option.map (reliftX c h g A0))) := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨o, ho, hoX⟩ := hX
  cases o with
  | none => simp at hoX
  | some X0 =>
      simp at hoX
      subst hoX
      obtain ⟨h1, h2, h3⟩ := hR X0 ho
      refine ⟨Fr_reliftX h1 _ _ _ _, Hd_reliftX h2 _ _ _ _, ?_⟩
      have := LowC_reliftX h3 h g A0
      rwa [reOff_zero_comp] at this

theorem RawLdsu_relift {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {c : ℕ} {Lds : List (List (Option TrioSeq))}
    (hL : ∀ us ∈ Lds, RawUc (c + reOff (fun _ => 0) h A0 k0) us) (g : ℕ → ℕ) :
    ∀ us ∈ Lds.map (fun us => us.map (Option.map (reliftX c h g A0))),
      RawUc (c + reOff (fun _ => 0) (addF h g) A0 k0) us := by
  intro us hus
  simp only [List.mem_map] at hus
  obtain ⟨us0, hus0, rfl⟩ := hus
  exact RawUc_relift (hL us0 hus0) g

theorem RawWsku_relWsu {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsAu A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWsku (reOff (fun _ => 0) (addF h g) A0 k0) b (relWsu A0 h g ws) := by
  intro w hw
  simp only [relWsu, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, RawLdsu_relift h0.2.1 g, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 h g A0
  rwa [reOff_zero_comp] at this

theorem RawWsAu_relWsu {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hR : RawWsAu A0 k0 H b ws) (g : ℕ → ℕ) :
    RawWsAu A0 k0 (addF H g) b (relWsu A0 H g ws) := by
  intro w hw
  simp only [relWsu, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, RawLdsu_relift h0.2.1 g, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 H g A0
  rwa [reOff_zero_comp] at this

theorem relWsu_snoc (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq))
    (Lds : List (List (Option TrioSeq))) (u : ℕ) (X : TrioSeq) :
    relWsu A0 H g (ws ++ [(Lds, u, X)])
      = relWsu A0 H g ws ++
        [(Lds.map (fun us => us.map (Option.map (reliftX u H g A0))), u, reliftX u H g A0 X)] := by
  simp [relWsu]

theorem relWsu_rep (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq))
    (Lds : List (List (Option TrioSeq))) (u : ℕ) (W : TrioSeq) (m : ℕ) :
    relWsu A0 H g (ws ++ List.replicate m (Lds, u, W))
      = relWsu A0 H g ws ++ List.replicate m
          (Lds.map (fun us => us.map (Option.map (reliftX u H g A0))), u, reliftX u H g A0 W) := by
  simp [relWsu, List.map_replicate]

theorem relWsu_comp (A0 : List ℕ) (H g g' : ℕ → ℕ)
    (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) :
    relWsu A0 (addF H g) g' (relWsu A0 H g ws) = relWsu A0 H (addF g g') ws := by
  simp [relWsu, reliftX_comp, Function.comp_def, Option.map_map]

theorem relWsu_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) :
    relWsu A0 H (fun _ => 0) ws = ws := by
  have e : ∀ c, reliftX c H (fun _ => 0) A0 = id := fun c => by funext Z; simp [reliftX_zero]
  simp [relWsu, e]

theorem relWsu_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) : relWsu A0 H g ws = relWsu A0 H' g ws := by
  unfold relWsu
  refine List.map_congr_left (fun w _ => ?_)
  have e : reliftX w.2.1 H g A0 = reliftX w.2.1 H' g A0 :=
    funext (fun X => reliftX_congr w.2.1 hH (fun _ _ => rfl) X)
  rw [e]

theorem reliftX_farWuA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsAu A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farWu b (b + liftOff f (S ++ A0) o + 1) (relWsu A0 h g ws))
      = farWu b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWsu A0 h (addF g g') ws)
  | [] => fun _ => by simp [farWu, relWsu, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsAu A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWsu A0 h g (w :: ws)
          = (w.1.map (fun us => us.map (Option.map (reliftX w.2.1 h g A0))), w.2.1,
              reliftX w.2.1 h g A0 w.2.2) :: relWsu A0 h g ws from rfl,
        show relWsu A0 h (addF g g') (w :: ws)
          = (w.1.map (fun us => us.map (Option.map (reliftX w.2.1 h (addF g g') A0))), w.2.1,
              reliftX w.2.1 h (addF g g') A0 w.2.2) :: relWsu A0 h (addF g g') ws from rfl,
        farWu_cons, farWu_cons, reliftX_app (Fr_fwH _ _ _ _ _) (Hd_farWu _ _ _)]
      have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
        have := LowC_reliftX hw.2.2.2.2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_fwuA hA hSA b hf g' hK hw.1 (RawLdsu_relift hw.2.1 g) (Fr_reliftX hw.2.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.2.1 _ _ _ _) hL]
      simp only [List.map_map, Function.comp_def, Option.map_map, reliftX_comp]
      rw [reliftX_farWuA hA hSA b hf g' hK ws hR']

end HcI
end TRIO
