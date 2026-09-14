/-
HcX.lean: 一般の接頭辞 PVE の上の字の中身の族 FLC（遠い字を中身に含める）。

    zst e b0 b := 埋め込み e = (A k H g S o f g') の段 b0 から b への階段（mlift, reliftX, mlift, reliftX の合成）
    Zemb e b0 b X := slift X (zst e b0 b)   （= reliftX b f g' (S ++ A) (embW … b (mlift X b0 (b − b0)))）
    FLC A k H b0 V := ∀ W, Fr W → PVE A k H b0 W → PVE A k H b0 (W ++ (1, b0 + liftOff H A k + 1, 1) :: V↑1)

- FLC_iff: FLC V ↔ 全ての埋め込み e と段 b で LC1R (PZ e b0) (S ++ A) o (f+g') b (Zemb e b0 b V)
  （PZ e b0 b X := X が PVE の接頭辞の Zemb）。字の子の階段は F の段より上で定数なので zst と同じ（zst_node_eq）。
- FLC_far（遠い字だけ、HcV.PVE_collapse）、FLC_oper / FLC_orph / FLC_tie / FLC_flat（HcW の LC1R の規則）。
-/
import HcW

namespace TRIO
namespace HcX

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcJ HcK HcL HcM HcN HcO HcU HcV HcW

/-! ## 埋め込みの階段 -/

def zst (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ) (b0 b : ℕ) : ℕ → ℕ :=
  fun m => reStair b f g' (S ++ A)
    (reStair b H g A (m + (if b0 < m then b - b0 else 0)) +
      (if b + liftOff (addF H g) A k < reStair b H g A (m + (if b0 < m then b - b0 else 0))
        then liftOff f (S ++ A) o - liftOff (addF H g) A k else 0))

theorem zst_stair (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ) (b0 b : ℕ) :
    Stair (zst A k H g S o f g' b0 b) := by
  have h1 := stair_comp (stair_step b0 (b - b0)) (reStair_stair b H g A)
  have h2 := stair_comp h1
    (stair_step (b + liftOff (addF H g) A k) (liftOff f (S ++ A) o - liftOff (addF H g) A k))
  have h3 := stair_comp h2 (reStair_stair b f g' (S ++ A))
  exact h3

noncomputable def Zemb (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ)
    (b0 b : ℕ) (X : TrioSeq) : TrioSeq :=
  slift X (zst A k H g S o f g' b0 b)

theorem Zemb_slift (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ)
    (b0 b : ℕ) (X : TrioSeq) :
    reliftX b f g' (S ++ A) (embW A k H g S o f b (mlift X b0 (b - b0)))
      = Zemb A k H g S o f g' b0 b X := by
  unfold Zemb embW reliftX
  rw [mlift_eq_slift X b0 (b - b0), slift_slift (stair_step b0 (b - b0)) (reStair_stair b H g A),
    mlift_eq_slift,
    slift_slift (stair_comp (stair_step b0 (b - b0)) (reStair_stair b H g A)) (stair_step _ _),
    slift_slift (stair_comp (stair_comp (stair_step b0 (b - b0)) (reStair_stair b H g A))
      (stair_step _ _)) (reStair_stair b f g' (S ++ A))]
  rfl

theorem Stair_mono {φ : ℕ → ℕ} (hφ : Stair φ) {m n : ℕ} (h : m ≤ n) : φ m ≤ φ n := by
  have h1 := hφ.step m n h
  have h2 := hφ.ge m
  have h3 := hφ.ge n
  omega

section
variable {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f g' : ℕ → ℕ} {b0 b : ℕ}

theorem zst_low (hb : b0 ≤ b) {m : ℕ} (hm : m ≤ b0) : zst A k H g S o f g' b0 b m = m := by
  unfold zst
  rw [if_neg (by omega), Nat.add_zero, reStair_low b H g A (by omega), if_neg (by omega), Nat.add_zero,
    reStair_low b f g' (S ++ A) (by omega)]

theorem zst_tie (hb : b0 ≤ b) (hA1 : ∀ a ∈ S ++ A, 1 ≤ a) (hk : 1 ≤ liftOff (addF H g) A k) :
    zst A k H g S o f g' b0 b (b0 + 1) = b + 1 := by
  have hA1' : ∀ a ∈ A, 1 ≤ a := fun a ha => hA1 a (List.mem_append_right _ ha)
  unfold zst
  rw [if_pos (by omega), show b0 + 1 + (b - b0) = b + 1 by omega, reStair_tie b H g hA1' le_rfl,
    if_neg (by omega), Nat.add_zero, reStair_tie b f g' hA1 le_rfl]

theorem zst_high (hAk : ∀ a ∈ A, a < k) (hE : EmbU A k H g S o f) (hb : b0 ≤ b) (s : ℕ) :
    zst A k H g S o f g' b0 b (b0 + liftOff H A k + 1 + s)
      = b + liftOff (addF f g') (S ++ A) o + 1 + s := by
  have hA := hE.2.2.1
  have hKL := EmbU_KL hE
  unfold zst
  rw [if_pos (by omega), show b0 + liftOff H A k + 1 + s + (b - b0) = b + (liftOff H A k + (1 + s)) by omega,
    reStair_base, reOff_above hAk H g (1 + s), if_pos (by omega),
    show b + (liftOff (addF H g) A k + (1 + s)) + (liftOff f (S ++ A) o - liftOff (addF H g) A k)
      = b + (liftOff f (S ++ A) o + (1 + s)) by omega,
    reStair_base, reOff_above hA f g' (1 + s)]
  omega

theorem zst_node_eq (hAk : ∀ a ∈ A, a < k) (hE : EmbU A k H g S o f) (hb : b0 ≤ b) :
    (fun m => m + (zst A k H g S o f g' b0 b (min (b0 + liftOff H A k + 1) m) -
      min (b0 + liftOff H A k + 1) m)) = zst A k H g S o f g' b0 b := by
  funext m
  have hst := zst_stair A k H g S o f g' b0 b
  by_cases hm : m ≤ b0 + liftOff H A k + 1
  · rw [min_eq_right hm]; have := hst.ge m; omega
  · rw [min_eq_left (by omega)]
    have h1 := zst_high (g' := g') hAk hE hb 0
    have h2 := zst_high (g' := g') hAk hE hb (m - (b0 + liftOff H A k + 1))
    rw [show b0 + liftOff H A k + 1 + (m - (b0 + liftOff H A k + 1)) = m by omega] at h2
    rw [Nat.add_zero, Nat.add_zero] at h1
    have hge := hst.ge (b0 + liftOff H A k + 1)
    rw [h1] at hge
    rw [h1, h2]; omega

theorem Fr_Zemb {X : TrioSeq} (hX : Fr X) : Fr (Zemb A k H g S o f g' b0 b X) := Fr_slift hX _

theorem Hd_Zemb {X : TrioSeq} (hX : Hd X) : Hd (Zemb A k H g S o f g' b0 b X) := Hd_slift hX _

theorem Zemb_length (X : TrioSeq) : (Zemb A k H g S o f g' b0 b X).length = X.length :=
  slift_length _ _

theorem Zemb_app {X U : TrioSeq} (hX : Fr X) (hU : Hd U) :
    Zemb A k H g S o f g' b0 b (X ++ U) = Zemb A k H g S o f g' b0 b X ++ Zemb A k H g S o f g' b0 b U :=
  slift_app hX hU _

theorem Zemb_oper (U : TrioSeq) (n : ℕ) :
    Zemb A k H g S o f g' b0 b (U⟦n⟧) = (Zemb A k H g S o f g' b0 b U)⟦n⟧ :=
  slift_oper (zst_stair _ _ _ _ _ _ _ _ _ _) n

theorem hasParent_Zemb_last {U : TrioSeq} (hU : 0 < U.length) :
    hasParent (Zemb A k H g S o f g' b0 b U)
        (srow (Zemb A k H g S o f g' b0 b U) ((Zemb A k H g S o f g' b0 b U).length - 1))
        ((Zemb A k H g S o f g' b0 b U).length - 1) ↔
      hasParent U (srow U (U.length - 1)) (U.length - 1) := by
  unfold Zemb
  rw [slift_length, srow_slift (zst_stair _ _ _ _ _ _ _ _ _ _) (by omega),
    hasParent_slift (zst_stair _ _ _ _ _ _ _ _ _ _)]

theorem Zemb_snoc_low (hb : b0 ≤ b) {U : TrioSeq} {h j : ℕ} (hj : j ≤ b0) :
    Zemb A k H g S o f g' b0 b (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
      = Zemb A k H g S o f g' b0 b U ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
  unfold Zemb
  exact slift_snoc_fix _ _ (fun m hm => zst_low hb (le_trans hm hj))

theorem amin_snoc_tie {U : TrioSeq} {x b0 : ℕ} (hc : coneV (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) b0 U.length) :
    amin (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) U.length = b0 + 1 := by
  have ha := coneV_iff_amin.mp hc
  have hle : amin (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) U.length ≤ b0 + 1 := by
    have := amin_le (A := U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) (j := U.length) (y := U.length)
      Relation.ReflTransGen.refl
    rw [show U.length = U.length + 0 from rfl, entry_append_right] at this
    exact this
  omega

theorem Zemb_snoc_tie (hb : b0 ≤ b) (hA1 : ∀ a ∈ S ++ A, 1 ≤ a) (hk : 1 ≤ liftOff (addF H g) A k)
    {U : TrioSeq} {x : ℕ} (hc : coneV (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) b0 U.length) :
    Zemb A k H g S o f g' b0 b (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)])
      = Zemb A k H g S o f g' b0 b U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
  unfold Zemb
  rw [slift_snoc, amin_snoc_tie hc, zst_tie hb hA1 hk]
  dsimp only
  rw [show b0 + 1 + (b + 1 - (b0 + 1)) = b + 1 by omega]

theorem coneV_Zemb_tie (hb : b0 ≤ b) (hA1 : ∀ a ∈ S ++ A, 1 ≤ a) (hk : 1 ≤ liftOff (addF H g) A k)
    {U : TrioSeq} {x : ℕ} (hc : coneV (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) b0 U.length) :
    coneV (Zemb A k H g S o f g' b0 b U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b
      (Zemb A k H g S o f g' b0 b U).length := by
  rw [← Zemb_snoc_tie hb hA1 hk hc, Zemb_length, coneV_iff_amin]
  unfold Zemb
  rw [amin_slift (zst_stair _ _ _ _ _ _ _ _ _ _) (by simp), amin_snoc_tie hc, zst_tie hb hA1 hk]
  omega

theorem Zemb_appendlow (hb : b0 ≤ b) {X B : TrioSeq}
    (hB : ∀ i, i < B.length → ∃ k', Relation.ReflTransGen (nextrel0 B) k' i ∧ entry B 1 k' ≤ b0) :
    Zemb A k H g S o f g' b0 b (X ++ B) = Zemb A k H g S o f g' b0 b X ++ B := by
  unfold Zemb
  exact slift_append_low hB (fun m hm => zst_low hb hm)

theorem Zemb_letter (hAk : ∀ a ∈ A, a < k) (hE : EmbU A k H g S o f) (hb : b0 ≤ b) {W V : TrioSeq}
    (hW : Fr W) (hV : Fr V) :
    Zemb A k H g S o f g' b0 b (W ++ ((1, b0 + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V)
      = Zemb A k H g S o f g' b0 b W ++ ((1, b + liftOff (addF f g') (S ++ A) o + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (Zemb A k H g S o f g' b0 b V) := by
  unfold Zemb
  rw [slift_app hW (Hd_letter _ _), slift_node hV _ _ (zst_stair _ _ _ _ _ _ _ _ _ _),
    zst_node_eq hAk hE hb]
  have h1 := zst_high (g' := g') hAk hE hb 0
  rw [Nat.add_zero, Nat.add_zero] at h1
  rw [h1]

end

theorem Zemb_lift_base (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ)
    {b0 b b'' : ℕ} (hb : b0 ≤ b) (hb'' : b ≤ b'') (X : TrioSeq) :
    mlift (Zemb A k H g S o f g' b0 b X) b (b'' - b) = Zemb A k H g S o f g' b0 b'' X := by
  rw [← Zemb_slift, ← Zemb_slift, mlift_reliftX, show b + (b'' - b) = b'' by omega, embW_lift_base,
    show b + (b'' - b) = b'' by omega]
  have e := mlift_mlift X b0 (b - b0) (b'' - b)
  rw [show b0 + (b - b0) = b by omega, show b - b0 + (b'' - b) = b'' - b0 by omega] at e
  rw [e]

theorem Zemb_rebase (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ)
    {b0 b1 b : ℕ} (hb01 : b0 ≤ b1) (hb1 : b1 ≤ b) (X : TrioSeq) :
    Zemb A k H g S o f g' b1 b (mlift X b0 (b1 - b0)) = Zemb A k H g S o f g' b0 b X := by
  rw [← Zemb_slift, ← Zemb_slift]
  have e := mlift_mlift X b0 (b1 - b0) (b - b1)
  rw [show b0 + (b1 - b0) = b1 by omega, show b1 - b0 + (b - b1) = b - b0 by omega] at e
  rw [e]

/-! ## 接頭辞の述語 -/

def PZ (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ) (b0 : ℕ) :
    ℕ → TrioSeq → Prop :=
  fun b X => ∃ W, Fr W ∧ PVE A k H b0 W ∧ X = Zemb A k H g S o f g' b0 b W

theorem LC1R_mono {P P' : ℕ → TrioSeq → Prop} {A : List ℕ} {o : ℕ} {H : ℕ → ℕ} {b : ℕ} {Y : TrioSeq}
    (hP : ∀ W, P' b W → P b W) (h : LC1R P A o H b Y) : LC1R P' A o H b Y :=
  fun W hW hPW hPV => h W hW (hP W hPW) hPV

theorem PZ_rebase {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f g' : ℕ → ℕ}
    {b0 b1 b : ℕ} (hb01 : b0 ≤ b1) (hb1 : b1 ≤ b) {X : TrioSeq}
    (h : PZ A k H g S o f g' b0 b X) : PZ A k H g S o f g' b1 b X := by
  obtain ⟨W0, hW0, hP0, rfl⟩ := h
  exact ⟨mlift W0 b0 (b1 - b0), Fr_mlift hW0 _ _, PVE_lift hP0 hb01,
    (Zemb_rebase _ _ _ _ _ _ _ _ hb01 hb1 W0).symm⟩

/-! ## 字の中身の族 -/

def FLC (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (b0 : ℕ) (V : TrioSeq) : Prop :=
  ∀ W, Fr W → PVE A k H b0 W →
    PVE A k H b0 (W ++ ((1, b0 + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V)

theorem FLC_iff {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ} {b0 : ℕ} {V : TrioSeq}
    (hV : Fr V) :
    FLC A k H b0 V ↔ ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ), EmbU A k H g S o f →
      ∀ b, b0 ≤ b → LC1R (PZ A k H g S o f g' b0) (S ++ A) o (addF f g') b
        (Zemb A k H g S o f g' b0 b V) := by
  constructor
  · intro h g S o f g' hE b hb W hW hPW hPV
    obtain ⟨W0, hW0, hP0, rfl⟩ := hPW
    have := h W0 hW0 hP0 g S o f g' b hE hb
    rw [Zemb_slift, Zemb_letter hAk hE hb hW0 hV] at this
    exact this
  · intro h W0 hW0 hP0 g S o f g' b hE hb
    rw [Zemb_slift, Zemb_letter hAk hE hb hW0 hV]
    refine h g S o f g' hE b hb _ (Fr_Zemb hW0) ⟨W0, hW0, hP0, rfl⟩ ?_
    have := hP0 g S o f g' b hE hb
    rwa [Zemb_slift] at this

/-- ★ 遠い字だけの中身。 -/
theorem FLC_far {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (H : ℕ → ℕ) (b0 : ℕ) :
    FLC A k H b0 [((1, b0 + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ)] := by
  intro W hW hP
  rw [← col_eq]
  exact PVE_collapse hAk hW hP

theorem FLC_oper {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ} {b0 : ℕ} {V U : TrioSeq}
    (hV : Fr V) (hU : Fr U) (hH : Hd U) (hlen : 2 ≤ U.length)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → FLC A k H b0 (V ++ U⟦m⟧)) : FLC A k H b0 (V ++ U) := by
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  refine (FLC_iff hAk (Fr_append hV hU)).mpr (fun g S o f g' hE b hb => ?_)
  rw [Zemb_app hV hH]
  refine LC1R_oper hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 (Fr_Zemb hV) (Fr_Zemb hU) (Hd_Zemb hH)
    (by rw [Zemb_length]; exact hlen) ((hasParent_Zemb_last (by omega)).mpr hp) (fun m hm => ?_)
  rw [← Zemb_oper, ← Zemb_app hV (Hd_oper hH hUne hm)]
  exact (FLC_iff hAk (Fr_append hV (Fr_oper hU m))).mp (hIH m hm) g S o f g' hE b hb

theorem FLC_orph {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ} {b0 : ℕ} {V U : TrioSeq}
    {h j : ℕ} (hV : Fr V) (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hj1 : 1 ≤ j) (hj : j ≤ b0)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → FLC A k H b0 (V ++ (U ++ shiftr01 h 0 z))) :
    FLC A k H b0 (V ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  refine (FLC_iff hAk (Fr_append hV hU)).mpr (fun g S o f g' hE b hb => ?_)
  rw [Zemb_app hV hH, Zemb_snoc_low hb hj]
  refine LC1R_orph hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 (Fr_Zemb hV)
    (by rw [← Zemb_snoc_low hb hj]; exact Fr_Zemb hU)
    (by rw [← Zemb_snoc_low hb hj]; exact Hd_Zemb hH) hj1 (le_trans hj hb) ?_ (fun z hz' hbz => ?_)
  · intro hh
    apply hnp
    rw [← Zemb_snoc_low hb hj, Zemb_length] at hh
    unfold Zemb at hh
    exact (hasParent_slift (zst_stair _ _ _ _ _ _ _ _ _ _)).mp hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
    have hFrz : Fr (U ++ shiftr01 h 0 z) := by
      have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      refine Fr_append hUc (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have := (FLC_iff hAk (Fr_append hV hFrz)).mp (hz z hz' hbz) g S o f g' hE b hb
    rw [Zemb_app hV hHz, Zemb_appendlow hb (low_of_Wg hzW h (show j ≤ b0 by omega))] at this
    exact this

theorem FLC_tie {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (hk1 : 1 ≤ k) {H : ℕ → ℕ} {b0 : ℕ}
    {V U : TrioSeq} {x : ℕ} (hV : Fr V)
    (hU : Fr (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)]) b0 U.length)
    (hload : ∀ b'', b0 ≤ b'' → ∀ Z ∈ Wg (2 * b''), based Z →
      FLC A k H b'' (mlift (V ++ U) b0 (b'' - b0) ++ shiftr01 x 0 Z)) :
    FLC A k H b0 (V ++ (U ++ [((x, b0 + 1, 0) : ℕ × ℕ × ℕ)])) := by
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  refine (FLC_iff hAk (Fr_append hV hU)).mpr (fun g S o f g' hE b hb => ?_)
  have hKg : 1 ≤ liftOff (addF H g) A k := by unfold liftOff; omega
  have hA1 := hE.2.2.2.1
  rw [Zemb_app hV hH, Zemb_snoc_tie hb hA1 hKg hc]
  refine LC1R_tie hE.2.2.1 hA1 hE.2.2.2.2.1 (Fr_Zemb hV)
    (by rw [← Zemb_snoc_tie hb hA1 hKg hc]; exact Fr_Zemb hU)
    (by rw [← Zemb_snoc_tie hb hA1 hKg hc]; exact Hd_Zemb hH) (coneV_Zemb_tie hb hA1 hKg hc) ?_
    (fun b' hb' Z hZ hbZ => ?_)
  · rintro W ⟨W0, hW0, hP0, rfl⟩ b'' hb''
    exact ⟨W0, hW0, hP0, Zemb_lift_base _ _ _ _ _ _ _ _ hb hb'' W0⟩
  · have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hFrZ : Fr (mlift (V ++ U) b0 (b' - b0) ++ shiftr01 x 0 Z) := by
      refine Fr_append (Fr_mlift (Fr_append hV hUc) _ _) (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have h1 := (FLC_iff hAk hFrZ).mp (hload b' (by omega) Z hZ hbZ) g S o f g' hE b' le_rfl
    rw [Zemb_appendlow le_rfl (low_of_Wg hZ x le_rfl),
      Zemb_rebase _ _ _ _ _ _ _ _ (show b0 ≤ b' by omega) le_rfl] at h1
    rw [← Zemb_app hV hHU, Zemb_lift_base _ _ _ _ _ _ _ _ hb hb']
    exact LC1R_mono (fun W hW => PZ_rebase (show b0 ≤ b' by omega) le_rfl hW) h1

theorem FLC_flat {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ} {b0 : ℕ} {V : TrioSeq}
    (hV : Fr V) (h : FLC A k H b0 V) : FLC A k H b0 (V ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  have hV1 : Fr (V ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := Fr_append hV (GzF.Fr_single le_rfl _ _)
  refine (FLC_iff hAk hV1).mpr (fun g S o f g' hE b hb => ?_)
  rw [Zemb_snoc_low hb (show 0 ≤ b0 by omega)]
  refine LC1R_flat hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 (Fr_Zemb hV)
    ((FLC_iff hAk hV).mp h g S o f g' hE b hb) ?_
  rintro W hW ⟨W0, hW0, hP0, rfl⟩ hPV
  refine ⟨W0 ++ ((1, b0 + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V,
    Fr_append hW0 (Fr_letter _ _), h W0 hW0 hP0, ?_⟩
  rw [Zemb_letter hAk hE hb hW0 hV]

end HcX
end TRIO
