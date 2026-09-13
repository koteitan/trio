/-
GxT.lean: 行 1 の段ごとの節点の子の述語 Gof σ（差し込み口によらない）。

    nestN u [(X₁,ρ₁), …, (X_k,ρ_k)] C = X₁ ++ n₁ :: (X₂ ++ n₂ :: (… X_k ++ n_k :: C))
    FarA G s Q : 差し込み口 Q で、入れ子（段 ≥ s）の一番下に行 1 が u+s の節点を足してよい。
                 塔の的の子の並びが G τ（τ < s）で良いことだけを仮定する（全ての段の底で）。
    Gof σ u L := ∀ Q, SlotAx Q → (∀ s ≤ σ, FarA Gof s Q) → nslot Q σ u L

塔の写しは的の下の隠れた接頭辞を同じ相対位置で使うので、的の文脈だけを一般化すれば閉じる。
-/
import GxR

namespace TRIO
namespace GxT

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN
open GxP
open GxR


theorem Fr_nodez (r z : ℕ) (W : TrioSeq) : Fr (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) := by
  intro x hx
  simp only [List.mem_cons, shiftr01, List.mem_map] at hx
  rcases hx with rfl | ⟨p, -, rfl⟩
  · show 1 ≤ 1; omega
  · dsimp only; omega

theorem Hd_nodez (r z : ℕ) (W : TrioSeq) : Hd (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) :=
  fun _ => rfl

theorem mlift_nodez {u r : ℕ} (hr : u < r) {V : TrioSeq} (hV : Fr V) (z t : ℕ) :
    mlift (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) u t
      = ((1, r + t, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift V u t) := by
  have e1 : ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V
      = shiftr01 1 0 (((0, r, z) : ℕ × ℕ × ℕ) :: V) := by simp [shiftr01]
  have e2 : ((1, r + t, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift V u t)
      = shiftr01 1 0 (((0, r + t, z) : ℕ × ℕ × ℕ) :: mlift V u t) := by simp [shiftr01]
  rw [e1, e2, mlift_shift0, mlift_cons_root hV hr]

/-! ## 入れ子 -/

def nestN (u : ℕ) : List (TrioSeq × ℕ × ℕ) → TrioSeq → TrioSeq
  | [], C => C
  | ((X, ρ, z) :: rest), C => X ++ ((1, u + ρ, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (nestN u rest C)

theorem nestN_app (u : ℕ) : ∀ (rest : List (TrioSeq × ℕ × ℕ)) (C Z : TrioSeq),
    nestN u rest (C ++ Z) = nestN u rest C ++ shiftr01 rest.length 0 Z
  | [], C, Z => by simp [nestN, shiftr01_zero']
  | ((X, ρ, z) :: rest), C, Z => by
      simp only [nestN, List.length_cons]
      rw [nestN_app u rest C Z, shiftr01_append0, shiftr01_add0]
      simp [List.append_assoc]

theorem Fr_nestN (u : ℕ) : ∀ (rest : List (TrioSeq × ℕ × ℕ)) (C : TrioSeq),
    (∀ p ∈ rest, Fr p.1) → Fr C → Fr (nestN u rest C)
  | [], C, _, hC => hC
  | ((X, ρ, z) :: rest), C, hr, hC => by
      simp only [nestN]
      refine Fr_append (hr (X, ρ, z) (by simp)) (Fr_nodez _ _ _)

noncomputable def liftRest (u t : ℕ) (rest : List (TrioSeq × ℕ × ℕ)) : List (TrioSeq × ℕ × ℕ) :=
  rest.map (fun p => (mlift p.1 u t, p.2))

theorem mlift_nestN (u t : ℕ) : ∀ (rest : List (TrioSeq × ℕ × ℕ)) (C : TrioSeq),
    (∀ p ∈ rest, Fr p.1 ∧ 1 ≤ p.2.1) → Fr C →
    mlift (nestN u rest C) u t = nestN (u + t) (liftRest u t rest) (mlift C u t)
  | [], C, _, _ => by simp [nestN, liftRest]
  | ((X, ρ, z) :: rest), C, hr, hC => by
      have hX : Fr X := (hr (X, ρ, z) (by simp)).1
      have hρ : 1 ≤ ρ := (hr (X, ρ, z) (by simp)).2
      have hr' : ∀ p ∈ rest, Fr p.1 ∧ 1 ≤ p.2.1 := fun p hp => hr p (by simp [hp])
      simp only [nestN, liftRest, List.map_cons]
      rw [mlift_app hX (Hd_nodez _ _ _), mlift_nodez (by omega) (Fr_nestN u rest C
        (fun p hp => (hr' p hp).1) hC), mlift_nestN u t rest C hr' hC]
      simp only [liftRest]
      rw [show u + ρ + t = u + t + ρ by omega]

theorem liftRest_length (u t : ℕ) (rest : List (TrioSeq × ℕ × ℕ)) :
    (liftRest u t rest).length = rest.length := by simp [liftRest]

/-! ## 遠い塔の公理と Gof -/

def FarA (G : ℕ → ℕ → TrioSeq → Prop) (s : ℕ) (Q : ℕ → TrioSeq → Prop) : Prop :=
  ∀ u (rest : List (TrioSeq × ℕ × ℕ)) (C : TrioSeq),
    (∀ p ∈ rest, Fr p.1 ∧ s ≤ p.2.1) → Fr C →
    (∀ u', u ≤ u' → Q u' (mlift (nestN u rest C) u (u' - u))) →
    (∀ u', u ≤ u' → ∀ τ L, 1 ≤ τ → τ < s → Fr L → G τ u' L →
      Q u' (mlift (nestN u rest C) u (u' - u) ++
        shiftr01 rest.length 0 (((1, u' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))) →
    Q u (nestN u rest (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)]))

def Gof (σ : ℕ) : ℕ → TrioSeq → Prop :=
  fun u L => ∀ Q : ℕ → TrioSeq → Prop, SlotAx Q →
    (∀ s, 2 ≤ s → ∀ (hs : s ≤ σ),
      FarA (fun τ => if τ < s then Gof τ else fun _ _ => True) s Q) →
    nslot Q σ u L
termination_by σ
decreasing_by omega


theorem FarA_congr {G G' : ℕ → ℕ → TrioSeq → Prop} {s : ℕ} {Q : ℕ → TrioSeq → Prop}
    (h : ∀ τ, τ < s → G τ = G' τ) : FarA G s Q ↔ FarA G' s Q := by
  unfold FarA
  constructor
  · intro H u rest C hr hC h1 h2
    exact H u rest C hr hC h1 (fun u' hu τ L h1τ hτ hL hG => h2 u' hu τ L h1τ hτ hL (by rw [← h τ hτ]; exact hG))
  · intro H u rest C hr hC h1 h2
    exact H u rest C hr hC h1 (fun u' hu τ L h1τ hτ hL hG => h2 u' hu τ L h1τ hτ hL (by rw [h τ hτ]; exact hG))

theorem Gof_eq (σ u : ℕ) (L : TrioSeq) :
    Gof σ u L ↔ ∀ Q : ℕ → TrioSeq → Prop, SlotAx Q →
      (∀ s, 2 ≤ s → s ≤ σ → FarA Gof s Q) → nslot Q σ u L := by
  rw [Gof]
  constructor
  · intro H Q hQ hF
    exact H Q hQ (fun s h2 hs => (FarA_congr (fun τ hτ => by simp [hτ])).mpr (hF s h2 hs))
  · intro H Q hQ hF
    exact H Q hQ (fun s h2 hs => (FarA_congr (fun τ hτ => by simp [hτ])).mp (hF s h2 hs))

def QC (σ : ℕ) (Q : ℕ → TrioSeq → Prop) : Prop :=
  SlotAx Q ∧ ∀ s, 2 ≤ s → s ≤ σ → FarA Gof s Q

theorem Gof_one_iff (u : ℕ) (L : TrioSeq) : Gof 1 u L ↔ GTs u L := by
  rw [Gof_eq]
  constructor
  · intro H ok hA; exact H ok hA (fun s h2 hs => by omega)
  · intro H Q hQ _; exact H Q hQ

theorem Gof_ax {σ : ℕ} (hσ : 1 ≤ σ) : SlotAx (Gof σ) where
  lift := by
    intro u W hW h u' hu
    rw [Gof_eq] at h ⊢
    exact fun Q hQ hF => (nslot_ax hQ hσ).lift u W hW (h Q hQ hF) u' hu
  oper := by
    intro u W U hW hU hH hlen hp hIH
    rw [Gof_eq]
    exact fun Q hQ hF => (nslot_ax hQ hσ).oper u W U hW hU hH hlen hp
      (fun m hm => (Gof_eq σ u _).mp (hIH m hm) Q hQ hF)
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    rw [Gof_eq]
    exact fun Q hQ hF => (nslot_ax hQ hσ).orph u W U h j hW hU hH hj1 hj hnp
      (fun z hz' hbz => (Gof_eq σ u _).mp (hz z hz' hbz) Q hQ hF)
  tie := by
    intro u W U x hW hU hH hc hload
    rw [Gof_eq]
    exact fun Q hQ hF => (nslot_ax hQ hσ).tie u W U x hW hU hH hc
      (fun u' hu Z hZ hbZ => (Gof_eq σ u' _).mp (hload u' hu Z hZ hbZ) Q hQ hF)
  flat := by
    intro u W hW h
    rw [Gof_eq] at h ⊢
    exact fun Q hQ hF => (nslot_ax hQ hσ).flat u W hW (h Q hQ hF)

#print axioms Gof_ax

/-! ## 入れ子の一番下の列の親 -/

theorem nestN_noParent (u s : ℕ) : ∀ (rest : List (TrioSeq × ℕ × ℕ)) (C : TrioSeq),
    (∀ p ∈ rest, Fr p.1 ∧ s ≤ p.2.1) → Fr C →
    ¬ hasParent (nestN u rest (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)])) 1
      ((nestN u rest (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)])).length - 1)
  | [], C, _, hC => by
      rintro ⟨k, hk, -⟩
      simp only [nestN] at hk ⊢
      have hk' : nextrel1 (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)]) k
          ((C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
        unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
      obtain ⟨-, -, hkl, -, hle0, -⟩ := hk'
      have hrec := rtg0_rec hle0.2.2 _ hkl le_rfl
      have hkC : k < C.length := by simp at hkl; omega
      rw [Small.entry_append_left hkC, show (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)]).length - 1
        = C.length + 0 by simp, entry_append_right] at hrec
      have := getD_row0_ge hC hkC
      have e : entry [((1, u + s, 0) : ℕ × ℕ × ℕ)] 0 0 = 1 := rfl
      rw [e] at hrec
      omega
  | ((X, ρ, z) :: rest), C, hr, hC => by
      have hX : Fr X := (hr (X, ρ, z) (by simp)).1
      have hρ : s ≤ ρ := (hr (X, ρ, z) (by simp)).2
      have hr' : ∀ p ∈ rest, Fr p.1 ∧ s ≤ p.2.1 := fun p hp => hr p (by simp [hp])
      have ih := nestN_noParent u s rest C hr' hC
      set N' := nestN u rest (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)]) with hN'
      have hN'ne : N' ≠ [] := by
        rw [hN', nestN_app]; simp [shiftr01]
      have hN'l : 0 < N'.length := List.length_pos_iff.mpr hN'ne
      have eN : nestN u ((X, ρ, z) :: rest) (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)])
          = (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N' := by
        simp only [nestN]; rw [hN']; simp [List.append_assoc]
      rw [eN]
      rintro ⟨k, hk, -⟩
      have hlen : ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N').length - 1
          = (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length + (N'.length - 1) := by
        simp [shiftr01]; omega
      rw [hlen] at hk
      have hk' : nextrel1 ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N') k
          ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length + (N'.length - 1)) := by
        unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
      obtain ⟨-, -, hkl, hk1, hle0, -⟩ := hk'
      have eL1 : entry ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N') 1
          ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length + (N'.length - 1))
          = entry N' 1 (N'.length - 1) := by rw [entry_append_right, entry1_shiftr01]
      rw [eL1] at hk1
      have hlast : entry N' 1 (N'.length - 1) = u + s := by
        have e := nestN_app u rest C [((1, u + s, 0) : ℕ × ℕ × ℕ)]
        rw [← hN'] at e
        rw [show N'.length - 1 = (nestN u rest C).length + 0 by rw [e]; simp [shiftr01]]
        conv_lhs => rw [e]
        rw [entry_append_right]
        simp [shiftr01, entry]
      rw [hlast] at hk1
      rcases Nat.lt_or_ge k (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length with hlt | hge
      · have hkX : k ≤ X.length := by simp at hlt; omega
        rcases Nat.lt_or_ge k X.length with hlt' | hge'
        · have hrec := rtg0_rec hle0.2.2 X.length hlt' (by simp; omega)
          have e1 : entry ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N') 0 k
              = entry X 0 k := by
            rw [Small.entry_append_left (show k < (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length
              by simp; omega), Small.entry_append_left hlt']
          have e2 : entry ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N') 0 X.length
              = 1 := by
            rw [Small.entry_append_left (show X.length < (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length
              by simp), show X.length = X.length + 0 from rfl, entry_append_right]; rfl
          rw [e1, e2] at hrec
          have := getD_row0_ge hX hlt'
          omega
        · have hkeq : k = X.length := by omega
          subst hkeq
          have e3 : entry ((X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 N') 1 X.length
              = u + ρ := by
            rw [Small.entry_append_left (show X.length < (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length
              by simp), show X.length = X.length + 0 from rfl, entry_append_right]; rfl
          rw [e3] at hk1
          omega
      · obtain ⟨q, rfl⟩ : ∃ q, k = (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length + q :=
          ⟨k - (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length, by omega⟩
        have h1 := rtg0_append_unlift (Nat.le_add_right _ _) hle0.2.2 (N'.length - 1) rfl
        rw [show (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length + q -
          (X ++ [((1, u + ρ, z) : ℕ × ℕ × ℕ)]).length = q by omega] at h1
        have h2 := rtg0_shiftr01.mp h1
        rw [entry_append_right, entry1_shiftr01] at hk1
        exact ih (H12Export.hasParent1_of_le0_witness (by omega) h2 (by rw [hlast]; exact hk1))

#print axioms nestN_noParent

theorem liftRest_comp (u t t' : ℕ) (rest : List (TrioSeq × ℕ × ℕ)) :
    liftRest (u + t) t' (liftRest u t rest) = liftRest u (t + t') rest := by
  simp only [liftRest, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  rw [mlift_mlift]


theorem mlift_snoc_node {C : TrioSeq} (hC : Fr C) {u s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    mlift (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)]) u t
      = mlift C u t ++ [((1, u + t + s, 0) : ℕ × ℕ × ℕ)] := by
  rw [mlift_snoc_cone C _ (coneV_top' hC (show u < u + s by omega)) t]
  show _ ++ [((1, u + s + t, 0) : ℕ × ℕ × ℕ)] = _
  rw [show u + s + t = u + t + s by omega]

theorem liftRest_cond {u t s : ℕ} {rest : List (TrioSeq × ℕ × ℕ)}
    (hr : ∀ p ∈ rest, Fr p.1 ∧ s ≤ p.2.1) : ∀ p ∈ liftRest u t rest, Fr p.1 ∧ s ≤ p.2.1 := by
  intro p hp
  simp only [liftRest, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨Fr_mlift (hr q hq).1 u t, (hr q hq).2⟩

theorem Fr_single_node (r : ℕ) : Fr [((1, r, 0) : ℕ × ℕ × ℕ)] := by
  intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega

/-- 入れ子を段 u から u'' へ持ち上げたもの（2 段階で持ち上げても同じ）。 -/
theorem mlift_nestN_twice {u u' u'' : ℕ} (hu : u ≤ u') (hu' : u' ≤ u'')
    {rest : List (TrioSeq × ℕ × ℕ)} {C : TrioSeq} (hr : ∀ p ∈ rest, Fr p.1 ∧ 1 ≤ p.2.1) (hC : Fr C) :
    mlift (nestN u' (liftRest u (u' - u) rest) (mlift C u (u' - u))) u' (u'' - u')
      = mlift (nestN u rest C) u (u'' - u) := by
  have hrl : ∀ p ∈ liftRest u (u' - u) rest, Fr p.1 ∧ 1 ≤ p.2.1 := liftRest_cond hr
  rw [mlift_nestN u' (u'' - u') _ _ hrl (Fr_mlift hC _ _), mlift_nestN u (u'' - u) rest C hr hC]
  have e := liftRest_comp u (u' - u) (u'' - u') rest
  rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e
  have e2 := mlift_mlift C u (u' - u) (u'' - u')
  rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e2
  rw [e, e2, show u' + (u'' - u') = u + (u'' - u) by omega]

theorem FarA_Gof_ge {ρ s : ℕ} (hρ1 : 1 ≤ ρ) (hs2 : 2 ≤ s) (hsρ : s ≤ ρ) :
    FarA Gof s (Gof ρ) := by
  intro u rest C hr hC h1 h2
  have hr1 : ∀ p ∈ rest, Fr p.1 ∧ 1 ≤ p.2.1 :=
    fun p hp => ⟨(hr p hp).1, by have := (hr p hp).2; omega⟩
  rw [Gof_eq]
  intro Q hQ hF u' hu X hX hQX
  have eT : mlift (nestN u rest (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
      = nestN u' (liftRest u (u' - u) rest)
          (mlift C u (u' - u) ++ [((1, u' + s, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_nestN u (u' - u) rest _ hr1 (Fr_append hC (Fr_single_node _)),
      mlift_snoc_node hC (by omega), show u + (u' - u) = u' by omega]
  rw [eT]
  have hrl : ∀ p ∈ (X, ρ, 0) :: liftRest u (u' - u) rest, Fr p.1 ∧ s ≤ p.2.1 := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hX, hsρ⟩
    · exact liftRest_cond hr p hp
  have hrl1 : ∀ p ∈ (X, ρ, 0) :: liftRest u (u' - u) rest, Fr p.1 ∧ 1 ≤ p.2.1 :=
    fun p hp => ⟨(hrl p hp).1, by have := (hrl p hp).2; omega⟩
  refine hF s hs2 hsρ u' ((X, ρ, 0) :: liftRest u (u' - u) rest) (mlift C u (u' - u)) hrl
    (Fr_mlift hC _ _) (fun u'' hu'' => ?_) (fun u'' hu'' τ L h1τ hτ hL hGL => ?_)
  · have hh := (Gof_eq ρ u'' _).mp (h1 u'' (le_trans hu hu'')) Q hQ hF u'' le_rfl
      (mlift X u' (u'' - u')) (Fr_mlift hX _ _) (hQ.lift u' X hX hQX u'' hu'')
    rw [Nat.sub_self, mlift_zero] at hh
    rw [mlift_nestN u' (u'' - u') _ _ hrl1 (Fr_mlift hC _ _)]
    simp only [nestN, liftRest, List.map_cons]
    have e := mlift_nestN_twice hu hu'' hr1 hC
    rw [mlift_nestN u' (u'' - u') _ _ (liftRest_cond hr1) (Fr_mlift hC _ _)] at e
    simp only [liftRest] at e
    rw [e, show u' + (u'' - u') = u'' by omega]
    exact hh
  · have hh := (Gof_eq ρ u'' _).mp (h2 u'' (le_trans hu hu'') τ L h1τ hτ hL hGL) Q hQ hF u''
      le_rfl (mlift X u' (u'' - u')) (Fr_mlift hX _ _) (hQ.lift u' X hX hQX u'' hu'')
    rw [Nat.sub_self, mlift_zero, shiftr01_append0, shiftr01_add0] at hh
    rw [mlift_nestN u' (u'' - u') _ _ hrl1 (Fr_mlift hC _ _)]
    simp only [nestN, liftRest, List.map_cons, List.length_cons, List.length_map]
    have e := mlift_nestN_twice hu hu'' hr1 hC
    rw [mlift_nestN u' (u'' - u') _ _ (liftRest_cond hr1) (Fr_mlift hC _ _)] at e
    simp only [liftRest] at e
    rw [e, show u' + (u'' - u') = u'' by omega]
    simpa [List.append_assoc] using hh

#print axioms FarA_Gof_ge

theorem FarA_Gof_lt {ρ s : ℕ} (hρ1 : 1 ≤ ρ) (hs2 : 2 ≤ s) (hρs : ρ < s) :
    FarA Gof s (Gof ρ) := by
  intro u rest C hr hC h1 h2
  have hr1 : ∀ p ∈ rest, Fr p.1 ∧ 1 ≤ p.2.1 :=
    fun p hp => ⟨(hr p hp).1, by have := (hr p hp).2; omega⟩
  rw [Gof_eq]
  intro Q hQ hF u' hu X hX hQX
  have eT : mlift (nestN u rest (C ++ [((1, u + s, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
      = nestN u' (liftRest u (u' - u) rest)
          (mlift C u (u' - u) ++ [((1, u' + s, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_nestN u (u' - u) rest _ hr1 (Fr_append hC (Fr_single_node _)),
      mlift_snoc_node hC (by omega), show u + (u' - u) = u' by omega]
  rw [eT]
  have hrl : ∀ p ∈ liftRest u (u' - u) rest, Fr p.1 ∧ s ≤ p.2.1 := liftRest_cond hr
  have hrl1 : ∀ p ∈ liftRest u (u' - u) rest, Fr p.1 ∧ 1 ≤ p.2.1 :=
    fun p hp => ⟨(hrl p hp).1, by have := (hrl p hp).2; omega⟩
  have hCl : Fr (mlift C u (u' - u)) := Fr_mlift hC _ _
  have h1' : Gof ρ u' (nestN u' (liftRest u (u' - u) rest) (mlift C u (u' - u))) := by
    have := h1 u' hu
    rwa [mlift_nestN u (u' - u) rest C hr1 hC, show u + (u' - u) = u' by omega] at this
  have h2' : ∀ L, Fr L → Gof ρ u' L →
      Gof ρ u' (nestN u' (liftRest u (u' - u) rest) (mlift C u (u' - u)) ++
        shiftr01 (liftRest u (u' - u) rest).length 0
          (((1, u' + ρ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
    intro L hL hGL
    have := h2 u' hu ρ L hρ1 hρs hL hGL
    rwa [mlift_nestN u (u' - u) rest C hr1 hC, show u + (u' - u) = u' by omega,
      ← liftRest_length u (u' - u) rest] at this
  obtain ⟨restl, hrestl⟩ : ∃ r, r = liftRest u (u' - u) rest := ⟨_, rfl⟩
  obtain ⟨Cl, hCleq⟩ : ∃ c, c = mlift C u (u' - u) := ⟨_, rfl⟩
  rw [← hrestl] at hrl hrl1 h1' h2' ⊢
  rw [← hCleq] at hCl h1' h2' ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = nestN u' restl (Cl ++ [((1, u' + s, 0) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  rw [← hR]
  have hRapp : R = nestN u' restl Cl ++ [((1 + restl.length, u' + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [hR, nestN_app, shift_col]
  have hRFr : Fr R := by
    rw [hR]; exact Fr_nestN u' restl _ (fun p hp => (hrl p hp).1) (Fr_append hCl (Fr_single_node _))
  have hRok : argOK R := fun p hp => by have := hRFr p hp; omega
  have hRne : R ≠ [] := by rw [hRapp]; simp
  have hRlen : R.length - 1 = (nestN u' restl Cl).length + 0 := by rw [hRapp]; simp
  have eL : ∀ r, entry R r (R.length - 1)
      = entry [((1 + restl.length, u' + s, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [hRlen]; conv_lhs => rw [hRapp]
    rw [entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 + restl.length := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = u' + s := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rw [hR]; exact nestN_noParent u' s restl Cl hrl hCl
  have hd : domT R (2 * (u' + s) - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1
      omega
    · rw [entry_cons_last hRne 1, e1]; show u' + ρ < u' + s; omega
  have hdl : R.dropLast = nestN u' restl Cl := by rw [hRapp, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow (u' + ρ) 0 R (j + 1))
      = ((1, u' + ρ, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (nestN u' restl (Cl ++ shiftr01 1 0 (tow (u' + ρ) 0 R j))) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl, nestN_app, shiftr01_add0]
    simp [shiftr01]
  have hFrj : ∀ j, Fr (nestN u' restl (Cl ++ shiftr01 1 0 (tow (u' + ρ) 0 R j))) :=
    fun j => Fr_nestN u' restl _ (fun p hp => (hrl p hp).1) (Fr_append hCl (Fr_shift1 _))
  have hG : ∀ j, Gof ρ u' (nestN u' restl (Cl ++ shiftr01 1 0 (tow (u' + ρ) 0 R j))) := by
    intro j
    induction j with
    | zero =>
        simp only [tow, shiftr01, List.map_nil, List.append_nil]
        exact h1'
    | succ j ih =>
        rw [nestN_app, htow]
        exact h2' _ (hFrj j) ih
  have eV : ((1, u' + ρ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R
      = shiftr01 1 0 (((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R) := by simp [shiftr01]
  rw [eV]
  have hlen2 : 2 ≤ (((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R) ((((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine hQ.oper u' X _ hX (Fr_shift1 _) (fun _ => ?_) (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m hm => ?_)
  · rw [entry0_shiftr01 (by simp)]; rfl
  · have eO := oper_shift [] (((0, u' + ρ, 0) : ℕ × ℕ × ℕ) :: R) 1 m hlen2 hpM'
    simp only [List.nil_append] at eO
    rw [eO, oper_cons_tower1 hRok hRne hd hsr hpM]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [htow]
    have := (Gof_eq ρ u' _).mp (hG j) Q hQ hF u' le_rfl X hX hQX
    rwa [Nat.sub_self, mlift_zero] at this

#print axioms FarA_Gof_lt

theorem FarA_Gof {ρ s : ℕ} (hρ1 : 1 ≤ ρ) (hs2 : 2 ≤ s) : FarA Gof s (Gof ρ) := by
  by_cases hρs : ρ < s
  · exact FarA_Gof_lt hρ1 hs2 hρs
  · exact FarA_Gof_ge hρ1 hs2 (by omega)

theorem Gof_nil {σ : ℕ} (hσ : 2 ≤ σ) (u : ℕ) : Gof σ u [] := by
  rw [Gof_eq]
  intro Q hQ hF u' _ X hX hQX
  have h := hF σ hσ le_rfl u' [] X (by simp) hX
    (fun u'' hu'' => by simpa [nestN] using hQ.lift u' X hX hQX u'' hu'')
    (fun u'' hu'' τ L h1τ hτ hL hGL => by
      have hh := (Gof_eq τ u'' L).mp hGL Q hQ (fun s' h2 hs' => hF s' h2 (by omega)) u'' le_rfl
        (mlift X u' (u'' - u')) (Fr_mlift hX _ _) (hQ.lift u' X hX hQX u'' hu'')
      simpa [nestN, shiftr01_zero', Nat.sub_self, mlift_zero] using hh)
  simpa [nestN, mlift_nil, shiftr01] using h

theorem Gof_node {ρ σ u : ℕ} {C E : TrioSeq} (hρ : 1 ≤ ρ) (hσ : 1 ≤ σ) (hC : Fr C)
    (hGC : Gof ρ u C) (hGE : Gof σ u E) :
    Gof ρ u (C ++ ((1, u + σ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  have := (Gof_eq σ u E).mp hGE (Gof ρ) (Gof_ax hρ) (fun s h2 _ => FarA_Gof hρ h2) u le_rfl C hC hGC
  rwa [Nat.sub_self, mlift_zero] at this

#print axioms Gof_node

/-! ## 森の条件つきの組み立て -/

def GF (σ u : ℕ) (L : TrioSeq) : Prop := Gof σ u L ∧ Fr L

theorem GF_nil1 (u : ℕ) : GF 1 u [] := ⟨(Gof_one_iff u []).mpr (GTs_nil u), Fr_nil⟩

theorem GF_nil {σ : ℕ} (hσ : 2 ≤ σ) (u : ℕ) : GF σ u [] := ⟨Gof_nil hσ u, Fr_nil⟩

theorem GF_load {σ u : ℕ} (hσ : 1 ≤ σ) {L Z : TrioSeq} (h : GF σ u L) (hZ : Z ∈ Wg (2 * u))
    (hb : based Z) : GF σ u (L ++ shiftr01 1 0 Z) :=
  ⟨slot_load (Gof_ax hσ) h.2 h.1 Z hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem GF_node {ρ σ u : ℕ} (hρ : 1 ≤ ρ) (hσ : 1 ≤ σ) {C E : TrioSeq} (h : GF ρ u C)
    (hE : GF σ u E) : GF ρ u (C ++ ((1, u + σ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) :=
  ⟨Gof_node hρ hσ h.2 h.1 hE.1, Fr_append h.2 (Fr_node _ _)⟩

theorem TF_tieG {u : ℕ} {K D : TrioSeq} (h : TF u K) (hD : GF 1 u D) :
    TF u (K ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) :=
  TF_tie h ⟨(Gof_one_iff u D).mp hD.1, hD.2⟩

/-- 行 913 の試し。 -/
theorem R913_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0)
    (WordsG_consT (TF_tieG (TF_nil 0) (GF_node (ρ := 1) (σ := 2) le_rfl (by omega) (GF_nil1 0)
      (GF_node (ρ := 2) (σ := 3) (by omega) (by omega) (GF_nil le_rfl 0) (GF_nil (by omega) 0))))
      (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R913_mem

end GxT
end TRIO
