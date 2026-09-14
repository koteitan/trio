/-
HbV.lean: 最上段の語の F のタイが荷の子を持つ文脈（行 1577〜1582 の形、HbK の写し）。

    wL v (Ds, us) := FTL0 (v+1) Ds ++ unitsC v us      （Ds は F のタイごとの子、荷だけの列。us は荷だけ）
    文脈 CL v L := L = ps.map (wL v)
- rword は farW0 u (u+1) (psL u ps)。中身の族は RA0（HbS）、F のタイの子は GoodL_units（HbU）。
- 中身なしの遠い語の潰れ（GTC_far_CL）: 塔 towW0（HbQ）。
- 荷（GTC_load_CL）: GTC_loadTop。
- 空の F のタイ（ChildT_nil）: GTC_tie。最後の F のタイの子の荷（ChildT_load）: based_Wg_ind と GTC_oper / GTC_orph。
-/
import HaG
import HbU

namespace TRIO
namespace HbV

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HbQ HbR HbS HbT HbU

/-! ## 荷だけの子 -/

theorem unitsC_noTie : ∀ us : List (Option TrioSeq), GzJ.NoTie us → ∀ a b : ℕ,
    unitsC a us = unitsC b us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _ _; rfl
  | append_singleton us o ih =>
      intro hNT a b
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z => rw [unitsC_snoc, unitsC_snoc, ih hNT' a b]; rfl

def LoadSeq (v : ℕ) (D : TrioSeq) : Prop :=
  ∃ us : List (Option TrioSeq), GzJ.NoTie us ∧ RawU v us ∧ D = unitsC v us

theorem LoadSeq_fr {v : ℕ} {D : TrioSeq} (h : LoadSeq v D) : Fr D ∧ LowC v D := by
  obtain ⟨us, hNT, hR, rfl⟩ := h
  have hu := HaT.units_ok v us hNT hR
  exact ⟨hu.1.1, hu.2⟩

theorem LoadSeq_mono {v u : ℕ} (hu : v ≤ u) {D : TrioSeq} (h : LoadSeq v D) : LoadSeq u D := by
  obtain ⟨us, hNT, hR, rfl⟩ := h
  exact ⟨us, hNT, RawU_mono hu hR, unitsC_noTie us hNT v u⟩

theorem LoadSeq_snoc {v : ℕ} {D : TrioSeq} (h : LoadSeq v D) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v))
    (hbZ : based Z) : LoadSeq v (D ++ shiftr01 1 0 Z) := by
  obtain ⟨us, hNT, hR, rfl⟩ := h
  refine ⟨us ++ [some Z], fun hn => ?_, fun Z' hZ' => ?_, by rw [unitsC_snoc]; rfl⟩
  · rcases List.mem_append.mp hn with hn | hn
    · exact hNT hn
    · simp at hn
  · rcases List.mem_append.mp hZ' with hZ' | hZ'
    · exact hR Z' hZ'
    · simp at hZ'; subst hZ'; exact ⟨hZ, hbZ⟩

def DsOK (v : ℕ) (Ds : List TrioSeq) : Prop := ∀ D ∈ Ds, LoadSeq v D

theorem GoodL_Ds {v : ℕ} : ∀ Ds : List TrioSeq, DsOK v Ds → GoodL v Ds := by
  intro Ds
  induction Ds using List.reverseRecOn with
  | nil => intro _; exact GoodL_nil v
  | append_singleton Ds D ih =>
      intro h
      obtain ⟨us, hNT, hR, hD⟩ := h D (List.mem_append_right _ (List.mem_singleton_self _))
      rw [hD]
      exact ChildG_units us hNT hR _ (ih (fun D' h' => h D' (List.mem_append_left _ h')))

/-! ## 語と rword -/

def wL (v : ℕ) (p : List TrioSeq × List (Option TrioSeq)) : TrioSeq := FTL0 (v + 1) p.1 ++ unitsC v p.2

def psL (u : ℕ) (ps : List (List TrioSeq × List (Option TrioSeq))) :
    List (List TrioSeq × ℕ × TrioSeq) :=
  ps.map (fun p => (p.1, u, unitsC u p.2))

theorem wL_nil (u : ℕ) (Ds : List TrioSeq) : wL u (Ds, []) = FTL0 (u + 1) Ds := by
  simp [wL, unitsC]

theorem rcol_wL (u : ℕ) (p : List TrioSeq × List (Option TrioSeq)) :
    rcol 0 u (wL u p) = fwH u (u + 1) (FTL0 (u + 1) p.1) u (unitsC u p.2) := by
  simp [wL, rcol, fwH, mlift_zero]

theorem rword_psL (u : ℕ) : ∀ ps : List (List TrioSeq × List (Option TrioSeq)),
    rword 0 u (ps.map (wL u)) = farW0 u (u + 1) (psL u ps) := by
  intro ps
  induction ps with
  | nil => simp [rword, farW0, psL]
  | cons p ps ih =>
      show rcol 0 u (wL u p) ++ rword 0 u (ps.map (wL u))
        = farW0 u (u + 1) ((p.1, u, unitsC u p.2) :: psL u ps)
      rw [ih, farW0_cons, rcol_wL]

theorem Fr_wL (v : ℕ) (p : List TrioSeq × List (Option TrioSeq)) : ∀ x ∈ wL v p, 1 ≤ x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Fr_FTL0 _ _ x hx
  · exact unitsC_ge v p.2 x hx

/-! ## 中身 -/

def PsL (v : ℕ) (ps : List (List TrioSeq × List (Option TrioSeq))) : Prop :=
  ∀ p ∈ ps, DsOK v p.1 ∧ GzJ.NoTie p.2 ∧ RawU v p.2

theorem DsOK_nil (v : ℕ) : DsOK v [] := fun _ h => by simp at h

theorem DsOK_cons {v : ℕ} {D : TrioSeq} {Ds : List TrioSeq} (hD : LoadSeq v D) (h : DsOK v Ds) :
    DsOK v (D :: Ds) := by
  intro D' hD'
  rcases List.mem_cons.mp hD' with rfl | hD'
  · exact hD
  · exact h D' hD'

theorem LoadSeq_of {v : ℕ} {us : List (Option TrioSeq)} (hNT : GzJ.NoTie us) (hR : RawU v us) :
    LoadSeq v (unitsC v us) := ⟨us, hNT, hR, rfl⟩

theorem PsL_nil (v : ℕ) : PsL v [] := fun _ h => by simp at h

theorem PsL_cons {v : ℕ} {Ds : List TrioSeq} {us : List (Option TrioSeq)}
    {ps : List (List TrioSeq × List (Option TrioSeq))} (hD : DsOK v Ds) (hNT : GzJ.NoTie us)
    (hR : RawU v us) (h : PsL v ps) : PsL v ((Ds, us) :: ps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hD, hNT, hR⟩
  · exact h p hp

theorem PsL_mono {v u : ℕ} (hu : v ≤ u) {ps : List (List TrioSeq × List (Option TrioSeq))}
    (h : PsL v ps) : PsL u ps :=
  fun p hp => ⟨fun D hD => LoadSeq_mono hu ((h p hp).1 D hD), (h p hp).2.1,
    RawU_mono hu (h p hp).2.2⟩

theorem units_RA0 {u : ℕ} {Ds : List TrioSeq} (hG : GoodL u Ds) :
    ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU u us →
      RA0 [] 1 (fun _ => 0) Ds u (unitsC u us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      intro _ _
      exact RA0_nilv (v := u) le_rfl (fun H' b0 c0 hc => hG [] 1 (by simp) le_rfl H' b0 c0 hc) _
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          have hu := HaT.units_ok u us hNT' (RawU_prefix hR)
          rw [unitsC_snoc]
          exact slot_load (RA0_ax (by simp) le_rfl _ Ds) hu.1.1 (ih hNT' (RawU_prefix hR)) Z hZ.1
            hZ.2

theorem FarCA0_ofA {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} (b0 : ℕ) :
    ∀ ws : List (List TrioSeq × ℕ × TrioSeq), (∀ w ∈ ws, okWA0 A0 k0 H w.1 w.2.1 w.2.2) →
      FarCA0 A0 k0 H b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact FarCA0_nil A0 k0 H b0
  | append_singleton ws w ih =>
      intro hok
      have hw := hok w (List.mem_append_right _ (List.mem_singleton_self _))
      exact hw.2.2 b0 ws (ih (fun w' h' => hok w' (List.mem_append_left _ h')))

theorem okW_psL {u : ℕ} {ps : List (List TrioSeq × List (Option TrioSeq))} (h : PsL u ps) :
    ∀ w ∈ psL u ps, okWA0 [] 1 (fun _ => 0) w.1 w.2.1 w.2.2 := by
  intro w hw
  simp only [psL, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact RA0_okWA (units_RA0 (GoodL_Ds p.1 (h p hp).1) p.2 (h p hp).2.1 (h p hp).2.2)

theorem FarCA0_of_PsL {u : ℕ} {ps : List (List TrioSeq × List (Option TrioSeq))} (h : PsL u ps)
    (b0 : ℕ) : FarCA0 [] 1 (fun _ => 0) b0 (psL u ps) :=
  FarCA0_ofA b0 _ (okW_psL h)

theorem RawWsA0_psL {u : ℕ} {ps : List (List TrioSeq × List (Option TrioSeq))} (h : PsL u ps) :
    RawWsA0 [] 1 (fun _ => 0) u (psL u ps) := by
  intro w hw
  have hok := okW_psL h w hw
  simp only [psL, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hu := HaT.units_ok u p.2 (h p hp).2.1 (h p hp).2.2
  exact ⟨le_rfl, fun D hD => LoadSeq_fr ((h p hp).1 D hD), hu.1.1, hok.1, hok.2.1⟩

theorem RawWsk0_psL (k : ℕ) {u : ℕ} {ps : List (List TrioSeq × List (Option TrioSeq))}
    (h : PsL u ps) : RawWsk0 k u (psL u ps) := by
  intro w hw
  simp only [psL, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hu := HaT.units_ok u p.2 (h p hp).2.1 (h p hp).2.2
  exact ⟨le_rfl, fun D hD => LoadSeq_fr ((h p hp).1 D hD), hu.1.1, hu.1.2.1,
    LowC_mono (Nat.le_add_right u k) hu.2⟩

/-! ## 文脈 -/

theorem mlift_wL {v u : ℕ} (hu : v ≤ u) {p : List TrioSeq × List (Option TrioSeq)}
    (hD : DsOK v p.1) (hNT : GzJ.NoTie p.2) (hR : RawU v p.2) :
    mlift (wL v p) v (u - v) = wL u p := by
  have hH := (HaT.units_ok v p.2 hNT hR).1.2.1
  unfold wL
  rw [mlift_app (Fr_FTL0 _ _) hH,
    mlift_FTL0 (show v < v + 1 by omega) (u - v) p.1 (fun D hD' => LoadSeq_fr (hD D hD')),
    mlift_unitsC p.2 hR v le_rfl (u - v), show v + 1 + (u - v) = u + 1 by omega,
    show v + (u - v) = u by omega]

theorem map_CL {v u : ℕ} (hu : v ≤ u) {ps : List (List TrioSeq × List (Option TrioSeq))}
    (h : PsL v ps) : (ps.map (wL v)).map (fun X => mlift X v (u - v)) = ps.map (wL u) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p hp => mlift_wL hu (h p hp).1 (h p hp).2.1 (h p hp).2.2)

def CL (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ ps : List (List TrioSeq × List (Option TrioSeq)), PsL v ps ∧ L = ps.map (wL v)

theorem CL_lift : ∀ (L : List TrioSeq) (v : ℕ), CL v L → ∀ u, v ≤ u →
    CL u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨ps, h, rfl⟩ := hC
  exact ⟨ps, PsL_mono hu h, map_CL hu h⟩

theorem Fr_CL (v : ℕ) (ps : List (List TrioSeq × List (Option TrioSeq))) :
    ∀ X ∈ ps.map (wL v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨p, -, rfl⟩ := hX
  exact Fr_wL v p

theorem topCL_Wg {u : ℕ} {ps : List (List TrioSeq × List (Option TrioSeq))} (h : PsL u ps)
    (hB : BwT u (ps.map (wL u))) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towW0 u (psL u ps) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (ps.map (wL u) ++ [K])) ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CL u ps) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_psL] at this
      simpa [towW0, rword, rcol, shiftr01] using this
  | succ m =>
      have hC := FarCA0_of_PsL h u
      have hG := towW0_GpT hC (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha) le_rfl
        (RawWsA0_psL h) (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, relWs0_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towW0 _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_psL] at this
      simpa [towW0, rword, rcol, shiftr01] using this

/-- ★ 文脈 CL で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CL (v : ℕ) : GTC CL v (fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨ps, h, rfl⟩ := hC
  have hu' : PsL u ps := PsL_mono hu h
  have hBu : BwT u (ps.map (wL u)) := by
    have := BwT_lift hB hu
    rwa [map_CL hu h] at this
  have eL : (ps.map (wL v) ++ [fwTop v []]).map (fun X => mlift X v (u - v))
      = ps.map (wL u) ++ [fwTop u []] := by
    rw [List.map_append, map_CL hu h, List.map_singleton, mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega]
  rw [eL, rword_append, rword_psL, rword_singleton]
  have eR : farW0 u (u + 1) (psL u ps) ++ rcol 0 u (fwTop u [])
      = (farW0 u (u + 1) (psL u ps) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, fwTop, unitsC, shiftr01]
  rw [eR]
  obtain ⟨hP, hcone⟩ := farW0_P u u (psL u ps)
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1),
    farW0_flat (RawWsk0_psL 0 hu') m u (by omega)]
  exact Wg_mono ha (topCL_Wg hu' hBu m)

theorem GTC_load_CL {v : ℕ} {Ds : List TrioSeq} (hDs : DsOK v Ds) {us : List (Option TrioSeq)}
    (hNT : GzJ.NoTie us) (hRus : RawU v us) (hG : GTC CL v (wL v (Ds, us))) :
    ∀ T ∈ Wg (2 * v), based T → GTC CL v (wL v (Ds, us ++ [some T])) := by
  intro T hT hbT
  have e : ∀ T' : TrioSeq, wL v (Ds, us ++ [some T']) = wL v (Ds, us) ++ shiftr01 1 0 T' := by
    intro T'
    show FTL0 (v + 1) Ds ++ unitsC v (us ++ [some T'])
      = FTL0 (v + 1) Ds ++ unitsC v us ++ shiftr01 1 0 T'
    rw [unitsC_snoc, List.append_assoc]; rfl
  rw [e]
  refine GTC_loadTop (Fr_wL v _) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨ps, h, rfl⟩ := hC
  refine ⟨ps ++ [(Ds, us ++ [some T'])], ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · simp at hp; subst hp
      refine ⟨hDs, fun hn => ?_, fun Z hZ => ?_⟩
      · rcases List.mem_append.mp hn with hn | hn
        · exact hNT hn
        · simp at hn
      · rcases List.mem_append.mp hZ with hZ | hZ
        · exact hRus Z hZ
        · simp at hZ; subst hZ; exact ⟨hT', hbT'⟩
  · rw [List.map_append, List.map_singleton, e] <;> rfl

/-! ## F のタイの子 -/

def GoodT (v : ℕ) (Ds : List TrioSeq) : Prop := ∀ u, v ≤ u → GTC CL u (wL u (Ds, []))

def ChildT (v : ℕ) (D : TrioSeq) : Prop := ∀ Ds, DsOK v Ds → GoodT v Ds → GoodT v (Ds ++ [D])

theorem GoodT_nil (v : ℕ) : GoodT v [] := fun u _ => GTC_far_CL u

theorem GTC_wL {v : ℕ} {Ds : List TrioSeq} (hDs : DsOK v Ds) (hG : GoodT v Ds) :
    ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us → GTC CL v (wL v (Ds, us)) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact hG v le_rfl
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_load_CL hDs hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-- ★ 空の F のタイ。 -/
theorem ChildT_nil (v : ℕ) : ChildT v [] := by
  intro Ds hDs hG u hu
  have e : wL u (Ds ++ [[]], []) = wL u (Ds, []) ++ [((1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [wL, FTL0_snoc, unitsC, shiftr01]
  rw [e]
  refine GTC_tie (C := CL) (coneV_top (Fr_wL u _) u) (fun u' hu' Z hZ hbZ => ?_)
    (fun L hC u' hu' => CL_lift L u hC u' hu')
  have hDs' : DsOK u' Ds := fun D hD => LoadSeq_mono (le_trans hu hu') (hDs D hD)
  rw [mlift_wL hu' (p := (Ds, [])) (fun D hD => LoadSeq_mono hu (hDs D hD))
    (by simp [GzJ.NoTie]) (RawU_nil u)]
  have := GTC_load_CL (v := u') (Ds := Ds) (us := []) hDs' (by simp [GzJ.NoTie]) (RawU_nil u')
    (hG u' (le_trans hu hu')) Z hZ hbZ
  rwa [show wL u' (Ds, [] ++ [some Z]) = wL u' (Ds, []) ++ shiftr01 1 0 Z by
    simp [wL, unitsC, unitC]] at this

theorem node_noParent {r : ℕ} {D Z : TrioSeq} {h j : ℕ} (hD : Fr D)
    (hbZ : based (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hjr : j ≤ r)
    (hnp : ¬ hasParent (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 Z.length) :
    ¬ hasParent ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++
      shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])))
      1 ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D).length + Z.length) := by
  have hZl : Z.length < (shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))).length := by
    simp [shiftr01]
  have hBH : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
    intro _
    rw [entry0_shiftr01 (by simp)]
    have : entry (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 0 0 = 0 := hbZ
    omega
  refine noParent_ctx (j := j) hZl (fun k hk hrt => ?_) ?_ ?_
  · have := node_anc_row1 hD hBH (by simp [shiftr01]) hk hZl hrt
    subst this
    show j ≤ r
    exact hjr
  · rw [entry1_shiftr01, entry1_shiftr01, show Z.length = Z.length + 0 from rfl,
      entry_append_right]
    rfl
  · rw [hasParent_shiftr01, hasParent_shiftr01]
    exact hnp

theorem GoodT_rep {v : ℕ} {D : TrioSeq} (hLS : LoadSeq v D) (hD : ChildT v D)
    {Ds : List TrioSeq} (hDs : DsOK v Ds) (hG : GoodT v Ds) :
    ∀ n, DsOK v (Ds ++ List.replicate n D) ∧ GoodT v (Ds ++ List.replicate n D)
  | 0 => by simp only [List.replicate_zero, List.append_nil]; exact ⟨hDs, hG⟩
  | n + 1 => by
      obtain ⟨h1, h2⟩ := GoodT_rep hLS hD hDs hG n
      rw [List.replicate_succ', ← List.append_assoc]
      refine ⟨fun D' hD' => ?_, hD _ h1 h2⟩
      rcases List.mem_append.mp hD' with hD' | hD'
      · exact h1 D' hD'
      · rw [List.mem_singleton] at hD'; rw [hD']; exact hLS

/-- ★ 最上段の最後の F のタイの子に荷を足す規則。 -/
theorem ChildT_load {v : ℕ} : ∀ Z ∈ Wg (2 * v), based Z →
    ∀ D, LoadSeq v D → ChildT v D → ChildT v (D ++ shiftr01 1 0 Z) := by
  refine based_Wg_ind (u := v)
    (Q := fun Z => ∀ D, LoadSeq v D → ChildT v D → ChildT v (D ++ shiftr01 1 0 Z)) ?_ ?_ ?_ ?_
  · intro D _ hD
    simpa [shiftr01] using hD
  · -- flat: 最後の F のタイの複製
    intro Z hZW hbZ hIH D hLS hCT Ds hDs hG u hu
    obtain ⟨D', hD'⟩ : ∃ D', D' = D ++ shiftr01 1 0 Z := ⟨_, rfl⟩
    have hLS' : LoadSeq v D' := by rw [hD']; exact LoadSeq_snoc hLS hZW hbZ
    have hCT' : ChildT v D' := by rw [hD']; exact hIH D hLS hCT
    obtain ⟨M, hM⟩ : ∃ M : TrioSeq, M = ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D' := ⟨_, rfl⟩
    have eK : wL u (Ds ++ [D ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])], [])
        = FTL0 (u + 1) Ds ++ M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
      rw [hM, hD']; simp [wL, FTL0_snoc, unitsC, shiftr01]
    show GTC CL u (wL u (Ds ++ [D ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])], []))
    rw [eK]
    have hFr' := (LoadSeq_fr hLS').1
    have hMne : M ≠ [] := by rw [hM]; simp
    have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
    have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
    have htail : ∀ r', 1 ≤ r' → r' < M.length → 2 ≤ entry M 0 r' := by
      intro r' hr1 hr2
      obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
      have hw' : w < D'.length := by
        rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
      rw [hM, entry_cons, entry0_shiftr01 hw']
      have := getD_row0_ge hFr' hw'
      omega
    have hlast : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
        (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
        ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
      have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
      rw [hidx, srow_append_right]
      have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
      rw [hs]
      refine (hasParent_zero_iff (by simp)).mpr ⟨0, by omega, ?_⟩
      rw [Small.entry_append_left hMpos, entry_append_right]
      exact hhead
    refine GTC_oper ?_ ?_ (fun n hn => ?_)
    · simp only [List.length_append, List.length_singleton]; omega
    · have hidx : (FTL0 (u + 1) Ds ++ M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
          = (FTL0 (u + 1) Ds).length + ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [hidx, List.append_assoc, srow_append_right]
      exact hasParent_append_right_of _ _ hlast
    · have eO := oper_snoc00'' (FTL0 (u + 1) Ds) hMne hhead htail n
      rw [eO, hM, ← FTL0_rep (u + 1) Ds D' n, ← wL_nil]
      exact (GoodT_rep hLS' hCT' hDs hG n).2 u hu
  · -- oper
    intro Z hZW hbZ hlen hp hIH D hLS hCT Ds hDs hG u hu
    have eK : ∀ Y : TrioSeq, wL u (Ds ++ [D ++ shiftr01 1 0 Y], [])
        = (FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++ shiftr01 2 0 Y := by
      intro Y; simp [wL, FTL0_snoc, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
    show GTC CL u (wL u (Ds ++ [D ++ shiftr01 1 0 Z], []))
    rw [eK]
    refine GTC_oper ?_ ?_ (fun n hn => ?_)
    · simp only [List.length_append, shiftr01_length]; omega
    · have hidx : ((FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++
            shiftr01 2 0 Z).length - 1
          = (FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D).length +
            (Z.length - 1) := by
        simp only [List.length_append, shiftr01_length]; omega
      rw [hidx, srow_append_right, srow_shiftr01]
      exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)
    · rw [oper_shift _ Z 2 n hlen hp, ← eK]
      exact (hIH n hn).2 D hLS hCT Ds hDs hG u hu
  · -- orph
    intro Z h j _ hbZ hj1 hjv hnp hz D hLS hCT Ds hDs hG u hu
    have eK : wL u (Ds ++ [D ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])], [])
        = (FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D ++ shiftr01 2 0 Z) ++
          [((h + 2, j, 0) : ℕ × ℕ × ℕ)] := by
      simp [wL, FTL0_snoc, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
    have eZ : ∀ z : TrioSeq, wL u (Ds ++ [D ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z)], [])
        = (FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D ++ shiftr01 2 0 Z) ++
          shiftr01 (h + 2) 0 z := by
      intro z; simp [wL, FTL0_snoc, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
    show GTC CL u (wL u (Ds ++ [D ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])], []))
    rw [eK]
    refine GTC_orph hj1 (by omega) ?_ (fun z hz' hbz => ?_)
    · have hN := node_noParent (r := u + 1) (LoadSeq_fr hLS).1 hbZ (by omega) hnp
      have eU : (((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++
            shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
          = ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (D ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
        simp [shiftr01]
      have eP : (FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D ++
            shiftr01 2 0 Z) ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)]
          = FTL0 (u + 1) Ds ++ ((((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++
            shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))) := by
        simp [shiftr01, Function.comp_def, Nat.add_assoc]
      have hidx : ((FTL0 (u + 1) Ds ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D ++
            shiftr01 2 0 Z) ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)]).length - 1
          = (FTL0 (u + 1) Ds).length +
            ((((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D).length + Z.length) := by
        simp only [List.length_append, List.length_cons, shiftr01_length, List.length_nil]
        omega
      rw [hidx, eP, hasParent_append_gen
        (by simp only [List.length_append, List.length_cons, shiftr01_length,
          List.length_nil]; omega)
        (rsum_of_Hd (Fr_FTL0 _ _) (by rw [eU]; exact Fr_node _ _) (by rw [eU]; exact Hd_node _ _))]
      exact hN
    · rw [← eZ z]
      exact (hz z hz' hbz).2 D hLS hCT Ds hDs hG u hu

theorem ChildT_units {v : ℕ} : ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us →
    ChildT v (unitsC v us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact ChildT_nil v
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          rw [unitsC_snoc]
          exact ChildT_load Z hZ.1 hZ.2 _ ⟨us, hNT', RawU_prefix hR, rfl⟩
            (ih hNT' (RawU_prefix hR))

theorem GoodT_Ds {v : ℕ} : ∀ Ds : List TrioSeq, DsOK v Ds → GoodT v Ds := by
  intro Ds
  induction Ds using List.reverseRecOn with
  | nil => intro _; exact GoodT_nil v
  | append_singleton Ds D ih =>
      intro h
      have h' : DsOK v Ds := fun D' hD' => h D' (List.mem_append_left _ hD')
      obtain ⟨us, hNT, hR, hD⟩ := h D (List.mem_append_right _ (List.mem_singleton_self _))
      rw [hD]
      exact ChildT_units us hNT hR Ds h' (ih h')

/-! ## 並び -/

/-- ★ F のタイが荷の子を持つ語の並びは最上段の全ての段で良い。 -/
theorem BwT_CL (v : ℕ) : ∀ ps : List (List TrioSeq × List (Option TrioSeq)), PsL v ps →
    BwT v (ps.map (wL v)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro _; exact BwT_nil v
  | append_singleton ps p ih =>
      intro h
      have h' : PsL v ps := fun q hq => h q (List.mem_append_left _ hq)
      have hp := h p (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := GTC_wL hp.1 (GoodT_Ds p.1 hp.1) p.2 hp.2.1 hp.2.2
      have := hG _ ⟨ps, h', rfl⟩ (Fr_CL v ps) (ih h')
      rw [List.map_append, List.map_singleton]
      exact this

/-- ★ そのあとに TF の語の並び。 -/
theorem starOK_CL {v : ℕ} (ps : List (List TrioSeq × List (Option TrioSeq))) (h : PsL v ps)
    {Ls : List TrioSeq} (hW : WordsG v Ls) : StarOK v (rword 0 v (ps.map (wL v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CL v ps) (BwT_CL v ps h) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HbV
end TRIO
