/-
HcS.lean: 最上段の語の F のタイの子に F の位置のタイを許す文脈（行 1615〜1646 の形、HbV の一般化）。

    wLU v (Uss, us) := FTL0 (v+1) (Uss.map (unitsC v)) ++ unitsC v us
      （Uss は F のタイごとの子の単位の並び: none = F の位置のタイ (1, v+1, 0)、some Z = 荷。us は荷だけ）
    文脈 CLU v L := L = ps.map (wLU v)
- rword は farWu u (u+1) (psLU u ps)（HcI の単位の語）。塔は HcP の族（GoodLow_none / okLow_load）と HcJ.towWu_GpT。
- F のタイの子: 空（ChildTU_nil）、荷（ChildTU_load、based_Wg_ind）、F の位置のタイ（ChildTU_none、GTC_tie で x = 2。
  展開の荷は同じ F のタイの子の荷になり、一つ上の段の ChildTU で出る）。単位の並びの帰納で ChildTU_all。
-/
import HbX
import HcR

namespace TRIO
namespace HcS

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HbQ HbR HbS HbT HbU HbV HbX HcI HcJ HcM HcN HcP

/-! ## 語と文脈 -/

def wLU (v : ℕ) (p : List (List (Option TrioSeq)) × List (Option TrioSeq)) : TrioSeq :=
  FTL0 (v + 1) (p.1.map (unitsC v)) ++ unitsC v p.2

def PsLU (v : ℕ) (ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) : Prop :=
  ∀ p ∈ ps, (∀ us ∈ p.1, RawU v us) ∧ GzJ.NoTie p.2 ∧ RawU v p.2

def CLU (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq)), PsLU v ps ∧ L = ps.map (wLU v)

noncomputable def psLU (u : ℕ) (ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) :
    List (List (List (Option TrioSeq)) × ℕ × TrioSeq) :=
  ps.map (fun p => (p.1.map (fun us => us.map (Option.map (shiftr01 1 0))), u, unitsC u p.2))

theorem PsLU_nil (v : ℕ) : PsLU v [] := fun _ h => by simp at h

theorem PsLU_cons {v : ℕ} {Uss : List (List (Option TrioSeq))} {us : List (Option TrioSeq)}
    {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))} (hU : ∀ us' ∈ Uss, RawU v us')
    (hNT : GzJ.NoTie us) (hR : RawU v us) (h : PsLU v ps) : PsLU v ((Uss, us) :: ps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hU, hNT, hR⟩
  · exact h p hp

theorem RawUs_nil (v : ℕ) : ∀ us ∈ ([] : List (List (Option TrioSeq))), RawU v us :=
  fun _ h => by simp at h

theorem RawUs_cons {v : ℕ} {us : List (Option TrioSeq)} {Uss : List (List (Option TrioSeq))}
    (h1 : RawU v us) (h2 : ∀ us' ∈ Uss, RawU v us') : ∀ us' ∈ us :: Uss, RawU v us' := by
  intro us' h
  rcases List.mem_cons.mp h with rfl | h
  · exact h1
  · exact h2 us' h

theorem PsLU_mono {v u : ℕ} (hu : v ≤ u) {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU v ps) : PsLU u ps :=
  fun p hp => ⟨fun us hus => RawU_mono hu ((h p hp).1 us hus), (h p hp).2.1, RawU_mono hu (h p hp).2.2⟩

theorem RawU_snoc_some {v : ℕ} {us : List (Option TrioSeq)} (h : RawU v us) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * v)) (hb : based Z) : RawU v (us ++ [some Z]) := by
  intro Z' hZ'
  rcases List.mem_append.mp hZ' with hZ' | hZ'
  · exact h Z' hZ'
  · simp at hZ'; subst hZ'; exact ⟨hZ, hb⟩

theorem Fr_wLU (v : ℕ) (p : List (List (Option TrioSeq)) × List (Option TrioSeq)) :
    ∀ x ∈ wLU v p, 1 ≤ x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Fr_FTL0 _ _ x hx
  · exact unitsC_ge v p.2 x hx

theorem Fr_CLU (v : ℕ) (ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) :
    ∀ X ∈ ps.map (wLU v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨p, -, rfl⟩ := hX
  exact Fr_wLU v p

theorem mlift_FTL0U {v : ℕ} (t : ℕ) : ∀ Uss : List (List (Option TrioSeq)), (∀ us ∈ Uss, RawU v us) →
    mlift (FTL0 (v + 1) (Uss.map (unitsC v))) v t = FTL0 (v + 1 + t) (Uss.map (unitsC (v + t))) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; simpa [FTL0] using mlift_one (show v < v + 1 by omega) t
  | append_singleton Uss us ih =>
      intro hR
      have hus := hR us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton, List.map_append, List.map_singleton, FTL0_snoc, FTL0_snoc,
        mlift_app (Fr_FTL0 _ _) (Hd_node _ _), ih (fun L hL' => hR L (List.mem_append_left _ hL')),
        mlift_node (show v < v + 1 by omega) (unitsC_ge v us), mlift_unitsC us hus v le_rfl t]

theorem mlift_wLU {v u : ℕ} (hu : v ≤ u) {p : List (List (Option TrioSeq)) × List (Option TrioSeq)}
    (hU : ∀ us ∈ p.1, RawU v us) (hNT : GzJ.NoTie p.2) (hR : RawU v p.2) :
    mlift (wLU v p) v (u - v) = wLU u p := by
  have hH := (HaT.units_ok v p.2 hNT hR).1.2.1
  unfold wLU
  rw [mlift_app (Fr_FTL0 _ _) hH, mlift_FTL0U (u - v) p.1 hU, mlift_unitsC p.2 hR v le_rfl (u - v),
    show v + 1 + (u - v) = u + 1 by omega, show v + (u - v) = u by omega]

theorem map_CLU {v u : ℕ} (hu : v ≤ u) {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU v ps) : (ps.map (wLU v)).map (fun X => mlift X v (u - v)) = ps.map (wLU u) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p hp => mlift_wLU hu (h p hp).1 (h p hp).2.1 (h p hp).2.2)

theorem CLU_lift : ∀ (L : List TrioSeq) (v : ℕ), CLU v L → ∀ u, v ≤ u →
    CLU u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨ps, h, rfl⟩ := hC
  exact ⟨ps, PsLU_mono hu h, map_CLU hu h⟩

/-! ## 単位の語への変換 -/

theorem chF_top (u : ℕ) : ∀ us : List (Option TrioSeq),
    chF u (u + 1) u (us.map (Option.map (shiftr01 1 0))) = unitsC u us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => simp [chF, unitsC]
  | append_singleton us o ih =>
      rw [List.map_append, List.map_singleton, chF_snoc, unitsC_snoc, ih]
      cases o with
      | none => rfl
      | some Z =>
          show unitsC u us ++ mlift (shiftr01 1 0 Z) u (u - u) = unitsC u us ++ shiftr01 1 0 Z
          rw [Nat.sub_self, mlift_zero]

theorem FTLu_top (u : ℕ) (Uss : List (List (Option TrioSeq))) :
    FTLu u (u + 1) u (Uss.map (fun us => us.map (Option.map (shiftr01 1 0))))
      = FTL0 (u + 1) (Uss.map (unitsC u)) := by
  induction Uss using List.reverseRecOn with
  | nil => simp [FTLu, FTL0]
  | append_singleton Uss us ih =>
      rw [List.map_append, List.map_singleton, List.map_append, List.map_singleton, FTLu_snoc,
        FTL0_snoc, ih, chF_top]

theorem rcol_wLU (u : ℕ) (p : List (List (Option TrioSeq)) × List (Option TrioSeq)) :
    rcol 0 u (wLU u p) = fwH u (u + 1) (FTLu u (u + 1) u
      (p.1.map (fun us => us.map (Option.map (shiftr01 1 0))))) u (unitsC u p.2) := by
  rw [FTLu_top]
  simp [wLU, rcol, fwH, mlift_zero]

theorem rword_psLU (u : ℕ) : ∀ ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq)),
    rword 0 u (ps.map (wLU u)) = farWu u (u + 1) (psLU u ps) := by
  intro ps
  induction ps with
  | nil => simp [rword, farWu, psLU]
  | cons p ps ih =>
      show rcol 0 u (wLU u p) ++ rword 0 u (ps.map (wLU u))
        = farWu u (u + 1) ((p.1.map (fun us => us.map (Option.map (shiftr01 1 0))), u, unitsC u p.2)
          :: psLU u ps)
      rw [ih, farWu_cons, rcol_wLU]

theorem Hd_shift1_based {Z : TrioSeq} (hb : based Z) : Hd (shiftr01 1 0 Z) := by
  intro hne
  have hZne : Z ≠ [] := by intro h; apply hne; simp [h, shiftr01]
  rw [entry0_shiftr01 (List.length_pos_iff.mpr hZne)]
  have : entry Z 0 0 = 0 := hb
  omega

theorem GoodLow_top {u : ℕ} : ∀ us : List (Option TrioSeq), RawU u us →
    GoodLow u (us.map (Option.map (shiftr01 1 0))) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; exact GoodLow_nil u
  | append_singleton us o ih =>
      intro hR
      have ih' := ih (RawU_prefix hR)
      rw [List.map_append, List.map_singleton]
      cases o with
      | none => exact GoodLow_none ih'
      | some Z =>
          have hZ := hR Z (by simp)
          have hX : okLow u (shiftr01 1 0 Z) := by
            have := okLow_load (okLow_nil u) hZ.1 hZ.2
            simpa using this
          exact GoodLow_some ih' hX

theorem GoodChuX_top {u : ℕ} : ∀ Uss : List (List (Option TrioSeq)), (∀ us ∈ Uss, RawU u us) →
    GoodChuX [] 1 (fun _ => 0) u (Uss.map (fun us => us.map (Option.map (shiftr01 1 0)))) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact GoodChuX_nil _ _ _ _
  | append_singleton Uss us ih =>
      intro hR
      rw [List.map_append, List.map_singleton]
      exact GoodChuX_snocU (by simp) (by simp) le_rfl (ih (fun L h' => hR L (List.mem_append_left _ h')))
        (GoodLow_top us (hR us (List.mem_append_right _ (List.mem_singleton_self _))))

theorem okRAu_units {u : ℕ} : ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU u us →
    okRAu [] 1 u (unitsC u us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact okRAu_nil [] 1 u
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          rw [unitsC_snoc]
          exact okRAu_load (by simp) le_rfl (ih hNT' (RawU_prefix hR)) hZ.1 hZ.2

theorem OkWsAu_psLU {u : ℕ} {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU u ps) : OkWsAu [] 1 u (psLU u ps) := by
  intro w hw
  simp only [psLU, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨le_rfl, GoodChuX_top p.1 (h p hp).1, okRAu_units p.2 (h p hp).2.1 (h p hp).2.2⟩

theorem FarCAu_of_PsLU {u : ℕ} {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU u ps) (b0 : ℕ) : FarCAu [] 1 (fun _ => 0) b0 (psLU u ps) :=
  FarCAu_of_OkWsAu (by simp) (by simp) le_rfl _ (OkWsAu_psLU h) b0

theorem RawWsAu_psLU {u : ℕ} {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU u ps) : RawWsAu [] 1 (fun _ => 0) u (psLU u ps) :=
  RawWsAu_of_OkWsAu (OkWsAu_psLU h)

theorem RawWsku0_psLU {u : ℕ} {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU u ps) : RawWsku 0 u (psLU u ps) := by
  intro w hw
  simp only [psLU, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hu := HaT.units_ok u p.2 (h p hp).2.1 (h p hp).2.2
  refine ⟨le_rfl, fun us hus => ?_, hu.1.1, hu.1.2.1, LowC_mono (show u ≤ u + 0 by omega) hu.2⟩
  simp only [List.mem_map] at hus
  obtain ⟨us0, hus0, rfl⟩ := hus
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨x, hx, hxX⟩ := hX
  cases x with
  | none => simp at hxX
  | some Z =>
      simp at hxX
      subst hxX
      have hZ := (h p hp).1 us0 hus0 Z hx
      exact ⟨Fr_shift1 Z, Hd_shift1_based hZ.2,
        LowC_mono (show u ≤ u + 0 by omega) (low_of_Wg hZ.1 1 le_rfl)⟩

theorem topCLU_Wg {u : ℕ} {ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq))}
    (h : PsLU u ps) (hB : BwT u (ps.map (wLU u))) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towWu u (psLU u ps) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (ps.map (wLU u) ++ [K])) ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CLU u ps) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_psLU] at this
      simpa [towWu, rword, rcol, shiftr01] using this
  | succ m =>
      have hC := FarCAu_of_PsLU h u
      have hG := towWu_GpT hC (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha) le_rfl
        (RawWsAu_psLU h) (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, relWsu_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWu _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_psLU] at this
      simpa [towWu, rword, rcol, shiftr01] using this

/-! ## 最上段の規則 -/

/-- ★ 文脈 CLU で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CLU (v : ℕ) : GTC CLU v (GzJ.fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨ps, h, rfl⟩ := hC
  have hu' : PsLU u ps := PsLU_mono hu h
  have hBu : BwT u (ps.map (wLU u)) := by
    have := BwT_lift hB hu
    rwa [map_CLU hu h] at this
  have eL : (ps.map (wLU v) ++ [GzJ.fwTop v []]).map (fun X => mlift X v (u - v))
      = ps.map (wLU u) ++ [GzJ.fwTop u []] := by
    rw [List.map_append, map_CLU hu h, List.map_singleton, GzJ.mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega]
  rw [eL, rword_append, rword_psLU, rword_singleton]
  have eR : farWu u (u + 1) (psLU u ps) ++ rcol 0 u (GzJ.fwTop u [])
      = (farWu u (u + 1) (psLU u ps) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, GzJ.fwTop, unitsC, shiftr01]
  rw [eR]
  obtain ⟨hP, hcone⟩ := farWu_P u u (psLU u ps)
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1),
    farWu_flat (RawWsku0_psLU hu') m u (by omega)]
  exact Wg_mono ha (topCLU_Wg hu' hBu m)

theorem GTC_load_CLU {v : ℕ} {Uss : List (List (Option TrioSeq))} (hU : ∀ us ∈ Uss, RawU v us)
    {us : List (Option TrioSeq)} (hNT : GzJ.NoTie us) (hRus : RawU v us)
    (hG : GTC CLU v (wLU v (Uss, us))) :
    ∀ T ∈ Wg (2 * v), based T → GTC CLU v (wLU v (Uss, us ++ [some T])) := by
  intro T hT hbT
  have e : ∀ T' : TrioSeq, wLU v (Uss, us ++ [some T']) = wLU v (Uss, us) ++ shiftr01 1 0 T' := by
    intro T'
    show FTL0 (v + 1) (Uss.map (unitsC v)) ++ unitsC v (us ++ [some T'])
      = FTL0 (v + 1) (Uss.map (unitsC v)) ++ unitsC v us ++ shiftr01 1 0 T'
    rw [unitsC_snoc, List.append_assoc]; rfl
  rw [e]
  refine GTC_loadTop (Fr_wLU v _) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨ps, h, rfl⟩ := hC
  refine ⟨ps ++ [(Uss, us ++ [some T'])], ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · simp at hp; subst hp
      refine ⟨hU, fun hn => ?_, fun Z hZ => ?_⟩
      · rcases List.mem_append.mp hn with hn | hn
        · exact hNT hn
        · simp at hn
      · rcases List.mem_append.mp hZ with hZ | hZ
        · exact hRus Z hZ
        · simp at hZ; subst hZ; exact ⟨hT', hbT'⟩
  · rw [List.map_append, List.map_singleton, e] <;> rfl

/-! ## F のタイの子 -/

def GoodTU (v : ℕ) (Uss : List (List (Option TrioSeq))) : Prop :=
  ∀ u, v ≤ u → GTC CLU u (wLU u (Uss, []))

def ChildTU (v : ℕ) (us : List (Option TrioSeq)) : Prop :=
  ∀ Uss, (∀ us' ∈ Uss, RawU v us') → GoodTU v Uss → GoodTU v (Uss ++ [us])

theorem GoodTU_nil (v : ℕ) : GoodTU v [] := by
  intro u _
  have e : wLU u ([], []) = GzJ.fwTop u [] := by simp [wLU, FTL0, GzJ.fwTop, unitsC]
  rw [e]
  exact GTC_far_CLU u

theorem GTC_wLU {v : ℕ} {Uss : List (List (Option TrioSeq))} (hU : ∀ us ∈ Uss, RawU v us)
    (hG : GoodTU v Uss) :
    ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us → GTC CLU v (wLU v (Uss, us)) := by
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
          exact GTC_load_CLU hU hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-- ★ 空の F のタイ。 -/
theorem ChildTU_nil (v : ℕ) : ChildTU v [] := by
  intro Uss hR hG u hu
  have e : wLU u (Uss ++ [[]], []) = wLU u (Uss, []) ++ [((1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [wLU, FTL0_snoc, unitsC, shiftr01]
  rw [e]
  refine GTC_tie (C := CLU) (coneV_top (Fr_wLU u _) u) (fun u' hu' Z hZ hbZ => ?_)
    (fun L hC u' hu' => CLU_lift L u hC u' hu')
  have hR' : ∀ us ∈ Uss, RawU u' us := fun us hus => RawU_mono (le_trans hu hu') (hR us hus)
  rw [mlift_wLU hu' (p := (Uss, [])) (fun us hus => RawU_mono hu (hR us hus))
    (by simp [GzJ.NoTie]) (RawU_nil u)]
  have := GTC_load_CLU (v := u') (Uss := Uss) (us := []) hR' (by simp [GzJ.NoTie]) (RawU_nil u')
    (hG u' (le_trans hu hu')) Z hZ hbZ
  rwa [show wLU u' (Uss, [] ++ [some Z]) = wLU u' (Uss, []) ++ shiftr01 1 0 Z by
    simp [wLU, unitsC, unitC]] at this

theorem GoodTU_rep {v : ℕ} {us : List (Option TrioSeq)} (hRus : RawU v us) (hCT : ChildTU v us)
    {Uss : List (List (Option TrioSeq))} (hR : ∀ us' ∈ Uss, RawU v us') (hG : GoodTU v Uss) :
    ∀ n, (∀ us' ∈ Uss ++ List.replicate n us, RawU v us') ∧ GoodTU v (Uss ++ List.replicate n us)
  | 0 => by simp only [List.replicate_zero, List.append_nil]; exact ⟨hR, hG⟩
  | n + 1 => by
      obtain ⟨h1, h2⟩ := GoodTU_rep hRus hCT hR hG n
      rw [List.replicate_succ', ← List.append_assoc]
      refine ⟨fun us' hus' => ?_, hCT _ h1 h2⟩
      rcases List.mem_append.mp hus' with hus' | hus'
      · exact h1 us' hus'
      · rw [List.mem_singleton] at hus'; rw [hus']; exact hRus

/-- ★ 最上段の F のタイの子の単位の並びに荷を足す規則。 -/
theorem ChildTU_load {v : ℕ} : ∀ Z ∈ Wg (2 * v), based Z →
    ∀ us, RawU v us → ChildTU v us → ChildTU v (us ++ [some Z]) := by
  refine based_Wg_ind (u := v)
    (Q := fun Z => ∀ us, RawU v us → ChildTU v us → ChildTU v (us ++ [some Z])) ?_ ?_ ?_ ?_
  · intro us _ hCT Uss hR hG u hu
    have e : wLU u (Uss ++ [us ++ [some []]], []) = wLU u (Uss ++ [us], []) := by
      simp [wLU, unitsC_snoc, unitC, shiftr01]
    rw [e]
    exact hCT Uss hR hG u hu
  · -- flat: F のタイの複製
    intro Z hZW hbZ hIH us hRus hCT Uss hR hG u hu
    have hRus' : RawU v (us ++ [some Z]) := RawU_snoc_some hRus hZW hbZ
    have hCT' : ChildTU v (us ++ [some Z]) := hIH us hRus hCT
    obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
        M = ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (unitsC u (us ++ [some Z])) := ⟨_, rfl⟩
    have eK : wLU u (Uss ++ [us ++ [some (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])]], [])
        = FTL0 (u + 1) (Uss.map (unitsC u)) ++ M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
      rw [hM]; simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01]
    show GTC CLU u (wLU u (Uss ++ [us ++ [some (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])]], []))
    rw [eK]
    have hFr' : Fr (unitsC u (us ++ [some Z])) := unitsC_ge u _
    have hMne : M ≠ [] := by rw [hM]; simp
    have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
    have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
    have htail : ∀ r', 1 ≤ r' → r' < M.length → 2 ≤ entry M 0 r' := by
      intro r' hr1 hr2
      obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
      have hw' : w < (unitsC u (us ++ [some Z])).length := by
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
    · have hidx : (FTL0 (u + 1) (Uss.map (unitsC u)) ++ M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
          = (FTL0 (u + 1) (Uss.map (unitsC u))).length +
            ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [hidx, List.append_assoc, srow_append_right]
      exact hasParent_append_right_of _ _ hlast
    · have eO := oper_snoc00'' (FTL0 (u + 1) (Uss.map (unitsC u))) hMne hhead htail n
      have eW : wLU u (Uss ++ List.replicate n (us ++ [some Z]), [])
          = FTL0 (u + 1) (Uss.map (unitsC u) ++ List.replicate n (unitsC u (us ++ [some Z]))) := by
        show FTL0 (u + 1) ((Uss ++ List.replicate n (us ++ [some Z])).map (unitsC u)) ++
          unitsC u ([] : List (Option TrioSeq)) = _
        rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil, List.map_append,
          List.map_replicate]
      rw [eO, hM, ← FTL0_rep (u + 1) (Uss.map (unitsC u)) (unitsC u (us ++ [some Z])) n, ← eW]
      exact (GoodTU_rep hRus' hCT' hR hG n).2 u hu
  · -- oper
    intro Z hZW hbZ hlen hp hIH us hRus hCT Uss hR hG u hu
    have eK : ∀ Y : TrioSeq, wLU u (Uss ++ [us ++ [some Y]], [])
        = (FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us)) ++ shiftr01 2 0 Y := by
      intro Y; simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
    show GTC CLU u (wLU u (Uss ++ [us ++ [some Z]], []))
    rw [eK]
    refine GTC_oper ?_ ?_ (fun n hn => ?_)
    · simp only [List.length_append, shiftr01_length]; omega
    · have hidx : ((FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us)) ++ shiftr01 2 0 Z).length - 1
          = (FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (unitsC u us)).length + (Z.length - 1) := by
        simp only [List.length_append, shiftr01_length]; omega
      rw [hidx, srow_append_right, srow_shiftr01]
      exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)
    · rw [oper_shift _ Z 2 n hlen hp, ← eK]
      exact (hIH n hn).2 us hRus hCT Uss hR hG u hu
  · -- orph
    intro Z h j _ hbZ hj1 hjv hnp hz us hRus hCT Uss hR hG u hu
    have eK : wLU u (Uss ++ [us ++ [some (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])]], [])
        = (FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us) ++ shiftr01 2 0 Z) ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)] := by
      simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
    have eZ : ∀ z : TrioSeq, wLU u (Uss ++ [us ++ [some (Z ++ shiftr01 h 0 z)]], [])
        = (FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us) ++ shiftr01 2 0 Z) ++ shiftr01 (h + 2) 0 z := by
      intro z; simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
    show GTC CLU u (wLU u (Uss ++ [us ++ [some (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])]], []))
    rw [eK]
    refine GTC_orph hj1 (by omega) ?_ (fun z hz' hbz => ?_)
    · have hN := node_noParent (r := u + 1) (unitsC_ge u us) hbZ (by omega) hnp
      have eU : (((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (unitsC u us)) ++
            shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
          = ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
        simp [shiftr01]
      have eP : (FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us) ++ shiftr01 2 0 Z) ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)]
          = FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (unitsC u us)) ++
            shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))) := by
        simp [shiftr01, Function.comp_def, Nat.add_assoc]
      have hidx : ((FTL0 (u + 1) (Uss.map (unitsC u)) ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (unitsC u us) ++ shiftr01 2 0 Z) ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)]).length - 1
          = (FTL0 (u + 1) (Uss.map (unitsC u))).length +
            ((((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (unitsC u us)).length + Z.length) := by
        simp only [List.length_append, List.length_cons, shiftr01_length, List.length_nil]
        omega
      rw [hidx, eP, hasParent_append_gen
        (by simp only [List.length_append, List.length_cons, shiftr01_length,
          List.length_nil]; omega)
        (rsum_of_Hd (Fr_FTL0 _ _) (by rw [eU]; exact Fr_node _ _) (by rw [eU]; exact Hd_node _ _))]
      exact hN
    · rw [← eZ z]
      exact (hz z hz' hbz).2 us hRus hCT Uss hR hG u hu

/-- ★ 最上段の F のタイの子の単位の並びに F の位置のタイを足す規則。 -/
theorem ChildTU_none {v : ℕ} {us : List (Option TrioSeq)} (hus : RawU v us)
    (hZ : ∀ u, v ≤ u → ∀ Z ∈ Wg (2 * u), based Z → ChildTU u (us ++ [some Z])) :
    ChildTU v (us ++ [none]) := by
  intro Uss hR hG u hu
  have e : wLU u (Uss ++ [us ++ [none]], [])
      = FTL0 (u + 1) ((Uss ++ [us]).map (unitsC u)) ++ [((2, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01]
  rw [e]
  have hFr : ∀ D ∈ (Uss ++ [us]).map (unitsC u), Fr D := by
    intro D hD
    simp only [List.mem_map] at hD
    obtain ⟨us', -, rfl⟩ := hD
    exact unitsC_ge u us'
  refine GTC_tie (C := CLU) (coneV_Fleaf hFr) (fun u' hu' Z hZW hbZ => ?_)
    (fun L hC u'' hu'' => CLU_lift L u hC u'' hu'')
  have hRall : ∀ us' ∈ Uss ++ [us], RawU u us' := by
    intro us' h'
    rcases List.mem_append.mp h' with h' | h'
    · exact RawU_mono hu (hR us' h')
    · rw [List.mem_singleton] at h'; rw [h']; exact RawU_mono hu hus
  rw [mlift_FTL0U (u' - u) _ hRall, show u + 1 + (u' - u) = u' + 1 by omega,
    show u + (u' - u) = u' by omega]
  have hG' := hZ u' (by omega) Z hZW hbZ Uss (fun us' h' => RawU_mono (by omega) (hR us' h'))
    (fun u'' hu'' => hG u'' (by omega)) u' le_rfl
  have e2 : wLU u' (Uss ++ [us ++ [some Z]], [])
      = FTL0 (u' + 1) ((Uss ++ [us]).map (unitsC u')) ++ shiftr01 2 0 Z := by
    simp [wLU, FTL0_snoc, unitsC_snoc, unitC, unitsC, shiftr01, Function.comp_def, Nat.add_assoc]
  rwa [e2] at hG'

theorem ChildTU_all : ∀ (us : List (Option TrioSeq)) (v : ℕ), RawU v us → ChildTU v us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro v _; exact ChildTU_nil v
  | append_singleton us o ih =>
      intro v hR
      have hR' := RawU_prefix hR
      cases o with
      | none =>
          exact ChildTU_none hR' (fun u hu Z hZ hbZ =>
            ChildTU_load (v := u) Z hZ hbZ us (RawU_mono hu hR') (ih u (RawU_mono hu hR')))
      | some Z =>
          have hZ := hR Z (by simp)
          exact ChildTU_load Z hZ.1 hZ.2 us hR' (ih v hR')

theorem GoodTU_all {v : ℕ} : ∀ Uss : List (List (Option TrioSeq)), (∀ us ∈ Uss, RawU v us) →
    GoodTU v Uss := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact GoodTU_nil v
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, RawU v us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      exact ChildTU_all us v (h us (List.mem_append_right _ (List.mem_singleton_self _))) Uss h' (ih h')

/-! ## 並び -/

theorem BwT_CLU (v : ℕ) : ∀ ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq)),
    PsLU v ps → BwT v (ps.map (wLU v)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro _; exact BwT_nil v
  | append_singleton ps p ih =>
      intro h
      have h' : PsLU v ps := fun q hq => h q (List.mem_append_left _ hq)
      have hp := h p (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := GTC_wLU hp.1 (GoodTU_all p.1 hp.1) p.2 hp.2.1 hp.2.2
      have := hG _ ⟨ps, h', rfl⟩ (Fr_CLU v ps) (ih h')
      rw [List.map_append, List.map_singleton]
      exact this

/-- ★ F のタイの子に F の位置のタイを含む語の並びと、そのあとに TF の語の並び。 -/
theorem starOK_CLU {v : ℕ} (ps : List (List (List (Option TrioSeq)) × List (Option TrioSeq)))
    (h : PsLU v ps) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (ps.map (wLU v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CLU v ps) (BwT_CLU v ps h) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HcS
end TRIO
