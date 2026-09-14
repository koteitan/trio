/-
HaT.lean: 最上段の [W_tie, W_tie]（行 1502 の形）。

文脈 CT v L := L = [W_tie] ++ （中身が荷だけの遠い語の並び）。
- rword は Pf (u+1) ++ farW u (u+1) (wsU u uss)（HaR の F の語で始まる遠い語の並び）。
- 中身なしの遠い語の潰れ（GTC_far_CT）: 展開の塔 towWF は、最上段の TF の語（タイの子は towWFk_GpT の級 ([], 1)）。
- 荷（GTC_load_CT）: GTC_loadTop。文脈は荷の語を足しても閉じる。
- 2 つ目の W_tie（BwT_tieTie）: GTC_tie。荷の実例は中身なしの遠い語に荷を足した語。
-/
import GzJ
import HaS

namespace TRIO
namespace HaT

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaI HaR HaS

/-! ## 荷だけの単位 -/

theorem LowC_append {v : ℕ} {X Y : TrioSeq} (hX : LowC v X) (hY : LowC v Y) : LowC v (X ++ Y) := by
  intro i hi
  rw [List.length_append] at hi
  rcases Nat.lt_or_ge i X.length with h | h
  · obtain ⟨k, hk, hle⟩ := hX i h
    have hkX := lt_of_le_of_lt (rtg0_le hk) h
    exact ⟨k, rtg0_append_left hk h, by rw [Small.entry_append_left hkX]; exact hle⟩
  · obtain ⟨q, rfl⟩ : ∃ q, i = X.length + q := ⟨i - X.length, by omega⟩
    obtain ⟨k, hk, hle⟩ := hY q (by omega)
    exact ⟨X.length + k, rtg_nextrel0_lift X Y hk, by rw [entry_append_right]; exact hle⟩

theorem units_ok (u : ℕ) : ∀ us : List (Option TrioSeq), NoTie us → RawU u us →
    okWFkF 1 u (unitsC u us) ∧ LowC u (unitsC u us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact ⟨okWFkF_nil 1 u, fun i hi => by simp [unitsC] at hi⟩
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          have ih' := ih hNT' (RawU_prefix hR)
          rw [unitsC_snoc]
          exact ⟨okWFkF_load le_rfl ih'.1 hZ.1 hZ.2,
            LowC_append ih'.2 (low_of_Wg hZ.1 1 le_rfl)⟩

def wsU (u : ℕ) (uss : List (List (Option TrioSeq))) : List (ℕ × TrioSeq) :=
  uss.map (fun us => (u, unitsC u us))

theorem okWFk_wsU {u : ℕ} {uss : List (List (Option TrioSeq))} (hR : RawUs u uss)
    (hNT : ∀ us ∈ uss, NoTie us) : ∀ w ∈ wsU u uss, okWFk 1 w.1 w.2 := by
  intro w hw
  simp only [wsU, List.mem_map] at hw
  obtain ⟨us, hus, rfl⟩ := hw
  exact (units_ok u us (hNT us hus) (hR us hus)).1.2

theorem RawWsk_wsU (k : ℕ) {u : ℕ} {uss : List (List (Option TrioSeq))} (hR : RawUs u uss)
    (hNT : ∀ us ∈ uss, NoTie us) : RawWsk k u (wsU u uss) := by
  intro w hw
  simp only [wsU, List.mem_map] at hw
  obtain ⟨us, hus, rfl⟩ := hw
  have h := units_ok u us (hNT us hus) (hR us hus)
  exact ⟨le_rfl, h.1.1, h.1.2.1, LowC_mono (by omega) h.2⟩

theorem rword_CT (u : ℕ) (uss : List (List (Option TrioSeq))) :
    rword 0 u ([fwTop u [none]] ++ uss.map (fwTop u)) = Pf (u + 1) ++ farW u (u + 1) (wsU u uss) := by
  rw [rword_append, rword_singleton]
  have e1 : rcol 0 u (fwTop u [none]) = Pf (u + 1) := by
    simp [rcol, fwTop, unitsC, unitC, Pf, shiftr01]
  have e2 : ∀ uss : List (List (Option TrioSeq)),
      rword 0 u (uss.map (fwTop u)) = farW u (u + 1) (wsU u uss) := by
    intro uss
    induction uss with
    | nil => simp [rword, farW, wsU]
    | cons us uss ih =>
        show rcol 0 u (fwTop u us) ++ rword 0 u (uss.map (fwTop u))
          = farW u (u + 1) ((u, unitsC u us) :: wsU u uss)
        rw [ih, farW_cons]
        simp [rcol, fwTop, fwW, mlift_zero]
  rw [e1, e2]

/-! ## 文脈 -/

def CT (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ uss : List (List (Option TrioSeq)), RawUs v uss ∧ (∀ us ∈ uss, NoTie us) ∧
    L = [fwTop v [none]] ++ uss.map (fwTop v)

theorem map_CT {v u : ℕ} (hu : v ≤ u) {uss : List (List (Option TrioSeq))} (hR : RawUs v uss) :
    ([fwTop v [none]] ++ uss.map (fwTop v)).map (fun X => mlift X v (u - v))
      = [fwTop u [none]] ++ uss.map (fwTop u) := by
  rw [List.map_append, List.map_singleton, map_mlift_fwTop hu hR,
    mlift_fwTop (RawU_cons_none (RawU_nil v)), show v + (u - v) = u by omega]

theorem CT_lift : ∀ (L : List TrioSeq) (v : ℕ), CT v L → ∀ u, v ≤ u →
    CT u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨uss, hR, hNT, rfl⟩ := hC
  exact ⟨uss, RawUs_mono hu hR, hNT, map_CT hu hR⟩

theorem Fr_CT (v : ℕ) (uss : List (List (Option TrioSeq))) :
    ∀ X ∈ [fwTop v [none]] ++ uss.map (fwTop v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  rcases List.mem_append.mp hX with h | h
  · simp only [List.mem_singleton] at h; subst h; exact Fr_fwTop v _
  · exact Fr_map_fwTop v uss X h

theorem topCT_Wg {u : ℕ} {uss : List (List (Option TrioSeq))} (hR : RawUs u uss)
    (hNT : ∀ us ∈ uss, NoTie us) (hB : BwT u ([fwTop u [none]] ++ uss.map (fwTop u))) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towWF u (wsU u uss) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u ([fwTop u [none]] ++ uss.map (fwTop u) ++ [K]))
        ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CT u uss) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_CT] at this
      simpa [towWF, rword, rcol, shiftr01] using this
  | succ m =>
      have hC1 : FarCFk 1 u (wsU u uss) := FarCFk_of 1 u _ (okWFk_wsU hR hNT)
      have hG := towWFk_GpT hC1 m [] 1 (fun _ => 0) u le_rfl (RawWsk_wsU 1 hR hNT) (by simp)
        (by simp) le_rfl (by simp) (by simp [liftOff, stepSum])
      rw [liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWF _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_CT] at this
      simpa [towWF, rword, rcol, shiftr01] using this

/-- ★ 文脈 CT で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CT (v : ℕ) : GTC CT v (fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨uss, hR, hNT, rfl⟩ := hC
  have hRu : RawUs u uss := RawUs_mono hu hR
  have hBu : BwT u ([fwTop u [none]] ++ uss.map (fwTop u)) := by
    have := BwT_lift hB hu
    rwa [map_CT hu hR] at this
  have eL : ([fwTop v [none]] ++ uss.map (fwTop v) ++ [fwTop v []]).map (fun X => mlift X v (u - v))
      = [fwTop u [none]] ++ uss.map (fwTop u) ++ [fwTop u []] := by
    rw [List.map_append, map_CT hu hR, List.map_singleton, mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega]
  rw [eL, rword_append, rword_CT, rword_singleton]
  have eR : Pf (u + 1) ++ farW u (u + 1) (wsU u uss) ++ rcol 0 u (fwTop u [])
      = ((Pf (u + 1) ++ farW u (u + 1) (wsU u uss)) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, fwTop, unitsC, shiftr01]
  rw [eR]
  obtain ⟨hP, hcone⟩ := farWF_P u u (wsU u uss)
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1),
    farWFk_flat (RawWsk_wsU 0 hRu hNT) m u (by omega)]
  exact Wg_mono ha (topCT_Wg hRu hNT hBu m)

theorem GTC_load_CT {v : ℕ} {us : List (Option TrioSeq)} (hNT : NoTie us) (hRus : RawU v us)
    (hG : GTC CT v (fwTop v us)) :
    ∀ T ∈ Wg (2 * v), based T → GTC CT v (fwTop v (us ++ [some T])) := by
  intro T hT hbT
  have e : fwTop v (us ++ [some T]) = fwTop v us ++ shiftr01 1 0 T := by
    simp [fwTop, unitsC_snoc, unitC]
  rw [e]
  refine GTC_loadTop (Fr_fwTop v us) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨uss, hR, hNTs, rfl⟩ := hC
  refine ⟨uss ++ [us ++ [some T']], ?_, ?_, ?_⟩
  · intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact hR us' hus'
    · simp at hus'; subst hus'
      intro Z hZ
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hRus Z hZ
      · simp at hZ; subst hZ; exact ⟨hT', hbT'⟩
  · intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact hNTs us' hus'
    · simp at hus'; subst hus'
      intro hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hNT hn
      · simp at hn
  · simp [fwTop, unitsC_snoc, unitC]

/-- ★ [W_tie, W_tie] は最上段の全ての段で良い。 -/
theorem BwT_tieTie (v : ℕ) : BwT v [fwTop v [none], fwTop v [none]] := by
  have e : fwTop v [none] = fwTop v [] ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwTop, unitsC, unitC]
  have hG : GTC CT v (fwTop v [] ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)]) := by
    refine GTC_tie (C := CT) (coneV_top (Fr_fwTop v []) v) (fun u hu Z hZ hbZ => ?_)
      (fun L hC u hu => CT_lift L v hC u hu)
    rw [mlift_fwTop (RawU_nil v), show v + (u - v) = u by omega]
    have := GTC_load_CT (us := []) (by simp [NoTie]) (RawU_nil u) (GTC_far_CT u) Z hZ hbZ
    have e2 : fwTop u ([] ++ [some Z]) = fwTop u [] ++ shiftr01 1 0 Z := by
      simp [fwTop, unitsC, unitC]
    rwa [e2] at this
  have hB0 : BwT v [fwTop v [none]] := by
    have := BwT_topFarTie (v := v) [] (RawUs_nil v) (by simp) [] (RawU_nil v) (by simp [NoTie])
    simpa using this
  have := hG [fwTop v [none]] ⟨[], RawUs_nil v, by simp, by simp⟩ (Fr_CT v [])
  rw [← e] at this
  simpa using this hB0

/-- ★ [W_tie, W_tie] のあとに TF の語の並び。 -/
theorem starOK_tieTie {v : ℕ} {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v ([fwTop v [none], fwTop v [none]] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hFr : ∀ X ∈ [fwTop v [none], fwTop v [none]], ∀ x ∈ X, 1 ≤ x.1 := by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;> exact Fr_fwTop v _
  have hB := BwT_append_words hFr (BwT_tieTie v) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HaT
end TRIO
