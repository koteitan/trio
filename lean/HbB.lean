/-
HbB.lean: 最上段の W_tie と W_far の並びのあとに、中身が荷だけの遠い語の並び（行 1520〜1524 の形）。

文脈 CQ v L := L = bs.map (wT v) ++ uss.map (fwTop v)（wT v true = W_tie、wT v false = W_far、uss は荷だけ）。
- rword は QB bs (u+1) ++ farW u (u+1) (wsU u uss)。QB bs は F の語（HaZ.QP）と中身なしの遠い語（HaN.QF）の塔で TowP。
- 中身なしの遠い語の潰れ（GTC_far_CQ）: 展開の塔 towWAQ（HaW）は、最上段の TF の語（タイの子は towWAQ_GpT の級 ([], 1)）。
- 荷（GTC_load_CQ）: GTC_loadTop。文脈は荷の語を足しても閉じる。
- W_tie（GTC_tie_CQ）: GTC_tie。荷の実例は中身なしの遠い語に荷を足した語。
-/
import HaT
import HaZ

namespace TRIO
namespace HbB

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaI HaN HaR HaS HaT HaW HaX HaY HaZ

/-! ## 接頭辞の塔 -/

def QWstep (Q : ℕ → TrioSeq) : Bool → ℕ → TrioSeq
  | true => QP Q
  | false => QF Q

def QB (bs : List Bool) : ℕ → TrioSeq := bs.foldl QWstep HaZ.QNil

theorem TowP_foldl : ∀ (bs : List Bool) (Q : ℕ → TrioSeq), TowP Q → TowP (bs.foldl QWstep Q)
  | [], _, hQ => hQ
  | x :: bs, Q, hQ => by
      rw [List.foldl_cons]
      refine TowP_foldl bs _ ?_
      cases x
      · exact TowP_QF hQ
      · exact TowP_QP hQ

theorem TowP_QB (bs : List Bool) : TowP (QB bs) := TowP_foldl bs HaZ.QNil TowP_nil

theorem QB_snoc (bs : List Bool) (x : Bool) : QB (bs ++ [x]) = QWstep (QB bs) x := by
  simp [QB, List.foldl_append]

/-! ## 最上段の語 -/

def wT (v : ℕ) : Bool → TrioSeq
  | true => fwTop v [none]
  | false => fwTop v []

theorem mlift_wT {v u : ℕ} (hu : v ≤ u) (x : Bool) : mlift (wT v x) v (u - v) = wT u x := by
  cases x
  · show mlift (fwTop v []) v (u - v) = fwTop u []
    rw [mlift_fwTop (RawU_nil v), show v + (u - v) = u by omega]
  · show mlift (fwTop v [none]) v (u - v) = fwTop u [none]
    rw [mlift_fwTop (RawU_cons_none (RawU_nil v)), show v + (u - v) = u by omega]

theorem rword_bs (u : ℕ) : ∀ bs : List Bool, rword 0 u (bs.map (wT u)) = QB bs (u + 1) := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => simp [rword, QB, HaZ.QNil]
  | append_singleton bs x ih =>
      rw [List.map_append, List.map_singleton, rword_append, ih, rword_singleton, QB_snoc]
      cases x
      · show QB bs (u + 1) ++ rcol 0 u (fwTop u []) = QF (QB bs) (u + 1)
        rw [QF_eq]; simp [rcol, fwTop, unitsC, shiftr01]
      · show QB bs (u + 1) ++ rcol 0 u (fwTop u [none]) = QP (QB bs) (u + 1)
        rw [QP]; simp [rcol, fwTop, unitsC, unitC, Pf, shiftr01]

theorem rword_uss (u : ℕ) : ∀ uss : List (List (Option TrioSeq)),
    rword 0 u (uss.map (fwTop u)) = farW u (u + 1) (wsU u uss) := by
  intro uss
  induction uss with
  | nil => simp [rword, farW, wsU]
  | cons us uss ih =>
      show rcol 0 u (fwTop u us) ++ rword 0 u (uss.map (fwTop u))
        = farW u (u + 1) ((u, unitsC u us) :: wsU u uss)
      rw [ih, farW_cons]
      simp [rcol, fwTop, fwW, mlift_zero]

theorem rword_CQ (u : ℕ) (bs : List Bool) (uss : List (List (Option TrioSeq))) :
    rword 0 u (bs.map (wT u) ++ uss.map (fwTop u)) = QB bs (u + 1) ++ farW u (u + 1) (wsU u uss) := by
  rw [rword_append, rword_bs, rword_uss]

/-! ## 中身（荷だけ） -/

theorem units_okQ {Q : ℕ → TrioSeq} (hQ : TowP Q) (u : ℕ) :
    ∀ us : List (Option TrioSeq), NoTie us → RawU u us → okRAQ Q [] 1 u (unitsC u us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact okRAQ_nil hQ [] 1 u
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          rw [unitsC_snoc]
          exact okRAQ_load hQ (by simp) le_rfl (ih hNT' (RawU_prefix hR)) hZ.1 hZ.2

theorem OkWsAQ_wsU {Q : ℕ → TrioSeq} (hQ : TowP Q) {u : ℕ} {uss : List (List (Option TrioSeq))}
    (hR : RawUs u uss) (hNT : ∀ us ∈ uss, NoTie us) : OkWsAQ Q [] 1 u (wsU u uss) := by
  intro w hw
  simp only [wsU, List.mem_map] at hw
  obtain ⟨us, hus, rfl⟩ := hw
  exact ⟨le_rfl, units_okQ hQ u us (hNT us hus) (hR us hus)⟩

theorem Fr_towWAQ {Q : ℕ → TrioSeq} (hQ : TowP Q) (b : ℕ) (ws : List (ℕ × TrioSeq)) :
    ∀ m r, Fr (towWAQ Q b ws r m)
  | 0, r => by rw [towWAQ]; exact Fr_append (Fr_QW hQ _ _ ws) (GzF.Fr_single le_rfl _ _)
  | m + 1, r => by rw [towWAQ]; exact Fr_append (Fr_QW hQ _ _ ws) (Fr_letter _ _)

/-! ## 文脈 -/

def CQ (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ bs : List Bool, ∃ uss : List (List (Option TrioSeq)), RawUs v uss ∧ (∀ us ∈ uss, NoTie us) ∧
    L = bs.map (wT v) ++ uss.map (fwTop v)

theorem map_CQ {v u : ℕ} (hu : v ≤ u) (bs : List Bool) {uss : List (List (Option TrioSeq))}
    (hR : RawUs v uss) :
    (bs.map (wT v) ++ uss.map (fwTop v)).map (fun X => mlift X v (u - v))
      = bs.map (wT u) ++ uss.map (fwTop u) := by
  rw [List.map_append, map_mlift_fwTop hu hR, List.map_map]
  congr 1
  exact List.map_congr_left (fun x _ => mlift_wT hu x)

theorem CQ_lift : ∀ (L : List TrioSeq) (v : ℕ), CQ v L → ∀ u, v ≤ u →
    CQ u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨bs, uss, hR, hNT, rfl⟩ := hC
  exact ⟨bs, uss, RawUs_mono hu hR, hNT, map_CQ hu bs hR⟩

theorem Fr_CQ (v : ℕ) (bs : List Bool) (uss : List (List (Option TrioSeq))) :
    ∀ X ∈ bs.map (wT v) ++ uss.map (fwTop v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  rcases List.mem_append.mp hX with h | h
  · simp only [List.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    cases x <;> exact Fr_fwTop v _
  · exact Fr_map_fwTop v uss X h

theorem topCQ_Wg {u : ℕ} (bs : List Bool) {uss : List (List (Option TrioSeq))} (hR : RawUs u uss)
    (hNT : ∀ us ∈ uss, NoTie us) (hB : BwT u (bs.map (wT u) ++ uss.map (fwTop u))) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towWAQ (QB bs) u (wsU u uss) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (bs.map (wT u) ++ uss.map (fwTop u) ++ [K]))
        ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CQ u bs uss) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_CQ] at this
      simpa [towWAQ, rword, rcol, shiftr01] using this
  | succ m =>
      have hQ := TowP_QB bs
      have hO := OkWsAQ_wsU hQ hR hNT
      have hC : FarCAQ (QB bs) [] 1 (fun _ => 0) u (wsU u uss) := FarCAQ_of_OkWsAQ hQ hO u
      have hG := towWAQ_GpT hQ hC (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha)
        le_rfl (RawWsA_of_OkWsAQ hO) (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, HaF.relWs_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWAQ hQ _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_CQ] at this
      simpa [towWAQ, rword, rcol, shiftr01] using this

/-- ★ 文脈 CQ で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CQ (v : ℕ) : GTC CQ v (fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨bs, uss, hR, hNT, rfl⟩ := hC
  have hRu : RawUs u uss := RawUs_mono hu hR
  have hBu : BwT u (bs.map (wT u) ++ uss.map (fwTop u)) := by
    have := BwT_lift hB hu
    rwa [map_CQ hu bs hR] at this
  have eL : (bs.map (wT v) ++ uss.map (fwTop v) ++ [fwTop v []]).map (fun X => mlift X v (u - v))
      = bs.map (wT u) ++ uss.map (fwTop u) ++ [fwTop u []] := by
    rw [List.map_append, map_CQ hu bs hR, List.map_singleton, mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega]
  rw [eL, rword_append, rword_CQ, rword_singleton]
  have eR : QB bs (u + 1) ++ farW u (u + 1) (wsU u uss) ++ rcol 0 u (fwTop u [])
      = ((QB bs (u + 1) ++ farW u (u + 1) (wsU u uss)) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, fwTop, unitsC, shiftr01]
  rw [eR]
  obtain ⟨hP, hcone⟩ := farWAQ_P (TowP_QB bs) u u (wsU u uss)
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1),
    farWAQ_flat (TowP_QB bs) (RawWsk_wsU 0 hRu hNT) m u (by omega)]
  exact Wg_mono ha (topCQ_Wg bs hRu hNT hBu m)

theorem GTC_load_CQ {v : ℕ} {us : List (Option TrioSeq)} (hNT : NoTie us) (hRus : RawU v us)
    (hG : GTC CQ v (fwTop v us)) :
    ∀ T ∈ Wg (2 * v), based T → GTC CQ v (fwTop v (us ++ [some T])) := by
  intro T hT hbT
  have e : fwTop v (us ++ [some T]) = fwTop v us ++ shiftr01 1 0 T := by
    simp [fwTop, unitsC_snoc, unitC]
  rw [e]
  refine GTC_loadTop (Fr_fwTop v us) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨bs, uss, hR, hNTs, rfl⟩ := hC
  refine ⟨bs, uss ++ [us ++ [some T']], ?_, ?_, ?_⟩
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

theorem GTC_fwTop_CQ {v : ℕ} : ∀ us : List (Option TrioSeq), NoTie us → RawU v us →
    GTC CQ v (fwTop v us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact GTC_far_CQ v
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_load_CQ hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-- ★ 文脈 CQ で W_tie。 -/
theorem GTC_tie_CQ (v : ℕ) : GTC CQ v (fwTop v [none]) := by
  have e : fwTop v [none] = fwTop v [] ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwTop, unitsC, unitC]
  rw [e]
  refine GTC_tie (C := CQ) (coneV_top (Fr_fwTop v []) v) (fun u hu Z hZ hbZ => ?_)
    (fun L hC u hu => CQ_lift L v hC u hu)
  rw [mlift_fwTop (RawU_nil v), show v + (u - v) = u by omega]
  have := GTC_load_CQ (us := []) (by simp [NoTie]) (RawU_nil u) (GTC_far_CQ u) Z hZ hbZ
  have e2 : fwTop u ([] ++ [some Z]) = fwTop u [] ++ shiftr01 1 0 Z := by
    simp [fwTop, unitsC, unitC]
  rwa [e2] at this

/-! ## 並び -/

/-- ★ W_tie と W_far の並びは最上段の全ての段で良い。 -/
theorem BwT_QB (v : ℕ) : ∀ bs : List Bool, BwT v (bs.map (wT v)) := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => exact BwT_nil v
  | append_singleton bs x ih =>
      have hC : CQ v (bs.map (wT v)) := ⟨bs, [], RawUs_nil v, by simp, by simp⟩
      have hFr : ∀ X ∈ bs.map (wT v), ∀ y ∈ X, 1 ≤ y.1 := by
        have := Fr_CQ v bs []
        simpa using this
      rw [List.map_append, List.map_singleton]
      cases x
      · exact GTC_far_CQ v _ hC hFr ih
      · exact GTC_tie_CQ v _ hC hFr ih

/-- ★ W_tie と W_far の並びのあとに、中身が荷だけの遠い語の並び。 -/
theorem BwT_CQ (v : ℕ) (bs : List Bool) : ∀ uss : List (List (Option TrioSeq)), RawUs v uss →
    (∀ us ∈ uss, NoTie us) → BwT v (bs.map (wT v) ++ uss.map (fwTop v)) := by
  intro uss
  induction uss using List.reverseRecOn with
  | nil => intro _ _; simpa using BwT_QB v bs
  | append_singleton uss us ih =>
      intro hR hNT
      have hR' : RawUs v uss := fun us' h => hR us' (List.mem_append_left _ h)
      have hNT' : ∀ us' ∈ uss, NoTie us' := fun us' h => hNT us' (List.mem_append_left _ h)
      have hG := GTC_fwTop_CQ us (hNT us (by simp)) (hR us (by simp))
      have := hG _ ⟨bs, uss, hR', hNT', rfl⟩ (Fr_CQ v bs uss) (ih hR' hNT')
      rw [List.map_append, List.map_singleton, ← List.append_assoc]
      exact this

/-- ★ W_tie と W_far の並び、荷だけの遠い語の並びのあとに TF の語の並び。 -/
theorem starOK_CQ {v : ℕ} (bs : List Bool) (uss : List (List (Option TrioSeq))) (hR : RawUs v uss)
    (hNT : ∀ us ∈ uss, NoTie us) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (bs.map (wT v) ++ uss.map (fwTop v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CQ v bs uss) (BwT_CQ v bs uss hR hNT) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HbB
end TRIO
