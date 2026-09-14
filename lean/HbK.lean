/-
HbK.lean: 最上段の語の単位が「タイ n 個、そのあとに荷」の並び（行 1525 以降の形、HbB の写し）。

    wN v (n, us) := fwTop v (none^n ++ us)            （us は荷だけ）
    文脈 CN v L := L = ps.map (wN v)
- rword は farWn u (u+1) (psW u ps)（語ごとに F のタイの本数 n、中身は荷）。
- 中身なしの遠い語の潰れ（GTC_far_CN）: 展開の塔 towWn（HbE）。タイの子は towWn_GpT の級 ([], 1)。
- 荷（GTC_load_CN）: GTC_loadTop。文脈は荷の語を足しても閉じる。
- タイ（GTC_wN_nil）: n の帰納で GTC_tie。荷の実例はタイ n 個の語に荷を足した語。
-/
import HaT
import HbJ

namespace TRIO
namespace HbK

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HbD HbE HbG HbH HbI HbJ

/-! ## 語と rword -/

def wN (v : ℕ) (p : ℕ × List (Option TrioSeq)) : TrioSeq := fwTop v (List.replicate p.1 none ++ p.2)

def psW (u : ℕ) (ps : List (ℕ × List (Option TrioSeq))) : List (ℕ × ℕ × TrioSeq) :=
  ps.map (fun p => (p.1, u, unitsC u p.2))

theorem unitsC_rep (u : ℕ) (us : List (Option TrioSeq)) :
    ∀ n, unitsC u (List.replicate n none ++ us)
      = List.replicate n ((1, u + 1, 0) : ℕ × ℕ × ℕ) ++ unitsC u us
  | 0 => by simp
  | n + 1 => by
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append,
        ← unitsC_rep u us n]
      simp [unitsC, unitC]

theorem rcol_wN (u : ℕ) (p : ℕ × List (Option TrioSeq)) :
    rcol 0 u (wN u p) = fwWn u (u + 1) p.1 u (unitsC u p.2) := by
  simp [wN, rcol, fwTop, fwWn, FT, unitsC_rep, mlift_zero, shiftr01]

theorem rword_psW (u : ℕ) : ∀ ps : List (ℕ × List (Option TrioSeq)),
    rword 0 u (ps.map (wN u)) = farWn u (u + 1) (psW u ps) := by
  intro ps
  induction ps with
  | nil => simp [rword, farWn, psW]
  | cons p ps ih =>
      show rcol 0 u (wN u p) ++ rword 0 u (ps.map (wN u))
        = farWn u (u + 1) ((p.1, u, unitsC u p.2) :: psW u ps)
      rw [ih, farWn_cons, rcol_wN]

/-! ## 中身（荷だけ） -/

def PsOK (v : ℕ) (ps : List (ℕ × List (Option TrioSeq))) : Prop :=
  ∀ p ∈ ps, NoTie p.2 ∧ RawU v p.2

theorem PsOK_nil (v : ℕ) : PsOK v [] := fun _ h => by simp at h

theorem PsOK_cons {v n : ℕ} {us : List (Option TrioSeq)} (hNT : NoTie us) (hR : RawU v us)
    {ps : List (ℕ × List (Option TrioSeq))} (h : PsOK v ps) : PsOK v ((n, us) :: ps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hNT, hR⟩
  · exact h p hp

theorem PsOK_mono {v u : ℕ} (hu : v ≤ u) {ps : List (ℕ × List (Option TrioSeq))} (h : PsOK v ps) :
    PsOK u ps := fun p hp => ⟨(h p hp).1, RawU_mono hu (h p hp).2⟩

theorem units_okN (u n : ℕ) : ∀ us : List (Option TrioSeq), NoTie us → RawU u us →
    okRAn [] 1 n u (unitsC u us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact okRAn_nil (by simp) le_rfl n u
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          rw [unitsC_snoc]
          exact okRAn_load (by simp) le_rfl (ih hNT' (RawU_prefix hR)) hZ.1 hZ.2

theorem OkWsAn_psW {u : ℕ} {ps : List (ℕ × List (Option TrioSeq))} (h : PsOK u ps) :
    OkWsAn [] 1 u (psW u ps) := by
  intro w hw
  simp only [psW, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨le_rfl, units_okN u p.1 p.2 (h p hp).1 (h p hp).2⟩

theorem RawWskn_psW (k : ℕ) {u : ℕ} {ps : List (ℕ × List (Option TrioSeq))} (h : PsOK u ps) :
    RawWskn k u (psW u ps) := by
  intro w hw
  simp only [psW, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hu := HaT.units_ok u p.2 (h p hp).1 (h p hp).2
  exact ⟨le_rfl, hu.1.1, hu.1.2.1, LowC_mono (Nat.le_add_right u k) hu.2⟩

/-! ## 文脈 -/

theorem RawU_rep {v : ℕ} {us : List (Option TrioSeq)} (h : RawU v us) (n : ℕ) :
    RawU v (List.replicate n none ++ us) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · simp [List.mem_replicate] at hZ
  · exact h Z hZ

theorem mlift_wN {v u : ℕ} (hu : v ≤ u) {p : ℕ × List (Option TrioSeq)} (hR : RawU v p.2) :
    mlift (wN v p) v (u - v) = wN u p := by
  unfold wN
  rw [mlift_fwTop (RawU_rep hR p.1), show v + (u - v) = u by omega]

theorem map_CN {v u : ℕ} (hu : v ≤ u) {ps : List (ℕ × List (Option TrioSeq))} (h : PsOK v ps) :
    (ps.map (wN v)).map (fun X => mlift X v (u - v)) = ps.map (wN u) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p hp => mlift_wN hu (h p hp).2)

def CN (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ ps : List (ℕ × List (Option TrioSeq)), PsOK v ps ∧ L = ps.map (wN v)

theorem CN_lift : ∀ (L : List TrioSeq) (v : ℕ), CN v L → ∀ u, v ≤ u →
    CN u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨ps, h, rfl⟩ := hC
  exact ⟨ps, PsOK_mono hu h, map_CN hu h⟩

theorem Fr_CN (v : ℕ) (ps : List (ℕ × List (Option TrioSeq))) :
    ∀ X ∈ ps.map (wN v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨p, -, rfl⟩ := hX
  exact Fr_fwTop v _

theorem topCN_Wg {u : ℕ} {ps : List (ℕ × List (Option TrioSeq))} (h : PsOK u ps)
    (hB : BwT u (ps.map (wN u))) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towWn u (psW u ps) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (ps.map (wN u) ++ [K])) ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CN u ps) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_psW] at this
      simpa [towWn, rword, rcol, shiftr01] using this
  | succ m =>
      have hO := OkWsAn_psW h
      have hC := FarCAn_of_OkWsAn hO u
      have hG := towWn_GpT hC (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha) le_rfl
        (RawWsAn_of_OkWsAn hO) (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, relWsn_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWn _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_psW] at this
      simpa [towWn, rword, rcol, shiftr01] using this

/-- ★ 文脈 CN で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CN (v : ℕ) : GTC CN v (fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨ps, h, rfl⟩ := hC
  have hu' : PsOK u ps := PsOK_mono hu h
  have hBu : BwT u (ps.map (wN u)) := by
    have := BwT_lift hB hu
    rwa [map_CN hu h] at this
  have eL : (ps.map (wN v) ++ [fwTop v []]).map (fun X => mlift X v (u - v))
      = ps.map (wN u) ++ [fwTop u []] := by
    rw [List.map_append, map_CN hu h, List.map_singleton, mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega]
  rw [eL, rword_append, rword_psW, rword_singleton]
  have eR : farWn u (u + 1) (psW u ps) ++ rcol 0 u (fwTop u [])
      = (farWn u (u + 1) (psW u ps) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, fwTop, unitsC, shiftr01]
  rw [eR]
  obtain ⟨hP, hcone⟩ := farWn_P u u (psW u ps)
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1),
    farWn_flat (RawWskn_psW 0 hu') m u (by omega)]
  exact Wg_mono ha (topCN_Wg hu' hBu m)

theorem GTC_load_CN {v n : ℕ} {us : List (Option TrioSeq)} (hNT : NoTie us) (hRus : RawU v us)
    (hG : GTC CN v (wN v (n, us))) :
    ∀ T ∈ Wg (2 * v), based T → GTC CN v (wN v (n, us ++ [some T])) := by
  intro T hT hbT
  have e : ∀ T' : TrioSeq, wN v (n, us ++ [some T']) = wN v (n, us) ++ shiftr01 1 0 T' := by
    intro T'
    show fwTop v (List.replicate n none ++ (us ++ [some T']))
      = fwTop v (List.replicate n none ++ us) ++ shiftr01 1 0 T'
    rw [← List.append_assoc]
    unfold fwTop
    rw [unitsC_snoc]
    rfl
  rw [e]
  refine GTC_loadTop (Fr_fwTop v _) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨ps, h, rfl⟩ := hC
  refine ⟨ps ++ [(n, us ++ [some T'])], ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · simp at hp; subst hp
      refine ⟨fun hn => ?_, fun Z hZ => ?_⟩
      · rcases List.mem_append.mp hn with hn | hn
        · exact hNT hn
        · simp at hn
      · rcases List.mem_append.mp hZ with hZ | hZ
        · exact hRus Z hZ
        · simp at hZ; subst hZ; exact ⟨hT', hbT'⟩
  · rw [List.map_append, List.map_singleton, e]
    rfl

/-- ★ 文脈 CN で、タイ n 個の語。 -/
theorem GTC_wN_nil : ∀ (n v : ℕ), GTC CN v (wN v (n, []))
  | 0, v => by
      have e : wN v (0, []) = fwTop v [] := rfl
      rw [e]; exact GTC_far_CN v
  | n + 1, v => by
      have e : wN v (n + 1, []) = wN v (n, []) ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)] := by
        show fwTop v (List.replicate (n + 1) none ++ [])
          = fwTop v (List.replicate n none ++ []) ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)]
        rw [List.append_nil, List.append_nil, List.replicate_succ']
        unfold fwTop
        rw [unitsC_snoc]
        rfl
      rw [e]
      refine GTC_tie (C := CN) (coneV_top (Fr_fwTop v _) v) (fun u hu Z hZ hbZ => ?_)
        (fun L hC u hu => CN_lift L v hC u hu)
      rw [mlift_wN hu (p := (n, [])) (RawU_nil v)]
      have := GTC_load_CN (n := n) (us := []) (by simp [NoTie]) (RawU_nil u) (GTC_wN_nil n u) Z hZ hbZ
      have e2 : wN u (n, [] ++ [some Z]) = wN u (n, []) ++ shiftr01 1 0 Z := by
        show fwTop u (List.replicate n none ++ ([] ++ [some Z]))
          = fwTop u (List.replicate n none ++ []) ++ shiftr01 1 0 Z
        rw [List.nil_append, List.append_nil]
        unfold fwTop
        rw [unitsC_snoc]
        rfl
      rwa [e2] at this

theorem GTC_wN (n : ℕ) {v : ℕ} : ∀ us : List (Option TrioSeq), NoTie us → RawU v us →
    GTC CN v (wN v (n, us)) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact GTC_wN_nil n v
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_load_CN hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-! ## 並び -/

/-- ★ 単位が「タイ n 個、そのあとに荷」の語の並びは最上段の全ての段で良い。 -/
theorem BwT_CN (v : ℕ) : ∀ ps : List (ℕ × List (Option TrioSeq)), PsOK v ps →
    BwT v (ps.map (wN v)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro _; exact BwT_nil v
  | append_singleton ps p ih =>
      intro h
      have h' : PsOK v ps := fun q hq => h q (List.mem_append_left _ hq)
      have hp := h p (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := GTC_wN p.1 p.2 hp.1 hp.2
      have := hG _ ⟨ps, h', rfl⟩ (Fr_CN v ps) (ih h')
      rw [List.map_append, List.map_singleton]
      exact this

/-- ★ そのあとに TF の語の並び。 -/
theorem starOK_CN {v : ℕ} (ps : List (ℕ × List (Option TrioSeq))) (h : PsOK v ps)
    {Ls : List TrioSeq} (hW : WordsG v Ls) : StarOK v (rword 0 v (ps.map (wN v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CN v ps) (BwT_CN v ps h) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HbK
end TRIO
