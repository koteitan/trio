/-
HdQ.lean: 最上段の語の F のタイの子を木の単位にした文脈 CLT（HcS の写し）と、その潰れ（HdL〜HdP の遠い段の木）。

    topT v (ch Z) = Z↑1、topT v (tie us) = (1, v+1, 0) :: (topTs v us)↑1
    wLT v (Uss, us) := FTL0 (v+1) (Uss.map (topTs v)) ++ unitsC v us
    CLT v L := ∃ ps, PsLT v ps ∧ L = ps.map (wLT v)（木の荷は Wg (2v) の based、中身は荷だけ）
- farT: 荷 Z を塊 Z↑1 にした遠い段の木。chT u (u+1) u (farTs us) = topTs u us。
- topCLT_Wg: 遠い語の並びは GoodChtX_snocL（低い木）で OkWsAt、towWt_GpT で潰れの塔。
-/
import HcS
import HdP

namespace TRIO
namespace HdQ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdL HdM HdN HdO HdP

/-! ## 最上段の木の単位の語 -/

mutual
def topT (v : ℕ) : UT → TrioSeq
  | .ch Z => shiftr01 1 0 Z
  | .tie us => ((1, v + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs v us)
def topTs (v : ℕ) : List UT → TrioSeq
  | [] => []
  | x :: us => topT v x ++ topTs v us
end

mutual
def TRaw (v : ℕ) : UT → Prop
  | .ch Z => Z ∈ Wg (2 * v) ∧ based Z
  | .tie us => TRaws v us
def TRaws (v : ℕ) : List UT → Prop
  | [] => True
  | x :: us => TRaw v x ∧ TRaws v us
end

theorem topTs_append (v : ℕ) : ∀ us vs : List UT, topTs v (us ++ vs) = topTs v us ++ topTs v vs
  | [], vs => by simp [topTs]
  | x :: us, vs => by simp only [List.cons_append, topTs, topTs_append v us vs, List.append_assoc]

theorem TRaws_append {v : ℕ} : ∀ {us vs : List UT}, TRaws v (us ++ vs) ↔ TRaws v us ∧ TRaws v vs
  | [], vs => by simp [TRaws]
  | x :: us, vs => by simp only [List.cons_append, TRaws, TRaws_append (us := us) (vs := vs), and_assoc]

theorem TRaws_snoc {v : ℕ} {us : List UT} {x : UT} : TRaws v (us ++ [x]) ↔ TRaws v us ∧ TRaw v x := by
  rw [TRaws_append]; simp [TRaws]

mutual
theorem TRaw_mono {v u : ℕ} (hvu : v ≤ u) : ∀ x : UT, TRaw v x → TRaw u x
  | .ch Z, h => ⟨Wg_mono (by omega) h.1, h.2⟩
  | .tie us, h => TRaws_mono hvu us h
theorem TRaws_mono {v u : ℕ} (hvu : v ≤ u) : ∀ us : List UT, TRaws v us → TRaws u us
  | [], _ => trivial
  | x :: us, h => ⟨TRaw_mono hvu x h.1, TRaws_mono hvu us h.2⟩
end

mutual
theorem Fr_topT (v : ℕ) : ∀ x : UT, Fr (topT v x)
  | .ch Z => Fr_shift1 Z
  | .tie us => Fr_node _ _
theorem Fr_topTs (v : ℕ) : ∀ us : List UT, Fr (topTs v us)
  | [] => Fr_nil
  | x :: us => Fr_append (Fr_topT v x) (Fr_topTs v us)
end

mutual
theorem Hd_topT {v0 : ℕ} (v : ℕ) : ∀ x : UT, TRaw v0 x → Hd (topT v x)
  | .ch _, h => HcS.Hd_shift1_based h.2
  | .tie _, _ => Hd_node _ _
theorem Hd_topTs {v0 : ℕ} (v : ℕ) : ∀ us : List UT, TRaws v0 us → Hd (topTs v us)
  | [], _ => fun h => absurd rfl h
  | x :: us, h => Hd_app (Hd_topT v x h.1) (Hd_topTs v us h.2)
end

mutual
theorem mlift_topT {v0 : ℕ} : ∀ x : UT, TRaw v0 x → ∀ v, v0 ≤ v → ∀ t,
    mlift (topT v x) v t = topT (v + t) x
  | .ch Z, h, v, hv, t => by
      simp only [topT]
      have := mlift_append_low (A := []) (low_of_Wg h.1 1 hv) t
      simpa [mlift_nil] using this
  | .tie us, h, v, hv, t => by
      simp only [topT]
      rw [mlift_node (show v < v + 1 by omega) (Fr_topTs v us), mlift_topTs us h v hv t,
        show v + 1 + t = v + t + 1 by omega]
theorem mlift_topTs {v0 : ℕ} : ∀ us : List UT, TRaws v0 us → ∀ v, v0 ≤ v → ∀ t,
    mlift (topTs v us) v t = topTs (v + t) us
  | [], _, v, _, t => by simp [topTs, mlift_nil]
  | x :: us, h, v, hv, t => by
      simp only [topTs]
      rw [mlift_app (Fr_topT v x) (Hd_topTs v us h.2), mlift_topT x h.1 v hv t,
        mlift_topTs us h.2 v hv t]
end

/-! ## 遠い段の木 -/

mutual
def farT : UT → UT
  | .ch Z => .ch (shiftr01 1 0 Z)
  | .tie us => .tie (farTs us)
def farTs : List UT → List UT
  | [] => []
  | x :: us => farT x :: farTs us
end

mutual
theorem unitT_farT (u : ℕ) : ∀ x : UT, unitT u (u + 1) u (farT x) = topT u x
  | .ch Z => by simp only [farT, unitT, topT, Nat.sub_self, mlift_zero]
  | .tie us => by simp only [farT, unitT, topT, chT_farTs u us]
theorem chT_farTs (u : ℕ) : ∀ us : List UT, chT u (u + 1) u (farTs us) = topTs u us
  | [] => by simp [farTs, chT, topTs]
  | x :: us => by simp only [farTs, chT, topTs, unitT_farT u x, chT_farTs u us]
end

theorem FTLt_top (u : ℕ) (Uss : List (List UT)) :
    FTLt u (u + 1) u (Uss.map farTs) = FTL0 (u + 1) (Uss.map (topTs u)) := by
  induction Uss using List.reverseRecOn with
  | nil => simp [FTLt, FTL0]
  | append_singleton Uss us ih =>
      rw [List.map_append, List.map_singleton, List.map_append, List.map_singleton, FTLt_snoc,
        FTL0_snoc, ih, chT_farTs]

mutual
theorem LRawT_farT {u : ℕ} : ∀ x : UT, TRaw u x → LRawT u (farT x)
  | .ch Z, h => by
      simp only [farT, LRawT]
      have := okLowS_load (okLowS_nil u) h.1 h.2
      simpa using this
  | .tie us, h => by simp only [farT, LRawT]; exact LRawTs_farTs us h
theorem LRawTs_farTs {u : ℕ} : ∀ us : List UT, TRaws u us → LRawTs u (farTs us)
  | [], _ => by simp [farTs, LRawTs]
  | x :: us, h => by simp only [farTs, LRawTs]; exact ⟨LRawT_farT x h.1, LRawTs_farTs us h.2⟩
end

mutual
theorem RawT_farT {u : ℕ} : ∀ x : UT, TRaw u x → RawT (u + 0) (farT x)
  | .ch Z, h => by
      simp only [farT, RawT]
      exact ⟨Fr_shift1 Z, HcS.Hd_shift1_based h.2,
        LowC_mono (show u ≤ u + 0 by omega) (low_of_Wg h.1 1 le_rfl)⟩
  | .tie us, h => by simp only [farT, RawT]; exact RawTs_farTs us h
theorem RawTs_farTs {u : ℕ} : ∀ us : List UT, TRaws u us → RawTs (u + 0) (farTs us)
  | [], _ => by simp [farTs, RawTs]
  | x :: us, h => by simp only [farTs, RawTs]; exact ⟨RawT_farT x h.1, RawTs_farTs us h.2⟩
end

/-! ## 語と文脈 -/

def wLT (v : ℕ) (p : List (List UT) × List (Option TrioSeq)) : TrioSeq :=
  FTL0 (v + 1) (p.1.map (topTs v)) ++ unitsC v p.2

def PsLT (v : ℕ) (ps : List (List (List UT) × List (Option TrioSeq))) : Prop :=
  ∀ p ∈ ps, (∀ us ∈ p.1, TRaws v us) ∧ GzJ.NoTie p.2 ∧ RawU v p.2

def CLT (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ ps : List (List (List UT) × List (Option TrioSeq)), PsLT v ps ∧ L = ps.map (wLT v)

def psLT (u : ℕ) (ps : List (List (List UT) × List (Option TrioSeq))) :
    List (List (List UT) × ℕ × TrioSeq) :=
  ps.map (fun p => (p.1.map farTs, u, unitsC u p.2))

theorem PsLT_nil (v : ℕ) : PsLT v [] := fun _ h => by simp at h

theorem PsLT_cons {v : ℕ} {Uss : List (List UT)} {us : List (Option TrioSeq)}
    {ps : List (List (List UT) × List (Option TrioSeq))} (hU : ∀ us' ∈ Uss, TRaws v us')
    (hNT : GzJ.NoTie us) (hR : RawU v us) (h : PsLT v ps) : PsLT v ((Uss, us) :: ps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hU, hNT, hR⟩
  · exact h p hp

theorem PsLT_mono {v u : ℕ} (hu : v ≤ u) {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT v ps) : PsLT u ps :=
  fun p hp => ⟨fun us hus => TRaws_mono hu us ((h p hp).1 us hus), (h p hp).2.1,
    RawU_mono hu (h p hp).2.2⟩

theorem Fr_wLT (v : ℕ) (p : List (List UT) × List (Option TrioSeq)) : ∀ x ∈ wLT v p, 1 ≤ x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Fr_FTL0 _ _ x hx
  · exact unitsC_ge v p.2 x hx

theorem Fr_CLT (v : ℕ) (ps : List (List (List UT) × List (Option TrioSeq))) :
    ∀ X ∈ ps.map (wLT v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨p, -, rfl⟩ := hX
  exact Fr_wLT v p

theorem mlift_FTL0T {v : ℕ} (t : ℕ) : ∀ Uss : List (List UT), (∀ us ∈ Uss, TRaws v us) →
    mlift (FTL0 (v + 1) (Uss.map (topTs v))) v t = FTL0 (v + 1 + t) (Uss.map (topTs (v + t))) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; simpa [FTL0] using mlift_one (show v < v + 1 by omega) t
  | append_singleton Uss us ih =>
      intro hR
      have hus := hR us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton, List.map_append, List.map_singleton, FTL0_snoc, FTL0_snoc,
        mlift_app (Fr_FTL0 _ _) (Hd_node _ _), ih (fun L hL' => hR L (List.mem_append_left _ hL')),
        mlift_node (show v < v + 1 by omega) (Fr_topTs v us), mlift_topTs us hus v le_rfl t]

theorem mlift_wLT {v u : ℕ} (hu : v ≤ u) {p : List (List UT) × List (Option TrioSeq)}
    (hU : ∀ us ∈ p.1, TRaws v us) (hNT : GzJ.NoTie p.2) (hR : RawU v p.2) :
    mlift (wLT v p) v (u - v) = wLT u p := by
  have hH := (HaT.units_ok v p.2 hNT hR).1.2.1
  unfold wLT
  rw [mlift_app (Fr_FTL0 _ _) hH, mlift_FTL0T (u - v) p.1 hU, mlift_unitsC p.2 hR v le_rfl (u - v),
    show v + 1 + (u - v) = u + 1 by omega, show v + (u - v) = u by omega]

theorem map_CLT {v u : ℕ} (hu : v ≤ u) {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT v ps) : (ps.map (wLT v)).map (fun X => mlift X v (u - v)) = ps.map (wLT u) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p hp => mlift_wLT hu (h p hp).1 (h p hp).2.1 (h p hp).2.2)

theorem CLT_lift : ∀ (L : List TrioSeq) (v : ℕ), CLT v L → ∀ u, v ≤ u →
    CLT u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨ps, h, rfl⟩ := hC
  exact ⟨ps, PsLT_mono hu h, map_CLT hu h⟩

theorem rcol_wLT (u : ℕ) (p : List (List UT) × List (Option TrioSeq)) :
    rcol 0 u (wLT u p) = fwH u (u + 1) (FTLt u (u + 1) u (p.1.map farTs)) u (unitsC u p.2) := by
  rw [FTLt_top]
  simp [wLT, rcol, fwH, mlift_zero]

theorem rword_psLT (u : ℕ) : ∀ ps : List (List (List UT) × List (Option TrioSeq)),
    rword 0 u (ps.map (wLT u)) = farWt u (u + 1) (psLT u ps) := by
  intro ps
  induction ps with
  | nil => simp [rword, farWt, psLT]
  | cons p ps ih =>
      show rcol 0 u (wLT u p) ++ rword 0 u (ps.map (wLT u))
        = farWt u (u + 1) ((p.1.map farTs, u, unitsC u p.2) :: psLT u ps)
      rw [ih, farWt_cons, rcol_wLT]

/-! ## 潰れ -/

theorem GoodChtX_top {u : ℕ} : ∀ Uss : List (List UT), (∀ us ∈ Uss, TRaws u us) →
    GoodChtX [] 1 (fun _ => 0) u (Uss.map farTs) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact GoodChtX_nil _ _ _ _
  | append_singleton Uss us ih =>
      intro hR
      rw [List.map_append, List.map_singleton]
      exact GoodChtX_snocL (by simp) (by simp) le_rfl (ih (fun L h' => hR L (List.mem_append_left _ h')))
        (LRawTs_farTs us (hR us (List.mem_append_right _ (List.mem_singleton_self _))))

theorem okRAt_units {u : ℕ} : ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU u us →
    okRAt [] 1 u (unitsC u us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact okRAt_nil [] 1 u
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          rw [unitsC_snoc]
          exact okRAt_load (by simp) le_rfl (ih hNT' (RawU_prefix hR)) hZ.1 hZ.2

theorem OkWsAt_psLT {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT u ps) : OkWsAt [] 1 u (psLT u ps) := by
  intro w hw
  simp only [psLT, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨le_rfl, GoodChtX_top p.1 (h p hp).1, okRAt_units p.2 (h p hp).2.1 (h p hp).2.2⟩

theorem FarCAt_of_PsLT {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT u ps) (b0 : ℕ) : FarCAt [] 1 (fun _ => 0) b0 (psLT u ps) :=
  FarCAt_of_OkWsAt (by simp) (by simp) le_rfl _ (OkWsAt_psLT h) b0

theorem RawWsAt_psLT {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT u ps) : RawWsAt [] 1 (fun _ => 0) u (psLT u ps) :=
  RawWsAt_of_OkWsAt (OkWsAt_psLT h)

theorem RawWskt0_psLT {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT u ps) : RawWskt 0 u (psLT u ps) := by
  intro w hw
  simp only [psLT, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hu := HaT.units_ok u p.2 (h p hp).2.1 (h p hp).2.2
  refine ⟨le_rfl, fun us hus => ?_, hu.1.1, hu.1.2.1, LowC_mono (show u ≤ u + 0 by omega) hu.2⟩
  simp only [List.mem_map] at hus
  obtain ⟨us0, hus0, rfl⟩ := hus
  exact RawTs_farTs us0 ((h p hp).1 us0 hus0)

theorem topCLT_Wg {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLT u ps) (hB : BwT u (ps.map (wLT u))) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towWt u (psLT u ps) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (ps.map (wLT u) ++ [K])) ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CLT u ps) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_psLT] at this
      simpa [towWt, rword, rcol, shiftr01] using this
  | succ m =>
      have hC := FarCAt_of_PsLT h u
      have hG := towWt_GpT hC (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha) le_rfl
        (RawWsAt_psLT h) (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, relWst_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWt _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_psLT] at this
      simpa [towWt, rword, rcol, shiftr01] using this

/-! ## 最上段の規則 -/

/-- ★ 文脈 CLT で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CLT (v : ℕ) : GTC CLT v (GzJ.fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨ps, h, rfl⟩ := hC
  have hu' : PsLT u ps := PsLT_mono hu h
  have hBu : BwT u (ps.map (wLT u)) := by
    have := BwT_lift hB hu
    rwa [map_CLT hu h] at this
  have eL : (ps.map (wLT v) ++ [GzJ.fwTop v []]).map (fun X => mlift X v (u - v))
      = ps.map (wLT u) ++ [GzJ.fwTop u []] := by
    rw [List.map_append, map_CLT hu h, List.map_singleton, GzJ.mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega]
  rw [eL, rword_append, rword_psLT, rword_singleton]
  have eR : farWt u (u + 1) (psLT u ps) ++ rcol 0 u (GzJ.fwTop u [])
      = (farWt u (u + 1) (psLT u ps) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, GzJ.fwTop, unitsC, shiftr01]
  rw [eR]
  obtain ⟨hP, hcone⟩ := farWt_P u u (psLT u ps)
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1),
    farWt_flat (RawWskt0_psLT hu') m u (by omega)]
  exact Wg_mono ha (topCLT_Wg hu' hBu m)

theorem GTC_load_CLT {v : ℕ} {Uss : List (List UT)} (hU : ∀ us ∈ Uss, TRaws v us)
    {us : List (Option TrioSeq)} (hNT : GzJ.NoTie us) (hRus : RawU v us)
    (hG : GTC CLT v (wLT v (Uss, us))) :
    ∀ T ∈ Wg (2 * v), based T → GTC CLT v (wLT v (Uss, us ++ [some T])) := by
  intro T hT hbT
  have e : ∀ T' : TrioSeq, wLT v (Uss, us ++ [some T']) = wLT v (Uss, us) ++ shiftr01 1 0 T' := by
    intro T'
    show FTL0 (v + 1) (Uss.map (topTs v)) ++ unitsC v (us ++ [some T'])
      = FTL0 (v + 1) (Uss.map (topTs v)) ++ unitsC v us ++ shiftr01 1 0 T'
    rw [unitsC_snoc, List.append_assoc]; rfl
  rw [e]
  refine GTC_loadTop (Fr_wLT v _) hG ?_ T hT hbT
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

end HdQ
end TRIO
