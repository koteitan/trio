/-
HeK.lean: 最上段の段つきの木（荷と段 l のタイ）を F のタイの子に持つ語の文脈 CLTL と、その潰れ（HdQ の写し、段つき）。

    TreeTs v p cl us: 荷は Wg (2v) の based、段 0 のタイの子は (0, true)、段 l+1 の節点は cl ∧ p < l+1 で子は (l+1, false)（HeI.TreeOKs と同じ条件）
    CLTL v L := ∃ ps, PsLTL v ps ∧ L = ps.map (wLT v)（F のタイの子は TreeTs v 0 true）
- TreeOKs_farTs: 遠い段の像は HeI.TreeOKs。GoodChtX_topL（HeI.GoodChtX_snocT）で潰れの塔 topCLT_WgL。
- GTC_far_CLTL / GTC_load_CLTL: 文脈 CLTL の潰れと荷。
-/
import HeI
import HdS

namespace TRIO
namespace HeK

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ
open HeG HeI

/-! ## 段つきの生の木 -/

mutual
def TRawL (v : ℕ) : UT → Prop
  | .ch Z => Z ∈ Wg (2 * v) ∧ based Z
  | .tie _ us => TRawLs v us
def TRawLs (v : ℕ) : List UT → Prop
  | [] => True
  | x :: us => TRawL v x ∧ TRawLs v us
end

theorem TRawLs_append {v : ℕ} : ∀ {us vs : List UT}, TRawLs v (us ++ vs) ↔ TRawLs v us ∧ TRawLs v vs
  | [], vs => by simp [TRawLs]
  | x :: us, vs => by simp only [List.cons_append, TRawLs, TRawLs_append (us := us) (vs := vs), and_assoc]

theorem TRawLs_snoc {v : ℕ} {us : List UT} {x : UT} : TRawLs v (us ++ [x]) ↔ TRawLs v us ∧ TRawL v x := by
  rw [TRawLs_append]; simp [TRawLs]

mutual
theorem TRawL_mono {v u : ℕ} (hvu : v ≤ u) : ∀ x : UT, TRawL v x → TRawL u x
  | .ch Z, h => ⟨Wg_mono (by omega) h.1, h.2⟩
  | .tie _ us, h => TRawLs_mono hvu us h
theorem TRawLs_mono {v u : ℕ} (hvu : v ≤ u) : ∀ us : List UT, TRawLs v us → TRawLs u us
  | [], _ => trivial
  | x :: us, h => ⟨TRawL_mono hvu x h.1, TRawLs_mono hvu us h.2⟩
end

mutual
theorem Hd_topTL {v0 : ℕ} (v : ℕ) : ∀ x : UT, TRawL v0 x → Hd (topT v x)
  | .ch _, h => HcS.Hd_shift1_based h.2
  | .tie _ _, _ => Hd_node _ _
theorem Hd_topTLs {v0 : ℕ} (v : ℕ) : ∀ us : List UT, TRawLs v0 us → Hd (topTs v us)
  | [], _ => fun h => absurd rfl h
  | x :: us, h => Hd_app (Hd_topTL v x h.1) (Hd_topTLs v us h.2)
end

mutual
theorem mlift_topTL {v0 : ℕ} : ∀ x : UT, TRawL v0 x → ∀ v, v0 ≤ v → ∀ t,
    mlift (topT v x) v t = topT (v + t) x
  | .ch Z, h, v, hv, t => by
      simp only [topT]
      have := mlift_append_low (A := []) (low_of_Wg h.1 1 hv) t
      simpa [mlift_nil] using this
  | .tie l us, h, v, hv, t => by
      simp only [topT]
      rw [mlift_node (show v < v + 1 + l by omega) (Fr_topTs v us), mlift_topTLs us h v hv t,
        show v + 1 + l + t = v + t + 1 + l by omega]
theorem mlift_topTLs {v0 : ℕ} : ∀ us : List UT, TRawLs v0 us → ∀ v, v0 ≤ v → ∀ t,
    mlift (topTs v us) v t = topTs (v + t) us
  | [], _, v, _, t => by simp [topTs, mlift_nil]
  | x :: us, h, v, hv, t => by
      simp only [topTs]
      rw [mlift_app (Fr_topT v x) (Hd_topTLs v us h.2), mlift_topTL x h.1 v hv t,
        mlift_topTLs us h.2 v hv t]
end

mutual
theorem RawT_farTL {u : ℕ} : ∀ x : UT, TRawL u x → RawT (u + 0) (farT x)
  | .ch Z, h => by
      simp only [farT, RawT]
      exact ⟨Fr_shift1 Z, HcS.Hd_shift1_based h.2,
        LowC_mono (show u ≤ u + 0 by omega) (low_of_Wg h.1 1 le_rfl)⟩
  | .tie _ us, h => by simp only [farT, RawT]; exact RawTs_farTLs us h
theorem RawTs_farTLs {u : ℕ} : ∀ us : List UT, TRawLs u us → RawTs (u + 0) (farTs us)
  | [], _ => by simp [farTs, RawTs]
  | x :: us, h => by simp only [farTs, RawTs]; exact ⟨RawT_farTL x h.1, RawTs_farTLs us h.2⟩
end

/-! ## 段の条件つきの木 -/

mutual
def TreeTU (v : ℕ) : ℕ → Bool → UT → Prop
  | _, _, .ch Z => Z ∈ Wg (2 * v) ∧ based Z
  | _, _, .tie 0 cs => TreeTs v 0 true cs
  | p, cl, .tie (l + 1) cs => cl = true ∧ p < l + 1 ∧ TreeTs v (l + 1) false cs
def TreeTs (v : ℕ) : ℕ → Bool → List UT → Prop
  | _, _, [] => True
  | p, cl, x :: us => TreeTU v p cl x ∧ TreeTs v p cl us
end

theorem TreeTs_nil (v p : ℕ) (cl : Bool) : TreeTs v p cl [] := trivial

theorem TreeTs_cons_ch {v p : ℕ} {cl : Bool} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v)) (hb : based Z)
    {us : List UT} (h : TreeTs v p cl us) : TreeTs v p cl (UT.ch Z :: us) := ⟨⟨hZ, hb⟩, h⟩

theorem TreeTs_cons_tie0 {v p : ℕ} {cl : Bool} {cs : List UT} (hcs : TreeTs v 0 true cs) {us : List UT}
    (h : TreeTs v p cl us) : TreeTs v p cl (UT.tie 0 cs :: us) := ⟨hcs, h⟩

theorem TreeTs_cons_up {v p l : ℕ} {cl : Bool} (hcl : cl = true) (hpl : p < l + 1) {cs : List UT}
    (hcs : TreeTs v (l + 1) false cs) {us : List UT} (h : TreeTs v p cl us) :
    TreeTs v p cl (UT.tie (l + 1) cs :: us) := ⟨⟨hcl, hpl, hcs⟩, h⟩

theorem TreeTs_append {v p : ℕ} {cl : Bool} : ∀ {us vs : List UT},
    TreeTs v p cl (us ++ vs) ↔ TreeTs v p cl us ∧ TreeTs v p cl vs
  | [], vs => by simp [TreeTs]
  | x :: us, vs => by simp only [List.cons_append, TreeTs, TreeTs_append (us := us) (vs := vs), and_assoc]

mutual
theorem TreeTU_raw {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (x : UT), TreeTU v p cl x → TRawL v x
  | _, _, .ch _, h => h
  | _, _, .tie 0 cs, h => TreeTs_raw 0 true cs h
  | _, _, .tie (l + 1) cs, h => TreeTs_raw (l + 1) false cs h.2.2
theorem TreeTs_raw {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TreeTs v p cl us → TRawLs v us
  | _, _, [], _ => trivial
  | p, cl, x :: us, h => ⟨TreeTU_raw p cl x h.1, TreeTs_raw p cl us h.2⟩
end

mutual
theorem TreeTU_mono {v u : ℕ} (hvu : v ≤ u) : ∀ {p : ℕ} {cl : Bool} {x : UT}, TreeTU v p cl x → TreeTU u p cl x
  | _, _, .ch _, h => ⟨Wg_mono (by omega) h.1, h.2⟩
  | _, _, .tie 0 cs, h => TreeTs_mono hvu h
  | _, _, .tie (l + 1) cs, h => ⟨h.1, h.2.1, TreeTs_mono hvu h.2.2⟩
theorem TreeTs_mono {v u : ℕ} (hvu : v ≤ u) : ∀ {p : ℕ} {cl : Bool} {us : List UT}, TreeTs v p cl us → TreeTs u p cl us
  | _, _, [], _ => trivial
  | _, _, _ :: _, h => ⟨TreeTU_mono hvu h.1, TreeTs_mono hvu h.2⟩
end

mutual
theorem TreeOK_farT {u : ℕ} : ∀ (p : ℕ) (cl : Bool) (x : UT), TreeTU u p cl x → TreeOK u p cl (farT x)
  | _, _, .ch Z, h => by
      simp only [farT, TreeOK]
      have := okLowP_load (okLowP_nil u) h.1 h.2
      simpa using this
  | _, _, .tie 0 cs, h => by simp only [farT, TreeOK]; exact TreeOKs_farTs 0 true cs h
  | _, _, .tie (l + 1) cs, h => by
      simp only [farT, TreeOK]
      exact ⟨h.1, h.2.1, TreeOKs_farTs (l + 1) false cs h.2.2⟩
theorem TreeOKs_farTs {u : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TreeTs u p cl us →
    TreeOKs u p cl (farTs us)
  | _, _, [], _ => by simp [farTs, TreeOKs]
  | p, cl, x :: us, h => by
      simp only [farTs, TreeOKs]; exact ⟨TreeOK_farT p cl x h.1, TreeOKs_farTs p cl us h.2⟩
end

/-! ## 語と文脈 -/

def PsLTL (v : ℕ) (ps : List (List (List UT) × List (Option TrioSeq))) : Prop :=
  ∀ p ∈ ps, (∀ us ∈ p.1, TreeTs v 0 true us) ∧ GzJ.NoTie p.2 ∧ RawU v p.2

def CLTL (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ ps : List (List (List UT) × List (Option TrioSeq)), PsLTL v ps ∧ L = ps.map (wLT v)

theorem PsLTL_nil (v : ℕ) : PsLTL v [] := fun _ h => by simp at h

theorem PsLTL_cons {v : ℕ} {Uss : List (List UT)} {us : List (Option TrioSeq)}
    {ps : List (List (List UT) × List (Option TrioSeq))} (hU : ∀ us' ∈ Uss, TreeTs v 0 true us')
    (hNT : GzJ.NoTie us) (hR : RawU v us) (h : PsLTL v ps) : PsLTL v ((Uss, us) :: ps) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hU, hNT, hR⟩
  · exact h p hp

theorem PsLTL_mono {v u : ℕ} (hu : v ≤ u) {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL v ps) : PsLTL u ps :=
  fun p hp => ⟨fun us hus => TreeTs_mono hu ((h p hp).1 us hus), (h p hp).2.1,
    RawU_mono hu (h p hp).2.2⟩

theorem mlift_FTL0TL {v : ℕ} (t : ℕ) : ∀ Uss : List (List UT), (∀ us ∈ Uss, TRawLs v us) →
    mlift (FTL0 (v + 1) (Uss.map (topTs v))) v t = FTL0 (v + 1 + t) (Uss.map (topTs (v + t))) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; simpa [FTL0] using mlift_one (show v < v + 1 by omega) t
  | append_singleton Uss us ih =>
      intro hR
      have hus := hR us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton, List.map_append, List.map_singleton, FTL0_snoc, FTL0_snoc,
        mlift_app (Fr_FTL0 _ _) (Hd_node _ _), ih (fun L hL' => hR L (List.mem_append_left _ hL')),
        mlift_node (show v < v + 1 by omega) (Fr_topTs v us), mlift_topTLs us hus v le_rfl t]

theorem mlift_wLTL {v u : ℕ} (hu : v ≤ u) {p : List (List UT) × List (Option TrioSeq)}
    (hU : ∀ us ∈ p.1, TRawLs v us) (hNT : GzJ.NoTie p.2) (hR : RawU v p.2) :
    mlift (wLT v p) v (u - v) = wLT u p := by
  have hH := (HaT.units_ok v p.2 hNT hR).1.2.1
  unfold wLT
  rw [mlift_app (Fr_FTL0 _ _) hH, mlift_FTL0TL (u - v) p.1 hU, mlift_unitsC p.2 hR v le_rfl (u - v),
    show v + 1 + (u - v) = u + 1 by omega, show v + (u - v) = u by omega]

theorem map_CLTL {v u : ℕ} (hu : v ≤ u) {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL v ps) : (ps.map (wLT v)).map (fun X => mlift X v (u - v)) = ps.map (wLT u) := by
  rw [List.map_map]
  exact List.map_congr_left (fun p hp => mlift_wLTL hu (fun us hus => TreeTs_raw 0 true us ((h p hp).1 us hus)) (h p hp).2.1 (h p hp).2.2)

theorem CLTL_lift : ∀ (L : List TrioSeq) (v : ℕ), CLTL v L → ∀ u, v ≤ u →
    CLTL u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨ps, h, rfl⟩ := hC
  exact ⟨ps, PsLTL_mono hu h, map_CLTL hu h⟩

/-! ## 潰れ -/

theorem GoodChtX_topL {u : ℕ} : ∀ Uss : List (List UT), (∀ us ∈ Uss, TreeTs u 0 true us) →
    GoodChtX [] 1 (fun _ => 0) u (Uss.map farTs) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact GoodChtX_nil _ _ _ _
  | append_singleton Uss us ih =>
      intro hR
      rw [List.map_append, List.map_singleton]
      exact GoodChtX_snocT (by simp) (by simp) le_rfl (ih (fun L h' => hR L (List.mem_append_left _ h')))
        (TreeOKs_farTs 0 true us (hR us (List.mem_append_right _ (List.mem_singleton_self _))))

theorem OkWsAt_psLTL {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL u ps) : OkWsAt [] 1 u (psLT u ps) := by
  intro w hw
  simp only [psLT, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨le_rfl, GoodChtX_topL p.1 (h p hp).1, okRAt_units p.2 (h p hp).2.1 (h p hp).2.2⟩

theorem FarCAt_of_PsLTL {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL u ps) (b0 : ℕ) : FarCAt [] 1 (fun _ => 0) b0 (psLT u ps) :=
  FarCAt_of_OkWsAt (by simp) (by simp) le_rfl _ (OkWsAt_psLTL h) b0

theorem RawWsAt_psLTL {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL u ps) : RawWsAt [] 1 (fun _ => 0) u (psLT u ps) :=
  RawWsAt_of_OkWsAt (OkWsAt_psLTL h)

theorem RawWskt0_psLTL {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL u ps) : RawWskt 0 u (psLT u ps) := by
  intro w hw
  simp only [psLT, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hu := HaT.units_ok u p.2 (h p hp).2.1 (h p hp).2.2
  refine ⟨le_rfl, fun us hus => ?_, hu.1.1, hu.1.2.1, LowC_mono (show u ≤ u + 0 by omega) hu.2⟩
  simp only [List.mem_map] at hus
  obtain ⟨us0, hus0, rfl⟩ := hus
  exact RawTs_farTLs us0 (TreeTs_raw 0 true us0 ((h p hp).1 us0 hus0))

theorem topCLT_WgL {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : PsLTL u ps) (hB : BwT u (ps.map (wLT u))) (m : ℕ) :
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
      have hC := FarCAt_of_PsLTL h u
      have hG := towWt_GpT hC (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha) le_rfl
        (RawWsAt_psLTL h) (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, relWst_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWt _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_psLT] at this
      simpa [towWt, rword, rcol, shiftr01] using this

/-! ## 最上段の規則 -/

/-- ★ 文脈 CLTL で、中身なしの遠い語（潰れ）。 -/
theorem GTC_far_CLTL (v : ℕ) : GTC CLTL v (GzJ.fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨ps, h, rfl⟩ := hC
  have hu' : PsLTL u ps := PsLTL_mono hu h
  have hBu : BwT u (ps.map (wLT u)) := by
    have := BwT_lift hB hu
    rwa [map_CLTL hu h] at this
  have eL : (ps.map (wLT v) ++ [GzJ.fwTop v []]).map (fun X => mlift X v (u - v))
      = ps.map (wLT u) ++ [GzJ.fwTop u []] := by
    rw [List.map_append, map_CLTL hu h, List.map_singleton, GzJ.mlift_fwTop (RawU_nil v),
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
    farWt_flat (RawWskt0_psLTL hu') m u (by omega)]
  exact Wg_mono ha (topCLT_WgL hu' hBu m)

theorem GTC_load_CLTL {v : ℕ} {Uss : List (List UT)} (hU : ∀ us ∈ Uss, TreeTs v 0 true us)
    {us : List (Option TrioSeq)} (hNT : GzJ.NoTie us) (hRus : RawU v us)
    (hG : GTC CLTL v (wLT v (Uss, us))) :
    ∀ T ∈ Wg (2 * v), based T → GTC CLTL v (wLT v (Uss, us ++ [some T])) := by
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

end HeK
end TRIO
