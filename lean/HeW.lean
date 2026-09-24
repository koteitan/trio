import HeV

namespace TRIO
namespace HeW

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeI HeK HeU HeV

/-- 一般化した collapse 文脈: 各語の子は TRawLs（段無視、深い葉も可）、荷は NoTie/RawU、
    そして遠い像が各段で RawWskt/FarCAt/RawWsAt。 -/
def GLctx (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ ps : List (List (List UT) × List (Option TrioSeq)),
    (∀ p ∈ ps, (∀ us ∈ p.1, TRawLs v us) ∧ GzJ.NoTie p.2 ∧ RawU v p.2) ∧
    (∀ u, v ≤ u → RawWskt 0 u (psLT u ps) ∧ FarCAt [] 1 (fun _ => 0) u (psLT u ps)
      ∧ RawWsAt [] 1 (fun _ => 0) u (psLT u ps)) ∧
    L = ps.map (wLT v)

/-- ★★ GTC_far_CLTL の一般版: 文脈 GLctx（深い葉も含む）に空 collapse 語 fwTop を足せる。 -/
theorem GTC_far_gen (v : ℕ) : GTC GLctx v (GzJ.fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨ps, hraw, hcond, rfl⟩ := hC
  obtain ⟨hRawWskt, hFar, hRawWs⟩ := hcond u hu
  have map_GL : (ps.map (wLT v)).map (fun X => mlift X v (u - v)) = ps.map (wLT u) := by
    rw [List.map_map]
    exact List.map_congr_left (fun p hp =>
      mlift_wLTL hu (hraw p hp).1 (hraw p hp).2.1 (hraw p hp).2.2)
  have hBu : BwT u (ps.map (wLT u)) := by
    have := BwT_lift hB hu
    rwa [map_GL] at this
  have eL : (ps.map (wLT v) ++ [GzJ.fwTop v []]).map (fun X => mlift X v (u - v))
      = ps.map (wLT u) ++ [GzJ.fwTop u []] := by
    rw [List.map_append, map_GL, List.map_singleton, GzJ.mlift_fwTop (RawU_nil v),
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
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1), farWt_flat hRawWskt m u (by omega)]
  exact Wg_mono ha (topCLT_WgL_gen hBu hFar hRawWs m)

/-- RawWskt の一般版（各語の子が TRawLs、荷が NoTie/RawU）。RawWskt0_psLTL の写し。 -/
theorem RawWskt0_gen {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (h : ∀ p ∈ ps, (∀ us ∈ p.1, TRawLs u us) ∧ GzJ.NoTie p.2 ∧ RawU u p.2) :
    RawWskt 0 u (psLT u ps) := by
  intro w hw
  simp only [psLT, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hunit := HaT.units_ok u p.2 (h p hp).2.1 (h p hp).2.2
  refine ⟨le_rfl, fun us hus => ?_, hunit.1.1, hunit.1.2.1, LowC_mono (show u ≤ u + 0 by omega) hunit.2⟩
  simp only [List.mem_map] at hus
  obtain ⟨us0, hus0, rfl⟩ := hus
  exact RawTs_farTLs us0 ((h p hp).1 us0 hus0)

/-- 深い葉のデータ。 -/
def p1 : List (List UT) × List (Option TrioSeq) := ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], [])

theorem TRawLs_deep (u : ℕ) : ∀ us ∈ p1.1, TRawLs u us := by
  intro us hus; simp only [p1, List.mem_singleton] at hus; subst hus; simp [TRawLs, TRawL]

theorem psLT_p1 (u : ℕ) : psLT u [p1] = HeV.dlws u := by
  simp [psLT, HeV.dlws, p1, farTs, farT, unitsC]

/-- ★ 深い葉の文脈 [K] は GLctx。 -/
theorem GLctx_deep : GLctx 0 [wLT 0 p1] := by
  refine ⟨[p1], ?_, ?_, by simp⟩
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact ⟨TRawLs_deep 0, by simp [p1, GzJ.NoTie], RawU_nil 0⟩
  · intro u hu
    rw [psLT_p1]
    refine ⟨?_, HeV.FarCAt_deep le_rfl u, HeV.RawWsAt_deep le_rfl⟩
    rw [← psLT_p1]
    exact RawWskt0_gen (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp
      exact ⟨TRawLs_deep u, by simp [p1, GzJ.NoTie], RawU_nil u⟩)

/-- 深い葉の語 K。 -/
def Kdeep : TrioSeq := wLT 0 ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))

/-- ★★ BwT 0 [K, 空collapse語]（深い葉のあとに collapse 語を足す）。 -/
theorem bwt_KK2 : BwT 0 [Kdeep, GzJ.fwTop 0 []] := by
  have hBK : BwT 0 [Kdeep] := by
    have := HeT.hK_pm [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
    simpa [Kdeep] using this
  have := GTC_far_gen 0 [Kdeep] (by simpa [Kdeep] using GLctx_deep)
    (by intro X hX x hx; simp only [List.mem_singleton] at hX; subst hX
        exact Fr_wLT 0 _ x hx) hBK
  simpa using this

/-- ★★★ シート行 (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(1,1,1)(2,1,1) ∈ W 0。 -/
theorem R_pm3 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(1,1,1),(2,1,1)] : TrioSeq) ∈ W 0 := by
  have hS : StarOK 0 (rword 0 0 [Kdeep, GzJ.fwTop 0 []]) := by
    refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
    have h2 := bwt_KK2 0 le_rfl
    rw [Nat.sub_self] at h2
    simpa only [mlift_zero, List.map_cons, List.map_nil] using h2
  have h := W0_of_starOK hS
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01, Kdeep, GzJ.fwTop] using h

end HeW
end TRIO
