/-
HeM.lean: 最上段の道の集合での荷・空のタイの規則と空の並び（HdS の写し、段つきの道）。

- GdT_load: GdT P us → Z（Wg (2v) の based）→ GdT P (us ++ [ch Z])（based_Wg_ind。flat は TPSDec の分解で、
  空の道は F のタイの複製、空でない道は親の集合の段 l の節点の複製）。
- GdT_tieE: GdT P us → GdT P (us ++ [tie 0 []])（gtc_tie、荷は上の段で GdT_load）。
- GdT_nil_TP0 / GdT_nil_tchS0: F のタイの子の位置とタイの子の位置の空の並び。
-/
import HeL

namespace TRIO
namespace HeM

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ
open HeB HeG HeI HeK HeL

theorem topTs_snoc_tieL (u : ℕ) (us cs : List UT) (l : ℕ) :
    topTs u (us ++ [UT.tie l cs])
      = topTs u us ++ ((1, u + 1 + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u cs) := by
  simp [topTs_append, topTs, topT]

theorem topTs_rep_tieL (u : ℕ) (us0 y : List UT) (l : ℕ) : ∀ n,
    topTs u (us0 ++ List.replicate n (UT.tie l y))
      = topTs u us0 ++ (List.range n).flatMap
          (fun _ => ((1, u + 1 + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u y))
  | 0 => by simp
  | n + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, topTs_snoc_tieL, topTs_rep_tieL u us0 y l n,
        List.range_succ, List.flatMap_append]
      simp

/-! ## 荷 -/

/-- ★ 最上段の道の集合で、並びの最後に荷を足す規則。 -/
theorem GdT_load {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) (hD : TPSDec P p cl) {v : ℕ} :
    ∀ Z ∈ Wg (2 * v), based Z → ∀ (us : List UT), GdT P p cl v us → GdT P p cl v (us ++ [UT.ch Z]) := by
  have key := based_Wg_ind (u := v)
    (Q := fun Z => Z ∈ Wg (2 * v) → ∀ (us : List UT), GdT P p cl v us → GdT P p cl v (us ++ [UT.ch Z]))
    ?_ ?_ ?_ ?_
  · exact fun Z hZ hb => key Z hZ hb hZ
  · -- nil
    intro _ us hus
    refine ⟨TreeTs_append.mpr ⟨hus.1, ⟨Wg_nil _, based_nil⟩, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    have := hus.2 u hu Uss hU hG Q hQ
    rw [BotCL_word] at this ⊢
    rwa [HdS.topTs_snoc_ch, show shiftr01 1 0 ([] : TrioSeq) = [] from rfl, List.append_nil]
  · -- flat
    intro Z hZW hbZ hIH hZW' us hus
    have hDZ := hIH hZW us hus
    refine ⟨TreeTs_append.mpr ⟨hus.1, ⟨hZW', HdS.based_snoc0 hbZ⟩, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    have hVF : Fr (topTs u us ++ shiftr01 1 0 Z) := Fr_append (Fr_topTs _ _) (Fr_shift1 Z)
    rcases hD u Q hQ with rfl | ⟨P', p', cl', Q', us0, l, rfl, hQ', hus0, hX, hT⟩
    · rw [BotCL_word, HdS.topTs_snoc_ch]
      obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
          M = ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u us ++ shiftr01 1 0 Z) := ⟨_, rfl⟩
      have eW : wLT u (Uss ++ [plugQ [] []], []) ++
            shiftr01 (([] : Path).length + 1) 0
              (topTs u us ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
          = FTL0 (u + 1) (Uss.map (topTs u)) ++ M ++ [((1 + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
        rw [hM]; simp [wLT, FTL0_snoc, plugQ, topTs, unitsC, shiftr01]
      rw [eW]
      refine HdR.gtc_flat (by rw [hM]; simp) (by rw [hM]; rfl) ?_ (fun n => ?_)
      · intro r' hr1 hr2
        obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
        have hw : w < (topTs u us ++ shiftr01 1 0 Z).length := by
          rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
        rw [hM, entry_cons, entry0_shiftr01 hw]
        have := getD_row0_ge hVF hw
        omega
      · have hDZt : TreeTs u 0 true (us ++ [UT.ch Z]) :=
          hP.tree u [] hQ _ (TreeTs_mono hu hDZ.1)
        have hGn : ∀ n, (∀ us' ∈ Uss ++ List.replicate n (us ++ [UT.ch Z]), TreeTs u 0 true us') ∧
            GoodTTL u (Uss ++ List.replicate n (us ++ [UT.ch Z])) := by
          intro n
          induction n with
          | zero => simpa using And.intro hU hG
          | succ n ih =>
              rw [List.replicate_succ', ← List.append_assoc]
              refine ⟨fun us' h' => ?_, ?_⟩
              · rcases List.mem_append.mp h' with h' | h'
                · exact ih.1 us' h'
                · simp at h'; subst h'; exact hDZt
              · have := GdT_good hP hDZ hu ih.1 ih.2 hQ
                simpa [plugQ] using this
        have := (hGn n).2 u le_rfl
        have eR : wLT u (Uss ++ List.replicate n (us ++ [UT.ch Z]), [])
            = FTL0 (u + 1) (Uss.map (topTs u)) ++ (List.range n).flatMap (fun _ => M) := by
          show FTL0 (u + 1) ((Uss ++ List.replicate n (us ++ [UT.ch Z])).map (topTs u)) ++
            unitsC u ([] : List (Option TrioSeq)) = _
          rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil, List.map_append,
            List.map_replicate, FTL0_rep, HdS.topTs_snoc_ch, hM]
        rwa [eR] at this
    · rw [BotCL_snoc_eq, BotCL_word, topTs_snoc_tieL, HdS.topTs_snoc_ch]
      obtain ⟨d', hd'⟩ : ∃ d', d' = Q'.length + 1 := ⟨_, rfl⟩
      rw [← hd']
      obtain ⟨M, hM⟩ : ∃ M : TrioSeq, M = shiftr01 d' 0 (((1, u + 1 + l, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (topTs u us ++ shiftr01 1 0 Z)) := ⟨_, rfl⟩
      have eG : wLT u (Uss ++ [plugQ Q' []], []) ++ shiftr01 d' 0 (topTs u us0 ++
            ((1, u + 1 + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u us ++
              shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
          = (wLT u (Uss ++ [plugQ Q' []], []) ++ shiftr01 d' 0 (topTs u us0)) ++ M ++
              [((d' + 1 + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
        rw [hM]
        simp [shiftr01] <;> omega
      rw [eG]
      refine HdR.gtc_flat (by rw [hM]; simp [shiftr01]) ?_ ?_ (fun n => ?_)
      · rw [hM, entry0_shiftr01 (by simp)]; show 1 + d' = d' + 1; omega
      · intro r' hr1 hr2
        obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
        have hw : w < (topTs u us ++ shiftr01 1 0 Z).length := by
          rw [hM] at hr2; simp only [shiftr01_length, List.length_cons] at hr2; omega
        have hr2' : w + 1 < (((1, u + 1 + l, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (topTs u us ++ shiftr01 1 0 Z)).length := by
          simp only [shiftr01_length, List.length_cons]; omega
        rw [hM, entry0_shiftr01 hr2', entry_cons, entry0_shiftr01 hw]
        have := getD_row0_ge hVF hw
        omega
      · have hrep : GdT P' p' cl' u (us0 ++ List.replicate n (UT.tie l (us ++ [UT.ch Z]))) := by
          induction n with
          | zero => simpa using hus0
          | succ n ih =>
              rw [List.replicate_succ', ← List.append_assoc]
              exact GdT_jump hX hT (GdT_mono hDZ hu) ih
        have := hrep.2 u le_rfl Uss hU hG Q' hQ'
        rw [BotCL_word, topTs_rep_tieL, HdS.topTs_snoc_ch, ← hd'] at this
        have eF : ∀ (l' : List ℕ) (g : ℕ → TrioSeq),
            shiftr01 d' 0 (l'.flatMap g) = l'.flatMap (fun i => shiftr01 d' 0 (g i)) := by
          intro l' g; simp [shiftr01, List.map_flatMap]
        rw [shiftr01_append0, eF] at this
        rw [hM]
        simp only [List.append_assoc] at this ⊢
        exact this
  · -- oper
    intro Z hZW hbZ hlen hp hIH hZW' us hus
    refine ⟨TreeTs_append.mpr ⟨hus.1, ⟨hZW', hbZ⟩, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc]
    refine HdR.gtc_oper hlen hp (fun n hn => ?_)
    have := ((hIH n hn).2 (hIH n hn).1 us hus).2 u hu Uss hU hG Q hQ
    rwa [BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc] at this
  · -- orph
    intro Z h j hZW hbZ hj1 hjv hnp hz hZW' us hus
    refine ⟨TreeTs_append.mpr ⟨hus.1, ⟨hZW', hbZ⟩, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [BotCL_word, HdS.topTs_snoc_ch]
    have eU : topTs u us ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
        = (topTs u us ++ shiftr01 1 0 Z) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
    rw [eU]
    have hHP : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := HcS.Hd_shift1_based hbZ
    refine HdR.gtc_orph (PathCone_YtopL u Uss Q (hP.raw u Q hQ))
      (by rw [← eU]; exact Hd_app (Hd_topTLs u us (TreeTs_raw p cl us hus.1)) hHP) hj1 (by omega) ?_
      (fun z hz' hbz => ?_)
    · have hlen : (topTs u us ++ shiftr01 1 0 Z).length = (topTs u us).length + Z.length := by
        simp only [List.length_append, shiftr01_length]
      rw [← eU, hlen, hasParent_append_gen (by simp [shiftr01])
        (rsum_of_Hd (Fr_topTs _ _) (Fr_shift1 _) hHP), hasParent_shiftr01]
      exact hnp
    · have hzz := ((hz z hz' hbz).2 (hz z hz' hbz).1 us hus).2 u hu Uss hU hG Q hQ
      rw [BotCL_word, HdS.topTs_snoc_ch] at hzz
      have ez : topTs u us ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z)
          = (topTs u us ++ shiftr01 1 0 Z) ++ shiftr01 (h + 1) 0 z := by
        rw [shiftr01_append0, shiftr01_add0, List.append_assoc]
      rwa [ez] at hzz

/-! ## 空のタイ -/

/-- ★ 最上段の道の集合で、並びの最後に空のタイを足す規則。 -/
theorem GdT_tieE {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) (hD : TPSDec P p cl) {v : ℕ}
    {us0 : List UT} (hus : GdT P p cl v us0) : GdT P p cl v (us0 ++ [UT.tie 0 []]) := by
  refine ⟨TreeTs_append.mpr ⟨hus.1, trivial, trivial⟩, fun u' hu' Uss hU hG Q hQ => ?_⟩
  rw [BotCL_word]
  have eT : topTs u' (us0 ++ [UT.tie 0 []]) = topTs u' us0 ++ [((1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rw [eT]
  have hQr := hP.raw u' Q hQ
  have hraw := TreeTs_raw p cl us0 hus.1
  refine HdR.gtc_tie (PathCone_YtopL u' Uss Q hQr) (Fr_append (Fr_topTs _ _) (GzF.Fr_single le_rfl _ _))
    (Hd_app (Hd_topTLs u' us0 hraw) (fun _ => rfl)) (coneV_top (Fr_topTs _ _) u')
    (fun u'' hu'' Z hZ hbZ => ?_) (fun L hC u3 hu3 => CLTL_lift L u' hC u3 hu3)
  rw [mlift_YtopL hu'' (fun us h' => TreeTs_raw 0 true us (hU us h')) hQr,
    mlift_topTLs us0 (TRawLs_mono hu' us0 hraw) u' le_rfl (u'' - u'), show u' + (u'' - u') = u'' by omega]
  have hD2 := GdT_load hP hD Z hZ hbZ us0 (GdT_mono hus (le_trans hu' hu''))
  have := hD2.2 u'' le_rfl Uss (fun us h' => TreeTs_mono hu'' (hU us h'))
    (fun u3 hu3 => hG u3 (le_trans hu'' hu3)) Q (hP.lift u' Q hQ u'' hu'')
  rwa [BotCL_word, HdS.topTs_snoc_ch] at this

/-! ## 空の並び -/

/-- 新しい F のタイ（子の並びは空）。 -/
theorem BotCL_nilF (u : ℕ) (Uss : List (List UT)) (hU : ∀ us ∈ Uss, TreeTs u 0 true us)
    (hG : GoodTTL u Uss) : BotCL u Uss [] [] := by
  show GTC CLTL u (wLT u (Uss ++ [[]], []))
  have e : wLT u (Uss ++ [[]], []) = wLT u (Uss, []) ++ [((1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [wLT, FTL0_snoc, topTs, unitsC, shiftr01]
  rw [e]
  refine GTC_tie (C := CLTL) (coneV_top (Fr_wLT u _) u) (fun u' hu' Z hZ hbZ => ?_)
    (fun L hC u'' hu'' => CLTL_lift L u hC u'' hu'')
  have hR' : ∀ us ∈ Uss, TreeTs u' 0 true us := fun us hus => TreeTs_mono hu' (hU us hus)
  rw [mlift_wLTL hu' (p := (Uss, [])) (fun us h => TreeTs_raw 0 true us (hU us h))
    (by simp [GzJ.NoTie]) (RawU_nil u)]
  have := GTC_load_CLTL (v := u') (Uss := Uss) (us := []) hR' (by simp [GzJ.NoTie]) (RawU_nil u')
    (hG u' hu') Z hZ hbZ
  rwa [show wLT u' (Uss, [] ++ [some Z]) = wLT u' (Uss, []) ++ shiftr01 1 0 Z by
    simp [wLT, unitsC, unitC]] at this

theorem GdT_nil_of {Pc : TPS} {pc : ℕ} {clc : Bool}
    (hdec : ∀ u Q, Pc u Q → Q = [] ∨ ∃ (P' : TPS) (p' : ℕ) (cl' : Bool) (Q' : Path) (us : List UT),
      TPSOK P' p' cl' ∧ TPSDec P' p' cl' ∧ Q = Q' ++ [(us, 0)] ∧ P' u Q' ∧ GdT P' p' cl' u us)
    {v : ℕ} : GdT Pc pc clc v [] := by
  refine ⟨trivial, fun u _ Uss hU hG Q hQ => ?_⟩
  rcases hdec u Q hQ with rfl | ⟨P', p', cl', Q', us, hok, hdc, rfl, hQ', hus⟩
  · exact BotCL_nilF u Uss hU hG
  · rw [BotCL_snoc_eq]
    exact (GdT_tieE hok hdc hus).2 u le_rfl Uss hU hG Q' hQ'

theorem tcl0_dec {B : TPS} (hBok : TPSOK B 0 true) (hBdec : TPSDec B 0 true)
    (hB : ∀ u Q, B u Q → Q = [] ∨ ∃ (P' : TPS) (p' : ℕ) (cl' : Bool) (Q' : Path) (us : List UT),
      TPSOK P' p' cl' ∧ TPSDec P' p' cl' ∧ Q = Q' ++ [(us, 0)] ∧ P' u Q' ∧ GdT P' p' cl' u us) :
    ∀ i u Q, tcl0 B i u Q → Q = [] ∨ ∃ (P' : TPS) (p' : ℕ) (cl' : Bool) (Q' : Path) (us : List UT),
      TPSOK P' p' cl' ∧ TPSDec P' p' cl' ∧ Q = Q' ++ [(us, 0)] ∧ P' u Q' ∧ GdT P' p' cl' u us
  | 0, u, Q, h => hB u Q h
  | i + 1, u, Q, h => by
      rcases h with h | ⟨Q', us, rfl, hQ', hus⟩
      · exact tcl0_dec hBok hBdec hB i u Q h
      · exact Or.inr ⟨tcl0 B i, 0, true, Q', us, TPSOK_tcl0 hBok i, TPSDec_tcl0 hBdec i, rfl, hQ', hus⟩
where
  TPSDec_tcl0 {B : TPS} (hBdec : TPSDec B 0 true) : ∀ i, TPSDec (tcl0 B i) 0 true
    | 0 => hBdec
    | i + 1 => by
        intro u Q hQ
        rcases hQ with hQ | ⟨Q', us, rfl, hQ', hus⟩
        · rcases TPSDec_tcl0 hBdec i u Q hQ with h | ⟨P', p', cl', Q', us0, l', rfl, hQ', hus0, hX, hT⟩
          · exact Or.inl h
          · exact Or.inr ⟨P', p', cl', Q', us0, l', rfl, hQ', hus0, TExt_mono hX (fun _ _ h => Or.inl h), hT⟩
        · exact Or.inr ⟨tcl0 B i, 0, true, Q', us, 0, rfl, hQ', hus,
            fun _ Q'' us' hQ'' hus' => Or.inr ⟨Q'', us', rfl, hQ'', hus'⟩, TieOK_zero 0 true⟩

/-- ★ F のタイの子の位置の空の並び。 -/
theorem GdT_nil_TP0 {v : ℕ} : GdT TP0 0 true v [] :=
  GdT_nil_of (fun u Q ⟨i, hi⟩ => tcl0_dec TPSOK_TPNil TPSDec_TPNil (fun _ _ h => Or.inl h) i u Q hi)

/-- ★ タイの子の位置の空の並び。 -/
theorem GdT_nil_tchS0 {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) (hD : TPSDec P p cl) {v : ℕ} :
    GdT (tchS0 P p cl) 0 true v [] := by
  refine GdT_nil_of (fun u Q ⟨i, hi⟩ =>
    tcl0_dec (TPSOK_text1 hP (TieOK_zero p cl)) (TPSDec_text1 P (TieOK_zero p cl)) ?_ i u Q hi)
  rintro u' Q' ⟨Q'', us, rfl, hQ'', hus⟩
  exact Or.inr ⟨P, p, cl, Q'', us, hP, hD, rfl, hQ'', hus⟩

end HeM
end TRIO
