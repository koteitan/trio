/-
HdS.lean: 最上段の F のタイの子の木の規則（荷・空のタイ）と、木の単位の語の並びの良さ（HcS の後半の写し）。

- DT_load: 高さ t の並びの最後に荷 Z（based_Wg_ind。flat は F のタイまたは道の最後のタイの複製）。
- DT_tieE: 高さ t の並びの最後に空のタイ（gtc_tie、荷は上の段で DT_load）。
- DT_allL / GoodTT_all: 木（荷は Wg の based）の並びは全ての高さで良い。starOK_CLT: 行の定理の形。
-/
import HdR

namespace TRIO
namespace HdS

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdL HdM HdN HdO HdP HdQ HdR

theorem BotC_word (u : ℕ) (Uss Q : List (List UT)) (T : List UT) :
    BotC u Uss Q T = GTC CLT u (wLT u (Uss ++ [plugQ Q []], []) ++ shiftr01 (Q.length + 1) 0 (topTs u T)) := by
  unfold BotC; rw [wLT_plugQ]

theorem topTs_snoc_ch (u : ℕ) (us : List UT) (Z : TrioSeq) :
    topTs u (us ++ [UT.ch Z]) = topTs u us ++ shiftr01 1 0 Z := by
  simp [topTs_append, topTs, topT]

theorem topTs_snoc_tie (u : ℕ) (us cs : List UT) :
    topTs u (us ++ [UT.tie cs]) = topTs u us ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u cs) := by
  simp [topTs_append, topTs, topT]

theorem topTs_rep_tie (u : ℕ) (us0 y : List UT) : ∀ n,
    topTs u (us0 ++ List.replicate n (UT.tie y))
      = topTs u us0 ++ (List.range n).flatMap (fun _ => ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u y))
  | 0 => by simp
  | n + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, topTs_snoc_tie, topTs_rep_tie u us0 y n,
        List.range_succ, List.flatMap_append]
      simp

theorem based_snoc0 {Z : TrioSeq} (hb : based Z) : based (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) := by
  by_cases hZ : Z = []
  · subst hZ; rfl
  · show entry (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) 0 0 = 0
    rw [Small.entry_append_left (List.length_pos_iff.mpr hZ)]; exact hb

/-! ## 荷 -/

/-- ★ 最上段の高さ t の並びの最後に荷を足す規則。 -/
theorem DT_load {v : ℕ} : ∀ Z ∈ Wg (2 * v), based Z →
    ∀ (t : ℕ) (us : List UT), DT t v us → DT t v (us ++ [UT.ch Z]) := by
  have key := based_Wg_ind (u := v)
    (Q := fun Z => Z ∈ Wg (2 * v) → ∀ (t : ℕ) (us : List UT), DT t v us → DT t v (us ++ [UT.ch Z]))
    ?_ ?_ ?_ ?_
  · exact fun Z hZ hb => key Z hZ hb hZ
  · -- nil
    intro _ t us hus
    refine ⟨TRaws_snoc.mpr ⟨hus.1, Wg_nil _, based_nil⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    have := hus.2 u hu Uss hU hG Q hQ
    rw [BotC_word] at this ⊢
    rwa [topTs_snoc_ch, show shiftr01 1 0 ([] : TrioSeq) = [] from rfl, List.append_nil]
  · -- flat
    intro Z hZW hbZ hIH hZW' t us hus
    have hDZ := hIH hZW t us hus
    refine ⟨TRaws_snoc.mpr ⟨hus.1, hZW', based_snoc0 hbZ⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    have hVF : Fr (topTs u us ++ shiftr01 1 0 Z) := Fr_append (Fr_topTs _ _) (Fr_shift1 Z)
    cases t with
    | zero =>
        simp only [PT] at hQ
        subst hQ
        rw [BotC_word, topTs_snoc_ch]
        obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
            M = ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u us ++ shiftr01 1 0 Z) := ⟨_, rfl⟩
        have eW : wLT u (Uss ++ [plugQ [] []], []) ++
              shiftr01 (([] : List (List UT)).length + 1) 0 (topTs u us ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
            = FTL0 (u + 1) (Uss.map (topTs u)) ++ M ++ [((1 + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [hM]; simp [wLT, FTL0_snoc, plugQ, topTs, unitsC, shiftr01]
        rw [eW]
        refine gtc_flat (by rw [hM]; simp) (by rw [hM]; rfl) ?_ (fun n => ?_)
        · intro r' hr1 hr2
          obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
          have hw : w < (topTs u us ++ shiftr01 1 0 Z).length := by
            rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
          rw [hM, entry_cons, entry0_shiftr01 hw]
          have := getD_row0_ge hVF hw
          omega
        · have hGn : ∀ n, (∀ us' ∈ Uss ++ List.replicate n (us ++ [UT.ch Z]), TRaws u us') ∧
              GoodTT u (Uss ++ List.replicate n (us ++ [UT.ch Z])) := by
            intro n
            induction n with
            | zero => simpa using And.intro hU hG
            | succ n ih =>
                rw [List.replicate_succ', ← List.append_assoc]
                refine ⟨fun us' h' => ?_, ?_⟩
                · rcases List.mem_append.mp h' with h' | h'
                  · exact ih.1 us' h'
                  · simp at h'; subst h'; exact TRaws_mono hu _ hDZ.1
                · have := DT_good hDZ hu ih.1 ih.2 (Q := []) rfl
                  simpa [plugQ] using this
          have := (hGn n).2 u le_rfl
          have eR : wLT u (Uss ++ List.replicate n (us ++ [UT.ch Z]), [])
              = FTL0 (u + 1) (Uss.map (topTs u)) ++ (List.range n).flatMap (fun _ => M) := by
            show FTL0 (u + 1) ((Uss ++ List.replicate n (us ++ [UT.ch Z])).map (topTs u)) ++
              unitsC u ([] : List (Option TrioSeq)) = _
            rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil, List.map_append,
              List.map_replicate, FTL0_rep, topTs_snoc_ch, hM]
          rwa [eR] at this
    | succ t' =>
        obtain ⟨Q', us0, rfl, hQ', hus0⟩ := hQ
        rw [BotC_snoc_eq, BotC_word, topTs_snoc_tie, topTs_snoc_ch]
        obtain ⟨d', hd'⟩ : ∃ d', d' = Q'.length + 1 := ⟨_, rfl⟩
        rw [← hd']
        obtain ⟨M, hM⟩ : ∃ M : TrioSeq, M = shiftr01 d' 0 (((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (topTs u us ++ shiftr01 1 0 Z)) := ⟨_, rfl⟩
        have eG : wLT u (Uss ++ [plugQ Q' []], []) ++ shiftr01 d' 0 (topTs u us0 ++
              ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u us ++
                shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            = (wLT u (Uss ++ [plugQ Q' []], []) ++ shiftr01 d' 0 (topTs u us0)) ++ M ++
                [((d' + 1 + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [hM]
          simp [shiftr01] <;> omega
        rw [eG]
        refine gtc_flat (by rw [hM]; simp [shiftr01]) ?_ ?_ (fun n => ?_)
        · rw [hM, entry0_shiftr01 (by simp)]; show 1 + d' = d' + 1; omega
        · intro r' hr1 hr2
          obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
          have hw : w < (topTs u us ++ shiftr01 1 0 Z).length := by
            rw [hM] at hr2; simp only [shiftr01_length, List.length_cons] at hr2; omega
          have hr2' : w + 1 < (((1, u + 1, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (topTs u us ++ shiftr01 1 0 Z)).length := by
            simp only [shiftr01_length, List.length_cons]; omega
          rw [hM, entry0_shiftr01 hr2', entry_cons, entry0_shiftr01 hw]
          have := getD_row0_ge hVF hw
          omega
        · have hrep : DT t' u (us0 ++ List.replicate n (UT.tie (us ++ [UT.ch Z]))) := by
            induction n with
            | zero => simpa using hus0
            | succ n ih => rw [List.replicate_succ', ← List.append_assoc]; exact DT_jump hDZ hu ih
          have := hrep.2 u le_rfl Uss hU hG Q' hQ'
          rw [BotC_word, topTs_rep_tie, topTs_snoc_ch, ← hd'] at this
          have eF : ∀ (l : List ℕ) (g : ℕ → TrioSeq),
              shiftr01 d' 0 (l.flatMap g) = l.flatMap (fun i => shiftr01 d' 0 (g i)) := by
            intro l g; simp [shiftr01, List.map_flatMap]
          rw [shiftr01_append0, eF] at this
          rw [hM]
          simp only [List.append_assoc] at this ⊢
          exact this
  · -- oper
    intro Z hZW hbZ hlen hp hIH hZW' t us hus
    refine ⟨TRaws_snoc.mpr ⟨hus.1, hZW', hbZ⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [BotC_word, topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc]
    refine gtc_oper hlen hp (fun n hn => ?_)
    have := ((hIH n hn).2 (hIH n hn).1 t us hus).2 u hu Uss hU hG Q hQ
    rwa [BotC_word, topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc] at this
  · -- orph
    intro Z h j hZW hbZ hj1 hjv hnp hz hZW' t us hus
    refine ⟨TRaws_snoc.mpr ⟨hus.1, hZW', hbZ⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [BotC_word, topTs_snoc_ch]
    have eU : topTs u us ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
        = (topTs u us ++ shiftr01 1 0 Z) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
    rw [eU]
    have hHP : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := HcS.Hd_shift1_based hbZ
    refine gtc_orph (PathCone_Ytop u Uss Q (PT_raw hQ))
      (by rw [← eU]; exact Hd_app (Hd_topTs u us hus.1) hHP) hj1 (by omega) ?_ (fun z hz' hbz => ?_)
    · have hlen : (topTs u us ++ shiftr01 1 0 Z).length = (topTs u us).length + Z.length := by
        simp only [List.length_append, shiftr01_length]
      rw [← eU, hlen, hasParent_append_gen (by simp [shiftr01])
        (rsum_of_Hd (Fr_topTs _ _) (Fr_shift1 _) hHP), hasParent_shiftr01]
      exact hnp
    · have hzz := ((hz z hz' hbz).2 (hz z hz' hbz).1 t us hus).2 u hu Uss hU hG Q hQ
      rw [BotC_word, topTs_snoc_ch] at hzz
      have ez : topTs u us ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z)
          = (topTs u us ++ shiftr01 1 0 Z) ++ shiftr01 (h + 1) 0 z := by
        rw [shiftr01_append0, shiftr01_add0, List.append_assoc]
      rwa [ez] at hzz

/-! ## 空のタイ -/

/-- ★ 最上段の高さ t の並びの最後に空のタイを足す規則。 -/
theorem DT_tieE {t u : ℕ} {us0 : List UT} (hus : DT t u us0) : DT t u (us0 ++ [UT.tie []]) := by
  refine ⟨TRaws_snoc.mpr ⟨hus.1, trivial⟩, fun u' hu' Uss hU hG Q hQ => ?_⟩
  rw [BotC_word]
  have eT : topTs u' (us0 ++ [UT.tie []]) = topTs u' us0 ++ [((1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rw [eT]
  have hQr := PT_raw hQ
  refine gtc_tie (PathCone_Ytop u' Uss Q hQr) (Fr_append (Fr_topTs _ _) (GzF.Fr_single le_rfl _ _))
    (Hd_app (Hd_topTs u' us0 hus.1) (fun _ => rfl)) (coneV_top (Fr_topTs _ _) u')
    (fun u'' hu'' Z hZ hbZ => ?_) (fun L hC u3 hu3 => CLT_lift L u' hC u3 hu3)
  rw [mlift_Ytop hu'' hU hQr, mlift_topTs us0 hus.1 u' hu' (u'' - u'), show u' + (u'' - u') = u'' by omega]
  have hD := DT_load Z hZ hbZ t us0 (DT_mono hus (le_trans hu' hu''))
  have := hD.2 u'' le_rfl Uss (fun us h' => TRaws_mono hu'' us (hU us h'))
    (fun u3 hu3 => hG u3 (le_trans hu'' hu3)) Q (PT_mono hQ hu'')
  rwa [BotC_word, topTs_snoc_ch] at this

theorem DT_nilS {t v : ℕ} : DT (t + 1) v [] :=
  DT_of_jump trivial (fun _ _ us0 hus0 => DT_tieE hus0)

theorem DT_nil : ∀ (t v : ℕ), DT t v []
  | 0, v => DT_nil0 v
  | _ + 1, _ => DT_nilS

/-! ## 全ての木 -/

mutual
theorem DT_allU {v : ℕ} : ∀ (x : UT) (t : ℕ) (pre : List UT), TRaw v x → DT t v pre →
    DT t v (pre ++ [x])
  | .ch Z, t, pre, hx, hpre => DT_load Z hx.1 hx.2 t pre hpre
  | .tie cs, t, pre, hx, hpre => by
      have hcs := DT_allL (v := v) cs (t + 1) [] hx (DT_nil (t + 1) v)
      rw [List.nil_append] at hcs
      exact DT_tie hpre hcs
theorem DT_allL {v : ℕ} : ∀ (us : List UT) (t : ℕ) (pre : List UT), TRaws v us → DT t v pre →
    DT t v (pre ++ us)
  | [], _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, t, pre, hx, hpre => by
      have := DT_allL (v := v) us t (pre ++ [x]) hx.2 (DT_allU (v := v) x t pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
end

theorem GoodTT_nil (v : ℕ) : GoodTT v [] := by
  intro u _
  have e : wLT u ([], []) = GzJ.fwTop u [] := by simp [wLT, FTL0, GzJ.fwTop, unitsC]
  rw [e]; exact GTC_far_CLT u

/-- ★ 木の単位の F のタイの子の並びの語は良い。 -/
theorem GoodTT_all {v : ℕ} : ∀ Uss : List (List UT), (∀ us ∈ Uss, TRaws v us) → GoodTT v Uss := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact GoodTT_nil v
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TRaws v us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      have hD := DT_allL (v := v) us 0 [] hus (DT_nil 0 v)
      rw [List.nil_append] at hD
      have := DT_good hD le_rfl h' (ih h') (Q := []) rfl
      simpa [plugQ] using this

theorem GTC_wLT {v : ℕ} {Uss : List (List UT)} (hU : ∀ us ∈ Uss, TRaws v us) (hG : GoodTT v Uss) :
    ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us → GTC CLT v (wLT v (Uss, us)) := by
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
          exact GTC_load_CLT hU hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-! ## 並び -/

theorem BwT_CLT (v : ℕ) : ∀ ps : List (List (List UT) × List (Option TrioSeq)),
    PsLT v ps → BwT v (ps.map (wLT v)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro _; exact BwT_nil v
  | append_singleton ps p ih =>
      intro h
      have h' : PsLT v ps := fun q hq => h q (List.mem_append_left _ hq)
      have hp := h p (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := GTC_wLT hp.1 (GoodTT_all p.1 hp.1) p.2 hp.2.1 hp.2.2
      have := hG _ ⟨ps, h', rfl⟩ (Fr_CLT v ps) (ih h')
      rw [List.map_append, List.map_singleton]
      exact this

/-- ★ F のタイの子に木の単位を持つ語の並びと、そのあとに TF の語の並び。 -/
theorem starOK_CLT {v : ℕ} (ps : List (List (List UT) × List (Option TrioSeq)))
    (h : PsLT v ps) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (ps.map (wLT v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CLT v ps) (BwT_CLT v ps h) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HdS
end TRIO
