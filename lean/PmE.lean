/-
PmE.lean: 主な証明側（GTC 側）の GdT の仕組みを、第 1 成分を木のクラス TX にして写す（PmB の写し）。
そのあと、許される集合全部の和集合 U0 で「任意の接頭辞の後ろの深い葉」と本定理。
-/
import PmD

namespace TRIO
namespace PmE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeK
open PmB (deepU)
open PmC PmD

/-! ## HeL の写し: 道の集合と GdT（第 1 成分 = TX） -/

open HeB HeC

abbrev TPS := ℕ → Path → Prop

/-- ★ 最上段の道の集合 P の全ての道の下で良い木の並び。 -/
def GdT (P : TPS) (p : ℕ) (cl : Bool) (v : ℕ) (x : List UT) : Prop :=
  TX v p cl x ∧ ∀ u, v ≤ u → ∀ Uss, WOK u Uss → HeL.GoodTTL u Uss →
    ∀ Q, P u Q → HeL.BotCL u Uss Q x

theorem GdT_mono {P : TPS} {p : ℕ} {cl : Bool} {v v' : ℕ} {x : List UT} (h : GdT P p cl v x)
    (hv : v ≤ v') : GdT P p cl v' x :=
  ⟨TX_mono hv h.1, fun u hu => h.2 u (le_trans hv hu)⟩

theorem GdT_sub {P P' : TPS} (hPP : ∀ u Q, P' u Q → P u Q) {p : ℕ} {cl : Bool} {v : ℕ} {x : List UT}
    (h : GdT P p cl v x) : GdT P' p cl v x :=
  ⟨h.1, fun u hu Uss hU hG Q hQ => h.2 u hu Uss hU hG Q (hPP u Q hQ)⟩

structure TPSOK (P : TPS) (p : ℕ) (cl : Bool) : Prop where
  tree : ∀ u Q, P u Q → ∀ T, TX u p cl T → ∀ Uss, WOK u Uss → WOK u (Uss ++ [plugQ Q T])
  raw : ∀ u Q, P u Q → ∀ q ∈ Q, TRawLs u q.1
  lift : ∀ u Q, P u Q → ∀ u', u ≤ u' → P u' Q

def TExt (P : TPS) (p : ℕ) (cl : Bool) (l : ℕ) (Pc : TPS) : Prop :=
  ∀ u Q us, P u Q → GdT P p cl u us → Pc u (Q ++ [(us, l)])

def TieOK (p : ℕ) (cl : Bool) (l pc : ℕ) (clc : Bool) : Prop :=
  ∀ v us cs, TX v p cl us → TX v pc clc cs → TX v p cl (us ++ [UT.tie l cs])

theorem TieOK_zero (p : ℕ) (cl : Bool) : TieOK p cl 0 0 true := fun _ _ _ hu hc => TX.tie0 hu hc

theorem TieOK_up {p l : ℕ} (hpl : p < l + 1) : TieOK p true (l + 1) (l + 1) false :=
  fun _ _ _ hu hc => TX.up hu hpl hc

theorem GdT_good {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) {v : ℕ} {x : List UT}
    (h : GdT P p cl v x) {u : ℕ} (hvu : v ≤ u) {Uss : List (List UT)}
    (hU : WOK u Uss) (hG : HeL.GoodTTL u Uss) {Q : Path} (hQ : P u Q) :
    HeL.GoodTTL u (Uss ++ [plugQ Q x]) :=
  fun u' hu' => h.2 u' (le_trans hvu hu') Uss (WOK_mono hu' hU)
    (fun u'' hu'' => hG u'' (le_trans hu' hu'')) Q (hP.lift _ _ hQ u' hu')

/-- ★ 延長の集合で良い子の並び cs を、段 l の節点の子として足す。 -/
theorem GdT_jump {P Pc : TPS} {p pc : ℕ} {cl clc : Bool} {l : ℕ} (hX : TExt P p cl l Pc)
    (hT : TieOK p cl l pc clc) {v : ℕ} {cs : List UT} (h : GdT Pc pc clc v cs) {us0 : List UT}
    (hus : GdT P p cl v us0) : GdT P p cl v (us0 ++ [UT.tie l cs]) := by
  refine ⟨hT v us0 cs hus.1 h.1, fun u hu Uss hU hG Q hQ => ?_⟩
  rw [← HeL.BotCL_snoc_eq]
  exact h.2 u hu Uss hU hG (Q ++ [(us0, l)]) (hX u Q us0 hQ (GdT_mono hus hu))

/-! ## 集合の作り方 -/

def text1 (P : TPS) (p : ℕ) (cl : Bool) (l : ℕ) : TPS := fun u Q =>
  ∃ Q' us, Q = Q' ++ [(us, l)] ∧ P u Q' ∧ GdT P p cl u us

def tcl0 (B : TPS) : ℕ → TPS
  | 0 => B
  | i + 1 => fun u Q => tcl0 B i u Q ∨ text1 (tcl0 B i) 0 true 0 u Q

def tclS (B : TPS) : TPS := fun u Q => ∃ i, tcl0 B i u Q

def TPNil : TPS := fun _ Q => Q = []

def TP0 : TPS := tclS TPNil

def tchS0 (P : TPS) (p : ℕ) (cl : Bool) : TPS := tclS (text1 P p cl 0)

def tchU (P : TPS) (p l : ℕ) : TPS := text1 P p true l

theorem TExt_text1 (P : TPS) (p : ℕ) (cl : Bool) (l : ℕ) : TExt P p cl l (text1 P p cl l) :=
  fun _ Q us hQ hus => ⟨Q, us, rfl, hQ, hus⟩

theorem TExt_mono {P Pc Pc' : TPS} {p : ℕ} {cl : Bool} {l : ℕ} (h : TExt P p cl l Pc)
    (hsub : ∀ u Q, Pc u Q → Pc' u Q) : TExt P p cl l Pc' :=
  fun u Q us hQ hus => hsub _ _ (h u Q us hQ hus)

theorem tcl0_sub (B : TPS) (i : ℕ) : ∀ u Q, tcl0 B i u Q → tclS B u Q := fun _ _ h => ⟨i, h⟩

theorem B_sub_tclS (B : TPS) : ∀ u Q, B u Q → tclS B u Q := fun _ _ h => ⟨0, h⟩

/-- ★ 閉包は段 0 の延長で閉じる。 -/
theorem tclS_closed (B : TPS) : TExt (tclS B) 0 true 0 (tclS B) := by
  intro u Q us hQ hus
  obtain ⟨i, hi⟩ := hQ
  exact ⟨i + 1, Or.inr ⟨Q, us, rfl, hi, GdT_sub (tcl0_sub B i) hus⟩⟩

theorem TExt_tchS0 (P : TPS) (p : ℕ) (cl : Bool) : TExt P p cl 0 (tchS0 P p cl) :=
  TExt_mono (TExt_text1 P p cl 0) (B_sub_tclS _)

theorem TExt_tchU (P : TPS) (p l : ℕ) : TExt P p true l (tchU P p l) := TExt_text1 P p true l

theorem TPNil_TP0 (u : ℕ) : TP0 u [] := ⟨0, rfl⟩

/-! ## TPSOK -/

theorem TPSOK_text1 {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) {l pc : ℕ} {clc : Bool}
    (hT : TieOK p cl l pc clc) : TPSOK (text1 P p cl l) pc clc where
  tree := by
    rintro u Q ⟨Q', us, rfl, hQ', hus⟩ T hT' Uss hU
    rw [plugQ_snoc]
    exact hP.tree u Q' hQ' _ (hT u us T hus.1 hT') Uss hU
  raw := by
    rintro u Q ⟨Q', us, rfl, hQ', hus⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hP.raw u Q' hQ' q hq
    · simp at hq; subst hq; exact TX_raw hus.1
  lift := by
    rintro u Q ⟨Q', us, rfl, hQ', hus⟩ u' hu
    exact ⟨Q', us, rfl, hP.lift u Q' hQ' u' hu, GdT_mono hus hu⟩

theorem TPSOK_tcl0 {B : TPS} (hB : TPSOK B 0 true) : ∀ i, TPSOK (tcl0 B i) 0 true
  | 0 => hB
  | i + 1 => by
      have ih := TPSOK_tcl0 hB i
      have hx := TPSOK_text1 ih (TieOK_zero 0 true)
      refine ⟨fun u Q h => ?_, fun u Q h => ?_, fun u Q h => ?_⟩
      · rcases h with h | h
        · exact ih.tree u Q h
        · exact hx.tree u Q h
      · rcases h with h | h
        · exact ih.raw u Q h
        · exact hx.raw u Q h
      · intro u' hu
        rcases h with h | h
        · exact Or.inl (ih.lift u Q h u' hu)
        · exact Or.inr (hx.lift u Q h u' hu)

theorem TPSOK_tclS {B : TPS} (hB : TPSOK B 0 true) : TPSOK (tclS B) 0 true where
  tree := fun u Q ⟨i, h⟩ => (TPSOK_tcl0 hB i).tree u Q h
  raw := fun u Q ⟨i, h⟩ => (TPSOK_tcl0 hB i).raw u Q h
  lift := fun u Q ⟨i, h⟩ u' hu => ⟨i, (TPSOK_tcl0 hB i).lift u Q h u' hu⟩

theorem TPSOK_TPNil : TPSOK TPNil 0 true where
  tree := by intro u Q h T hT Uss hU; simp only [TPNil] at h; subst h; exact PmD.WOK_snoc_TX hU hT
  raw := by intro u Q h q hq; simp only [TPNil] at h; subst h; simp at hq
  lift := by intro u Q h u' _; exact h

theorem TPSOK_TP0 : TPSOK TP0 0 true := TPSOK_tclS TPSOK_TPNil

theorem TPSOK_tchS0 {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) : TPSOK (tchS0 P p cl) 0 true :=
  TPSOK_tclS (TPSOK_text1 hP (TieOK_zero p cl))

theorem TPSOK_tchU {P : TPS} {p l : ℕ} (hP : TPSOK P p true) (hpl : p < l + 1) :
    TPSOK (tchU P p (l + 1)) (l + 1) false := TPSOK_text1 hP (TieOK_up hpl)

/-! ## 分解 -/

def TPSDec (P : TPS) (p : ℕ) (cl : Bool) : Prop :=
  ∀ u Q, P u Q → Q = [] ∨ ∃ (P' : TPS) (p' : ℕ) (cl' : Bool) (Q' : Path) (us0 : List UT) (l : ℕ),
    Q = Q' ++ [(us0, l)] ∧ P' u Q' ∧ GdT P' p' cl' u us0 ∧ TExt P' p' cl' l P ∧ TieOK p' cl' l p cl

theorem TPSDec_text1 (P : TPS) {p : ℕ} {cl : Bool} {l pc : ℕ} {clc : Bool} (hT : TieOK p cl l pc clc) :
    TPSDec (text1 P p cl l) pc clc := by
  rintro u Q ⟨Q', us, rfl, hQ', hus⟩
  exact Or.inr ⟨P, p, cl, Q', us, l, rfl, hQ', hus, TExt_text1 P p cl l, hT⟩

theorem TPSDec_tclS {B : TPS} (hB : TPSDec B 0 true) : TPSDec (tclS B) 0 true := by
  rintro u Q ⟨i, hi⟩
  induction i generalizing Q with
  | zero =>
      rcases hB u Q hi with h | ⟨P', p', cl', Q', us0, l', rfl, hQ', hus, hX, hT⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', p', cl', Q', us0, l', rfl, hQ', hus, TExt_mono hX (B_sub_tclS B), hT⟩
  | succ i ih =>
      rcases hi with hi | ⟨Q', us, rfl, hQ', hus⟩
      · exact ih Q hi
      · refine Or.inr ⟨tcl0 B i, 0, true, Q', us, 0, rfl, hQ', hus, ?_, TieOK_zero 0 true⟩
        intro u' Q'' us' hQ'' hus'
        exact ⟨i + 1, Or.inr ⟨Q'', us', rfl, hQ'', hus'⟩⟩

theorem TPSDec_TPNil : TPSDec TPNil 0 true := fun _ _ h => Or.inl h

theorem TPSDec_TP0 : TPSDec TP0 0 true := TPSDec_tclS TPSDec_TPNil

theorem TPSDec_tchS0 (P : TPS) (p : ℕ) (cl : Bool) : TPSDec (tchS0 P p cl) 0 true :=
  TPSDec_tclS (TPSDec_text1 P (TieOK_zero p cl))

theorem TPSDec_tchU (P : TPS) {p l : ℕ} (hpl : p < l + 1) : TPSDec (tchU P p (l + 1)) (l + 1) false :=
  TPSDec_text1 P (TieOK_up hpl)

/-! ## 最後の段 -/

def TLast (P : TPS) (p : ℕ) : Prop := ∀ u Q, P u Q → HeC.lastL Q = p

theorem TLast_text1 (P : TPS) (p : ℕ) (cl : Bool) (l : ℕ) : TLast (text1 P p cl l) l := by
  rintro u Q ⟨Q', us, rfl, -, -⟩
  exact HeC.lastL_snoc Q' us l

theorem TLast_tclS {B : TPS} (hB : TLast B 0) : TLast (tclS B) 0 := by
  rintro u Q ⟨i, hi⟩
  induction i generalizing Q with
  | zero => exact hB u Q hi
  | succ i ih =>
      rcases hi with hi | ⟨Q', us, rfl, -, -⟩
      · exact ih Q hi
      · exact HeC.lastL_snoc Q' us 0

theorem TLast_TP0 : TLast TP0 0 := TLast_tclS (fun _ Q h => by simp only [TPNil] at h; subst h; rfl)

theorem TLast_tchS0 (P : TPS) (p : ℕ) (cl : Bool) : TLast (tchS0 P p cl) 0 := TLast_tclS (TLast_text1 P p cl 0)

theorem TLast_tchU (P : TPS) (p l : ℕ) : TLast (tchU P p l) l := TLast_text1 P p true l

theorem TP0_closed : TExt TP0 0 true 0 TP0 := tclS_closed TPNil

theorem tchS0_closed (P : TPS) (p : ℕ) (cl : Bool) : TExt (tchS0 P p cl) 0 true 0 (tchS0 P p cl) :=
  tclS_closed _


/-! ## HeM の写し: 荷・空のタイの規則と空の並び -/

open HeG HeI

/-- ★ 最上段の道の集合で、並びの最後に荷を足す規則。 -/
theorem GdT_load {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) (hD : TPSDec P p cl) {v : ℕ} :
    ∀ Z ∈ Wg (2 * v), based Z → ∀ (us : List UT), GdT P p cl v us → GdT P p cl v (us ++ [UT.ch Z]) := by
  have key := based_Wg_ind (u := v)
    (Q := fun Z => Z ∈ Wg (2 * v) → ∀ (us : List UT), GdT P p cl v us → GdT P p cl v (us ++ [UT.ch Z]))
    ?_ ?_ ?_ ?_
  · exact fun Z hZ hb => key Z hZ hb hZ
  · -- nil
    intro _ us hus
    refine ⟨TX.ch hus.1 (Wg_nil _) based_nil, fun u hu Uss hU hG Q hQ => ?_⟩
    have := hus.2 u hu Uss hU hG Q hQ
    rw [HeL.BotCL_word] at this ⊢
    rwa [HdS.topTs_snoc_ch, show shiftr01 1 0 ([] : TrioSeq) = [] from rfl, List.append_nil]
  · -- flat
    intro Z hZW hbZ hIH hZW' us hus
    have hDZ := hIH hZW us hus
    refine ⟨TX.ch hus.1 hZW' (HdS.based_snoc0 hbZ), fun u hu Uss hU hG Q hQ => ?_⟩
    have hVF : Fr (topTs u us ++ shiftr01 1 0 Z) := Fr_append (Fr_topTs _ _) (Fr_shift1 Z)
    rcases hD u Q hQ with rfl | ⟨P', p', cl', Q', us0, l, rfl, hQ', hus0, hX, hT⟩
    · rw [HeL.BotCL_word, HdS.topTs_snoc_ch]
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
      · have hDZt : TX u p cl (us ++ [UT.ch Z]) := TX_mono hu hDZ.1
        have hGn : ∀ n, WOK u (Uss ++ List.replicate n (us ++ [UT.ch Z])) ∧
            HeL.GoodTTL u (Uss ++ List.replicate n (us ++ [UT.ch Z])) := by
          intro n
          induction n with
          | zero => simpa using And.intro hU hG
          | succ n ih =>
              rw [List.replicate_succ', ← List.append_assoc]
              refine ⟨by simpa [plugQ] using hP.tree u [] hQ _ hDZt _ ih.1, ?_⟩
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
    · rw [HeL.BotCL_snoc_eq, HeL.BotCL_word, HeM.topTs_snoc_tieL, HdS.topTs_snoc_ch]
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
        rw [HeL.BotCL_word, HeM.topTs_rep_tieL, HdS.topTs_snoc_ch, ← hd'] at this
        have eF : ∀ (l' : List ℕ) (g : ℕ → TrioSeq),
            shiftr01 d' 0 (l'.flatMap g) = l'.flatMap (fun i => shiftr01 d' 0 (g i)) := by
          intro l' g; simp [shiftr01, List.map_flatMap]
        rw [shiftr01_append0, eF] at this
        rw [hM]
        simp only [List.append_assoc] at this ⊢
        exact this
  · -- oper
    intro Z hZW hbZ hlen hp hIH hZW' us hus
    refine ⟨TX.ch hus.1 hZW' hbZ, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc]
    refine HdR.gtc_oper hlen hp (fun n hn => ?_)
    have := ((hIH n hn).2 (hIH n hn).1 us hus).2 u hu Uss hU hG Q hQ
    rwa [HeL.BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc] at this
  · -- orph
    intro Z h j hZW hbZ hj1 hjv hnp hz hZW' us hus
    refine ⟨TX.ch hus.1 hZW' hbZ, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch]
    have eU : topTs u us ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
        = (topTs u us ++ shiftr01 1 0 Z) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
    rw [eU]
    have hHP : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := HcS.Hd_shift1_based hbZ
    refine HdR.gtc_orph (HeL.PathCone_YtopL u Uss Q (hP.raw u Q hQ))
      (by rw [← eU]; exact Hd_app (Hd_topTLs u us (TX_raw hus.1)) hHP) hj1 (by omega) ?_
      (fun z hz' hbz => ?_)
    · have hlen : (topTs u us ++ shiftr01 1 0 Z).length = (topTs u us).length + Z.length := by
        simp only [List.length_append, shiftr01_length]
      rw [← eU, hlen, hasParent_append_gen (by simp [shiftr01])
        (rsum_of_Hd (Fr_topTs _ _) (Fr_shift1 _) hHP), hasParent_shiftr01]
      exact hnp
    · have hzz := ((hz z hz' hbz).2 (hz z hz' hbz).1 us hus).2 u hu Uss hU hG Q hQ
      rw [HeL.BotCL_word, HdS.topTs_snoc_ch] at hzz
      have ez : topTs u us ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z)
          = (topTs u us ++ shiftr01 1 0 Z) ++ shiftr01 (h + 1) 0 z := by
        rw [shiftr01_append0, shiftr01_add0, List.append_assoc]
      rwa [ez] at hzz

/-! ## 空のタイ -/

/-- ★ 最上段の道の集合で、並びの最後に空のタイを足す規則。 -/
theorem GdT_tieE {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) (hD : TPSDec P p cl) {v : ℕ}
    {us0 : List UT} (hus : GdT P p cl v us0) : GdT P p cl v (us0 ++ [UT.tie 0 []]) := by
  refine ⟨TX.tie0 hus.1 (TX.nil 0 true), fun u' hu' Uss hU hG Q hQ => ?_⟩
  rw [HeL.BotCL_word]
  have eT : topTs u' (us0 ++ [UT.tie 0 []]) = topTs u' us0 ++ [((1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rw [eT]
  have hQr := hP.raw u' Q hQ
  have hraw := TX_raw hus.1
  refine HdR.gtc_tie (HeL.PathCone_YtopL u' Uss Q hQr) (Fr_append (Fr_topTs _ _) (GzF.Fr_single le_rfl _ _))
    (Hd_app (Hd_topTLs u' us0 hraw) (fun _ => rfl)) (coneV_top (Fr_topTs _ _) u')
    (fun u'' hu'' Z hZ hbZ => ?_) (fun L hC u3 hu3 => CLTL_lift L u' hC u3 hu3)
  rw [HeL.mlift_YtopL hu'' hU.1 hQr,
    mlift_topTLs us0 (TRawLs_mono hu' us0 hraw) u' le_rfl (u'' - u'), show u' + (u'' - u') = u'' by omega]
  have hD2 := GdT_load hP hD Z hZ hbZ us0 (GdT_mono hus (le_trans hu' hu''))
  have := hD2.2 u'' le_rfl Uss (WOK_mono hu'' hU)
    (fun u3 hu3 => hG u3 (le_trans hu'' hu3)) Q (hP.lift u' Q hQ u'' hu'')
  rwa [HeL.BotCL_word, HdS.topTs_snoc_ch] at this

/-! ## 空の並び -/

theorem GdT_nil_of {Pc : TPS} {pc : ℕ} {clc : Bool}
    (hdec : ∀ u Q, Pc u Q → Q = [] ∨ ∃ (P' : TPS) (p' : ℕ) (cl' : Bool) (Q' : Path) (us : List UT),
      TPSOK P' p' cl' ∧ TPSDec P' p' cl' ∧ Q = Q' ++ [(us, 0)] ∧ P' u Q' ∧ GdT P' p' cl' u us)
    {v : ℕ} : GdT Pc pc clc v [] := by
  refine ⟨TX.nil _ _, fun u _ Uss hU hG Q hQ => ?_⟩
  rcases hdec u Q hQ with rfl | ⟨P', p', cl', Q', us, hok, hdc, rfl, hQ', hus⟩
  · exact PmB.HeM.BotCL_nilF u Uss hU hG
  · rw [HeL.BotCL_snoc_eq]
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


/-! ## HeN の写し: 塔・上の葉・木の規則 -/

open HeH

theorem GdT_towT {P : TPS} (hcl : TExt P 0 true 0 P) {v : ℕ} {us : List UT} (h : GdT P 0 true v us) :
    ∀ j, GdT P 0 true v (HeH.towT 0 us j)
  | 0 => h
  | j + 1 => GdT_jump hcl (TieOK_zero 0 true) (GdT_towT hcl h j) h

/-- ★ 最上段の上の葉: 段 0 の延長で閉じた集合で、段 l+1 の空の節点を足せる。 -/
theorem GdT_upleaf {P : TPS} (hP : TPSOK P 0 true) (hcl : TExt P 0 true 0 P) (hlast : TLast P 0) {l : ℕ}
    {v : ℕ} {us : List UT} (h : GdT P 0 true v us) : GdT P 0 true v (us ++ [UT.tie (l + 1) []]) := by
  refine ⟨TX.up h.1 (by omega) (TX.nil _ _), fun u hu Uss hU hG Q hQ => ?_⟩
  have hT := GdT_towT hcl h
  have hrep : ∀ j, HeL.BotCL u Uss Q (HeH.towT 0 us j) := fun j => (hT j).2 u hu Uss hU hG Q hQ
  have hDF : Fr (topTs u us) := Fr_topTs u us
  have eT : topTs u (us ++ [UT.tie (l + 1) []])
      = topTs u us ++ [((1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v', p'⟩, rfl⟩
  · have eW : ∀ T : List UT, HeL.BotCL u Uss [] T
        = GTC CLTL u (FTL0 (u + 1) (Uss.map (topTs u)) ++ shiftr01 0 0
            (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      show GTC CLTL u (wLT u (Uss ++ [T], [])) = _
      rw [shiftr01_zero', Nat.add_zero]
      simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc]
      rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil]
    rw [eW, eT]
    refine HeN.upleafT_core hDF (by omega) (fun j => ?_)
    have := hrep j
    rwa [eW, HeN.topTs_towT] at this
  · simp only [List.concat_eq_append] at hQ hrep ⊢
    have hp' : p' = 0 := by have := hlast u _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have eW : ∀ T : List UT, HeL.BotCL u Uss (Q' ++ [(v', 0)]) T
        = GTC CLTL u ((wLT u (Uss ++ [plugQ Q' []], []) ++ shiftr01 (Q'.length + 1) 0 (topTs u v')) ++
            shiftr01 (Q'.length + 1) 0
              (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      rw [HeL.BotCL_snoc_eq, HeL.BotCL_word, HeM.topTs_snoc_tieL, shiftr01_append0, List.append_assoc]
    rw [eW, eT]
    refine HeN.upleafT_core hDF (by omega) (fun j => ?_)
    have := hrep j
    rwa [eW, HeN.topTs_towT] at this

/-- ★ 段 l+1 の節点の子の位置の空の並び（親の集合で上の葉）。 -/
theorem GdT_nil_tchU {P : TPS} (hP : TPSOK P 0 true) (hcl : TExt P 0 true 0 P) (hlast : TLast P 0)
    {l v : ℕ} : GdT (tchU P 0 (l + 1)) (l + 1) false v [] := by
  refine ⟨TX.nil _ _, fun u _ Uss hU hG Q hQ => ?_⟩
  obtain ⟨Q', us, rfl, hQ', hus⟩ := hQ
  rw [HeL.BotCL_snoc_eq]
  exact (GdT_upleaf hP hcl hlast hus).2 u le_rfl Uss hU hG Q' hQ'


/-! ## 許される集合全部の和集合 U0 -/

/-- 許される集合（段 0 の子の位置）。 -/
def Adm (P : TPS) : Prop :=
  TPSOK P 0 true ∧ TPSDec P 0 true ∧ TExt P 0 true 0 P ∧ TLast P 0 ∧ ∀ v, GdT P 0 true v []

/-- ★ 許される集合全部の和集合。 -/
def U0 : TPS := fun u Q => ∃ P, Adm P ∧ P u Q

theorem U0_sub {P : TPS} (hP : Adm P) {p : ℕ} {cl : Bool} {v : ℕ} {x : List UT}
    (h : GdT U0 p cl v x) : GdT P p cl v x :=
  GdT_sub (fun u Q hQ => ⟨P, hP, hQ⟩) h

theorem U0_TPSOK : TPSOK U0 0 true where
  tree := fun u Q ⟨P, hP, hQ⟩ => hP.1.tree u Q hQ
  raw := fun u Q ⟨P, hP, hQ⟩ => hP.1.raw u Q hQ
  lift := fun u Q ⟨P, hP, hQ⟩ u' hu => ⟨P, hP, hP.1.lift u Q hQ u' hu⟩

theorem U0_TPSDec : TPSDec U0 0 true := by
  rintro u Q ⟨P, hP, hQ⟩
  rcases hP.2.1 u Q hQ with h | ⟨P', p', cl', Q', us0, l, h1, h2, h3, h4, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨P', p', cl', Q', us0, l, h1, h2, h3, TExt_mono h4 (fun u Q h => ⟨P, hP, h⟩), h5⟩

theorem U0_closed : TExt U0 0 true 0 U0 := by
  rintro u Q us ⟨P, hP, hQ⟩ hus
  exact ⟨P, hP, hP.2.2.1 u Q us hQ (U0_sub hP hus)⟩

theorem U0_last : TLast U0 0 := fun u Q ⟨P, hP, hQ⟩ => hP.2.2.2.1 u Q hQ

theorem U0_nil {v : ℕ} : GdT U0 0 true v [] := by
  refine ⟨TX.nil _ _, fun u hu Uss hU hG Q hQ => ?_⟩
  obtain ⟨P, hP, hQ⟩ := hQ
  exact (hP.2.2.2.2 v).2 u hu Uss hU hG Q hQ

theorem Adm_tchS0 {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) (hD : TPSDec P p cl) :
    Adm (tchS0 P p cl) :=
  ⟨TPSOK_tchS0 hP, TPSDec_tchS0 P p cl, tchS0_closed P p cl, TLast_tchS0 P p cl,
    fun _ => GdT_nil_tchS0 hP hD⟩

theorem Adm_TP0 : Adm TP0 := ⟨TPSOK_TP0, TPSDec_TP0, TP0_closed, TLast_TP0, fun _ => GdT_nil_TP0⟩

theorem GdT_nil_tchU1 {l v : ℕ} : GdT (tchU U0 0 (l + 1)) (l + 1) false v [] :=
  GdT_nil_tchU U0_TPSOK U0_closed U0_last

theorem TPSOK_tchU1 (l : ℕ) : TPSOK (tchU U0 0 (l + 1)) (l + 1) false := TPSOK_tchU U0_TPSOK (by omega)

theorem TPSDec_tchU1 (l : ℕ) : TPSDec (tchU U0 0 (l + 1)) (l + 1) false := TPSDec_tchU U0 (by omega)

/-! ## 任意の接頭辞の後ろの深い葉 -/

/-- U0 で良い並びの後ろの深い葉の塔は U0 で良い。 -/
theorem GdT_Lt {v : ℕ} {pre : List UT} (h : GdT U0 0 true v pre) : ∀ j, GdT U0 0 true v (Lt pre j)
  | 0 => GdT_upleaf U0_TPSOK U0_closed U0_last h
  | j + 1 => by
      have hin : GdT (tchS0 (tchU U0 0 (0 + 1)) (0 + 1) false) 0 true v (Lt pre j) :=
        U0_sub (Adm_tchS0 (TPSOK_tchU1 0) (TPSDec_tchU1 0)) (GdT_Lt h j)
      have hcs := GdT_jump (TExt_tchS0 (tchU U0 0 (0 + 1)) (0 + 1) false) (TieOK_zero (0 + 1) false) hin
        (GdT_nil_tchU1 (l := 0))
      rw [List.nil_append] at hcs
      exact GdT_jump (TExt_tchU U0 0 (0 + 1)) (TieOK_up (by omega)) hcs h

/-- ★★★ U0 で良い並びの後ろに深い葉を置いても U0 で良い。 -/
theorem GdT_deepAfter {v : ℕ} {pre : List UT} (h : GdT U0 0 true v pre) :
    GdT U0 0 true v (pre ++ [deepU]) := by
  refine ⟨TX.deep h.1, fun u hu Uss hU hG Q hQ => ?_⟩
  have hrep : ∀ j, HeL.BotCL u Uss Q (Lt pre j) := fun j => (GdT_Lt h j).2 u hu Uss hU hG Q hQ
  have eD : topTs u (pre ++ [deepU])
      = topTs u pre ++ [((1, u + 1 + 1, 0) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, deepU, topTs, topT, shiftr01]
  have e1 : (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0
        (topTs u pre ++ [((1, u + 1 + 1, 0) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 0) : ℕ × ℕ × ℕ)]))
      = shiftr01 1 0 (((0, u + 1, 0) : ℕ × ℕ × ℕ) ::
          (topTs u pre ++ [((1, u + 1 + 1, 0) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 0) : ℕ × ℕ × ℕ)])) := by
    simp [shiftr01]
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v', p'⟩, rfl⟩
  · have eW : ∀ T : List UT, HeL.BotCL u Uss [] T
        = GTC CLTL u (FTL0 (u + 1) (Uss.map (topTs u)) ++ shiftr01 0 0
            (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      show GTC CLTL u (wLT u (Uss ++ [T], [])) = _
      rw [shiftr01_zero', Nat.add_zero]
      simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc]
      rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil]
    rw [eW, eD, e1]
    refine upleaf_deep_coreE (C := CLTL) (Fr_topTs u pre) (d := 0) (q := u + 1) (m := u + 1 + 1)
      (by omega) (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [topTs_Lt u pre j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this
  · simp only [List.concat_eq_append] at hQ hrep ⊢
    have hp' : p' = 0 := by have := U0_last u _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have eW : ∀ T : List UT, HeL.BotCL u Uss (Q' ++ [(v', 0)]) T
        = GTC CLTL u ((wLT u (Uss ++ [HeB.plugQ Q' []], []) ++ shiftr01 (Q'.length + 1) 0 (topTs u v')) ++
            shiftr01 (Q'.length + 1) 0
              (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      rw [HeL.BotCL_snoc_eq, HeL.BotCL_word, HeM.topTs_snoc_tieL, shiftr01_append0, List.append_assoc]
    rw [eW, eD, e1]
    refine upleaf_deep_coreE (C := CLTL) (Fr_topTs u pre) (d := Q'.length + 1) (q := u + 1) (m := u + 1 + 1)
      (by omega) (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [topTs_Lt u pre j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this

/-- ★ 深い節点の子の位置（tchU U0 0 1）で先頭の tie 1 [] は良い。 -/
theorem GdT_head1 {v : ℕ} : GdT (tchU U0 0 (0 + 1)) (0 + 1) false v [UT.tie 1 []] := by
  refine ⟨by simpa using TX.same (l := 0) (TX.nil (v := v) 1 false) (TX.nil 1 false),
    fun u hu Uss hU hG Q hQ => ?_⟩
  obtain ⟨Q', us, rfl, hQ', hus⟩ := hQ
  rw [HeL.BotCL_snoc_eq]
  exact (GdT_deepAfter hus).2 u le_rfl Uss hU hG Q' hQ'

/-! ## 深い節点の鎖の位置の集合 SLT -/

theorem TieOK_same (l : ℕ) : TieOK (l + 1) false (l + 1) (l + 1) false := fun _ _ _ hu hc => TX.same hu hc

/-- 段 lv の延長で閉じた閉包（一般の (p, cl)）。 -/
def tcG (B : TPS) (p : ℕ) (cl : Bool) (lv : ℕ) : ℕ → TPS
  | 0 => B
  | i + 1 => fun u Q => tcG B p cl lv i u Q ∨ text1 (tcG B p cl lv i) p cl lv u Q

def tcS (B : TPS) (p : ℕ) (cl : Bool) (lv : ℕ) : TPS := fun u Q => ∃ i, tcG B p cl lv i u Q

theorem TPSOK_tcG {B : TPS} {p : ℕ} {cl : Bool} {lv : ℕ} (hB : TPSOK B p cl) (hT : TieOK p cl lv p cl) :
    ∀ i, TPSOK (tcG B p cl lv i) p cl
  | 0 => hB
  | i + 1 => by
      have ih := TPSOK_tcG hB hT i
      have hx := TPSOK_text1 ih hT
      refine ⟨fun u Q h => ?_, fun u Q h => ?_, fun u Q h => ?_⟩
      · rcases h with h | h
        · exact ih.tree u Q h
        · exact hx.tree u Q h
      · rcases h with h | h
        · exact ih.raw u Q h
        · exact hx.raw u Q h
      · intro u' hu
        rcases h with h | h
        · exact Or.inl (ih.lift u Q h u' hu)
        · exact Or.inr (hx.lift u Q h u' hu)

theorem TPSDec_tcG {B : TPS} {p : ℕ} {cl : Bool} {lv : ℕ} (hB : TPSDec B p cl) (hT : TieOK p cl lv p cl) :
    ∀ i, TPSDec (tcG B p cl lv i) p cl
  | 0 => hB
  | i + 1 => by
      intro u Q hQ
      rcases hQ with hQ | ⟨Q', us, rfl, hQ', hus⟩
      · rcases TPSDec_tcG hB hT i u Q hQ with h | ⟨P', p', cl', Q', us0, l', rfl, hQ', hus0, hX, hT'⟩
        · exact Or.inl h
        · exact Or.inr ⟨P', p', cl', Q', us0, l', rfl, hQ', hus0, TExt_mono hX (fun _ _ h => Or.inl h), hT'⟩
      · exact Or.inr ⟨tcG B p cl lv i, p, cl, Q', us, lv, rfl, hQ', hus,
          fun _ Q'' us' hQ'' hus' => Or.inr ⟨Q'', us', rfl, hQ'', hus'⟩, hT⟩

theorem TPSOK_tcS {B : TPS} {p : ℕ} {cl : Bool} {lv : ℕ} (hB : TPSOK B p cl) (hT : TieOK p cl lv p cl) :
    TPSOK (tcS B p cl lv) p cl where
  tree := fun u Q ⟨i, h⟩ => (TPSOK_tcG hB hT i).tree u Q h
  raw := fun u Q ⟨i, h⟩ => (TPSOK_tcG hB hT i).raw u Q h
  lift := fun u Q ⟨i, h⟩ u' hu => ⟨i, (TPSOK_tcG hB hT i).lift u Q h u' hu⟩

theorem TPSDec_tcS {B : TPS} {p : ℕ} {cl : Bool} {lv : ℕ} (hB : TPSDec B p cl) (hT : TieOK p cl lv p cl) :
    TPSDec (tcS B p cl lv) p cl := by
  rintro u Q ⟨i, hi⟩
  rcases TPSDec_tcG hB hT i u Q hi with h | ⟨P', p', cl', Q', us0, l', rfl, hQ', hus0, hX, hT'⟩
  · exact Or.inl h
  · exact Or.inr ⟨P', p', cl', Q', us0, l', rfl, hQ', hus0, TExt_mono hX (fun _ _ h => ⟨i, h⟩), hT'⟩

theorem TLast_tcS {B : TPS} {p : ℕ} {cl : Bool} {lv : ℕ} (hB : TLast B lv) : TLast (tcS B p cl lv) lv := by
  rintro u Q ⟨i, hi⟩
  induction i generalizing Q with
  | zero => exact hB u Q hi
  | succ i ih =>
      rcases hi with hi | ⟨Q', us, rfl, -, -⟩
      · exact ih Q hi
      · exact HeC.lastL_snoc Q' us lv

theorem tcS_closed (B : TPS) (p : ℕ) (cl : Bool) (lv : ℕ) : TExt (tcS B p cl lv) p cl lv (tcS B p cl lv) := by
  rintro u Q us ⟨i, hi⟩ hus
  exact ⟨i + 1, Or.inr ⟨Q, us, rfl, hi, GdT_sub (fun _ _ h => ⟨i, h⟩) hus⟩⟩

/-- 段 l+1 の節点の子の位置（段 l+1 の延長で閉じる）。 -/
def SLT (l : ℕ) : TPS := tcS (tchU U0 0 (l + 1)) (l + 1) false (l + 1)

theorem SLT_TPSOK (l : ℕ) : TPSOK (SLT l) (l + 1) false := TPSOK_tcS (TPSOK_tchU1 l) (TieOK_same l)

theorem SLT_TPSDec (l : ℕ) : TPSDec (SLT l) (l + 1) false := TPSDec_tcS (TPSDec_tchU1 l) (TieOK_same l)

theorem SLT_closed (l : ℕ) : TExt (SLT l) (l + 1) false (l + 1) (SLT l) := tcS_closed _ _ _ _

theorem tchU_sub_SLT (l : ℕ) : ∀ u Q, tchU U0 0 (l + 1) u Q → SLT l u Q := fun _ _ h => ⟨0, h⟩

/-- ★ 鎖への分解: SLT の段 i の道 = U0 の道 Qr ＋ 段 l+1 の鎖 C。鎖に良い並びを差し込むと U0 で良い。 -/
theorem unplugT (l : ℕ) : ∀ (i u : ℕ) (Q : Path), tcG (tchU U0 0 (l + 1)) (l + 1) false (l + 1) i u Q →
    ∃ Qr C, Q = Qr ++ C ∧ (∀ e ∈ C, e.2 = l + 1) ∧ U0 u Qr ∧
      ∀ Y, GdT (tcG (tchU U0 0 (l + 1)) (l + 1) false (l + 1) i) (l + 1) false u Y →
        GdT U0 0 true u (HeB.plugQ C Y)
  | 0, u, Q, hQ => by
      obtain ⟨Qr, p, rfl, hQr, hp⟩ := hQ
      refine ⟨Qr, [(p, l + 1)], rfl, fun e he => by simp at he; subst he; rfl, hQr, fun Y hY => ?_⟩
      exact GdT_jump (TExt_tchU U0 0 (l + 1)) (TieOK_up (by omega)) hY hp
  | i + 1, u, Q, hQ => by
      rcases hQ with hQ | ⟨Q'', p, rfl, hQ'', hp⟩
      · obtain ⟨Qr, C, hQe, hC, hQr, hY⟩ := unplugT l i u Q hQ
        exact ⟨Qr, C, hQe, hC, hQr, fun Y hY' => hY Y (GdT_sub (fun _ _ h => Or.inl h) hY')⟩
      · obtain ⟨Qr, C, rfl, hC, hQr, hY⟩ := unplugT l i u Q'' hQ''
        refine ⟨Qr, C ++ [(p, l + 1)], by simp, fun e he => ?_, hQr, fun Y hY' => ?_⟩
        · rcases List.mem_append.mp he with he | he
          · exact hC e he
          · simp at he; subst he; rfl
        · rw [PmC.HeB.plugQ_append]
          exact hY _ (GdT_jump (TExt_text1 _ (l + 1) false (l + 1)) (TieOK_same l)
            (GdT_sub (fun _ _ h => Or.inr h) hY') hp)

/-- ★★★ 鎖の末尾の並び p の後ろの同じ段の葉 tie (l+1) []。 -/
theorem BotCL_chainLeaf (l i : ℕ) {u : ℕ} {Q'' : Path} {p : List UT}
    (hQ : tcG (tchU U0 0 (l + 1)) (l + 1) false (l + 1) i u Q'')
    (hp : GdT (tcG (tchU U0 0 (l + 1)) (l + 1) false (l + 1) i) (l + 1) false u p)
    (Uss : List (List UT)) (hU : WOK u Uss) (hG : HeL.GoodTTL u Uss) :
    HeL.BotCL u Uss Q'' (p ++ [UT.tie (l + 1) []]) := by
  have hPok := TPSOK_tcG (TPSOK_tchU1 l) (TieOK_same l) i
  have hPdec := TPSDec_tcG (TPSDec_tchU1 l) (TieOK_same l) i
  obtain ⟨Qr, C, rfl, hC, hQr, hY⟩ := unplugT l i u Q'' hQ
  have hLc : ∀ j, GdT U0 0 true u (Lc C p j) := by
    intro j
    induction j with
    | zero => exact hY p hp
    | succ j ih =>
        exact hY _ (GdT_jump (TExt_tchS0 _ (l + 1) false) (TieOK_zero (l + 1) false)
          (U0_sub (Adm_tchS0 hPok hPdec) ih) hp)
  have hrep : ∀ j, HeL.BotCL u Uss Qr (Lc C p j) := fun j => (hLc j).2 u le_rfl Uss hU hG Qr hQr
  have eP : ∀ T, HeL.BotCL u Uss (Qr ++ C) T = HeL.BotCL u Uss Qr (HeB.plugQ C T) := by
    intro T; unfold HeL.BotCL; rw [PmC.HeB.plugQ_append]
  rw [eP]
  have hAt : ∀ xs ys, topTs u (xs ++ ys) = topTs u xs ++ topTs u ys := topTs_append u
  have hTt : ∀ l cs, topTs u [UT.tie l cs]
      = ((1, u + 1 + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u cs) := fun l cs => by
    simp [topTs, topT]
  obtain ⟨E, hEd⟩ : ∃ E, E = topTs u (HeB.plugQ C p) := ⟨_, rfl⟩
  have eC : topTs u (HeB.plugQ C (p ++ [UT.tie (l + 1) []]))
      = E ++ [((C.length + 1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)] := by
    rw [F_plugQ_app hAt hTt, hEd, hTt]; simp [topTs, shiftr01]; omega
  have hnp : ¬ hasParent (E ++ [((C.length + 1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)]) 1 E.length := by
    have hA := AncM_chain hAt hTt (l + 1) C p hC (fun e _ => Fr_topTs u e.1) (Fr_topTs u p)
    rw [← hEd] at hA
    have := hnp_of_AncM hA (by simp)
      (by rw [show (E ++ [((C.length + 1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)]).length - 1 = E.length + 0 by
        simp, entry_append_right]; rfl)
    simpa using this
  have htow : ∀ j, (tow (u + 1) 0 (E ++ [((C.length + 1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)]) (j + 1) : TrioSeq)
      = ((0, u + 1, 0) : ℕ × ℕ × ℕ) :: topTs u (Lc C p j) := by
    intro j; rw [hEd]; exact tow_chain hAt hTt (l + 1) C p j
  have hEF : Fr E := by rw [hEd]; exact Fr_topTs u _
  have e1 : (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0
        (E ++ [((C.length + 1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)]))
      = shiftr01 1 0 (((0, u + 1, 0) : ℕ × ℕ × ℕ) ::
          (E ++ [((C.length + 1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)])) := by
    simp [shiftr01]
  rcases List.eq_nil_or_concat Qr with rfl | ⟨Q', ⟨v', p'⟩, rfl⟩
  · have eW : ∀ T : List UT, HeL.BotCL u Uss [] T
        = GTC CLTL u (FTL0 (u + 1) (Uss.map (topTs u)) ++ shiftr01 0 0
            (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      show GTC CLTL u (wLT u (Uss ++ [T], [])) = _
      rw [shiftr01_zero', Nat.add_zero]
      simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc]
      rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil]
    rw [eW, eC, e1]
    refine upleaf_deep_coreDT' (C := CLTL) hEF hnp (d := 0) (q := u + 1) (by omega) (by omega) (by omega)
      (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [htow j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this
  · simp only [List.concat_eq_append] at hQr hrep ⊢
    have hp' : p' = 0 := by have := U0_last u _ hQr; rwa [HeC.lastL_snoc] at this
    subst hp'
    have eW : ∀ T : List UT, HeL.BotCL u Uss (Q' ++ [(v', 0)]) T
        = GTC CLTL u ((wLT u (Uss ++ [HeB.plugQ Q' []], []) ++ shiftr01 (Q'.length + 1) 0 (topTs u v')) ++
            shiftr01 (Q'.length + 1) 0
              (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      rw [HeL.BotCL_snoc_eq, HeL.BotCL_word, HeM.topTs_snoc_tieL, shiftr01_append0, List.append_assoc]
    rw [eW, eC, e1]
    refine upleaf_deep_coreDT' (C := CLTL) hEF hnp (d := Q'.length + 1) (q := u + 1) (by omega) (by omega)
      (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [htow j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this

theorem BotCL_nil_tcG (l : ℕ) : ∀ (i u : ℕ) (Q : Path), tcG (tchU U0 0 (l + 1)) (l + 1) false (l + 1) i u Q →
    ∀ Uss, WOK u Uss → HeL.GoodTTL u Uss → HeL.BotCL u Uss Q []
  | 0, u, Q, hQ, Uss, hU, hG => (GdT_nil_tchU1 (l := l) (v := u)).2 u le_rfl Uss hU hG Q hQ
  | i + 1, u, Q, hQ, Uss, hU, hG => by
      rcases hQ with hQ | ⟨Q'', p, rfl, hQ'', hp⟩
      · exact BotCL_nil_tcG l i u Q hQ Uss hU hG
      · rw [HeL.BotCL_snoc_eq]
        exact BotCL_chainLeaf l i hQ'' hp Uss hU hG

/-- ★ SLT で空の並びは良い。 -/
theorem GdT_nil_SLT (l : ℕ) {v : ℕ} : GdT (SLT l) (l + 1) false v [] :=
  ⟨TX.nil _ _, fun u _ Uss hU hG Q ⟨i, hi⟩ => BotCL_nil_tcG l i u Q hi Uss hU hG⟩

/-! ## 本定理: TX の並びは良い -/

/-- ★★★ TX の並びは、(0,true) なら U0 で、(l+1,false) なら SLT l で良い。 -/
theorem GdT_TX {v p : ℕ} {cl : Bool} {us : List UT} (h : TX v p cl us) :
    (cl = true → p = 0 → GdT U0 p cl v us) ∧
    (∀ l, cl = false → p = l + 1 → GdT (SLT l) p cl v us) := by
  induction h with
  | nil p cl =>
      exact ⟨fun h1 h2 => by subst h1; subst h2; exact U0_nil,
        fun l h1 h2 => by subst h1; subst h2; exact GdT_nil_SLT l⟩
  | @ch p cl us Z _ hZ hb ih =>
      refine ⟨fun h1 h2 => ?_, fun l h1 h2 => ?_⟩
      · subst h1; subst h2
        exact GdT_load U0_TPSOK U0_TPSDec Z hZ hb us (ih.1 rfl rfl)
      · subst h1; subst h2
        exact GdT_load (SLT_TPSOK l) (SLT_TPSDec l) Z hZ hb us (ih.2 l rfl rfl)
  | @tie0 p cl us cs _ _ ih ihc =>
      have hcs := ihc.1 rfl rfl
      refine ⟨fun h1 h2 => ?_, fun l h1 h2 => ?_⟩
      · subst h1; subst h2
        exact GdT_jump (TExt_tchS0 U0 0 true) (TieOK_zero 0 true)
          (U0_sub (Adm_tchS0 U0_TPSOK U0_TPSDec) hcs) (ih.1 rfl rfl)
      · subst h1; subst h2
        exact GdT_jump (TExt_tchS0 (SLT l) (l + 1) false) (TieOK_zero (l + 1) false)
          (U0_sub (Adm_tchS0 (SLT_TPSOK l) (SLT_TPSDec l)) hcs) (ih.2 l rfl rfl)
  | @up p us l cs _ hpl _ ih ihc =>
      refine ⟨fun _ h2 => ?_, fun _ h1 _ => absurd h1 (by simp)⟩
      subst h2
      exact GdT_jump (TExt_tchU U0 0 (l + 1)) (TieOK_up hpl) (GdT_sub (tchU_sub_SLT l) (ihc.2 l rfl rfl))
        (ih.1 rfl rfl)
  | @deep us _ ih =>
      exact ⟨fun _ _ => GdT_deepAfter (ih.1 rfl rfl), fun _ h1 _ => absurd h1 (by simp)⟩
  | @same l us cs _ _ ih ihc =>
      refine ⟨fun h1 _ => absurd h1 (by simp), fun l' _ h2 => ?_⟩
      obtain rfl : l' = l := by omega
      exact GdT_jump (SLT_closed l') (TieOK_same l') (ihc.2 l' rfl rfl) (ih.2 l' rfl rfl)

theorem GdT_TP0_TX {v : ℕ} {us : List UT} (h : TX v 0 true us) : GdT TP0 0 true v us :=
  U0_sub Adm_TP0 ((GdT_TX h).1 rfl rfl)

/-! ## 族: TX の子の並びを持つ語 -/

/-- ★ TX の子の並びだけからなる語は良い（WOK と GoodTTL）。 -/
theorem GoodTTL_allX {v : ℕ} : ∀ Uss : List (List UT), (∀ us ∈ Uss, TX v 0 true us) →
    WOK v Uss ∧ HeL.GoodTTL v Uss := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact ⟨WOK_of_TreeTs (fun _ h => by simp at h), HeN.GoodTTL_nil v⟩
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TX v 0 true us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨hW, hG⟩ := ih h'
      refine ⟨WOK_snoc_TX hW hus, ?_⟩
      have := GdT_good TPSOK_TP0 (GdT_TP0_TX hus) le_rfl hW hG (TPNil_TP0 v)
      simpa [HeB.plugQ] using this

/-- ★★ 先頭の語（TX の子の並び Uss0、荷 us0）のあとに段つきの木の語の並び qs。 -/
theorem BwT_X (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TX 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0) :
    ∀ qs : List (List (List UT) × List (Option TrioSeq)),
    PsLTL 0 qs → BwT 0 (((Uss0, us0) :: qs).map (wLT 0)) := by
  obtain ⟨hWk, hGt⟩ := GoodTTL_allX Uss0 hU0
  intro qs
  induction qs using List.reverseRecOn with
  | nil =>
      intro _
      have := PmA.GTC_wLTLw hWk hGt us0 hNT hR [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
      simpa using this
  | append_singleton qs q ih =>
      intro h
      have h' : PsLTL 0 qs := fun r hr => h r (List.mem_append_left _ hr)
      have hq := h q (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := HeN.GTC_wLTL hq.1 (HeN.GoodTTL_all q.1 hq.1) q.2 hq.2.1 hq.2.2
      have hC : PsLd 0 ((Uss0, us0) :: qs) := by
        have := PsLd_append (PsLd_word hWk hNT hR) (PsLd_of_PsLTL h')
        simpa using this
      have := hG _ ⟨(Uss0, us0) :: qs, hC, rfl⟩ (Fr_CLT 0 ((Uss0, us0) :: qs)) (ih h')
      simpa [List.map_append] using this

theorem starOK_X (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TX 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) :
    StarOK 0 (rword 0 0 (((Uss0, us0) :: qs).map (wLT 0) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have hB := BwT_append_words (Fr_CLT 0 ((Uss0, us0) :: qs)) (BwT_X Uss0 hU0 us0 hNT hR qs h) Ls hW 0 le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- ★ 族: 先頭の語（TX の子の並び、荷）＋ 語の並び ＋ 遠い語 ＋ 吊るした荷。 -/
theorem X_hang (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TX 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 (((Uss0, us0) :: qs).map (wLT 0) ++ Ls) ++ shiftr01 1 0 Z)) ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_X Uss0 hU0 us0 hNT hR qs h hW) hZ hb))

theorem W0_of_X (x : List UT) (hx : TX 0 0 true x) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: rword 0 0 [wLT 0 ([x], [])]) ∈ W 0 := by
  have hS := starOK_X [x] (fun us h => by simp at h; subst h; exact hx) [] (by simp [GzJ.NoTie]) (RawU_nil 0)
    [] (PsLTL_nil 0) (WordsG_nil 0)
  have := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa using this

/-! ## 行1693 -/

/-- 行1693 の木: [tie 1 [tie 1 [], tie 0 []]]。 -/
theorem TX_1693 : TX 0 0 true [UT.tie 1 [UT.tie 1 [], UT.tie 0 []]] := by
  have := TX.up (TX.nil 0 true) (by omega : 0 < 0 + 1)
    (TX.tie0 (TX.same (l := 0) (TX.nil (v := 0) 1 false) (TX.nil 1 false)) (TX.nil 0 true))
  simpa using this

/-- ★★★ シート行 1693 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0) ∈ W 0。 -/
theorem R1693 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(4,1,0)] : TrioSeq) ∈ W 0 := by
  have h := W0_of_X _ TX_1693
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ シート行 1694 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(1,1,1)(2,1,1) ∈ W 0。 -/
theorem R1694 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(4,1,0),(1,1,1),(2,1,1)] : TrioSeq) ∈ W 0 := by
  have hS := starOK_X [[UT.tie 1 [UT.tie 1 [], UT.tie 0 []]]] (fun us h => by simp at h; subst h; exact TX_1693)
    [] (by simp [GzJ.NoTie]) (RawU_nil 0) [PmA.p0]
    (PsLTL_cons (fun _ h => by simp [PmA.p0] at h) (by simp [PmA.p0, GzJ.NoTie]) (RawU_nil 0) (PsLTL_nil 0))
    (WordsG_nil 0)
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01, PmA.p0] using h

end PmE
end TRIO
