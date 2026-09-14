/-
HeL.lean: 最上段の段つきの道と、道の集合で定義する木の良さ（HdR の写し、HeB・HeC の最上段版）。

    BotCL u Uss Q T := GTC CLTL u (wLT u (Uss ++ [plugQ Q T], []))（Q は段つきの道）
    GdT P p cl v x := TreeTs v p cl x ∧ 全ての段 u ≥ v、良い Uss（GoodTTL）、P u の道 Q で BotCL
    集合: text1（延長）、tclS（段 0 の閉包）、TP0 := tclS {[]}、tchS0 P（段 0 のタイの子）、tchU P l（段 l の節点の子）

- 語は wLT u (Uss ++ [plugQ Q []], []) ++ (T の語)↑(|Q|+1)（wLT_plugQL）。道の成分の節点は行 1 が u+1+l（PathCone_YtopL）。
- TieOK p cl l pc clc: 親 (p, cl) の位置に段 l の節点を置き、その子の位置が (pc, clc)（木の条件 TreeTs）。
- GdT_jump: TExt P p cl l Pc → TieOK → GdT Pc cs → GdT P us0 → GdT P (us0 ++ [tie l cs])。
- TPSOK（木の条件・成分の生の条件・段の持ち上げ）、TPSDec（flat の分解）、閉包、最後の段。
-/
import HeK

namespace TRIO
namespace HeL

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ
open HeB HeG HeI HeK

/-! ## 語の形 -/

theorem mem_mapQ {φ : List UT → List UT} : ∀ {Q : Path} {p : List UT × ℕ}, p ∈ mapQ φ Q →
    ∃ q ∈ Q, p = (φ q.1, q.2)
  | [], p, h => by simp [mapQ] at h
  | (us, l) :: Q, p, h => by
      simp only [mapQ, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨(us, l), by simp, rfl⟩
      · obtain ⟨q, hq, rfl⟩ := mem_mapQ h
        exact ⟨q, by simp [hq], rfl⟩

theorem farTs_plugQL : ∀ (Q : Path) (T : List UT), farTs (plugQ Q T) = plugQ (mapQ farTs Q) (farTs T)
  | [], T => by simp [plugQ, mapQ]
  | (us, l) :: Q, T => by
      simp only [plugQ, mapQ, HdR.farTs_append]
      rw [show farTs [UT.tie l (plugQ Q T)] = [UT.tie l (farTs (plugQ Q T))] by simp [farTs, farT],
        farTs_plugQL Q T]

theorem topTs_plugQL (u : ℕ) (Q : Path) (T : List UT) :
    topTs u (plugQ Q T) = topTs u (plugQ Q []) ++ shiftr01 Q.length 0 (topTs u T) := by
  rw [← chT_farTs, ← chT_farTs, ← chT_farTs, farTs_plugQL, farTs_plugQL, HeB.chT_plugQ, HeB.chT_plugQ,
    mapQ_length]
  simp [farTs, chT, shiftr01]

theorem wLT_plugQL (u : ℕ) (Uss : List (List UT)) (Q : Path) (T : List UT) :
    wLT u (Uss ++ [plugQ Q T], [])
      = wLT u (Uss ++ [plugQ Q []], []) ++ shiftr01 (Q.length + 1) 0 (topTs u T) := by
  simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc, unitsC, List.flatMap_nil,
    List.append_nil]
  rw [topTs_plugQL u Q T, shiftr01_append0, shiftr01_add0]
  simp

theorem PathCone_YtopL (u : ℕ) (Uss : List (List UT)) (Q : Path) (hQ : ∀ q ∈ Q, TRawLs u q.1) :
    PathCone u (Q.length + 1) (wLT u (Uss ++ [plugQ Q []], [])) := by
  have e1 : topTs u (plugQ Q []) = HeB.chTQ u (u + 1) u (mapQ farTs Q) := by
    rw [← chT_farTs, farTs_plugQL, HeB.chT_plugQ]; simp [farTs, chT, shiftr01]
  have e : wLT u (Uss ++ [plugQ Q []], [])
      = [] ++ FTL0 (u + 1) (Uss.map (topTs u)) ++ [((0 + 1, u + 1, 0) : ℕ × ℕ × ℕ)] ++
          shiftr01 1 0 (HeB.chTQ u (u + 1) u (mapQ farTs Q)) := by
    simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc, unitsC, List.flatMap_nil,
      List.append_nil, e1]
    simp
  rw [e]
  have h0 : PathCone u 0 ([] : TrioSeq) := fun y hy => by simp at hy
  have h1 := HeD.PathCone_tieSnoc (show u < u + 1 by omega) h0 (V := FTL0 (u + 1) (Uss.map (topTs u)))
    (fun c hc => Fr_FTL0 _ _ c hc)
  have h2 := HeD.PathCone_chTQ (show u < u + 1 by omega) u u (u + 0) (mapQ farTs Q) (0 + 1) _
    (fun p h' => by
      obtain ⟨q, hq, rfl⟩ := mem_mapQ h'
      exact RawTs_farTLs q.1 (hQ q hq)) h1
  rwa [mapQ_length, show 0 + 1 + Q.length = Q.length + 1 by omega] at h2

theorem TRawLs_plugQ {u : ℕ} : ∀ (Q : Path) (T : List UT), (∀ q ∈ Q, TRawLs u q.1) →
    TRawLs u T → TRawLs u (plugQ Q T)
  | [], T, _, hT => hT
  | (us, l) :: Q, T, hQ, hT => by
      simp only [plugQ]
      exact TRawLs_snoc.mpr ⟨hQ (us, l) (by simp), TRawLs_plugQ Q T (fun q h => hQ q (by simp [h])) hT⟩

theorem mlift_YtopL {u u' : ℕ} (hu : u ≤ u') {Uss : List (List UT)} {Q : Path}
    (hU : ∀ us ∈ Uss, TRawLs u us) (hQ : ∀ q ∈ Q, TRawLs u q.1) :
    mlift (wLT u (Uss ++ [plugQ Q []], [])) u (u' - u) = wLT u' (Uss ++ [plugQ Q []], []) := by
  refine mlift_wLTL hu (fun us hus => ?_) (by simp [GzJ.NoTie]) (RawU_nil u)
  rcases List.mem_append.mp hus with hus | hus
  · exact hU us hus
  · simp at hus; subst hus; exact TRawLs_plugQ Q [] hQ trivial

/-! ## 定義 -/

def GoodTTL (v : ℕ) (Uss : List (List UT)) : Prop := ∀ u, v ≤ u → GTC CLTL u (wLT u (Uss, []))

def BotCL (u : ℕ) (Uss : List (List UT)) (Q : Path) (T : List UT) : Prop :=
  GTC CLTL u (wLT u (Uss ++ [plugQ Q T], []))

theorem BotCL_snoc_eq (u : ℕ) (Uss : List (List UT)) (Q : Path) (us T : List UT) (l : ℕ) :
    BotCL u Uss (Q ++ [(us, l)]) T = BotCL u Uss Q (us ++ [UT.tie l T]) := by
  unfold BotCL; rw [plugQ_snoc]

theorem BotCL_word (u : ℕ) (Uss : List (List UT)) (Q : Path) (T : List UT) :
    BotCL u Uss Q T
      = GTC CLTL u (wLT u (Uss ++ [plugQ Q []], []) ++ shiftr01 (Q.length + 1) 0 (topTs u T)) := by
  unfold BotCL; rw [wLT_plugQL]

abbrev TPS := ℕ → Path → Prop

/-- ★ 最上段の道の集合 P の全ての道の下で良い木の並び。 -/
def GdT (P : TPS) (p : ℕ) (cl : Bool) (v : ℕ) (x : List UT) : Prop :=
  TreeTs v p cl x ∧ ∀ u, v ≤ u → ∀ Uss, (∀ us ∈ Uss, TreeTs u 0 true us) → GoodTTL u Uss →
    ∀ Q, P u Q → BotCL u Uss Q x

theorem GdT_mono {P : TPS} {p : ℕ} {cl : Bool} {v v' : ℕ} {x : List UT} (h : GdT P p cl v x)
    (hv : v ≤ v') : GdT P p cl v' x :=
  ⟨TreeTs_mono hv h.1, fun u hu => h.2 u (le_trans hv hu)⟩

theorem GdT_sub {P P' : TPS} (hPP : ∀ u Q, P' u Q → P u Q) {p : ℕ} {cl : Bool} {v : ℕ} {x : List UT}
    (h : GdT P p cl v x) : GdT P' p cl v x :=
  ⟨h.1, fun u hu Uss hU hG Q hQ => h.2 u hu Uss hU hG Q (hPP u Q hQ)⟩

structure TPSOK (P : TPS) (p : ℕ) (cl : Bool) : Prop where
  tree : ∀ u Q, P u Q → ∀ T, TreeTs u p cl T → TreeTs u 0 true (plugQ Q T)
  raw : ∀ u Q, P u Q → ∀ q ∈ Q, TRawLs u q.1
  lift : ∀ u Q, P u Q → ∀ u', u ≤ u' → P u' Q

def TExt (P : TPS) (p : ℕ) (cl : Bool) (l : ℕ) (Pc : TPS) : Prop :=
  ∀ u Q us, P u Q → GdT P p cl u us → Pc u (Q ++ [(us, l)])

def TieOK (p : ℕ) (cl : Bool) (l pc : ℕ) (clc : Bool) : Prop :=
  ∀ v cs, TreeTs v pc clc cs → TreeTU v p cl (UT.tie l cs)

theorem TieOK_zero (p : ℕ) (cl : Bool) : TieOK p cl 0 0 true := fun _ _ h => h

theorem TieOK_up {p l : ℕ} (hpl : p < l + 1) : TieOK p true (l + 1) (l + 1) false :=
  fun _ _ h => ⟨rfl, hpl, h⟩

theorem GdT_good {P : TPS} {p : ℕ} {cl : Bool} (hP : TPSOK P p cl) {v : ℕ} {x : List UT}
    (h : GdT P p cl v x) {u : ℕ} (hvu : v ≤ u) {Uss : List (List UT)}
    (hU : ∀ us ∈ Uss, TreeTs u 0 true us) (hG : GoodTTL u Uss) {Q : Path} (hQ : P u Q) :
    GoodTTL u (Uss ++ [plugQ Q x]) :=
  fun u' hu' => h.2 u' (le_trans hvu hu') Uss (fun us hus => TreeTs_mono hu' (hU us hus))
    (fun u'' hu'' => hG u'' (le_trans hu' hu'')) Q (hP.lift _ _ hQ u' hu')

/-- ★ 延長の集合で良い子の並び cs を、段 l の節点の子として足す。 -/
theorem GdT_jump {P Pc : TPS} {p pc : ℕ} {cl clc : Bool} {l : ℕ} (hX : TExt P p cl l Pc)
    (hT : TieOK p cl l pc clc) {v : ℕ} {cs : List UT} (h : GdT Pc pc clc v cs) {us0 : List UT}
    (hus : GdT P p cl v us0) : GdT P p cl v (us0 ++ [UT.tie l cs]) := by
  refine ⟨TreeTs_append.mpr ⟨hus.1, hT v cs h.1, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
  rw [← BotCL_snoc_eq]
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
    rintro u Q ⟨Q', us, rfl, hQ', hus⟩ T hT'
    rw [plugQ_snoc]
    exact hP.tree u Q' hQ' _ (TreeTs_append.mpr ⟨hus.1, hT u T hT', trivial⟩)
  raw := by
    rintro u Q ⟨Q', us, rfl, hQ', hus⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hP.raw u Q' hQ' q hq
    · simp at hq; subst hq; exact TreeTs_raw p cl us hus.1
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
  tree := by intro u Q h T hT; simp only [TPNil] at h; subst h; exact hT
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

end HeL
end TRIO
