/-
PmB.lean: 壁 A の基盤。GdT の仕組み（HeL〜HeN）を「深い葉の先頭つき」で写す。

深い葉 = tie 1 [tie 1 []]。(p = 0, cl = true) の子の並び（F のタイの子、段 0 のタイの子）は
入れ子のどこでも先頭に深い葉を 1 つ持ってよい（TsH / TOH）。先頭の深い葉の規則は
GTC 側 = PmA.BotCL_deep (G) の写し、遠い像側 = PmA.Gd_deep_gen (F)。
-/
import PmA

namespace TRIO
namespace PmB

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeK

/-- 深い葉。 -/
def deepU : UT := UT.tie 1 [UT.tie 1 []]

/-! ## GTC 側の木: (0, true) の並びは先頭に深い葉を 1 つ許す -/

mutual
def TUH (v : ℕ) : ℕ → Bool → UT → Prop
  | _, _, .ch Z => Z ∈ Wg (2 * v) ∧ based Z
  | _, _, .tie 0 cs => TsH v 0 true cs
  | p, cl, .tie (l + 1) cs => cl = true ∧ p < l + 1 ∧ TsH v (l + 1) false cs
def TsE (v : ℕ) : ℕ → Bool → List UT → Prop
  | _, _, [] => True
  | p, cl, x :: us => TUH v p cl x ∧ TsE v p cl us
def TsH (v : ℕ) : ℕ → Bool → List UT → Prop
  | _, _, [] => True
  | p, cl, x :: us => (TUH v p cl x ∧ TsE v p cl us) ∨ (p = 0 ∧ cl = true ∧ x = deepU ∧ TsE v 0 true us)
end

theorem TsE_snoc {v p : ℕ} {cl : Bool} : ∀ {us : List UT} {x : UT}, TsE v p cl us → TUH v p cl x →
    TsE v p cl (us ++ [x])
  | [], _, _, hx => ⟨hx, trivial⟩
  | _ :: _, _, h, hx => ⟨h.1, TsE_snoc h.2 hx⟩

theorem TsH_snoc {v p : ℕ} {cl : Bool} {us : List UT} {x : UT} (h : TsH v p cl us) (hx : TUH v p cl x) :
    TsH v p cl (us ++ [x]) := by
  cases us with
  | nil => exact Or.inl ⟨hx, trivial⟩
  | cons y ys =>
      rcases h with ⟨hy, hys⟩ | ⟨rfl, rfl, hy, hys⟩
      · exact Or.inl ⟨hy, TsE_snoc hys hx⟩
      · exact Or.inr ⟨rfl, rfl, hy, TsE_snoc hys hx⟩

theorem TsH_of_TsE {v p : ℕ} {cl : Bool} : ∀ {us : List UT}, TsE v p cl us → TsH v p cl us
  | [], _ => trivial
  | _ :: _, h => Or.inl h

theorem TsH_deep (v : ℕ) : TsH v 0 true [deepU] := Or.inr ⟨rfl, rfl, rfl, trivial⟩

theorem TsH_deep_cons {v : ℕ} {us : List UT} (h : TsE v 0 true us) : TsH v 0 true (deepU :: us) :=
  Or.inr ⟨rfl, rfl, rfl, h⟩

mutual
theorem TUH_raw {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (x : UT), TUH v p cl x → TRawL v x
  | _, _, .ch _, h => h
  | _, _, .tie 0 cs, h => TsH_raw 0 true cs h
  | _, _, .tie (l + 1) cs, h => TsH_raw (l + 1) false cs h.2.2
theorem TsE_raw {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TsE v p cl us → TRawLs v us
  | _, _, [], _ => trivial
  | p, cl, x :: us, h => ⟨TUH_raw p cl x h.1, TsE_raw p cl us h.2⟩
theorem TsH_raw {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TsH v p cl us → TRawLs v us
  | _, _, [], _ => trivial
  | p, cl, x :: us, h => by
      rcases h with ⟨hx, hus⟩ | ⟨_, _, rfl, hus⟩
      · exact ⟨TUH_raw p cl x hx, TsE_raw p cl us hus⟩
      · exact ⟨by simp [deepU, TRawL, TRawLs], TsE_raw 0 true us hus⟩
end

mutual
theorem TUH_mono {v u : ℕ} (hvu : v ≤ u) : ∀ {p : ℕ} {cl : Bool} {x : UT}, TUH v p cl x → TUH u p cl x
  | _, _, .ch _, h => ⟨Wg_mono (by omega) h.1, h.2⟩
  | _, _, .tie 0 _, h => TsH_mono hvu h
  | _, _, .tie (_ + 1) _, h => ⟨h.1, h.2.1, TsH_mono hvu h.2.2⟩
theorem TsE_mono {v u : ℕ} (hvu : v ≤ u) : ∀ {p : ℕ} {cl : Bool} {us : List UT}, TsE v p cl us → TsE u p cl us
  | _, _, [], _ => trivial
  | _, _, _ :: _, h => ⟨TUH_mono hvu h.1, TsE_mono hvu h.2⟩
theorem TsH_mono {v u : ℕ} (hvu : v ≤ u) : ∀ {p : ℕ} {cl : Bool} {us : List UT}, TsH v p cl us → TsH u p cl us
  | _, _, [], _ => trivial
  | _, _, _ :: _, h => by
      rcases h with ⟨hx, hus⟩ | ⟨hp, hcl, hx, hus⟩
      · exact Or.inl ⟨TUH_mono hvu hx, TsE_mono hvu hus⟩
      · exact Or.inr ⟨hp, hcl, hx, TsE_mono hvu hus⟩
end

mutual
theorem TUH_of_TreeTU {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (x : UT), TreeTU v p cl x → TUH v p cl x
  | _, _, .ch _, h => h
  | _, _, .tie 0 cs, h => TsH_of_TsE (TsE_of_TreeTs 0 true cs h)
  | _, _, .tie (l + 1) cs, h => ⟨h.1, h.2.1, TsH_of_TsE (TsE_of_TreeTs (l + 1) false cs h.2.2)⟩
theorem TsE_of_TreeTs {v : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TreeTs v p cl us → TsE v p cl us
  | _, _, [], _ => trivial
  | p, cl, x :: us, h => ⟨TUH_of_TreeTU p cl x h.1, TsE_of_TreeTs p cl us h.2⟩
end

theorem TsH_of_TreeTs {v p : ℕ} {cl : Bool} {us : List UT} (h : TreeTs v p cl us) : TsH v p cl us :=
  TsH_of_TsE (TsE_of_TreeTs p cl us h)

/-! ## 遠い像側の木 -/

mutual
def TOU (c : ℕ) : ℕ → Bool → UT → Prop
  | _, _, .ch X => HeG.okLowP c X
  | _, _, .tie 0 cs => TOH c 0 true cs
  | p, cl, .tie (l + 1) cs => cl = true ∧ p < l + 1 ∧ TOH c (l + 1) false cs
def TOE (c : ℕ) : ℕ → Bool → List UT → Prop
  | _, _, [] => True
  | p, cl, x :: us => TOU c p cl x ∧ TOE c p cl us
def TOH (c : ℕ) : ℕ → Bool → List UT → Prop
  | _, _, [] => True
  | p, cl, x :: us => (TOU c p cl x ∧ TOE c p cl us) ∨ (p = 0 ∧ cl = true ∧ x = deepU ∧ TOE c 0 true us)
end

mutual
theorem TOU_farT {u : ℕ} : ∀ (p : ℕ) (cl : Bool) (x : UT), TUH u p cl x → TOU u p cl (farT x)
  | _, _, .ch Z, h => by
      simp only [farT, TOU]
      have := HeG.okLowP_load (HeG.okLowP_nil u) h.1 h.2
      simpa using this
  | _, _, .tie 0 cs, h => by simp only [farT, TOU]; exact TOH_farTs 0 true cs h
  | _, _, .tie (l + 1) cs, h => by
      simp only [farT, TOU]
      exact ⟨h.1, h.2.1, TOH_farTs (l + 1) false cs h.2.2⟩
theorem TOE_farTs {u : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TsE u p cl us → TOE u p cl (farTs us)
  | _, _, [], _ => by simp [farTs, TOE]
  | p, cl, x :: us, h => by
      simp only [farTs, TOE]
      exact ⟨TOU_farT p cl x h.1, TOE_farTs p cl us h.2⟩
theorem TOH_farTs {u : ℕ} : ∀ (p : ℕ) (cl : Bool) (us : List UT), TsH u p cl us → TOH u p cl (farTs us)
  | _, _, [], _ => by simp [farTs, TOH]
  | p, cl, x :: us, h => by
      simp only [farTs, TOH]
      rcases h with ⟨hx, hus⟩ | ⟨hp, hcl, rfl, hus⟩
      · exact Or.inl ⟨TOU_farT p cl x hx, TOE_farTs p cl us hus⟩
      · refine Or.inr ⟨hp, hcl, by simp [deepU, farT, farTs], ?_⟩
        subst hp; subst hcl
        exact TOE_farTs 0 true us hus
end

section
variable {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) (H : ℕ → ℕ)
include hA01 hk hAk

mutual
theorem Gd_treeUH {c : ℕ} : ∀ (x : UT) (P : HeB.PS) (p : ℕ) (cl : Bool), HeB.PSOK P → HeC.PSDec P →
    HeC.LastL P p → (cl = true → HeB.Ext P p P) → ∀ (pre : List UT), TOU c p cl x →
    HeB.Gd P A k H c pre → HeB.Gd P A k H c (pre ++ [x])
  | .ch X, P, _, _, hP, hD, _, _, pre, hx, hpre => HeI.Gd_snoc_ch hP hD hA01 hk hpre hx
  | .tie 0 cs, P, _, _, hP, hD, _, _, pre, hx, hpre => by
      have hcs := Gd_treeHH (c := c) cs (HeC.chS0 P) 0 true (HeC.PSOK_chS0 hP) (HeC.PSDec_chS0 P)
        (HeC.LastL_chS0 P) (fun _ => HeC.chS0_closed P) hx (HeG.Gd_nil_chS0 hP hD)
      exact HeB.Gd_tie (HeC.Ext_chS0 P) hA01 hk hAk hpre hcs
  | .tie (l + 1) cs, P, p, cl, hP, hD, hlast, hcl, pre, hx, hpre => by
      obtain ⟨hcl1, hpl, hx⟩ := hx
      have hcs := Gd_treeHH (c := c) cs (HeC.chU P (l + 1)) (l + 1) false (HeC.PSOK_chU hP (l + 1))
        (HeC.PSDec_chU P (l + 1)) (HeC.LastL_chU P (l + 1)) (fun h => absurd h (by simp)) hx
        (HeH.Gd_nil_chU hP (hcl hcl1) hlast hpl)
      exact HeB.Gd_tie (HeC.Ext_chU P (l + 1)) hA01 hk hAk hpre hcs
theorem Gd_treeEH {c : ℕ} : ∀ (us : List UT) (P : HeB.PS) (p : ℕ) (cl : Bool), HeB.PSOK P → HeC.PSDec P →
    HeC.LastL P p → (cl = true → HeB.Ext P p P) → ∀ (pre : List UT), TOE c p cl us →
    HeB.Gd P A k H c pre → HeB.Gd P A k H c (pre ++ us)
  | [], _, _, _, _, _, _, _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, P, p, cl, hP, hD, hlast, hcl, pre, hx, hpre => by
      have := Gd_treeEH (c := c) us P p cl hP hD hlast hcl (pre ++ [x]) hx.2
        (Gd_treeUH (c := c) x P p cl hP hD hlast hcl pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
theorem Gd_treeHH {c : ℕ} : ∀ (us : List UT) (P : HeB.PS) (p : ℕ) (cl : Bool), HeB.PSOK P → HeC.PSDec P →
    HeC.LastL P p → (cl = true → HeB.Ext P p P) → TOH c p cl us →
    HeB.Gd P A k H c [] → HeB.Gd P A k H c us
  | [], _, _, _, _, _, _, _, _, hnil => hnil
  | x :: us, P, p, cl, hP, hD, hlast, hcl, hx, hnil => by
      rcases hx with ⟨hx, hus⟩ | ⟨rfl, rfl, rfl, hus⟩
      · have h1 := Gd_treeUH (c := c) x P p cl hP hD hlast hcl [] hx hnil
        have := Gd_treeEH (c := c) us P p cl hP hD hlast hcl [x] hus (by simpa using h1)
        simpa using this
      · have h1 : HeB.Gd P A k H c [deepU] :=
          PmA.Gd_deep_gen hP hD (hcl rfl) hlast hA01 hk hAk hnil
        have := Gd_treeEH (c := c) us P 0 true hP hD hlast hcl [deepU] hus h1
        simpa using this
end

theorem Gd_treeP0H {c : ℕ} {us : List UT} (h : TOH c 0 true us) : HeB.Gd HeC.P0 A k H c us :=
  Gd_treeHH hA01 hk hAk H us HeC.P0 0 true HeC.PSOK_P0 HeC.PSDec_P0 HeC.LastL_P0 (fun _ => HeC.P0_closed)
    h HeG.Gd_nil_P0

end

/-- ★ TsH の子の並びを後ろに足しても WOK。 -/
theorem WOK_snoc_TsH {u : ℕ} {Uss : List (List UT)} {T : List UT} (hU : WOK u Uss) (hT : TsH u 0 true T) :
    WOK u (Uss ++ [T]) := by
  refine ⟨fun us hus => ?_, fun u' hu' => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact hU.1 us hus
    · simp only [List.mem_singleton] at hus; subst hus; exact TsH_raw 0 true _ hT
  · have hL : GoodChtX ([] ++ []) 1 (fun _ => 0) u' (Uss.map farTs) := by simpa using hU.2 u' hu'
    have hG := Gd_treeP0H (A := []) (k := 1) (by simp) (le_refl 1) (by simp) (fun _ => 0) (c := u')
      (TOH_farTs 0 true T (TsH_mono hu' hT))
    have := HeC.Gd_P0_good hG (HcM.EmbU_triv (A := []) (by simp) (by simp) (by decide) (fun _ => 0))
      le_rfl hL
    rw [List.map_append, List.map_singleton]
    simpa [HeB.imgT_zero] using this

/-! ## HeL の写し: 道の集合と GdT（第 1 成分 = TsH、TPSOK.tree = 差し込んでも WOK） -/

open HeB HeC

abbrev TPS := ℕ → Path → Prop

/-- ★ 最上段の道の集合 P の全ての道の下で良い木の並び。 -/
def GdT (P : TPS) (p : ℕ) (cl : Bool) (v : ℕ) (x : List UT) : Prop :=
  TsH v p cl x ∧ ∀ u, v ≤ u → ∀ Uss, WOK u Uss → HeL.GoodTTL u Uss →
    ∀ Q, P u Q → HeL.BotCL u Uss Q x

theorem GdT_mono {P : TPS} {p : ℕ} {cl : Bool} {v v' : ℕ} {x : List UT} (h : GdT P p cl v x)
    (hv : v ≤ v') : GdT P p cl v' x :=
  ⟨TsH_mono hv h.1, fun u hu => h.2 u (le_trans hv hu)⟩

theorem GdT_sub {P P' : TPS} (hPP : ∀ u Q, P' u Q → P u Q) {p : ℕ} {cl : Bool} {v : ℕ} {x : List UT}
    (h : GdT P p cl v x) : GdT P' p cl v x :=
  ⟨h.1, fun u hu Uss hU hG Q hQ => h.2 u hu Uss hU hG Q (hPP u Q hQ)⟩

structure TPSOK (P : TPS) (p : ℕ) (cl : Bool) : Prop where
  tree : ∀ u Q, P u Q → ∀ T, TsH u p cl T → ∀ Uss, WOK u Uss → WOK u (Uss ++ [plugQ Q T])
  raw : ∀ u Q, P u Q → ∀ q ∈ Q, TRawLs u q.1
  lift : ∀ u Q, P u Q → ∀ u', u ≤ u' → P u' Q

def TExt (P : TPS) (p : ℕ) (cl : Bool) (l : ℕ) (Pc : TPS) : Prop :=
  ∀ u Q us, P u Q → GdT P p cl u us → Pc u (Q ++ [(us, l)])

def TieOK (p : ℕ) (cl : Bool) (l pc : ℕ) (clc : Bool) : Prop :=
  ∀ v cs, TsH v pc clc cs → TUH v p cl (UT.tie l cs)

theorem TieOK_zero (p : ℕ) (cl : Bool) : TieOK p cl 0 0 true := fun _ _ h => h

theorem TieOK_up {p l : ℕ} (hpl : p < l + 1) : TieOK p true (l + 1) (l + 1) false :=
  fun _ _ h => ⟨rfl, hpl, h⟩

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
  refine ⟨TsH_snoc hus.1 (hT v cs h.1), fun u hu Uss hU hG Q hQ => ?_⟩
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
    exact hP.tree u Q' hQ' _ (TsH_snoc hus.1 (hT u T hT')) Uss hU
  raw := by
    rintro u Q ⟨Q', us, rfl, hQ', hus⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hP.raw u Q' hQ' q hq
    · simp at hq; subst hq; exact TsH_raw p cl us hus.1
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
  tree := by intro u Q h T hT Uss hU; simp only [TPNil] at h; subst h; exact WOK_snoc_TsH hU hT
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
    refine ⟨TsH_snoc hus.1 ⟨Wg_nil _, based_nil⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    have := hus.2 u hu Uss hU hG Q hQ
    rw [HeL.BotCL_word] at this ⊢
    rwa [HdS.topTs_snoc_ch, show shiftr01 1 0 ([] : TrioSeq) = [] from rfl, List.append_nil]
  · -- flat
    intro Z hZW hbZ hIH hZW' us hus
    have hDZ := hIH hZW us hus
    refine ⟨TsH_snoc hus.1 ⟨hZW', HdS.based_snoc0 hbZ⟩, fun u hu Uss hU hG Q hQ => ?_⟩
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
      · have hDZt : TsH u p cl (us ++ [UT.ch Z]) := TsH_mono hu hDZ.1
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
    refine ⟨TsH_snoc hus.1 ⟨hZW', hbZ⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc]
    refine HdR.gtc_oper hlen hp (fun n hn => ?_)
    have := ((hIH n hn).2 (hIH n hn).1 us hus).2 u hu Uss hU hG Q hQ
    rwa [HeL.BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc] at this
  · -- orph
    intro Z h j hZW hbZ hj1 hjv hnp hz hZW' us hus
    refine ⟨TsH_snoc hus.1 ⟨hZW', hbZ⟩, fun u hu Uss hU hG Q hQ => ?_⟩
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch]
    have eU : topTs u us ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
        = (topTs u us ++ shiftr01 1 0 Z) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
    rw [eU]
    have hHP : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := HcS.Hd_shift1_based hbZ
    refine HdR.gtc_orph (HeL.PathCone_YtopL u Uss Q (hP.raw u Q hQ))
      (by rw [← eU]; exact Hd_app (Hd_topTLs u us (TsH_raw p cl us hus.1)) hHP) hj1 (by omega) ?_
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
  refine ⟨TsH_snoc hus.1 trivial, fun u' hu' Uss hU hG Q hQ => ?_⟩
  rw [HeL.BotCL_word]
  have eT : topTs u' (us0 ++ [UT.tie 0 []]) = topTs u' us0 ++ [((1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rw [eT]
  have hQr := hP.raw u' Q hQ
  have hraw := TsH_raw p cl us0 hus.1
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

/-- 新しい F のタイ（子の並びは空）。 -/
theorem HeM.BotCL_nilF (u : ℕ) (Uss : List (List UT)) (hU : WOK u Uss)
    (hG : HeL.GoodTTL u Uss) : HeL.BotCL u Uss [] [] := by
  show GTC CLTL u (wLT u (Uss ++ [[]], []))
  have e : wLT u (Uss ++ [[]], []) = wLT u (Uss, []) ++ [((1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [wLT, FTL0_snoc, topTs, unitsC, shiftr01]
  rw [e]
  refine GTC_tie (C := CLTL) (coneV_top (Fr_wLT u _) u) (fun u' hu' Z hZ hbZ => ?_)
    (fun L hC u'' hu'' => CLTL_lift L u hC u'' hu'')
  have hR' : WOK u' Uss := WOK_mono hu' hU
  rw [mlift_wLTL hu' (p := (Uss, [])) hU.1
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
  · exact HeM.BotCL_nilF u Uss hU hG
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
  refine ⟨TsH_snoc h.1 ⟨rfl, by omega, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
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
  refine ⟨trivial, fun u _ Uss hU hG Q hQ => ?_⟩
  obtain ⟨Q', us, rfl, hQ', hus⟩ := hQ
  rw [HeL.BotCL_snoc_eq]
  exact (GdT_upleaf hP hcl hlast hus).2 u le_rfl Uss hU hG Q' hQ'

/-! ## 木 -/

mutual
theorem GdT_treeU0 : ∀ (x : UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl → TLast P p →
    (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ) (pre : List UT), TreeTU v p cl x →
    GdT P p cl v pre → GdT P p cl v (pre ++ [x])
  | .ch Z, P, _, _, hP, hD, _, _, _, pre, hx, hpre => GdT_load hP hD Z hx.1 hx.2 pre hpre
  | .tie 0 cs, P, p, cl, hP, hD, _, _, v, pre, hx, hpre => by
      have hcs := GdT_treeL0 cs (tchS0 P p cl) 0 true (TPSOK_tchS0 hP) (TPSDec_tchS0 P p cl)
        (TLast_tchS0 P p cl) (fun _ => ⟨rfl, tchS0_closed P p cl⟩) v [] hx (GdT_nil_tchS0 hP hD)
      rw [List.nil_append] at hcs
      exact GdT_jump (TExt_tchS0 P p cl) (TieOK_zero p cl) hcs hpre
  | .tie (l + 1) cs, P, p, cl, hP, hD, hlast, hcl, v, pre, hx, hpre => by
      obtain ⟨hcl1, hpl, hx⟩ := hx
      subst hcl1
      obtain ⟨rfl, hclo⟩ := hcl rfl
      have hcs := GdT_treeL0 cs (tchU P 0 (l + 1)) (l + 1) false (TPSOK_tchU hP hpl) (TPSDec_tchU P hpl)
        (TLast_tchU P 0 (l + 1)) (fun h => absurd h (by simp)) v [] hx (GdT_nil_tchU hP hclo hlast)
      rw [List.nil_append] at hcs
      exact GdT_jump (TExt_tchU P 0 (l + 1)) (TieOK_up hpl) hcs hpre
theorem GdT_treeL0 : ∀ (us : List UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl →
    TLast P p → (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ) (pre : List UT), TreeTs v p cl us →
    GdT P p cl v pre → GdT P p cl v (pre ++ us)
  | [], _, _, _, _, _, _, _, _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, P, p, cl, hP, hD, hlast, hcl, v, pre, hx, hpre => by
      have := GdT_treeL0 us P p cl hP hD hlast hcl v (pre ++ [x]) hx.2
        (GdT_treeU0 x P p cl hP hD hlast hcl v pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
end


/-! ## 先頭の深い葉の規則 (G) と、深い葉の先頭つきの木の規則 -/

/-- ★★★ 閉じた道の集合で空の並びが GdT なら、[深い葉] も GdT（PmA.BotCL_deep の写し）。 -/
theorem GdT_deep_head {P : TPS} (hP : TPSOK P 0 true) (hD : TPSDec P 0 true)
    (hcl : TExt P 0 true 0 P) (hlast : TLast P 0) {v : ℕ} (hnil : GdT P 0 true v []) :
    GdT P 0 true v [deepU] := by
  refine ⟨TsH_deep v, fun u hu Uss hU hG Q hQ => ?_⟩
  have hdt : ∀ j, HeL.BotCL u Uss Q [HeT.dtree j] := by
    intro j
    have := GdT_treeL0 [HeT.dtree j] P 0 true hP hD hlast (fun _ => ⟨rfl, hcl⟩) v [] (PmA.TreeTs_dtree_u v j) hnil
    exact this.2 u hu Uss hU hG Q hQ
  have eD : ∀ u' : ℕ, shiftr01 1 0 (topTs u' [deepU])
      = shiftr01 1 0 ([((1,u'+2,0):ℕ×ℕ×ℕ)] ++ [((2,u'+2,0):ℕ×ℕ×ℕ)]) := by
    intro u'; simp [deepU, topTs, topT, shiftr01]
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v', p'⟩, rfl⟩
  · have eW : ∀ T : List UT, HeL.BotCL u Uss [] T
        = GTC CLTL u (FTL0 (u + 1) (Uss.map (topTs u)) ++ shiftr01 0 0
            (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      show GTC CLTL u (wLT u (Uss ++ [T], [])) = _
      rw [shiftr01_zero', Nat.add_zero]
      simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc]
      rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil]
    rw [eW, eD u]
    refine HeN.upleaf_deep_coreDT (C := CLTL) (u := u) (d := 0) (q := u+1) (d0 := 2) (m := u+2)
      (D := [(1,u+2,0)]) (by intro p hp; simp at hp; subst hp; simp)
      (by intro p hp; simp at hp; subst hp; simp) (by decide) (by omega) (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    have := hdt j
    rw [eW] at this
    rw [show ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) = [((1,u+2,0):ℕ×ℕ×ℕ),((2,u+2,0):ℕ×ℕ×ℕ)] from rfl,
      HeU.tow_dtreeQ u j, PmA.topTs_dtreeQ u j]
    simpa [shiftr01] using this
  · simp only [List.concat_eq_append] at hQ hdt ⊢
    have hp' : p' = 0 := by have := hlast u _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have eW : ∀ T : List UT, HeL.BotCL u Uss (Q' ++ [(v', 0)]) T
        = GTC CLTL u ((wLT u (Uss ++ [HeB.plugQ Q' []], []) ++ shiftr01 (Q'.length + 1) 0 (topTs u v')) ++
            shiftr01 (Q'.length + 1) 0
              (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      rw [HeL.BotCL_snoc_eq, HeL.BotCL_word, HeM.topTs_snoc_tieL, shiftr01_append0, List.append_assoc]
    rw [eW, eD u]
    refine HeN.upleaf_deep_coreDT (C := CLTL) (u := u) (d := Q'.length + 1) (q := u+1) (d0 := 2) (m := u+2)
      (D := [(1,u+2,0)]) (by intro p hp; simp at hp; subst hp; simp)
      (by intro p hp; simp at hp; subst hp; simp) (by decide) (by omega) (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    have := hdt j
    rw [eW] at this
    rw [show ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) = [((1,u+2,0):ℕ×ℕ×ℕ),((2,u+2,0):ℕ×ℕ×ℕ)] from rfl,
      HeU.tow_dtreeQ u j, PmA.topTs_dtreeQ u j]
    simpa [shiftr01] using this

mutual
theorem GdT_treeUH : ∀ (x : UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl → TLast P p →
    (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ) (pre : List UT), TUH v p cl x →
    GdT P p cl v pre → GdT P p cl v (pre ++ [x])
  | .ch Z, P, _, _, hP, hD, _, _, _, pre, hx, hpre => GdT_load hP hD Z hx.1 hx.2 pre hpre
  | .tie 0 cs, P, p, cl, hP, hD, _, _, v, pre, hx, hpre => by
      have hcs := GdT_treeHH cs (tchS0 P p cl) 0 true (TPSOK_tchS0 hP) (TPSDec_tchS0 P p cl)
        (TLast_tchS0 P p cl) (fun _ => ⟨rfl, tchS0_closed P p cl⟩) v hx (GdT_nil_tchS0 hP hD)
      exact GdT_jump (TExt_tchS0 P p cl) (TieOK_zero p cl) hcs hpre
  | .tie (l + 1) cs, P, p, cl, hP, hD, hlast, hcl, v, pre, hx, hpre => by
      obtain ⟨hcl1, hpl, hx⟩ := hx
      subst hcl1
      obtain ⟨rfl, hclo⟩ := hcl rfl
      have hcs := GdT_treeHH cs (tchU P 0 (l + 1)) (l + 1) false (TPSOK_tchU hP hpl) (TPSDec_tchU P hpl)
        (TLast_tchU P 0 (l + 1)) (fun h => absurd h (by simp)) v hx (GdT_nil_tchU hP hclo hlast)
      exact GdT_jump (TExt_tchU P 0 (l + 1)) (TieOK_up hpl) hcs hpre
theorem GdT_treeEH : ∀ (us : List UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl →
    TLast P p → (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ) (pre : List UT), TsE v p cl us →
    GdT P p cl v pre → GdT P p cl v (pre ++ us)
  | [], _, _, _, _, _, _, _, _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, P, p, cl, hP, hD, hlast, hcl, v, pre, hx, hpre => by
      have := GdT_treeEH us P p cl hP hD hlast hcl v (pre ++ [x]) hx.2
        (GdT_treeUH x P p cl hP hD hlast hcl v pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
theorem GdT_treeHH : ∀ (us : List UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl →
    TLast P p → (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ), TsH v p cl us →
    GdT P p cl v [] → GdT P p cl v us
  | [], _, _, _, _, _, _, _, _, _, hnil => hnil
  | x :: us, P, p, cl, hP, hD, hlast, hcl, v, hx, hnil => by
      rcases hx with ⟨hx, hus⟩ | ⟨rfl, rfl, rfl, hus⟩
      · have h1 := GdT_treeUH x P p cl hP hD hlast hcl v [] hx hnil
        have := GdT_treeEH us P p cl hP hD hlast hcl v [x] hus (by simpa using h1)
        simpa using this
      · have h1 : GdT P 0 true v [deepU] := GdT_deep_head hP hD (hcl rfl).2 hlast hnil
        have := GdT_treeEH us P 0 true hP hD hlast hcl v [deepU] hus h1
        simpa using this
end

/-- ★ 深い葉の先頭つきの木の並びは F のタイの子の位置 TP0 で良い。 -/
theorem GdT_treeTP0H {v : ℕ} {us : List UT} (h : TsH v 0 true us) : GdT TP0 0 true v us :=
  GdT_treeHH us TP0 0 true TPSOK_TP0 TPSDec_TP0 TLast_TP0 (fun _ => ⟨rfl, TP0_closed⟩) v h GdT_nil_TP0


/-! ## 族: 深い葉の先頭つきの木の子の並びを持つ語 -/

/-- ★ 深い葉の先頭つきの木の子の並びだけからなる語は良い（WOK と GoodTTL）。 -/
theorem GoodTTL_allH {v : ℕ} : ∀ Uss : List (List UT), (∀ us ∈ Uss, TsH v 0 true us) →
    WOK v Uss ∧ HeL.GoodTTL v Uss := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact ⟨WOK_of_TreeTs (fun _ h => by simp at h), HeN.GoodTTL_nil v⟩
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TsH v 0 true us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨hW, hG⟩ := ih h'
      refine ⟨WOK_snoc_TsH hW hus, ?_⟩
      have := GdT_good TPSOK_TP0 (GdT_treeTP0H hus) le_rfl hW hG (TPNil_TP0 v)
      simpa [HeB.plugQ] using this

/-- ★★ 先頭の語（深い葉の先頭つきの木の子の並び Uss0、荷 us0）のあとに段つきの木の語の並び qs。 -/
theorem BwT_H (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TsH 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0) :
    ∀ qs : List (List (List UT) × List (Option TrioSeq)),
    PsLTL 0 qs → BwT 0 (((Uss0, us0) :: qs).map (wLT 0)) := by
  obtain ⟨hWk, hGt⟩ := GoodTTL_allH Uss0 hU0
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

theorem starOK_H (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TsH 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) :
    StarOK 0 (rword 0 0 (((Uss0, us0) :: qs).map (wLT 0) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have hB := BwT_append_words (Fr_CLT 0 ((Uss0, us0) :: qs)) (BwT_H Uss0 hU0 us0 hNT hR qs h) Ls hW 0 le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- ★ 族: 先頭の語（深い葉の先頭つきの木の子の並び、荷）＋ 語の並び ＋ 遠い語 ＋ 吊るした荷。 -/
theorem H_hang (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TsH 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 (((Uss0, us0) :: qs).map (wLT 0) ++ Ls) ++ shiftr01 1 0 Z)) ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_H Uss0 hU0 us0 hNT hR qs h hW) hZ hb))

theorem W0_of_H (x : List UT) (hx : TsH 0 0 true x) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: rword 0 0 [wLT 0 ([x], [])]) ∈ W 0 := by
  have hS := starOK_H [x] (fun us h => by simp at h; subst h; exact hx) [] (by simp [GzJ.NoTie]) (RawU_nil 0)
    [] (PsLTL_nil 0) (WordsG_nil 0)
  have := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa using this

/-- ★ R_pm ＋ シート行 1675 の尾: (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(3,1,0)(4,2,0) ∈ W 0。 -/
theorem Rpm_1675 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(3,1,0),(4,2,0)] : TrioSeq) ∈ W 0 := by
  have h := W0_of_H [deepU, UT.tie 0 [UT.tie 1 []]]
    (TsH_deep_cons ⟨Or.inl ⟨⟨rfl, by omega, trivial⟩, trivial⟩, trivial⟩)
  simpa [deepU, rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★★★ シート行 1691 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(3,2,0) ∈ W 0（壁 A）。 -/
theorem R1691 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(3,2,0)] : TrioSeq) ∈ W 0 := by
  have h := W0_of_H [deepU, UT.tie 1 []] (TsH_deep_cons ⟨⟨rfl, by omega, trivial⟩, trivial⟩)
  simpa [deepU, rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

end PmB
end TRIO
