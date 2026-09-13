/-
GxL.lean: 頭の直上の単位（錐のタイ `(1,v+1,0)` か、1 段ずらした Wg の荷）を並べた中身の閉包と、
行の組み立て。

    unitsC v us = us.flatMap (none ↦ [(1,v+1,0)], some Z ↦ Z↑1)
    RawU v us  : 荷 Z はすべて Wg (2v) の元で based
    GT_unitsC  : RawU v0 us → ∀ v ≥ v0, GT v (unitsC v us)

行 = 語 `rword 0 v (Ls.map (unitsC v))` に Wg の元を吊るしたもの（`StarOK`）。
-/
import GxK

namespace TRIO
namespace GxL

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK

def unitC (v : ℕ) : Option TrioSeq → TrioSeq
  | none => [((1, v + 1, 0) : ℕ × ℕ × ℕ)]
  | some Z => shiftr01 1 0 Z

def unitsC (v : ℕ) (us : List (Option TrioSeq)) : TrioSeq := us.flatMap (unitC v)

def RawU (v : ℕ) (us : List (Option TrioSeq)) : Prop :=
  ∀ Z, some Z ∈ us → Z ∈ Wg (2 * v) ∧ based Z

theorem RawU_nil (v : ℕ) : RawU v [] := fun _ h => by simp at h

theorem RawU_cons_none {v : ℕ} {us : List (Option TrioSeq)} (h : RawU v us) :
    RawU v (none :: us) := fun Z hZ => h Z (by simpa using hZ)

theorem RawU_cons_some {v : ℕ} {us : List (Option TrioSeq)} {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * v)) (hb : based Z) (h : RawU v us) : RawU v (some Z :: us) := by
  intro Z' hZ'
  simp only [List.mem_cons, Option.some.injEq] at hZ'
  rcases hZ' with rfl | hZ'
  · exact ⟨hZ, hb⟩
  · exact h Z' hZ'

theorem unitsC_snoc (v : ℕ) (us : List (Option TrioSeq)) (o : Option TrioSeq) :
    unitsC v (us ++ [o]) = unitsC v us ++ unitC v o := by
  simp [unitsC, List.flatMap_append]

theorem unitC_ge (v : ℕ) (o : Option TrioSeq) : ∀ y ∈ unitC v o, 1 ≤ y.1 := by
  cases o with
  | none => intro y hy; simp [unitC] at hy; subst hy; exact le_rfl
  | some Z =>
      intro y hy
      simp only [unitC, shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega

theorem unitsC_ge (v : ℕ) (us : List (Option TrioSeq)) : ∀ y ∈ unitsC v us, 1 ≤ y.1 := by
  intro y hy
  simp only [unitsC, List.mem_flatMap] at hy
  obtain ⟨o, -, hy⟩ := hy
  exact unitC_ge v o y hy

theorem RawU_prefix {v : ℕ} {us : List (Option TrioSeq)} {o : Option TrioSeq}
    (h : RawU v (us ++ [o])) : RawU v us := fun Z hZ => h Z (List.mem_append_left _ hZ)

theorem coneV_top {K : TrioSeq} (hK : ∀ y ∈ K, 1 ≤ y.1) (v : ℕ) :
    coneV (K ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)]) v K.length := by
  intro y hy
  have hyle := rtg0_le hy
  rcases Nat.lt_or_ge y K.length with hlt | hge
  · exfalso
    have hrec := rtg0_rec hy K.length hlt le_rfl
    rw [Small.entry_append_left hlt, show K.length = K.length + 0 from rfl,
      entry_append_right] at hrec
    have hmem : K.getD y (0, 0, 0) ∈ K := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
    have h1 := hK _ hmem
    have e : entry [((1, v + 1, 0) : ℕ × ℕ × ℕ)] 0 0 = 1 := rfl
    have e2 : entry K 0 y = (K.getD y (0, 0, 0)).1 := rfl
    rw [e] at hrec
    omega
  · have hy' : y = K.length := by simp at hyle; omega
    subst hy'
    rw [show K.length = K.length + 0 from rfl, entry_append_right]
    show v < v + 1; omega

theorem mlift_unitsC {v0 : ℕ} : ∀ (us : List (Option TrioSeq)), RawU v0 us →
    ∀ v, v0 ≤ v → ∀ t, mlift (unitsC v us) v t = unitsC (v + t) us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ v _ t; simp [unitsC, mlift_nil]
  | append_singleton us o ih =>
      intro hR v hv t
      have ih' := ih (RawU_prefix hR) v hv t
      rw [unitsC_snoc, unitsC_snoc]
      cases o with
      | none =>
          simp only [unitC]
          rw [mlift_snoc_cone _ _ (coneV_top (unitsC_ge v us) v) t, ih']
          show _ ++ [((1, v + 1 + t, 0) : ℕ × ℕ × ℕ)] = _
          rw [show v + 1 + t = v + t + 1 by omega]
      | some Z =>
          simp only [unitC]
          have hZ := hR Z (by simp)
          rw [mlift_append_low (low_of_Wg (Wg_mono (by omega) hZ.1 : Z ∈ Wg (2 * v)) 1 le_rfl) t,
            ih']

theorem GT_unitsC {v0 : ℕ} : ∀ (us : List (Option TrioSeq)), RawU v0 us →
    ∀ v, v0 ≤ v → GT v (unitsC v us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ v _; simpa [unitsC] using GT_nil v
  | append_singleton us o ih =>
      intro hR v hv
      have hR' := RawU_prefix hR
      rw [unitsC_snoc]
      cases o with
      | none =>
          simp only [unitC]
          refine GT_tie (coneV_top (unitsC_ge v us) v) (fun u hu Z hZ hbZ => ?_)
          rw [mlift_unitsC us hR' v hv (u - v), show v + (u - v) = u by omega]
          exact GT_loadTop (unitsC_ge u us) (ih hR' u (le_trans hv hu)) Z hZ hbZ
      | some Z =>
          simp only [unitC]
          have hZ := hR Z (by simp)
          exact GT_loadTop (unitsC_ge v us) (ih hR' v hv) Z (Wg_mono (by omega) hZ.1) hZ.2

#print axioms GT_unitsC

/-! ## 語と行 -/

def WordsOK (v : ℕ) (Ls : List (List (Option TrioSeq))) : Prop := ∀ us ∈ Ls, RawU v us

theorem WordsOK_nil (v : ℕ) : WordsOK v [] := fun _ h => by simp at h

theorem WordsOK_cons {v : ℕ} {us : List (Option TrioSeq)} {Ls : List (List (Option TrioSeq))}
    (h1 : RawU v us) (h2 : WordsOK v Ls) : WordsOK v (us :: Ls) := by
  intro us' h
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact h1
  · exact h2 us' h

theorem BwT_words {v : ℕ} : ∀ (Ls : List (List (Option TrioSeq))), WordsOK v Ls →
    BwT v (Ls.map (unitsC v)) := by
  intro Ls
  induction Ls using List.reverseRecOn with
  | nil => intro _; simpa using BwT_nil v
  | append_singleton Ls us ih =>
      intro hW
      rw [List.map_append, List.map_singleton]
      exact GT_unitsC us (hW us (by simp)) v le_rfl _
        (fun X hX => by
          simp only [List.mem_map] at hX
          obtain ⟨us', -, rfl⟩ := hX
          exact unitsC_ge v us')
        (ih (fun us' h => hW us' (List.mem_append_left _ h)))

def StarOK (v : ℕ) (A : TrioSeq) : Prop := A ∈ Wstarv v ∧ ∀ p ∈ A, 1 ≤ p.1

theorem starOK_words {v : ℕ} {Ls : List (List (Option TrioSeq))} (h : WordsOK v Ls) :
    StarOK v (rword 0 v (Ls.map (unitsC v))) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_words Ls h v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

theorem starOK_hang {v : ℕ} {A : TrioSeq} (hA : StarOK v A) {u : ℕ} {Z : TrioSeq}
    (hZ : Z ∈ Wg u) (hb : based Z) : StarOK v (A ++ shiftr01 1 0 Z) := by
  have h1 : entry (shiftr01 1 0 Z) 0 0 ≤ 1 := by
    cases Z with
    | nil => simp [shiftr01, entry]
    | cons c Z' =>
        rw [entry0_shiftr01 (by simp)]
        have : entry (c :: Z') 0 0 = 0 := hb
        omega
  have hge : ∀ p ∈ A ++ shiftr01 1 0 Z, 1 ≤ p.1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hA.2 p hp
    · simp only [shiftr01, List.mem_map] at hp
      obtain ⟨q, -, rfl⟩ := hp
      dsimp only; omega
  refine ⟨hang_Wg hA.1 (Wg_shift hZ 1) (fun p hp => ?_), hge⟩
  have := hge p hp
  omega

theorem Wg_of_starOK {v : ℕ} {A : TrioSeq} (hA : StarOK v A) :
    (((0, v, 0) : ℕ × ℕ × ℕ) :: A) ∈ Wg (2 * v) :=
  hA.1 (fun p hp => by have := hA.2 p hp; omega) (2 * v) le_rfl

theorem W0_of_starOK {A : TrioSeq} (hA : StarOK 0 A) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: A) ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK hA)

theorem Wg_up {u w : ℕ} {M : TrioSeq} (h : M ∈ Wg u) (huw : u ≤ w) : M ∈ Wg w :=
  Wg_mono huw h

/-- 行 519 の試し。 -/
theorem R519_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq)
    ∈ W 0 := by
  have h := W0_of_starOK (starOK_words (v := 0) (Ls := [[none, some [((0, 0, 0) : ℕ × ℕ × ℕ)]], [none]])
    (WordsOK_cons (RawU_cons_none (RawU_cons_some (Om_mem_Wg 0) rfl (RawU_nil 0)))
      (WordsOK_cons (RawU_cons_none (RawU_nil 0)) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

#print axioms R519_mem

end GxL
end TRIO
