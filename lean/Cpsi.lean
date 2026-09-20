/-
Cpsi.lean: psi(I) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0) ∈ W 0 への還元。

psi(I) の展開: psi(I)⟦n⟧ = (0,0,0) :: Rc4^n  (Rc4 = (1,1,1)(2,1,1)(3,1,0), flat, t=0)。
Rc4 = rcol 0 0 Trc4, Trc4 = [(1,1,1),(2,1,0)]  (入れ子 far-word)。
∴ 族 (0,0,0)::Rc4^n ∈ W 0 は単一残余 GT 0 Trc4 に還元(WordsG + starOK_wordsG + W0_of_starOK)。
-/
import GzD
import GxN
import Wchar

namespace TRIO
namespace Cpsi

open Wset Small GwS Gw GxK GxL GxN GzD

/-- 遠い語の中身(入れ子 tie + 行1 letter)。rcol 0 0 Trc4 = Rc4。 -/
def Trc4 : TrioSeq := [((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)]

/-- psi(I) の展開ブロック。 -/
def Rc4 : TrioSeq := [((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)]

theorem Trc4_row0 : ∀ y ∈ Trc4, 1 ≤ y.1 := by decide

/-- rcol 0 0 Trc4 = Rc4 (rcol の頭 (1,1,1) + shiftr01 1 0 Trc4)。 -/
theorem rcol_Trc4 : rcol 0 0 Trc4 = Rc4 := by
  simp [rcol, Trc4, Rc4, shiftr01]

/-- Trc4 のみからなる語のリスト(n 反復)は WordsG(残余 GT 0 Trc4 を法として)。 -/
theorem wordsG_replicate (hGT : GT 0 Trc4) : ∀ n, WordsG 0 (List.replicate n Trc4) := by
  intro n K hK
  rw [List.eq_of_mem_replicate hK]
  exact ⟨hGT, Trc4_row0⟩

/-- **族 (0,0,0) :: (rword 0 0 (replicate n Trc4)) ∈ W 0**、GT 0 Trc4 を法として。 -/
theorem fam_far_mem (hGT : GT 0 Trc4) (n : ℕ) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: rword 0 0 (List.replicate n Trc4)) ∈ W 0 :=
  W0_of_starOK (starOK_wordsG (wordsG_replicate hGT n))

/-- rword 0 0 (replicate n Trc4) = Rc4 を n 個 flat 連結。 -/
theorem rword_replicate_Rc4 (n : ℕ) :
    rword 0 0 (List.replicate n Trc4) = (List.range n).flatMap (fun _ => Rc4) := by
  rw [rword_replicate, rcol_Trc4]

/-! ## psi(I) 本体への接続 -/

/-- psi(I) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)。 -/
def psiI : TrioSeq :=
  [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 1) : ℕ × ℕ × ℕ),
   ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)]

theorem psiI_srow : srow psiI 4 = 0 := by decide

theorem psiI_nextrel0_1_4 : nextrel0 psiI 1 4 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro j hj
  obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
  · decide
  · decide

/-- (2,0,0) の行0親は列 1 で一意。 -/
theorem psiI_hasParent : hasParent psiI (srow psiI 4) 4 := by
  rw [psiI_srow]
  refine ⟨1, ?_, ?_⟩
  · show nextR psiI 0 1 4
    rw [nextR, if_pos rfl]; exact psiI_nextrel0_1_4
  · intro y hy
    rw [nextR, if_pos rfl] at hy
    obtain ⟨hylen, -, hylt, hyent, hymin⟩ := hy
    -- entry psiI 0 y < entry psiI 0 4 = 2, y < 4
    have hy4 : entry psiI 0 4 = 2 := by decide
    rw [hy4] at hyent
    -- y ∈ {0,1,2,3}
    obtain rfl | rfl | rfl | rfl : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by omega
    · -- y=0: hymin 1 gives 2 ≤ entry 0 1 = 1, contradiction
      have := hymin 1 ⟨by omega, by omega⟩
      rw [hy4] at this; revert this; decide
    · rfl
    · revert hyent; decide
    · revert hyent; decide

theorem psiI_parent : parent psiI (srow psiI 4) 4 = 1 :=
  psiI_hasParent.unique (parent_nextR psiI_hasParent)
    (by rw [psiI_srow, nextR, if_pos rfl]; exact psiI_nextrel0_1_4)

/-- gcopy は d0=d1=0 なので Rc4 そのもの。 -/
theorem gcopy_psiI (k : ℕ) : gcopy psiI 1 3 0 0 k = Rc4 := by
  unfold gcopy Rc4
  simp only [Nat.mul_zero, ite_self, Nat.add_zero]
  decide

/-- **psi(I)⟦n⟧ = (0,0,0) :: (range n).flatMap (fun _ => Rc4)**。 -/
theorem psiI_oper (n : ℕ) :
    psiI⟦n⟧ = ((0, 0, 0) : ℕ × ℕ × ℕ) :: (List.range n).flatMap (fun _ => Rc4) := by
  have hL : psiI.length - 1 ≠ 0 := by decide
  have hz : ¬ (entry psiI 0 (psiI.length - 1) = 0 ∧ entry psiI 1 (psiI.length - 1) = 0 ∧
      entry psiI 2 (psiI.length - 1) = 0) := by decide
  have hp : hasParent psiI (srow psiI (psiI.length - 1)) (psiI.length - 1) := by
    show hasParent psiI (srow psiI 4) 4; exact psiI_hasParent
  rw [oper_gcopies n hL hz hp]
  have hlen : psiI.length - 1 = 4 := by decide
  have hpar : parent psiI (srow psiI (psiI.length - 1)) (psiI.length - 1) = 1 := by
    rw [hlen]; exact psiI_parent
  rw [hpar, hlen]
  have hsr : srow psiI 4 = 0 := psiI_srow
  rw [hsr]
  simp only [Nat.not_lt_zero, reduceIte, Nat.lt_irrefl]
  -- goal: psiI.take 1 ++ gcopies psiI 1 (4-1) 0 0 n = (0,0,0) :: flatMap
  have htake : psiI.take 1 = [((0, 0, 0) : ℕ × ℕ × ℕ)] := by decide
  have hgc : gcopies psiI 1 (4 - 1) 0 0 n = (List.range n).flatMap (fun _ => Rc4) := by
    unfold gcopies
    apply List.flatMap_congr
    intro k _
    exact gcopy_psiI k
  rw [show (4 : ℕ) - 1 = 3 by rfl, htake, hgc]
  rfl

/-- **psi(I) ∈ W 0、残余 GT 0 Trc4 を法として**(検証済み還元)。 -/
theorem psiI_mem (hGT : GT 0 Trc4) : psiI ∈ W 0 := by
  refine mem_of_oper_mem (fun n _ => ?_)
  rw [psiI_oper n, ← rword_replicate_Rc4 n]
  exact fam_far_mem hGT n

end Cpsi
end TRIO
