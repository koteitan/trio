/-
The structural part of the deep return witness is a theorem.

For an upgrade `n → k` to an ancestor (`m = P0 k`), let `j` be the LAST bump child of `k`
and `c` the FIRST child of `j`.  Then (Std, below SRO):
  `j < n`, `c < n`, `entry 2 c = 0`, and `c` sits on the row-1 level of some
  row-1 ancestor `a` of `m` (`Up1 a m`, `entry 1 a = entry 1 c`).
Ingredients: UAB (no bump child of `k` is an ancestor of `n`), SibDec + Z1C (a child of
`k` before a bump child is itself a bump child), BumpLeaf (a grandchild at row 1 of `k`
makes `j` the last child of `k`), RowJ (row 2 of `c` is `0` since row 1 drops from `j`),
R1S (row-1 parent steps are unit steps, so every level `≤ entry 1 m` is on the chain).

What is left of `HUACDeepShape` is the value part only (`HUACCanon` below):
survival of `o(c)` in `G_j` and `StepDom` at the chain level of `c`.
-/
import Ytosk.WfHUACDeep
import Ytosk.V3InvJ
import Ytosk.V3Top
import Ytosk.V3T0H10Core

namespace Ytosk.WfHUAC2Canon
open T
open WfHUACDeep

/-- In a sorted list, a later larger element lies behind a split point. -/
theorem mem_after_of_sorted {l l₁ l₂ : List Nat} {d j : Nat} (hs : l.Pairwise (· < ·))
    (hl : l = l₁ ++ d :: l₂) (hj : j ∈ l) (hdj : d < j) : j ∈ l₂ := by
  subst hl
  rcases List.mem_append.mp hj with hj | hj
  · have := (List.pairwise_append.mp hs).2.2 j hj d (by simp)
    omega
  · rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · exact hj

/-- Every row-1 level `≤ entry 1 x` is met on the row-1 chain of `x` (R1S). -/
theorem chain_level {M : Mat} (h00 : entry M 0 0 = 0) (hR01 : R01 M) (hR1 : R1S M) :
    ∀ x l, l ≤ entry M 1 x → ∃ a, Up1 M a x ∧ entry M 1 a = l := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro l hl
    rcases Nat.eq_or_lt_of_le hl with heq | hlt
    · exact ⟨x, Up1.refl x, heq.symm⟩
    · obtain ⟨p, hp⟩ := par1_exists h00 hR01 (j := x) (by omega)
      have hstep := T0H10Core.par1_row_eq_succ hR1 hp
      obtain ⟨a, ha, hae⟩ := ih p (par_lt M 1 x p hp) l (by omega)
      exact ⟨a, Up1.step hp ha, hae⟩

/-- **Structure of the canonical deep witness.** -/
theorem canon_struct {N : Mat} (hN : Std N) (hNe : N ≠ SRO) {n k m : Nat}
    (hu : upg N n = some k) (hkn : k < n) (hkm : par N 0 k = some m)
    {L R C : List Nat} {j c : Nat}
    (hL : children N k = L ++ j :: R) (hjb : col N j = bump N k)
    (hC : children N j = c :: C) :
    c < n ∧ entry N 2 c = 0 ∧ ∃ a, Up1 N a m ∧ entry N 1 a = entry N 1 c := by
  have SX : SInvX N := (sInvX_std' hN).resolve_left hNe
  have S : SInv N := SX.toSInv
  have hJ : RowJ N := rowJ_std hN
  have hj : j ∈ children N k := by rw [hL]; simp
  have hc : c ∈ children N j := by rw [hC]; simp
  -- the upgrade geometry
  obtain ⟨m', hm', hk1, hcol, hcase⟩ := upg_spec hu
  obtain ⟨m'', hm'', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  rw [hm'] at hm''; cases hm''
  have hAkn : Anc0 N k n := by rcases hcase with h | h; omega; exact h.1
  have hk2 : entry N 2 k = 1 := by have := e2_of_col hcol; have := S.z2 k; omega
  have hk1e : entry N 1 k = entry N 1 n := e1_of_col hcol
  have hkm1 : entry N 1 k = entry N 1 m + 1 := T0H10Core.par1_row_eq_succ SX.r1s hk1
  have hj1 : entry N 1 j = entry N 1 k := e1_of_col hjb
  have hj2 : entry N 2 j = 1 := e2_of_col hjb
  have hj0 : entry N 0 j = entry N 0 k + 1 := e0_of_col hjb
  have hjp : par N 0 j = some k := (mem_children_iff.mp hj).2
  have hcp : par N 0 c = some j := (mem_children_iff.mp hc).2
  have hnN : n < N.length := by have := upg_succ_lt hu; omega
  -- no bump child of `k` is an ancestor of `n`
  have hUAB : ∀ d ∈ children N k, col N d = bump N k → ¬ Anc0 N d n :=
    S.uab n k hu (by omega)
  have hnotj : ¬ Anc0 N j n := hUAB j hj hjb
  -- `j < n`
  have hjn : j < n := by
    by_contra hnj
    have hnj' : n < j := by
      rcases Nat.lt_or_ge n j with h | h
      · exact h
      · exact absurd (by rw [show j = n by omega]; exact Anc0.refl n) hnotj
    obtain ⟨d, hdk, hdn⟩ := anc0_child hAkn (by omega)
    have hdN : d ∈ children N k := mem_children_iff.mpr ⟨by have := hdn.le; omega, hdk⟩
    have hdj : d < j := by have := hdn.le; omega
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hdN
    have hjl₂ : j ∈ l₂ := mem_after_of_sorted (children_sorted N k) hl hj hdj
    have hle := sib_le S.sibDec l₂ l₁ d hl j hjl₂
    have hd0 : entry N 0 d = entry N 0 k + 1 := S.r0p d k hdk
    have hd1 : entry N 1 d ≤ entry N 1 k := S.z1c k d hk2 hdN
    have hd2 : entry N 2 d ≤ 1 := S.z2 d
    have hcolj : col N j = (entry N 0 j, entry N 1 j, entry N 2 j) := by
      rw [hjb]; unfold bump; rw [hj0, hj1, hj2]
    have hcold : col N d = (entry N 0 d, entry N 1 d, entry N 2 d) := by
      simp [entry, col]
    rw [hcolj, hcold] at hle
    unfold colLe at hle
    simp only at hle
    have hdb : col N d = bump N k := by
      rw [hcold]; unfold bump
      have : entry N 1 d = entry N 1 k ∧ entry N 2 d = 1 := by omega
      rw [hd0, this.1, this.2]
    exact hUAB d hdN hdb hdn
  -- the subtree of `j` ends before `n`
  have hcn : c < n := by
    by_contra hcn
    have hAjc : Anc0 N j c := Anc0.step hcp (Anc0.refl j)
    exact hnotj (anc_between hAjc n (by omega) (by omega))
  refine ⟨hcn, ?_⟩
  -- row 1 of `c` is below that of `k`
  have hc1 : entry N 1 c ≤ entry N 1 k := by
    have := S.z1c j c hj2 hc; omega
  have hc1' : entry N 1 c < entry N 1 k := by
    rcases Nat.lt_or_ge (entry N 1 c) (entry N 1 k) with h | h
    · exact h
    · exfalso
      obtain ⟨_, _, _, hlast⟩ := SX.loc.2.2.2 k j c hj hjb hc h
      -- `j` is the last child of `k`, so `n` (after `j`, below `k`) is below `j`
      obtain ⟨d, hdk, hdn⟩ := anc0_child hAkn (by omega)
      have hdN : d ∈ children N k := mem_children_iff.mpr ⟨by have := hdn.le; omega, hdk⟩
      have hdle : d ≤ j := by
        have hl' := List.getLast?_eq_some_iff.mp hlast
        obtain ⟨ys, hys⟩ := hl'
        rw [hys] at hdN
        rcases List.mem_append.mp hdN with hd | hd
        · have hs := children_sorted N k
          rw [hys] at hs
          have := (List.pairwise_append.mp hs).2.2 d hd j (by simp)
          omega
        · simp at hd; omega
      rcases Nat.eq_or_lt_of_le hdle with hdj | hdj
      · subst hdj; exact hnotj hdn
      · have := sib_after_gt hdk hdn hj hdj
        omega
  refine ⟨?_, ?_⟩
  · -- RowJ: row 2 of `c` nonzero would need `entry 1 j ≤ entry 1 c`
    by_contra h2
    have := hJ c j h2 hcp
    omega
  · exact chain_level SX.e00 SX.r01 SX.r1s m (entry N 1 c) (by omega)

/-- **Residual (value part only).**  At a dangerous absorption with nonzero head index,
the last bump child `j` of `k` has a first child `c`, `o(c)` survives in `G_j`, and
`StepDom` holds at the row-1 level of `c` on the chain of `m`. -/
def HUACCanon : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      HUACShapes.Danger (vOpt σ (par N 1 n)) (bumpW N σ k) →
      lev (bumpW N σ k) = z ∨
      ∃ L j R c C, children N k = L ++ j :: R ∧ col N j = bump N k ∧
        (∀ d ∈ R, col N d ≠ bump N k) ∧ children N j = c :: C ∧
        σ.o c ∈ summands (sumN ((children N j).map σ.o)) ∧
        ∀ a, Up1 N a m → entry N 1 a = entry N 1 c → StepDom N σ a m

/-- **Bridge**: the value residual gives the deep shape residual. -/
theorem deepShape_of_canon (h : HUACCanon) : HUACDeepShape := by
  intro N σ rk hN hNe hC hR hG n k m hu hkn hkm hd
  rcases h N σ rk hN hNe hC hR hG n k m hu hkn hkm hd with hz | ⟨L, j, R, c, C, hL, hjb, hR', hCc, hoG, hst⟩
  · exact Or.inl hz
  · obtain ⟨hcn, hc2, a, ha, hae⟩ := canon_struct hN hNe hu hkn hkm hL hjb hCc
    refine Or.inr (Or.inr ⟨L, j, R, c, a, hL, hjb, hR', by rw [hCc]; simp, hoG, hcn, ha,
      hae.symm, hc2, hst a ha hae⟩)

/-- HUAC from the value residual. -/
theorem hUAC_of_canon (h : HUACCanon) : HUAC := hUAC_of_deep (deepShape_of_canon h)

end Ytosk.WfHUAC2Canon
