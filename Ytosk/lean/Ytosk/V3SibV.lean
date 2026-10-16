/-
**UpgSibV を難しい 2 つの形に絞る（2026-10-17、top）。**

UpgSibV（V3CBigV）の前件: 同じ親 p の隣り合う子 a < b、a は a − 1 から上げられ topped、b は b − 1 から
上げられない。このとき col a = (e0 p + 1, y, 1)、P_1 a = p、e2 p = 0（y = e1 (a − 1)）。SibDec で
col b ≤ col a なので、場合は次の 4 つ。
- e1 b < y: 難しい（`UpgSibVHard` の右）。
- col b = col a で a に子がある: 難しい（`UpgSibVHard` の左）。S1 の値の版。
- col b = col a で a に子がない: S1 から sub(b) ≤ sub(a) = [col a] なので b にも子がなく、v(b) = v(a)。
- col b = (e0 p + 1, y, 0): b の上げの的は次の列 b + 1（p の子で列 (e0 p + 1, y, 1)）しかありえず、
  S1 の (b, b + 1) で矛盾。よって upg b = none、v(b) = v(p) + 1 ≤ v(p) + ω^{W_a} = v(a)。
`upgSibV_of_hard`: SInvX・S1・Cons・Good3 と `UpgSibVHard` から UpgSibV。
-/
import Ytosk.V3CBigV
import Ytosk.V3EqSibS1
import Ytosk.V3OmegaLhd

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The hard shapes of `UpgSibV`**: the same column with `a` having children, or a smaller row 1. -/
def UpgSibVHard (N : Mat) (τ : Valn) : Prop :=
  ∀ p a b, a ∈ children N p → b ∈ children N p → a < b → (∀ e ∈ children N p, a < e → b ≤ e) →
    upg N (a - 1) = some a → topped N a = true → upg N (b - 1) ≠ some b →
    (col N b = col N a ∧ children N a ≠ []) ∨ entry N 1 b < entry N 1 a → τ.v b ≤ τ.v a

/-- A column without children is its own subtree. -/
theorem subT_leaf {N : Mat} {a : Nat} (h : children N a = []) : subT N a = [col N a] := by
  unfold subT
  rcases tw_drop N (a + 1) (fun q => decide (entry N 0 a < q.1)) with h0 | ⟨hl, hp, _⟩
  · rw [h0]
  · exfalso
    have he : entry N 0 a < entry N 0 (a + 1) := by
      have : entry N 0 (a + 1) = (col N (a + 1)).1 := by rw [entry_col]
      rw [this]; simpa using hp
    have hc : a + 1 ∈ children N a := mem_children_iff.mpr ⟨hl, par0_next he⟩
    rw [h] at hc; simp at hc

/-- A column with a child has a nonempty tail in its subtree. -/
theorem subT_tail_ne {N : Mat} {b c : Nat} (hc : c ∈ children N b) :
    (N.drop (b + 1)).takeWhile (fun q => decide (entry N 0 b < q.1)) ≠ [] := by
  have hpc : par N 0 c = some b := (mem_children_iff.mp hc).2
  have hcL := (mem_children hc).2
  obtain ⟨hbc, he, hbet⟩ := (par0_spec N).mp hpc
  have hl : b + 1 < N.length := by omega
  have he1 : entry N 0 b < entry N 0 (b + 1) := by
    rcases Nat.eq_or_lt_of_le (show b + 1 ≤ c by omega) with h | h
    · rw [h]; exact he
    · have := hbet (b + 1) (by omega) h; omega
  rw [List.drop_eq_getElem_cons hl, ← col_getElem' hl, List.takeWhile_cons]
  have : (col N (b + 1)).1 = entry N 0 (b + 1) := by rw [entry_col]
  rw [this]
  simp [he1]

/-- **`UpgSibV` from its hard shapes.** -/
theorem upgSibV_of_hard {N : Mat} {τ : Valn} (hX : SInvX N) (hS1 : S1 N) (hC : Cons N τ) (hG : Good3 N τ)
    (hH : UpgSibVHard N τ) : UpgSibV N τ := by
  intro p a b ha hb hab hcons hua htop hnub
  have hpa : par N 0 a = some p := (mem_children_iff.mp ha).2
  have hpb : par N 0 b = some p := (mem_children_iff.mp hb).2
  have haL := (mem_children ha).2
  have hbL := (mem_children hb).2
  have hpL : p < N.length := by have := (mem_children ha).1; omega
  -- the shape of `a`
  obtain ⟨m, hm1, hm0, he1a, _⟩ := upg_facts hua
  have hmp : m = p := by rw [hpa] at hm0; exact (Option.some.inj hm0).symm
  subst hmp
  obtain ⟨m', hm1', hp1a, hcola, _⟩ := upg_spec hua
  rw [hm1] at hm1'; cases hm1'
  obtain ⟨he1a0, _⟩ := upg_e12 hua
  have he0a : entry N 0 a = entry N 0 m + 1 := by
    have : entry N 0 a = (col N a).1 := by rw [entry_col]
    rw [this, hcola]
  have he2a' : entry N 2 a = entry N 2 m + 1 := by
    have : entry N 2 a = (col N a).2.2 := by rw [entry_col]
    rw [this, hcola]
  have he2m : entry N 2 m = 0 := by have := hX.z2 a; omega
  have he2a : entry N 2 a = 1 := by omega
  have hlt1a : entry N 1 m < entry N 1 a := (par1_facts hp1a).2.2.1
  have he1a0' : entry N 1 a ≠ 0 := by omega
  -- the consecutive pair in the children list
  obtain ⟨l1, l2, hsplit⟩ := consec_split (children_sorted N m) ha hb hab
    (fun e he ⟨h1, h2⟩ => by have := hcons e he h1; omega)
  have hSD := hX.loc.1 m l1 l2 a b hsplit
  have hS := hS1 m l1 l2 a b hsplit
  have he0b : entry N 0 b = entry N 0 m + 1 := hX.r0p b m hpb
  unfold colLe at hSD
  rw [entry_col N b, entry_col N a] at hSD
  simp only at hSD
  by_cases h1 : entry N 1 b < entry N 1 a
  · exact hH m a b ha hb hab hcons hua htop hnub (Or.inr h1)
  have he1b : entry N 1 b = entry N 1 a := by omega
  have hp1b : par N 1 b = some m := par1_of_child hpb (by omega)
  have hvp := hG.ot_v m hpL
  -- `v(a) = v(m) + ω^{W_a}`
  have hbot : ∀ i j, isOT (bumpTerm N τ i j) = true := fun i j => isOT_bumpTerm hG i j
  have hWot : ∀ i, isOT (sumN (one :: (children N i).map (bumpTerm N τ i))) = true := by
    intro i; apply isOT_sumN; intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact hbot i j
  have hva : τ.v a = add (τ.v m) (omega (sumN (one :: (children N a).map (bumpTerm N τ a)))) := by
    rw [(hC a haL).2]; unfold vRhs; rw [if_neg he1a0', if_neg (by omega), hp1a]
    exact sf_ot (isOT_add hvp (isOT_omega (hWot a)))
  have he2b : entry N 2 b = 0 ∨ entry N 2 b = 1 := by have := hX.z2 b; omega
  rcases he2b with he2b | he2b
  · -- `col b = (e0 m + 1, y, 0)`: `b` is not upgraded
    have hub : upg N b = none := by
      cases hk : upg N b with
      | none => rfl
      | some k =>
        exfalso
        obtain ⟨m2, hm2, hpk, _, hcase⟩ := upg_facts hk
        rw [hp1b] at hm2; cases hm2
        rcases hcase with hk1 | ⟨hAkb, hkb⟩
        · subst hk1
          obtain ⟨m3, hm3, _, hcolk, _⟩ := upg_spec hk
          rw [hp1b] at hm3; cases hm3
          have hkL : b + 1 < N.length := upg_succ_lt hk
          have hkC : b + 1 ∈ children N m := mem_children_iff.mpr ⟨hkL, hpk⟩
          obtain ⟨k1, k2, hsplit2⟩ := consec_split (children_sorted N m) hb hkC (by omega)
            (fun e _ ⟨h1, h2⟩ => by omega)
          have hS2 := hS1 m k1 k2 b (b + 1) hsplit2
          unfold subT at hS2
          have hlt := (seqLtB_cons_false hS2).1
          have := colLtB_false hlt
          rw [hcolk, entry_col N b] at this
          simp only at this
          omega
        · have := (anc0_par hAkb (by omega) hpb).le
          have := par_lt N 0 k m hpk; omega
    have hvb : τ.v b = add (τ.v m) one := by
      rw [(hC b hbL).2]; unfold vRhs; rw [if_neg (by omega), if_pos he2b, hp1b, hub]
      exact sf_ot (isOT_add hvp isOT_one)
    rw [hvb, hva]
    exact add_le_add_left _ (one_le_omega (hWot a))
  · -- the same column
    have hcolab : col N b = col N a := by
      rw [entry_col N b, entry_col N a, he1b, he2b, he2a, he0b, he0a]
    by_cases hca : children N a = []
    · -- `a` has no children: neither has `b`
      have hcb : children N b = [] := by
        by_contra hne
        obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
        have htw := subT_tail_ne hc
        rw [subT_leaf hca] at hS
        unfold subT at hS
        rw [hcolab] at hS
        have h2 := (seqLtB_cons_false hS).2 rfl
        cases htw' : (N.drop (b + 1)).takeWhile (fun q => decide (entry N 0 b < q.1)) with
        | nil => exact htw htw'
        | cons q U => rw [htw'] at h2; simp [seqLtB] at h2
      have hvb : τ.v b = τ.v a := by
        rw [(hC b hbL).2, (hC a haL).2]; unfold vRhs
        rw [if_neg (by omega), if_neg (by omega), if_neg he1a0', if_neg (by omega), hp1b, hp1a, hcb, hca]
        rfl
      exact le_of_eq hvb
    · exact hH m a b ha hb hab hcons hua htop hnub (Or.inl ⟨hcolab, hca⟩)

end Ytosk
