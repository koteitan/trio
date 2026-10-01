/-
**3 行・t = 1: 写しの列の等式は P の等式。**

N の写しの列 x + a に P の r + a の値を置いた割り当て（x より前は貼り合わせ `glue`）は、写しの列で N の等式を満たす
（`cons_copy`）。仮定は、写しの列の P_1・上げが r 以前の列 g を指すとき、その g の v が N と P で同じこと（`hagree`）。
-/
import Ytosk.V3Copy4

namespace Ytosk

open T

/-- The valuation of `P` shifted by one copy. -/
def shiftV (ρP : Valn) (L : Nat) : Valn := ⟨fun i => ρP.o (i - L), fun i => ρP.v (i - L)⟩

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- The contribution of a child of a copy column is the shifted one. -/
theorem cnt_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hz2 : entry M 2 r ≤ 1)
    {ρ ρP : Valn} {Z : Nat → T} {a d : Nat} (ha : a < (n - 1) * L)
    (hd : d ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) :
    cnt (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) (r + L + a) (d + L) =
      cnt (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a) d := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hdc := mem_children hd
  rw [hlP] at hdc
  have hda : d - r < (n - 1) * L := by omega
  have hd' : d + L = r + L + (d - r) := by omega
  unfold cnt
  have hcol : (col (TRIO.gexp M r L d0 0 n) (d + L) = bump (TRIO.gexp M r L d0 0 n) (r + L + a)) ↔
      (col (TRIO.gexp M r L d0 0 (n - 1)) d = bump (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) := by
    rw [hd', col_copy (d0 := d0) hlen hL hn hda, show r + (d - r) = d by omega]
    unfold bump
    rw [e0_copy (d0 := d0) hlen hL hn ha, e1_gexp_shift hlen hL hn ha, col_eq_entries]
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  have hup : isUpg (TRIO.gexp M r L d0 0 n) (d + L) = isUpg (TRIO.gexp M r L d0 0 (n - 1)) d := by
    rw [hd', isUpg_copy hlen hL hA hd0e hn hpath hz2 (by omega) hda, show r + (d - r) = d by omega]
  have htop : topped (TRIO.gexp M r L d0 0 n) (d + L) = topped (TRIO.gexp M r L d0 0 (n - 1)) d := by
    rw [hd', topped_copy hlen hL hA hd0e hn hda, show r + (d - r) = d by omega]
  have hval : (glueZ M (r + L) ρ (shiftV ρP L) Z).o (d + L) = ρP.o d := by
    rw [glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (d + L - L) = ρP.o d
    rw [Nat.add_sub_cancel]
  by_cases h1 : col (TRIO.gexp M r L d0 0 (n - 1)) d = bump (TRIO.gexp M r L d0 0 (n - 1)) (r + a)
  · rw [if_pos (hcol.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hcol.mp h)), if_neg h1, hup, htop, hval]

/-- The bump term of a child of a copy column is the shifted one. -/
theorem bumpTerm_copy {ρ ρP : Valn} {Z : Nat → T} {a d : Nat} (ha : a < (n - 1) * L)
    (hd : d ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) :
    bumpTerm (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) (r + L + a) (d + L) =
      bumpTerm (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a) d := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hdc := mem_children hd
  rw [hlP] at hdc
  have hda : d - r < (n - 1) * L := by omega
  have hd' : d + L = r + L + (d - r) := by omega
  unfold bumpTerm
  have hcol : (col (TRIO.gexp M r L d0 0 n) (d + L) = bump (TRIO.gexp M r L d0 0 n) (r + L + a)) ↔
      (col (TRIO.gexp M r L d0 0 (n - 1)) d = bump (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) := by
    rw [hd', col_copy (d0 := d0) hlen hL hn hda, show r + (d - r) = d by omega]
    unfold bump
    rw [e0_copy (d0 := d0) hlen hL hn ha, e1_gexp_shift hlen hL hn ha, col_eq_entries]
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  by_cases h1 : col (TRIO.gexp M r L d0 0 (n - 1)) d = bump (TRIO.gexp M r L d0 0 (n - 1)) (r + a)
  · rw [if_pos (hcol.mpr h1), if_pos h1]
    congr 2
    rw [hd', children_shift hlen hL hA hd0e hn hda, show r + (d - r) = d by omega, List.map_map]
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp]
    have hkc := mem_children hk
    rw [hlP] at hkc
    rw [glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (k + L - L) = ρP.o k
    rw [Nat.add_sub_cancel]
  · rw [if_neg (fun h => h1 (hcol.mp h)), if_neg h1]

/-- **The equations of the copy columns.** -/
theorem cons_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hz2 : entry M 2 r ≤ 1)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v g = ρP.v g) :
    ∀ a, a < (n - 1) * L →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).o (r + L + a) =
        oRhs (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) (r + L + a) ∧
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v (r + L + a) =
        vRhs (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) (r + L + a) := by
  intro a ha
  have hlP := len_P (d0 := d0) (n := n) hlen
  set ρ' := glueZ M (r + L) ρ (shiftV ρP L) Z with hρ'
  have hvo : ρ'.o (r + L + a) = ρP.o (r + a) := by
    rw [hρ', glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a)
    congr 1; omega
  have hvv : ρ'.v (r + L + a) = ρP.v (r + a) := by
    rw [hρ', glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a)
    congr 1; omega
  have hshv : ∀ t, r ≤ t → ρ'.v (t + L) = ρP.v t := by
    intro t ht
    rw [hρ', glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (t + L - L) = ρP.v t
    rw [Nat.add_sub_cancel]
  have hP := hCP (r + a) (by omega)
  have hch := children_shift (d0 := d0) hlen hL hA hd0e hn ha
  refine ⟨?_, ?_⟩
  · rw [hvo, hP.1]
    unfold oRhs
    rw [hvv, hch, List.map_map]
    congr 3
    apply List.map_congr_left
    intro d hd
    exact (cnt_copy hlen hL hA hd0e hn hpath hz2 ha hd).symm
  · rw [hvv, hP.2]
    unfold vRhs
    have he1 := e1_gexp_shift (d0 := d0) hlen hL hn ha
    have he2 := e2_copy (d0 := d0) hlen hL hn ha
    -- the row-1 parent
    have hpar : vOpt ρ' (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a)) =
        vOpt ρP (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a)) := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        rw [show r + L + 0 = r + L by omega, show r + 0 = r by omega,
          par1_root hlen hL hA hd0e hn hpath, ← par_gexp_pre (m := n - 1) hlen (by omega) 1 (by omega)]
        cases ht : par (TRIO.gexp M r L d0 0 (n - 1)) 1 r with
        | none => rfl
        | some t =>
          have htr := par_lt _ 1 r t ht
          exact hagree t (by omega) 0 (by omega) (Or.inl (by simpa using ht))
      · rw [par1_copy hlen hL hA hd0e hn hpath h0 ha]
        cases ht : par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) with
        | none => rfl
        | some t =>
          simp only [Option.map_some, vOpt]
          split
          · rename_i htr; exact hshv t htr
          · rename_i htr; exact hagree t (by omega) a ha (Or.inl ht)
    -- the bump terms
    have hbt : (children (TRIO.gexp M r L d0 0 n) (r + L + a)).map
        (bumpTerm (TRIO.gexp M r L d0 0 n) ρ' (r + L + a)) =
        (children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map
          (bumpTerm (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a)) := by
      rw [hch, List.map_map]
      apply List.map_congr_left
      intro d hd
      exact bumpTerm_copy hlen hL hA hd0e hn ha hd
    rw [he1, he2, hpar, hbt]
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      rw [show r + L + 0 = r + L by omega, show r + 0 = r by omega,
        upg_root hlen hL hA hd0e hn hpath hz2]
      rw [show r + L + 0 = r + L by omega, show r + 0 = r by omega] at *
      cases ht : upg (TRIO.gexp M r L d0 0 (n - 1)) r with
      | none => rfl
      | some t =>
        have htr := upgP_root_lt hlen hL hA hd0e hn ht
        simp only
        rw [hagree t (by omega) 0 (by omega) (Or.inr (by simpa using ht))]
    · rw [upg_copy hlen hL hA hd0e hn hpath h0 ha]
      cases ht : upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) with
      | none => rfl
      | some t =>
        simp only [Option.map_some]
        by_cases htr : r < t
        · rw [if_pos htr, hshv t (by omega)]
        · rw [if_neg htr, hagree t (by omega) a ha (Or.inr ht)]

end

end Ytosk
