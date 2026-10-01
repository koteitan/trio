/-
**3 行・t = 1: 展開 N = M[n] の貼り合わせの評価でも、のりしろの子の値と段の項は増えない
（BumpKidsDec・BumpTermDec）。**

x より前の列の構造は M と同じ（`sameAt_lt`）。のりしろの子 j の子で D に入るものは、`VShape`（D の v の形）から
「i の最後の子 j′ の最後の子 k′」だけ。その値だけが下がる（fsD(o(k′), Z) ≤ o(k′)、k′ = x なら M[n − 1] の o(r) ≤ o(x)）。
したがって並びは最後の項だけが下がり（`pairwise_snoc_lower`）、段の項 ω^{Σ} も最後の子 j′ の分だけが下がる。
x 以後の列は M[n − 1] の写し（`children_shift`・`col_copy`・`bumpTerm_copy`）。
-/
import Ytosk.V3FrameOTN
import Ytosk.V3DropPres
import Ytosk.V3QRIdx

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0)
  (hxnb : ∀ c, par M 0 (r + L) = some c →
    col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hz2 : entry M 2 r ≤ 1)
  (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
  (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
  {ρ ρP : Valn} {Z : Nat → T}
  (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
  (hle : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c ∧ fsD (ρ.o c) (Z c) ≠ z)
  (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z)
include hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hVS hle hlex

/-- The shape of the children of a bump child below `x`: unchanged, or only the last one lowered, and then
`j` is the last child of `i`. -/
theorem bumpKids_shape {i j : Nat} (hi : i < r + L) (he1 : entry M 1 i ≠ 0) (he2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (hjb : col M j = bump M i) :
    ((children M j).map (glueZ M (r + L) ρ (shiftV ρP L) Z).o = (children M j).map ρ.o) ∨
    (∃ Li K k, children M i = Li ++ [j] ∧ children M j = K ++ [k] ∧
      K.map (glueZ M (r + L) ρ (shiftV ρP L) Z).o = K.map ρ.o ∧
      (glueZ M (r + L) ρ (shiftV ρP L) Z).o k ≤ ρ.o k) := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  -- values off `D` do not change
  have hoff : ∀ k, k ≤ r + L → ¬ DepX M (r + L) true k → σ.o k = ρ.o k := by
    intro k hk hd
    have hkx : k < r + L := by
      rcases Nat.lt_or_ge k (r + L) with h | h
      · exact h
      · exact absurd (show k = r + L by omega ▸ DepX.leaf) hd
    rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hkx hd]
  have hles : ∀ k, k ≤ r + L → σ.o k ≤ ρ.o k := by
    intro k hk
    by_cases hd : DepX M (r + L) true k
    · rcases Nat.lt_or_ge k (r + L) with h | h
      · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z h hd]; exact (hle k h hd).1
      · have : k = r + L := by omega
        subst this
        rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (le_refl _)]
        show ρP.o (r + L - L) ≤ _
        rw [Nat.add_sub_cancel]; exact hlex.1
    · rw [hoff k hk hd]
  have hjl := (mem_children hj).2
  have hkle : ∀ k ∈ children M j, k ≤ r + L := fun k hk => by have := (mem_children hk).2; omega
  by_cases hiv : DepX M (r + L) false i
  · obtain ⟨_, _, hcase⟩ := hVS i hi hiv
    rcases hcase with ⟨h2, _⟩ | ⟨_, Li, K, j', k', hch, _, hchj, _, hKnd, hLnd⟩
    · exact absurd h2 he2
    · rw [hch] at hj
      rcases List.mem_append.mp hj with hjL | hjL
      · left
        apply List.map_congr_left
        intro k hk
        exact hoff k (hkle k hk) (hLnd j hjL k hk).2
      · rw [List.mem_singleton] at hjL
        subst hjL
        right
        refine ⟨Li, K, k', hch, hchj, ?_, hles k' (hkle k' (by rw [hchj]; simp))⟩
        apply List.map_congr_left
        intro k hk
        exact hoff k (hkle k (by rw [hchj]; simp [hk])) (hKnd k hk)
  · left
    apply List.map_congr_left
    intro k hk
    exact hoff k (hkle k hk) (fun hd => hiv (DepX.vbump he1 he2 hj hjb hk hd))

omit hVS in
/-- Off `D` (and before `x`) the glued values are those of `M`; all values up to `x` are lowered. -/
theorem glue_off_le :
    (∀ k, k ≤ r + L → ¬ DepX M (r + L) true k → (glueZ M (r + L) ρ (shiftV ρP L) Z).o k = ρ.o k) ∧
    (∀ k, k ≤ r + L → (glueZ M (r + L) ρ (shiftV ρP L) Z).o k ≤ ρ.o k) := by
  have hoff : ∀ k, k ≤ r + L → ¬ DepX M (r + L) true k →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).o k = ρ.o k := by
    intro k hk hd
    have hkx : k < r + L := by
      rcases Nat.lt_or_ge k (r + L) with h | h
      · exact h
      · exact absurd (show k = r + L by omega ▸ DepX.leaf) hd
    rw [glueZ_o_lt ρ (shiftV ρP L) Z hkx hd]
  refine ⟨hoff, fun k hk => ?_⟩
  by_cases hd : DepX M (r + L) true k
  · rcases Nat.lt_or_ge k (r + L) with h | h
    · rw [glueZ_o_dep ρ (shiftV ρP L) Z h hd]; exact (hle k h hd).1
    · have : k = r + L := by omega
      subst this
      rw [glueZ_o_ge ρ (shiftV ρP L) Z (le_refl _)]
      show ρP.o (r + L - L) ≤ _
      rw [Nat.add_sub_cancel]; exact hlex.1
  · rw [hoff k hk hd]

/-- `col N (j + L) = bump N (r + L + a)` iff the same in `P` (copies). -/
theorem colbump_copy {a j : Nat} (ha : a < (n - 1) * L) (hj0 : r ≤ j)
    (hj : j < r + (n - 1) * L) :
    (col (TRIO.gexp M r L d0 0 n) (j + L) = bump (TRIO.gexp M r L d0 0 n) (r + L + a)) ↔
      (col (TRIO.gexp M r L d0 0 (n - 1)) j = bump (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) := by
  have hda : j - r < (n - 1) * L := by omega
  rw [show j + L = r + L + (j - r) by omega, col_copy (d0 := d0) hlen hL hn hda,
    show r + (j - r) = j by omega]
  unfold bump
  rw [e0_copy (d0 := d0) hlen hL hn ha, e1_gexp_shift hlen hL hn ha, col_eq_entries]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

/-- **BumpKidsDec passes to the glued valuation of `M[n]`.** -/
theorem bumpKidsDec_N_t1 (hKD : BumpKidsDec M ρ) (hKDP : BumpKidsDec (TRIO.gexp M r L d0 0 (n - 1)) ρP) :
    BumpKidsDec (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  intro i he1 he2 j hj hjb
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    rw [hS.e1] at he1; rw [hS.e2] at he2; rw [hS.ch] at hj
    have hb : bump (TRIO.gexp M r L d0 0 n) i = bump M i := by
      unfold bump; rw [entry_gexp_pre hlen (by omega) 0 h, entry_gexp_pre hlen (by omega) 1 h]
    have hjx : j < r + L := by
      have := (mem_children hj).2
      rcases Nat.lt_or_ge j (r + L) with h' | h'
      · exact h'
      · exfalso
        have hjx : j = r + L := by omega
        subst hjx
        exact hxnb i (mem_children_iff.mp hj).2 hjb
    rw [col_gexp_pre hlen (by omega) hjx, hb] at hjb
    rw [(hSA j hjx).ch]
    rcases bumpKids_shape hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hVS hle hlex h he1 he2 hj hjb with
      heq | ⟨Li, K, k, _, hchj, hK, hk⟩
    · rw [← hσ] at heq; rw [heq]; exact hKD i he1 he2 j hj hjb
    · have hM := hKD i he1 he2 j hj hjb
      rw [hchj, List.map_append, List.map_singleton] at hM ⊢
      rw [← hσ] at hK hk
      rw [hK]; exact pairwise_snoc_lower hM hk
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have hjl := mem_children hj
    have ha : a < (n - 1) * L := by omega
    rw [e1_gexp_shift hlen hL hn ha] at he1
    rw [e2_copy (d0 := d0) hlen hL hn ha] at he2
    rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha] at hj
    obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hj
    have hj0l := mem_children hj0
    rw [hlP] at hj0l
    rw [colbump_copy hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hVS hle hlex ha (by omega) (by omega)]
      at hjb
    have hda : j0 - r < (n - 1) * L := by omega
    rw [show j0 + L = r + L + (j0 - r) by omega, children_shift (d0 := d0) hlen hL hA hd0e hn hda,
      show r + (j0 - r) = j0 by omega, List.map_map]
    have : (children (TRIO.gexp M r L d0 0 (n - 1)) j0).map (σ.o ∘ (· + L)) =
        (children (TRIO.gexp M r L d0 0 (n - 1)) j0).map ρP.o := by
      apply List.map_congr_left
      intro k hk
      have hkl := mem_children hk
      rw [hlP] at hkl
      simp only [Function.comp, hσ]
      rw [glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (k + L - L) = ρP.o k
      rw [Nat.add_sub_cancel]
    rw [this]
    exact hKDP (r + a) he1 he2 j0 hj0 hjb

/-- **BumpTermDec passes to the glued valuation of `M[n]`.** -/
theorem bumpTermDec_N_t1 (hG : Good3 M ρ)
    (hGσ : ∀ k, k ≤ r + L → isOT ((glueZ M (r + L) ρ (shiftV ρP L) Z).o k) = true)
    (hTD : BumpTermDec M ρ) (hTDP : BumpTermDec (TRIO.gexp M r L d0 0 (n - 1)) ρP) :
    BumpTermDec (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  obtain ⟨hoff, hles⟩ := glue_off_le hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hle hlex (ρ := ρ) (ρP := ρP)
    (Z := Z)
  rw [← hσ] at hoff hles
  intro i he1 he2
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    rw [hS.e1] at he1; rw [hS.e2] at he2
    have hlist : (children (TRIO.gexp M r L d0 0 n) i).map (bumpTerm (TRIO.gexp M r L d0 0 n) σ i) =
        (children M i).map (bumpTerm M σ i) := by
      rw [hS.ch]; exact List.map_congr_left (fun c hc => hS.bt c hc σ)
    rw [hlist]
    have hkle : ∀ c ∈ children M i, ∀ k ∈ children M c, k ≤ r + L := fun c _ k hk => by
      have := (mem_children hk).2; omega
    -- a bump term whose children do not change
    have hsame : ∀ c ∈ children M i, (∀ k ∈ children M c, ¬ DepX M (r + L) true k) →
        bumpTerm M σ i c = bumpTerm M ρ i c := by
      intro c hc hnd
      unfold bumpTerm
      split
      · congr 2
        exact List.map_congr_left (fun k hk => hoff k (hkle c hc k hk) (hnd k hk))
      · rfl
    by_cases hiv : DepX M (r + L) false i
    · obtain ⟨_, _, hcase⟩ := hVS i h hiv
      rcases hcase with ⟨h2, _⟩ | ⟨_, Li, K, j', k', hch, hjb, hchj, _, hKnd, hLnd⟩
      · exact absurd h2 he2
      · have hM := hTD i he1 he2
        have hj'c : j' ∈ children M i := by rw [hch]; simp
        rw [hch, List.map_append, List.map_singleton] at hM ⊢
        have hLi : Li.map (bumpTerm M σ i) = Li.map (bumpTerm M ρ i) :=
          List.map_congr_left (fun c hc => hsame c (by rw [hch]; simp [hc]) (fun k hk => (hLnd c hc k hk).2))
        have hlt : bumpTerm M σ i j' ≤ bumpTerm M ρ i j' := by
          unfold bumpTerm
          rw [if_pos hjb, if_pos hjb]
          have hot1 : ∀ t ∈ (children M j').map σ.o, isOT t = true := by
            intro t ht; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hGσ k (hkle j' hj'c k hk)
          have hot2 : ∀ t ∈ (children M j').map ρ.o, isOT t = true := by
            intro t ht; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2
          exact omega_le_omega (isOT_sumN _ hot1) (isOT_sumN _ hot2)
            (sumN_le2 (forall2_map_le (fun k hk => hles k (hkle j' hj'c k hk))) hot1 hot2)
        have hnz : ∀ t, bumpTerm M t i j' ≠ z := by
          intro t; unfold bumpTerm; rw [if_pos hjb]; exact omega_ne_z _
        rw [nzs_append, nzs_single (hnz ρ)] at hM
        rw [hLi, nzs_append, nzs_single (hnz σ)]
        exact pairwise_snoc_lower hM hlt
    · have : (children M i).map (bumpTerm M σ i) = (children M i).map (bumpTerm M ρ i) := by
        apply List.map_congr_left
        intro c hc
        by_cases hcb : col M c = bump M i
        · exact hsame c hc (fun k hk hd => hiv (DepX.vbump he1 he2 hc hcb hk hd))
        · unfold bumpTerm; rw [if_neg hcb, if_neg hcb]
      rw [this]; exact hTD i he1 he2
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    by_cases ha : a < (n - 1) * L
    · rw [e1_gexp_shift hlen hL hn ha] at he1
      rw [e2_copy (d0 := d0) hlen hL hn ha] at he2
      rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.map_map]
      have : (children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map
          (bumpTerm (TRIO.gexp M r L d0 0 n) σ (r + L + a) ∘ (· + L)) =
          (children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map
            (bumpTerm (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a)) := by
        apply List.map_congr_left
        intro d hd
        exact bumpTerm_copy hlen hL hA hd0e hn ha hd
      rw [this]; exact hTDP (r + a) he1 he2
    · have hnil : children (TRIO.gexp M r L d0 0 n) (r + L + a) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc; have := mem_children hc; omega
      rw [hnil]; exact List.Pairwise.nil

end

/-- The two bump invariants as one carried property. -/
def BumpDec (N : Mat) (σ : Valn) : Prop := BumpKidsDec N σ ∧ BumpTermDec N σ

/-- **BumpKidsDec and BumpTermDec are carried** (`t = 1`), with the structural hypotheses from the invariants
of `M`. -/
theorem expStep_bumpDec_t1 {M : Mat} {r L d0 q : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some q)
    {ρ : Valn} (hG : Good3 M ρ) (hB : BumpDec M ρ) : ExpStepT1 BumpDec M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hv => dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  intro n hn ρP Z _ _ hBP _ hGN _ _ hle hlex
  have hlN := len_N (d0 := d0) hlen hn
  have hxnb := hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn
  exact ⟨bumpKidsDec_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (hZ2 r) hiu hiux hVS hle hlex hB.1 hBP.1,
    bumpTermDec_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (hZ2 r) hiu hiux hVS hle hlex hG
      (fun k hk => hGN.ot_o k (by have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)) hB.2 hBP.2⟩

end Ytosk
