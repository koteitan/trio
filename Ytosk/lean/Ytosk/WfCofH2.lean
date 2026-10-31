/-
**WfCofH2 (2026-11-01): the copy shift `HShiftD` from `true_glue_eq`.**

For a standard `A ≠ SRO` whose last column has type `t = 1` (`lastTy A = 1`), bad root `r`, `x = r + L`:
the true valuation of `A[n+1]` (`n ≥ 2`) at `x` is the value of `A[n]` at `r`:

    o_{A[n+1]}(x) = o_{A[n]}(r).

Proof: `true_glue_eq` (WfQrL18) says the true valuation of `N = A[n+1]` is the glue of its own `D` values, the
values of `A` off `D`, and the valuation of `P = A[n]` shifted by one copy (`shiftV`, `cons_copy`). Its hypothesis
`hagree` (the copies of `P` read the same good-part `v` in `A` and `P`) is carried by induction on the number of
copies: at `P = A[1] = A.take x` by `base_v_read` (V3BaseDrop, needs `Good3 A ρ`), and for `P = A[m]`, `m ≥ 2`, by
the conclusion `σ.v g = ρ.v g` off `DepX` of `true_glue_eq` itself together with `hnd_t1`. All structural
hypotheses come from `sInv_std`; the valuations of `A[m]` from `Desc3`.

Named hypotheses (both measured with 0 failures, both outside this file's reach):
- `HGood3` : the valuation of a standard `A ≠ SRO` satisfies `Good3` (audit field `good`: 0 / 708,797,194).
- `HDiagT1` : a diagonal point in `tA` forces `lastTy A = 1` (WfCofL probe: t = 1 ⇔ DiagAt on all 73 files).
-/
import Ytosk.WfCofH1
import Ytosk.WfQrL18
import Ytosk.V3MainT1D

namespace Ytosk.WfCofH2

open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL18

set_option linter.unusedSectionVars false

/-- The valuation of a standard matrix other than SRO is `Good3`. -/
def HGood3 : Prop :=
  ∀ A ρ rk, Std A → A ≠ SRO → A ≠ [] → Cons A ρ → Rk A rk → Good3 A ρ

/-- A diagonal point forces the last column type `t = 1`. -/
def HDiagT1 : Prop := ∀ A tA a b μ, DiagCase A tA a b μ → lastTy A = 1

/-- The copy shift for `t = 1`, for every standard matrix (no diagonal point needed). -/
def HShift1 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 1 →
    ∀ r, BRoot A r → ∀ n, 2 ≤ n → ∀ ρ rk ρ' rk', Cons (expand A n) ρ → Rk (expand A n) rk →
      Cons (expand A (n + 1)) ρ' → Rk (expand A (n + 1)) rk' →
      ρ'.o (A.length - 1) = ρ.o r

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0) (hz2 : entry M 2 r ≤ 1)
  (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
  {ρ : Valn} (hC : Cons M ρ)
include hlen hL hA hd0e hpath hx2 hz2 hxnb hnd hC

/-- **One step**: from a valuation `ρP` of `M[m]` whose copies read the good-part `v` of `M`, the true valuation `σ`
of `M[m+1]` has `σ.o x = ρP.o r` and keeps the `v` of `M` off `DepX`. -/
theorem shift_step {m : Nat} (hm : 1 ≤ m) {ρP σ : Valn} {rkN : Bool → Nat → Nat}
    (hCP : Cons (TRIO.gexp M r L d0 0 m) ρP)
    (hPv : ∀ g, g ≤ r → ∀ a, a < m * L →
      (par (TRIO.gexp M r L d0 0 m) 1 (r + a) = some g ∨ upg (TRIO.gexp M r L d0 0 m) (r + a) = some g) →
      ρ.v g = ρP.v g)
    (hCN : Cons (TRIO.gexp M r L d0 0 (m + 1)) σ) (hRN : Rk (TRIO.gexp M r L d0 0 (m + 1)) rkN) :
    σ.o (r + L) = ρP.o r ∧ (∀ g, g < r + L → ¬ DepX M (r + L) false g → σ.v g = ρ.v g) ∧
      (∀ c, c < r + L → ¬ DepX M (r + L) true c → σ.o c = ρ.o c) := by
  have hn : 2 ≤ m + 1 := by omega
  have hsub : m + 1 - 1 = m := by omega
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 hz2 hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 hz2 hn
  have hCP' : Cons (TRIO.gexp M r L d0 0 (m + 1 - 1)) ρP := by rw [hsub]; exact hCP
  have hagree : ∀ g, g ≤ r → ∀ a, a < (m + 1 - 1) * L →
      (par (TRIO.gexp M r L d0 0 (m + 1 - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (m + 1 - 1)) (r + a) = some g) →
      (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v).v g = ρP.v g := by
    intro g hg a ha hr
    rw [glueQ_v_lt (by omega) (hnd (m + 1) hn g hg a ha hr)]
    rw [hsub] at ha hr
    exact hPv g hg a ha hr
  obtain ⟨hag, -, -⟩ := true_glue_eq hlen hL hA hd0e hn hpath hx2 (hxnb (m + 1) hn) hz2 hiu hiux hC hCP'
    hCN hRN hagree
  have hlN := len_N (d0 := d0) (n := m + 1) hlen hn
  have hpos : 0 < (m + 1 - 1) * L := Nat.mul_pos (by omega) hL
  refine ⟨?_, fun g hg hd => ?_, fun c hc hd => ?_⟩
  · rw [(hag (r + L) (by omega)).1, glueQ_o_ge (le_refl _)]
    show ρP.o (r + L - L) = ρP.o r
    rw [Nat.add_sub_cancel]
  · rw [(hag g (by omega)).2, glueQ_v_lt hg hd]
  · rw [(hag c (by omega)).1, glueQ_o_lt hc hd]

end

theorem e2_zero_of_lastTy {A : Mat} (h : lastTy A = 1) : entry A 2 (A.length - 1) = 0 := by
  unfold lastTy at h
  by_contra hne
  rw [if_pos (by omega)] at h
  cases h


/-- **The true valuation of `A[n+1]` for `t = 1`** (`n ≥ 1`), from `Desc3` and `Good3`: at `x` it is the value of
`A[n]` at `r`, and off `DepX` (o side) it is the valuation of `A`. -/
theorem t1_core (hD : Desc3) (hG : HGood3) (A : Mat) (hAs : Std A) (hS : A ≠ SRO) (hE : A ≠ [])
    (hz : col A (A.length - 1) ≠ (0, 0, 0)) (ht : lastTy A = 1) (r : Nat) (hr : BRoot A r)
    (ρ : Valn) (rkA : Bool → Nat → Nat) (hC : Cons A ρ) (hRA : Rk A rkA) :
    ∀ n, 1 ≤ n → ∀ ρN rkN ρN' rkN', Cons (expand A n) ρN → Rk (expand A n) rkN →
      Cons (expand A (n + 1)) ρN' → Rk (expand A (n + 1)) rkN' →
      ρN'.o (A.length - 1) = ρN.o r ∧
      ∀ c, c < A.length - 1 → ¬ DepX A (A.length - 1) true c → ρN'.o c = ρ.o c := by
  intro n hn ρN rkN ρN' rkN' hCN hRN hCN' hRN'
  have I := sInv_std hAs hS
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hE
  have hr1 : par A 1 (A.length - 1) = some r := by
    have := hr; unfold BRoot at this; rw [ht] at this; exact this
  have hrx : r < A.length - 1 := par_lt A 1 _ r hr1
  obtain ⟨L, hLd⟩ : ∃ L, L = A.length - 1 - r := ⟨_, rfl⟩
  have hlen : r + L + 1 = A.length := by omega
  have hL : 0 < L := by omega
  have hxe : A.length - 1 = r + L := by omega
  have h1 : par A 1 (r + L) = some r := by rw [← hxe]; exact hr1
  have hA0 : Anc0 A r (r + L) := anc0_of_par A 1 r (r + L) h1
  obtain ⟨d0, hd0d⟩ : ∃ d0, d0 = entry A 0 (A.length - 1) - entry A 0 r := ⟨_, rfl⟩
  have hd0e : entry A 0 (r + L) = entry A 0 r + d0 := by
    have := anc0_interval hA0 (r + L) (by omega) (le_refl _)
    rw [hd0d, hxe]; omega
  have hx2 : entry A 2 (r + L) = 0 := by rw [← hxe]; exact e2_zero_of_lastTy ht
  have hrne : r ≠ r + L := by omega
  have hpath := hpath_of_par1 h1 hA0 hrne
  have hz2 : entry A 2 r ≤ 1 := I.z2 r
  have hxnb := hxnb_t1 hlen hL hA0 hd0e I.z2 I.z1c h1
  have hnd := hnd_t1 hlen hL hA0 hd0e I.r0p I.z2 I.sibDec I.z1c I.uat I.uab h1 hx2
  -- the expansion is `gexp`
  have hsrow : TRIO.srow A (A.length - 1) = 1 := by rw [← WfCofH1.lastTy_eq]; exact ht
  have hzT : ¬ (TRIO.entry A 0 (A.length - 1) = 0 ∧ TRIO.entry A 1 (A.length - 1) = 0 ∧
      TRIO.entry A 2 (A.length - 1) = 0) := fun h => hz ((col_zero_iff A _).mpr h)
  have hpar : par A (TRIO.srow A (A.length - 1)) (A.length - 1) = some r := by rw [hsrow]; exact hr1
  have hexp : ∀ k, expand A k = TRIO.gexp A r L d0 0 k := by
    intro k
    rw [expand_eq_gexp_t1 A k (by omega) hzT hpar hsrow, ← hLd, ← hd0d]
  have hGA := hG A ρ rkA hAs hS hE hC hRA
  have hval : ∀ k, ∃ ρk rkk, Cons (TRIO.gexp A r L d0 0 k) ρk ∧ Rk (TRIO.gexp A r L d0 0 k) rkk := by
    intro k
    obtain ⟨_, tk, _, hvk, _, _⟩ := hD A k hAs hS hE
    obtain ⟨ρk, rkk, hCk, hRk, _⟩ := hvk
    exact ⟨ρk, rkk, by rw [← hexp]; exact hCk, by rw [← hexp]; exact hRk⟩
  -- the reads of the copies, by induction on the number of copies
  have Q : ∀ m, 1 ≤ m → ∀ ρP rkP, Cons (TRIO.gexp A r L d0 0 m) ρP → Rk (TRIO.gexp A r L d0 0 m) rkP →
      ∀ g, g ≤ r → ∀ a, a < m * L →
        (par (TRIO.gexp A r L d0 0 m) 1 (r + a) = some g ∨ upg (TRIO.gexp A r L d0 0 m) (r + a) = some g) →
        ρ.v g = ρP.v g := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro ρP rkP hCP hRP g hg a ha hrd
      have h1eq := gexp_one_eq (d0 := d0) hlen
      rw [h1eq] at hCP hRP hrd
      exact base_v_read hlen I.r0p I.z2 I.sibDec I.z1c I.uat I.uab hC hGA hCP hRP hg (by omega) hrd
    | succ m hm ih =>
      intro ρP rkP hCP hRP g hg a ha hrd
      obtain ⟨ρQ, rkQ, hCQ, hRQ⟩ := hval m
      have hst := shift_step hlen hL hA0 hd0e hpath hx2 hz2 hxnb hnd hC hm hCQ (ih ρQ rkQ hCQ hRQ) hCP hRP
      have hndg := hnd (m + 1 + 1) (by omega) g hg a (by simpa using ha) (by simpa using hrd)
      exact (hst.2.1 g (by omega) hndg).symm
  rw [hexp] at hCN hRN hCN' hRN'
  have hst := shift_step hlen hL hA0 hd0e hpath hx2 hz2 hxnb hnd hC (m := n) hn hCN
    (Q n hn ρN rkN hCN hRN) hCN' hRN'
  rw [hxe]; exact ⟨hst.1, hst.2.2⟩

/-- **The copy shift for `t = 1`** from `Desc3` and `Good3`. -/
theorem hShift1 (hD : Desc3) (hG : HGood3) : HShift1 := by
  intro A hAs hS hE hz ht r hr n hn ρN rkN ρN' rkN' hCN hRN hCN' hRN'
  obtain ⟨tA, _, hvA, _, _, _⟩ := hD A 0 hAs hS hE
  obtain ⟨ρ, rkA, hC, hRA, _⟩ := hvA
  exact (t1_core hD hG A hAs hS hE hz ht r hr ρ rkA hC hRA n (by omega) ρN rkN ρN' rkN' hCN hRN hCN' hRN').1

/-- **`HShiftD`** from `Desc3`, `Good3` on standard matrices, and `t = 1` on the diagonal type. -/
theorem hShiftD_of (hD : Desc3) (hG : HGood3) (hT : HDiagT1) : HShiftD := by
  intro A tA a b μ hcase r hr n hn ρ rk ρ' rk' hC hR hC' hR'
  have ht := hT A tA a b μ hcase
  obtain ⟨hA, hS, hE, hz, _, _⟩ := hcase
  exact hShift1 hD hG A hA hS hE hz ht r hr n hn ρ rk ρ' rk' hC hR hC' hR'

end Ytosk.WfCofH2
