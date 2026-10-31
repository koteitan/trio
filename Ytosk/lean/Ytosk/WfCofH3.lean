/-
**WfCofH3 (2026-11-01): `HEngD` and `HPathRD` from one engine lower bound on the path.**

The engine lemma that gives both (named hypothesis `HEngPath`): for the diagonal type (`t = 1`), the true valuation
`σ` of `A[n]` (`n ≥ 2`) satisfies, at every row-0 ancestor `c` of `x` with `c ≤ r` (the path `Rt → … → r`, all
inside `DepX A x true`, `dep_anc_x`),

    fsD(o_A(c), Y_n) ≤ σ.o(c),        Y_n = σ.o(x).

This is the lower half of the engines' conclusions: (E3) of the q ≠ r engine (`fsD(old, ζ) ≤ σ < old` on the
closure, WfQnE) and, for q = r, `DQ η false (o_A c) (σ.o c)` of `qr_engineDQ2` (a `DQ` value is `fsD` with summands
`≥ lN` inserted, so it is `≥ fsD`), both at the index `ζ = η = Y_n`.

- `hPathRD_of` : `HEngPath → HPathRD` (`c = r`).
- `hEngD_of`   : `Desc3 → HGood3 → HDiagT1 → HEngPath → HRootSP → HEngD` (`c = Rt`, the last root; the earlier
  roots keep their values by `t1_core` (they are not in `DepX`, `depX_ge`), and
  `fsD(app S o(Rt), Y) = app S (fsD(o(Rt), Y)) ≤ app S σ.o(Rt)`).
- `HRootSP` : the root values of a standard matrix are single and decreasing (audit fields `rootS`, `rootP`: 0
  failures on 23,201,224 matrices).
-/
import Ytosk.WfCofH2
import Ytosk.WfQnL7

namespace Ytosk.WfCofH3

open T Ytosk Ytosk.WfCofH2

set_option linter.unusedSectionVars false

/-- **The engine lower bound on the path** (diagonal type). -/
def HEngPath : Prop :=
  ∀ A tA a b μ, DiagCase A tA a b μ → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ n, 2 ≤ n → ∀ σ rk, Cons (expand A n) σ → Rk (expand A n) rk →
      ∀ c, Anc0 A c (A.length - 1) → c ≤ r → fsD (ρA.o c) (σ.o (A.length - 1)) ≤ σ.o c

/-- The root values of a standard matrix are single and decreasing. -/
def HRootSP : Prop :=
  ∀ M ρ rk, Std M → Cons M ρ → Rk M rk →
    (∀ i ∈ roots M, Single (ρ.o i)) ∧ ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

theorem anc_of_broot {A : Mat} {r : Nat} (hr : BRoot A r) : Anc0 A r (A.length - 1) :=
  anc0_of_par A _ r _ hr

/-- **`HPathRD`** is the engine bound at `c = r`. -/
theorem hPathRD_of (hE : HEngPath) : HPathRD := by
  intro A tA a b μ hcase r hr ρA rkA hCA hRA n hn σ rk hC hR
  exact hE A tA a b μ hcase r hr ρA rkA hCA hRA n hn σ rk hC hR r (anc_of_broot hr) (le_refl r)

/-- **`HEngD`** from the engine bound at the last root. -/
theorem hEngD_of (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP) : HEngD := by
  intro A hAs hS hNE hz tA hv a b μ hDg n hn σ rk hC hR
  have hcase : DiagCase A tA a b μ := ⟨hAs, hS, hNE, hz, hv, hDg⟩
  obtain ⟨r, hr⟩ := WfCofH1.hRootD A tA a b μ hcase
  have ht := hT A tA a b μ hcase
  obtain ⟨ρA, rkA, hCA, hRA, rfl⟩ := hv
  have I := sInv_std hAs hS
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hNE
  have hx : A.length - 1 + 1 = A.length := by omega
  -- the last root
  obtain ⟨Rt, hRA0, hR0, hRl⟩ := root_t1 I.r01 I.r12 I.e00 (A.length - 1)
  have hR0e : entry A 0 Rt = 0 := e0_of_col hR0
  have hrA := anc_of_broot hr
  have hRr : Rt ≤ r := by
    by_contra hlt
    have := anc0_interval hrA Rt (by omega) hRA0.le
    omega
  have hEP := hE A _ a b μ hcase r hr ρA rkA hCA hRA n hn σ rk hC hR Rt hRA0 hRr
  -- the earlier roots keep their values
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨_, tP, _, hvP, _, _⟩ := hD A m hAs hS hNE
  obtain ⟨ρP, rkP, hCP, hRP, _⟩ := hvP
  have hcore := (t1_core hD hG A hAs hS hNE hz ht r hr ρA rkA hCA hRA m (by omega) ρP rkP σ rk hCP hRP hC hR).2
  -- the roots of `A[n]`
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
  have hsrow : TRIO.srow A (A.length - 1) = 1 := by rw [← WfCofH1.lastTy_eq]; exact ht
  have hzT : ¬ (TRIO.entry A 0 (A.length - 1) = 0 ∧ TRIO.entry A 1 (A.length - 1) = 0 ∧
      TRIO.entry A 2 (A.length - 1) = 0) := fun h => hz ((col_zero_iff A _).mpr h)
  have hpar : par A (TRIO.srow A (A.length - 1)) (A.length - 1) = some r := by rw [hsrow]; exact hr1
  have hexp : expand A (m + 1) = TRIO.gexp A r L d0 0 (m + 1) := by
    rw [expand_eq_gexp_t1 A (m + 1) (by omega) hzT hpar hsrow, ← hLd, ← hd0d]
  have hroots : roots (expand A (m + 1)) = roots A := by
    rw [hexp]; exact roots_N_t1 hlen hL hA0 hd0e hn
  -- split the roots at `Rt`
  have hsplit := roots_split hx hRA0 hR0
  set pre := (roots A).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hpre_eq : ∀ c ∈ pre, σ.o c = ρA.o c := by
    intro c hc
    have hcR := hpre_lt c hc
    apply hcore c (by omega)
    intro hd
    have := depX_ge hx hR0e hRA0.le hRl hd
    omega
  have hMl : (roots A).map ρA.o = pre.map ρA.o ++ [ρA.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  have hNl : (roots (expand A (m + 1))).map σ.o = pre.map ρA.o ++ [σ.o Rt] := by
    rw [hroots, hsplit, List.map_append, List.map_singleton]
    congr 1
    exact List.map_congr_left hpre_eq
  obtain ⟨hsA, hpA⟩ := hRS A ρA rkA hAs hCA hRA
  obtain ⟨hsN, hpN⟩ := hRS _ σ rk (Std.exp _ hAs) hC hR
  have hsAl : ∀ t ∈ pre.map ρA.o ++ [ρA.o Rt], Single t := by
    intro t ht'
    rw [← hMl] at ht'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
    exact hsA i hi
  have hsNl : ∀ t ∈ pre.map ρA.o ++ [σ.o Rt], Single t := by
    intro t ht'
    rw [← hNl] at ht'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
    exact hsN i hi
  have hrootA : root A ρA = app (sumN (pre.map ρA.o)) (ρA.o Rt) := by
    rw [root_eq_roots hsA hpA, hMl]
    rw [hMl] at hpA
    exact sumN_snoc_dec hsAl hpA
  have hrootN : root (expand A (m + 1)) σ = app (sumN (pre.map ρA.o)) (σ.o Rt) := by
    rw [root_eq_roots hsN hpN, hNl]
    rw [hNl] at hpN
    exact sumN_snoc_dec hsNl hpN
  have hRne : ρA.o Rt ≠ z := by
    obtain ⟨s, y, hsy⟩ := o_psi_form hCA (i := Rt) (by omega)
    rw [hsy]; simp
  rw [hrootA, hrootN, fsD_app _ hRne]
  exact app_le_app_left _ hEP

/-- **`EvalFSNZ 2`** with the remaining named facts: `HEngPath` (engine), `HGood3`, `HRootSP` (value invariants),
`HDiagT1`, `HCID`, `HCountS`. -/
theorem evalFSNZ2_of_H (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (h3 : HCID) (hCS : HCountS) : EvalFSNZ 2 :=
  evalFSNZ2_of_facts hD (hEngD_of hD hG hT hE hRS) WfCofH1.hRootD (hShiftD_of hD hG hT) (hPathRD_of hE) h3
    WfCofH1.hNotSucc hCS

end Ytosk.WfCofH3
