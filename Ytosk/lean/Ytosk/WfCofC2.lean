/-
**WfCofC2 (2026-11-01): `HCID` from a local fact at `r` and a one-edge transmission on the path.**

`HCID` (WfCofL3): for the diagonal type, `o_A(r) = ψ_μ(b)` where `ψ_a(b)` is the diagonal point of `tA`
(`DiagAt a b μ tA`) and `r` the bad root.

Proved here:
- `diagAt_unique` : the diagonal point of a term is unique (`a`, `b`, `μ`).
- `diagAt_app`    : a diagonal point of `t ≠ 0` is a diagonal point of `S + t`.
- `hCID_of : HRootSP → HDiagLoc → HDiagStep → HCID`.

Named hypotheses (measured, tmp/wf/WfCofC/notes.md):
- `HDiagLoc`  : `o_A(r) = ψ_ν(B)` with `cof B = Ω_{ν+1}` (so `ψ_ν(B)` is its own diagonal point, subscript `= μ`).
- `HDiagStep` : one edge `c → d` of the row-0 path to `r` (`P_0(d) = c`, `d` an ancestor of `r`): a diagonal point
  `(·, B, ν)` of `o_A(d)` gives a diagonal point `(·, B, ν)` of `o_A(c)` (same `B`, `ν`; the subscript may change —
  measured: the subscript of the point of `tA` differs from `ν` in 12 of 50 samples).
-/
import Ytosk.WfCofC1
import Ytosk.V3FrameT1
import Ytosk.V3ChgS

namespace Ytosk.WfCofC2

open T Ytosk Ytosk.WfCofH2 Ytosk.WfCofH3

set_option linter.unusedSectionVars false

/-- **The diagonal point is unique.** -/
theorem diagAt_unique {a b μ t : T} (h : DiagAt a b μ t) :
    ∀ {a' b' μ'}, DiagAt a' b' μ' t → a = a' ∧ b = b' ∧ μ = μ' := by
  induction h with
  | here hb hc hμ =>
    intro a' b' μ' h'
    cases h' with
    | here _ hc' _ =>
      rw [hc] at hc'
      cases hc'
      exact ⟨rfl, rfl, rfl⟩
    | arg _ _ hD =>
      have := hD.cof_omega
      rw [hc] at this; cases this
    | sub ha _ _ => exact absurd rfl hb
  | rest _ ih =>
    intro a' b' μ' h'
    cases h' with
    | rest h'' => exact ih h''
  | arg hb hs hD ih =>
    intro a' b' μ' h'
    cases h' with
    | here _ hc' _ =>
      have := hD.cof_omega
      rw [hc'] at this; cases this
    | arg _ _ h'' => exact ih h''
    | sub _ _ _ => exact absurd rfl hb
  | sub ha hs hD ih =>
    intro a' b' μ' h'
    cases h' with
    | here hb' _ _ => exact absurd rfl hb'
    | arg hb' _ _ => exact absurd rfl hb'
    | sub _ _ h'' => exact ih h''

/-- A diagonal point survives a prefix. -/
theorem diagAt_app {a b μ t : T} (h : DiagAt a b μ t) : ∀ S, DiagAt a b μ (app S t)
  | z => by simpa [app] using h
  | psi a' b' c => by
    show DiagAt a b μ (psi a' b' (app c t))
    have hne : app c t ≠ z := by
      intro he
      exact h.ne_z (app_eq_z he).2
    obtain ⟨c1, d1, e1, he⟩ : ∃ c1 d1 e1, app c t = psi c1 d1 e1 := by
      cases hct : app c t with
      | z => exact absurd hct hne
      | psi c1 d1 e1 => exact ⟨c1, d1, e1, rfl⟩
    have ih := diagAt_app h c
    rw [he] at ih ⊢
    exact DiagAt.rest ih

/-- A strict ancestor has a child on the path. -/
theorem anc0_child {M : Mat} {c k : Nat} (h : Anc0 M c k) (hne : c ≠ k) :
    ∃ d, par M 0 d = some c ∧ Anc0 M d k := by
  induction h with
  | refl => exact absurd rfl hne
  | @step b k' hp hab ih =>
    by_cases hcb : c = b
    · subst hcb; exact ⟨k', hp, Anc0.refl k'⟩
    · obtain ⟨d, hd, hdb⟩ := ih hcb
      exact ⟨d, hd, Anc0.step hp hdb⟩

/-- **Local fact at the bad root** (diagonal type): `o_A(r) = ψ_ν(B)` with `cof B = Ω_{ν+1}`. -/
def HDiagLoc : Prop :=
  ∀ A tA a b μ, DiagCase A tA a b μ → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∃ ν B, ρA.o r = psi ν B z ∧ B ≠ z ∧ cof B = .big ν

/-- **One edge of the path** (diagonal type): a diagonal point `(·, B, ν)` of `o_A(d)` gives one of `o_A(c)`,
`c = P_0(d)`, `d` an ancestor of `r`. -/
def HDiagStep : Prop :=
  ∀ A tA a b μ, DiagCase A tA a b μ → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ c d, par A 0 d = some c → Anc0 A d r → ∀ a' B ν, DiagAt a' B ν (ρA.o d) →
      ∃ a'', DiagAt a'' B ν (ρA.o c)

theorem hCID_of (hRS : HRootSP) (hL : HDiagLoc) (hSt : HDiagStep) : HCID := by
  intro A tA a b μ hcase r hr ρA rkA hCA hRA
  obtain ⟨hAs, hS, hNE, hz, hv, hDg⟩ := hcase
  have hcase : DiagCase A tA a b μ := ⟨hAs, hS, hNE, hz, hv, hDg⟩
  have I := sInv_std hAs hS
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hNE
  have hx : A.length - 1 + 1 = A.length := by omega
  obtain ⟨ν, B, hor, hB, hcB⟩ := hL A tA a b μ hcase r hr ρA rkA hCA hRA
  have hloc : DiagAt ν B ν (ρA.o r) := by
    rw [hor]; exact DiagAt.here hB hcB (lt_irrefl' ν)
  -- up the path
  have hrA : Anc0 A r (A.length - 1) := anc0_of_par A _ r _ hr
  have key : ∀ m c, r - c = m → Anc0 A c r → ∃ a', DiagAt a' B ν (ρA.o c) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro c hm hc
      by_cases hcr : c = r
      · subst hcr; exact ⟨ν, hloc⟩
      · obtain ⟨d, hd, hdr⟩ := anc0_child hc hcr
        have hcd : c < d := par_lt A 0 d c hd
        have hdr' := hdr.le
        obtain ⟨a', ha'⟩ := ih (r - d) (by omega) d rfl hdr
        exact hSt A tA a b μ hcase r hr ρA rkA hCA hRA c d hd hdr a' B ν ha'
  -- the last root
  obtain ⟨Rt, hRA0, hR0, hRl⟩ := root_t1 I.r01 I.r12 I.e00 (A.length - 1)
  have hRr : Rt ≤ r := by
    by_contra hlt
    have := anc0_interval hrA Rt (by omega) hRA0.le
    have := e0_of_col hR0
    omega
  have hRtr : Anc0 A Rt r := anc_between hRA0 r hRr hrA.le
  obtain ⟨a', hRt⟩ := key (r - Rt) Rt rfl hRtr
  -- the value is the sum of the roots
  have hsplit := roots_split hx hRA0 hR0
  set pre := (roots A).filter (fun c => decide (c < Rt)) with hpre
  have hMl : (roots A).map ρA.o = pre.map ρA.o ++ [ρA.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  obtain ⟨hsA, hpA⟩ := hRS A ρA rkA hAs hCA hRA
  have hsAl : ∀ t ∈ pre.map ρA.o ++ [ρA.o Rt], Single t := by
    intro t ht'
    rw [← hMl] at ht'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
    exact hsA i hi
  have hrootA : root A ρA = app (sumN (pre.map ρA.o)) (ρA.o Rt) := by
    rw [root_eq_roots hsA hpA, hMl]
    rw [hMl] at hpA
    exact sumN_snoc_dec hsAl hpA
  have htA : tA = root A ρA := val_unique hv ⟨ρA, rkA, hCA, hRA, rfl⟩
  have hD' : DiagAt a' B ν tA := by
    rw [htA, hrootA]; exact diagAt_app hRt _
  obtain ⟨_, hbB, hμν⟩ := diagAt_unique hDg hD'
  rw [hor, hbB, hμν]

end Ytosk.WfCofC2
