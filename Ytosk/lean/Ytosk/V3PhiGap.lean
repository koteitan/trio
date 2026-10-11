/-
**PhiX の分解: 正の段の穴は「隙間なし」から、残りは段 0 の穴だけ。**

実測（C′、2026-10-11、groupA）:
- 行 1 の子を持つ列 p の v(p) は、正の段 μ の隙間 [ψ_μ(Ω_{μ+1}), Ω_{μ+1}) に部分項を持たない
  （`NoGapP`、215 万件で例外 0）。行 1 の子を持つ列は行 2 が 0 で、1 列落としで v(p) は変わらない（53 万件）。
- したがって PhiX の場面のうち穴の段が 0 でないものは `reach_gap` で出る（`phiX_of_noGap`）。
- 段 0 の穴（`PhiX0`）は隙間の形では書けない: 段 0 の隙間に入る部分項は C′ で 126 場面ある（v(p) 自身が
  [ψ_0(Ω_1), Ω_1) にある場合だけ）。そこでは比較が穴の位置に届かないことで PhiX が成り立つ。
-/
import Ytosk.V3GroupA

namespace Ytosk

open T

/-- **No gap at a positive level**: no subterm of `V` lies in `[ψ_μ(Ω_{μ+1}), Ω_{μ+1})` for `μ ≠ 0`. -/
def NoGap (V : T) : Prop :=
  ∀ μ, μ ≠ z → ∀ u, SubS V u → u < psi (succ μ) z z → u < etaOm μ

/-- **No gap at level 0**: no subterm of `V` lies in `[ψ_0(Ω_1), Ω_1)`. -/
def NoGap0 (V : T) : Prop :=
  ∀ u, SubS V u → u < psi (succ z) z z → u < etaOm z

/-- **Value invariant**: every column with a row-1 child has a `v` without gaps at positive levels. -/
def NoGapP (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p, c < M.length → par M 1 c = some p → NoGap (ρ.v p)

/-- **PhiX at holes of level 0.** -/
def PhiX0 (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p, c < M.length → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c → OHole (bumpW M ρ c) →
    holeLev (bumpW M ρ c) = z →
    Reach (SubS (ρ.v p)) (bumpW M ρ c) (etaOm (holeLev (bumpW M ρ c)))

/-- A column on the row-1 chain of a column of `M` is the row-1 parent of a column of `M`. -/
theorem P1Chain.has_child {M : Mat} {p c : Nat} (h : P1Chain M p c) (hc : c < M.length) :
    ∃ c', c' < M.length ∧ par M 1 c' = some p := by
  induction h with
  | one hp => exact ⟨_, hc, hp⟩
  | step hm _ ih => exact ih (by have := par_lt M 1 _ _ hm; omega)

/-- **Reach from the absence of a gap at the hole level.** -/
theorem reach_of_gapFree {V X : T} (hO : OHole X)
    (hg : ∀ u, SubS V u → u < psi (succ (holeLev X)) z z → u < etaOm (holeLev X)) :
    Reach (SubS V) X (etaOm (holeLev X)) :=
  reach_gap (subClosed_subS V) hO hg

/-- **A PhiX instance at a hole of positive level** follows from `NoGap`. -/
theorem reach_of_noGap {V X : T} (hO : OHole X) (hμ : holeLev X ≠ z) (h : NoGap V) :
    Reach (SubS V) X (etaOm (holeLev X)) :=
  reach_of_gapFree hO (h _ hμ)

/-- **A PhiX instance at a hole of level 0** follows from `NoGap0`. -/
theorem reach_of_noGap0 {V X : T} (hO : OHole X) (hμ : holeLev X = z) (h : NoGap0 V) :
    Reach (SubS V) X (etaOm (holeLev X)) :=
  reach_of_gapFree hO (by rw [hμ]; exact h)

section
variable {M : Mat} {ρ : Valn}

/-- **PhiX from `NoGapP` and the level-0 part.** -/
theorem phiX_of_noGap (hN : NoGapP M ρ) (h0 : PhiX0 M ρ) : PhiX M ρ := by
  intro c p hc h1 h2 hch hO
  by_cases hμ : holeLev (bumpW M ρ c) = z
  · exact h0 c p hc h1 h2 hch hO hμ
  · obtain ⟨c', hc', hp⟩ := hch.has_child hc
    exact reach_of_noGap hO hμ (hN c' p hc' hp)

/-- **PhiX0 from `NoGap0` on the chain** (the level-0 part needs an argument only where some `v(p)` on the
chain has a subterm in `[ψ_0(Ω_1), Ω_1)`). -/
theorem phiX0_of_noGap0 (h : ∀ c p, c < M.length → par M 1 c = some p → NoGap0 (ρ.v p)) : PhiX0 M ρ := by
  intro c p hc _ _ hch hO hμ
  obtain ⟨c', hc', hp⟩ := hch.has_child hc
  exact reach_of_noGap0 hO hμ (h c' p hc' hp)

/-- **The level-0 residual of PhiX**: level-0 holes where `v(p)` has a subterm in `[ψ_0(Ω_1), Ω_1)`
(C′ で 122 場面、v(p) 自身がその区間にある場合だけ). -/
def PhiX0R (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p, c < M.length → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c → OHole (bumpW M ρ c) →
    holeLev (bumpW M ρ c) = z → ¬ NoGap0 (ρ.v p) →
    Reach (SubS (ρ.v p)) (bumpW M ρ c) (etaOm (holeLev (bumpW M ρ c)))

theorem phiX0_of_res (h : PhiX0R M ρ) : PhiX0 M ρ := by
  intro c p hc h1 h2 hch hO hμ
  by_cases hg : NoGap0 (ρ.v p)
  · exact reach_of_noGap0 hO hμ hg
  · exact h c p hc h1 h2 hch hO hμ hg

/-- **The carried form**: `NoGapP ∧ PhiX0R` gives PhiX (hence AbsD and AbsU). -/
theorem phiX_of_noGapR (hN : NoGapP M ρ) (h0 : PhiX0R M ρ) : PhiX M ρ :=
  phiX_of_noGap hN (phiX0_of_res h0)

end

/-! ## 1 列落とし M → M.take x

行 1 の子を持つ列の v は変わらない（`chg_struct`: 変わる v の列は行 1 の子を持たない）。したがって `NoGapP` は
そのまま運べる。PhiX の残りは段 0 の穴で、v(p) が [ψ_0(Ω_1), Ω_1) に部分項を持ち、W が変わる場面だけ
（C′ で 45 件、穴への経路の最後はどれも ψ_a(…Ω_1) の引数）。
-/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **A column with a row-1 child keeps its `v` in the drop.** -/
theorem v_take_of_par1 {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') {c p : Nat} (hc : c < x)
    (hp : par M 1 c = some p) : ρ'.v p = ρ.v p := by
  have hpc := par_lt M 1 c p hp
  exact (chg_off hx hC hG hC' hR' p (by omega)).2 (fun hch =>
    ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hch).1 rfl (by omega)).2.2 c hc hp)

/-- **`NoGapP` passes to `M.take x`.** -/
theorem noGapP_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hN : NoGapP M ρ) : NoGapP (M.take x) ρ' := by
  intro c p hc hp
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  rw [hlen] at hc
  rw [par_take M 1 c hc] at hp
  rw [v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc hp]
  exact hN c p (by omega) hp

omit hR0 hZ2 hSD hZ1 hUAT hUAB in
/-- The row-1 chain of a column of `M.take x` is its chain in `M`. -/
theorem p1Chain_of_take {p c : Nat} (h : P1Chain (M.take x) p c) (hc : c < x) : P1Chain M p c := by
  induction h with
  | one hp => rw [par_take M 1 _ hc] at hp; exact .one hp
  | @step m c hm _ ih =>
    rw [par_take M 1 _ hc] at hm
    exact .step hm (ih (by have := par_lt M 1 _ _ hm; omega))

/-- **The level-0 residual of the drop**: a level-0 hole of a changed bump term, with `v(p)` having a subterm
in `[ψ_0(Ω_1), Ω_1)`. -/
def DropPhi0Res (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ c p, c < x → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c →
    OHole (bumpW (M.take x) ρ' c) → holeLev (bumpW (M.take x) ρ' c) = z → ¬ NoGap0 (ρ.v p) →
    bumpW (M.take x) ρ' c ≠ bumpW M ρ c →
    Reach (SubS (ρ.v p)) (bumpW (M.take x) ρ' c) (etaOm (holeLev (bumpW (M.take x) ρ' c)))

/-- **The carried form passes to `M.take x`**, modulo the level-0 residual `DropPhi0Res`. -/
theorem phiXR_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hN : NoGapP M ρ) (h0 : PhiX0R M ρ)
    (hres : DropPhi0Res M x ρ ρ') : NoGapP (M.take x) ρ' ∧ PhiX0R (M.take x) ρ' := by
  have hN' := noGapP_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hN
  refine ⟨hN', ?_⟩
  intro c p hc h1 h2 hch hO hμ hg
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  rw [hlen] at hc
  rw [entry_take M 1 hc] at h1
  rw [entry_take M 2 hc] at h2
  have hchM := p1Chain_of_take hx hch hc
  obtain ⟨c', hc', hp⟩ := hch.has_child (by rw [hlen]; exact hc)
  rw [hlen] at hc'
  rw [par_take M 1 c' hc'] at hp
  rw [v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc' hp] at hg ⊢
  by_cases hW : bumpW (M.take x) ρ' c = bumpW M ρ c
  · rw [hW] at hO hμ ⊢
    exact h0 c p (by omega) h1 h2 hchM hO hμ hg
  · exact hres c p hc h1 h2 hchM hO hμ hg hW

/-- **PhiX passes to `M.take x`**, modulo the level-0 residual `DropPhi0Res`. -/
theorem phiX_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hN : NoGapP M ρ) (h0 : PhiX0R M ρ)
    (hres : DropPhi0Res M x ρ ρ') : PhiX (M.take x) ρ' ∧ NoGapP (M.take x) ρ' := by
  obtain ⟨hN', h0'⟩ := phiXR_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hN h0 hres
  exact ⟨phiX_of_noGapR hN' h0', hN'⟩

end

end Ytosk
