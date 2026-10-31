/-
**WfQnH8 (2026-11-01): (E3) inside the closure via the `◁` engine `WfQnH7.deps_lhd_otU`.**
Seeds `S` = the bad leaves `(false, i)`, `i ∈ B`; then `DepS M S = DepXB M B` (`depS_iff`).  The unchanged set
`U b i := ¬ DepX M x b i`.  Here:
- `hoff_of_E1`: the `hoff` of the engine from (E1) (`WfQnL5.E1_M` / `WfQnH5.t1_E1B`): off `D` the solution is `ρ`.
- `hOTn_of_E1`: the `hOTn` of the engine from (E1) and the standard form of the glue values on `D`.
- `e3_root`: the engine's conclusion at the root gives the `hE3` of `WfQnH5.t1_rootB`.
-/
import Ytosk.WfQnH6
import Ytosk.WfQnH7

namespace Ytosk.WfQnH8
open T Ytosk Ytosk.WfQnE3

/-- The seeds: the bad leaves. -/
def SB (B : Nat → Prop) : Bool → Nat → Prop := fun b i => b = false ∧ B i

theorem depS_of_depXB {M : Mat} {B : Nat → Prop} : ∀ {b i}, DepXB M B b i → DepS M (SB B) b i := by
  intro b i h
  induction h with
  | leaf h => exact DepS.seed ⟨rfl, h⟩
  | ochild hc hb hu _ ih => exact DepS.ochild hc hb hu ih
  | ov _ ih => exact DepS.ov ih
  | vpar h1 hm _ ih => exact DepS.vpar h1 hm ih
  | vupg h1 h2 hk _ ih => exact DepS.vupg h1 h2 hk ih
  | vbump h1 h2 hj hb hk _ ih => exact DepS.vbump h1 h2 hj hb hk ih

theorem depXB_of_depS {M : Mat} {B : Nat → Prop} : ∀ {b i}, DepS M (SB B) b i → DepXB M B b i := by
  intro b i h
  induction h with
  | seed h => obtain ⟨rfl, h⟩ := h; exact DepXB.leaf h
  | ochild hc hb hu _ ih => exact DepXB.ochild hc hb hu ih
  | ov _ ih => exact DepXB.ov ih
  | vpar h1 hm _ ih => exact DepXB.vpar h1 hm ih
  | vupg h1 h2 hk _ ih => exact DepXB.vupg h1 h2 hk ih
  | vbump h1 h2 hj hb hk _ ih => exact DepXB.vbump h1 h2 hj hb hk ih

theorem depS_iff {M : Mat} {B : Nat → Prop} {b : Bool} {i : Nat} : DepS M (SB B) b i ↔ DepXB M B b i :=
  ⟨depXB_of_depS, depS_of_depXB⟩

section
variable {M N : Mat} {x : Nat} {ρ ρN σ : Valn} {B : Nat → Prop} {ζ : T}
  (hB : ∀ i, B i → DepX M x false i) (hxN : x < N.length)
  (hE1o : ∀ i, i < N.length → ¬ (i < x ∧ DepXB M B true i) → σ.o i = (glueZ M x ρ ρN (fun _ => ζ)).o i)
  (hE1v : ∀ i, i < N.length → ¬ (i < x ∧ DepXB M B false i) → σ.v i = (glueZ M x ρ ρN (fun _ => ζ)).v i)
include hB hxN hE1o hE1v

/-- **`hoff` of the engine** with `U b i := ¬ DepX M x b i`. -/
theorem hoff_of_E1 : ∀ i, i < x →
    ((fun b i => ¬ DepX M x b i) true i → σ.o i = ρ.o i) ∧
    ((fun b i => ¬ DepX M x b i) false i → σ.v i = ρ.v i) := by
  intro i hi
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · rw [hE1o i (by omega) (fun h => hn (DepXB.sub hB h.2)), glueZ_o_lt ρ ρN _ hi hn]
  · rw [hE1v i (by omega) (fun h => hn (DepXB.sub hB h.2)), glueZ_v_lt ρ ρN _ hi hn]

/-- **`hOTn` of the engine**: off the closure the solution is the glue, standard by `hOTD` on `D`. -/
theorem hOTn_of_E1 (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hOTD : ∀ b j, j < x → DepX M x b j → isOT (fsD (valB ρ b j) ζ) = true) :
    ∀ b j, j < x → ¬ DepS M (SB B) b j → isOT (valB σ b j) = true := by
  intro b j hj hn
  have hnb : ¬ DepXB M B b j := fun h => hn (depS_of_depXB h)
  cases b
  · show isOT (σ.v j) = true
    rw [hE1v j (by omega) (fun h => hnb h.2)]
    by_cases hd : DepX M x false j
    · rw [glueZ_v_dep ρ ρN _ hj hd]; exact hOTD false j hj hd
    · rw [glueZ_v_lt ρ ρN _ hj hd]; exact hG.ot_v j (by omega)
  · show isOT (σ.o j) = true
    rw [hE1o j (by omega) (fun h => hnb h.2)]
    by_cases hd : DepX M x true j
    · rw [glueZ_o_dep ρ ρN _ hj hd]; exact hOTD true j hj hd
    · rw [glueZ_o_lt ρ ρN _ hj hd]; exact hG.ot_o j (by omega)

end

/-- **(E3) at the root from the engine's conclusion.** -/
theorem e3_root {M N : Mat} {x : Nat} {ρ σ : Valn} {B : Nat → Prop} {Rt : Nat}
    (hCN : Cons N σ) (hRx : Rt < x) (hxN : x ≤ N.length)
    (hEng : ∀ b i, DepS M (SB B) b i → i < x → Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true) :
    DepXB M B true Rt → Single (σ.o Rt) ∧ σ.o Rt < ρ.o Rt := by
  intro h
  have := hEng true Rt (depS_of_depXB h) hRx
  exact WfQnH6.e3_of_lhd hCN (by omega) this.1 this.2

end Ytosk.WfQnH8
