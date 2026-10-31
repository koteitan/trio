/-
**WfQnH4 (2026-11-01): pieces of the assembly of the q ≠ r engine with the bad closure.**
- `hF_of_pathB`: the conclusion of `WfQnL3.t1_pathB` is the exchange field `hF` of `WfQnL5.E1_M`
  (`Z = fun _ => ζ`).
- `v_bad_M`: in `M` the bad call has the value of the node, `v(i) = A = o(r)` (absorption, `V < A`).
- `leaf_E3`: (E3) at a bad call `i` that is not nested (no bump grandchild of `i` in the closure): a solution `σ`
  of `N = M[n]` that equals the glue off the closure has `σ.v i = sf(v(P₁ i) + A[ζ])`, and
  `fsD(ρ.v i, ζ) ≤ σ.v i < ρ.v i`.
-/
import Ytosk.WfQnH3
import Ytosk.WfQnL7
import Ytosk.WfQnL6

namespace Ytosk.WfQnH4
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad

/-- **The exchange field of (E1) from the path theorem off the closure.** -/
theorem hF_of_pathB {M : Mat} {x : Nat} {ρ ρN : Valn} {B : Nat → Prop} {μ br vr ζ : T}
    (hP : ∀ b i, DepX M x b i → ¬ DepXB M B b i → (i < x ∨ (i = x ∧ b = true)) →
      HoleT μ br vr (valB ρ b i) ∧ (i < x → rhsB M (glue M x ρ ρN ζ) b i = fsD (valB ρ b i) ζ)) :
    ∀ i, i < x →
      (DepX M x true i → ¬ DepXB M B true i →
        oRhs M (glueZ M x ρ ρN (fun _ => ζ)) i = fsD (ρ.o i) ((fun _ => ζ) i)) ∧
      (DepX M x false i → ¬ DepXB M B false i →
        vRhs M (glueZ M x ρ ρN (fun _ => ζ)) i = fsD (ρ.v i) ((fun _ => ζ) i)) :=
  fun i hi => ⟨fun hd hnb => (hP true i hd hnb (Or.inl hi)).2 hi,
    fun hd hnb => (hP false i hd hnb (Or.inl hi)).2 hi⟩

/-- **In `M` the bad call has the value of the node** (`v(P₁ i) < A` is absorbed by `A = W`). -/
theorem v_bad_M {M : Mat} {ρ : Valn} {r i : Nat} {a b : T} (hC : Cons M ρ) (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (hW : bumpW M ρ i = ρ.o r) (hro : ρ.o r = psi a b z)
    (hAot : isOT (ρ.o r) = true) (hVlt : vOpt ρ (par M 1 i) < psi a b z) : ρ.v i = ρ.o r := by
  rw [(hC i hiM).2]
  unfold vRhs
  rw [if_neg h1, if_neg h2]
  have hW' : omega (sumN (one :: (children M i).map (bumpTerm M ρ i))) = ρ.o r := hW
  rw [hW', hro, WfQnE2.add_absorb hVlt, ← hro, sf_ot hAot]

/-- **(E3) at a non-nested bad call.** -/
theorem leaf_E3 {M N : Mat} {x r : Nat} {ρ ρN σ : Valn} {B : Nat → Prop} {ζ a b : T} {i : Nat}
    (hx : x + 1 = M.length) (hxN' : x < N.length) (hC : Cons M ρ) (hCN : Cons N σ) (hS : SameAt M N i)
    (hxN : ρN.o x = fsD (ρ.o x) ζ) (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m) (hna : WfQnL6.BumpNA M x ρ ζ i)
    (hW : bumpW M ρ i = ρ.o r) (hro : ρ.o r = psi a b z) (hAot : isOT (ρ.o r) = true)
    (hVot : isOT (vOpt ρ (par M 1 i)) = true) (hfot : isOT (fsD (psi a b z) ζ) = true)
    (hVlt : vOpt ρ (par M 1 i) < psi a b z) (hflt : fsD (psi a b z) ζ < psi a b z)
    (hB : ∀ j, B j → DepX M x false j)
    (hE1o : ∀ k, k < N.length → ¬ (k < x ∧ DepXB M B true k) →
      σ.o k = (glueZ M x ρ ρN (fun _ => ζ)).o k)
    (hE1v : ∀ k, k < N.length → ¬ (k < x ∧ DepXB M B false k) →
      σ.v k = (glueZ M x ρ ρN (fun _ => ζ)).v k)
    (hnest : ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, ¬ DepXB M B true k) :
    σ.v i = sf (add (vOpt ρ (par M 1 i)) (fsD (ρ.o r) ζ)) ∧ σ.v i < ρ.v i ∧ fsD (ρ.v i) ζ ≤ σ.v i := by
  have hiN : i < N.length := by omega
  have hbad := WfQnL6.vRhs_glue_bad (r := r) hx hxN hi h1 h2 hpd hna hW hro hVot hfot hVlt hflt
  have hσ : σ.v i = sf (add (vOpt ρ (par M 1 i)) (fsD (ρ.o r) ζ)) := by
    rw [(hCN i hiN).2, vRhs_same hS σ, ← hbad.1]
    apply vRhs_congr
    · intro m _ hm
      have hmi := par_lt M 1 i m hm
      exact hE1v m (by omega) (fun h => hpd m hm (DepXB.sub hB h.2))
    · intro k _ h2' _
      exact absurd h2' h2
    · intro j hj _ _ hjb k hk
      have hkM := (mem_children hk).2
      exact hE1o k (by omega) (fun h => hnest j hj hjb k hk h.2)
  have hvi := v_bad_M hC (by omega) h1 h2 hW hro hAot hVlt
  refine ⟨hσ, ?_, ?_⟩
  · rw [hσ, hvi]; exact hbad.2
  · rw [hσ, hvi, hro, sf_ot (isOT_add hVot hfot)]
    exact le_add_left_self hfot _

end Ytosk.WfQnH4
