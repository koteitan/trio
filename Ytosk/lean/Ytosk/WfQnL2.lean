/-
**WfQnL2 (2026-11-01): agreement off a dependency closure, by induction on the rank (step 2 of the generalized
t = 1, q ≠ r engine).**
If `σ` solves the equations of `N` (with a ranking `rk`) and `τ` satisfies the equations at every call outside
the closure `DepXB N B`, then `σ = τ` outside the closure (`agree_off_rk`, `agreeOffB_of_eqs`).
With `σ = cons_of_rk` and `τ` = the engine's glue, this is (E1) once the glue's equations are known off `DepXB`.
-/
import Ytosk.WfQnE3
import Ytosk.V3PathT

namespace Ytosk.WfQnL2
open T Ytosk Ytosk.WfQnE3

/-- **Agreement off the closure, by rank.** -/
theorem agree_off_rk {N : Mat} {σ τ : Valn} {rk : Bool → Nat → Nat} {B : Nat → Prop}
    (hC : Cons N σ) (hR : Rk N rk)
    (hτo : ∀ i, i < N.length → ¬ DepXB N B true i → τ.o i = oRhs N τ i)
    (hτv : ∀ i, i < N.length → ¬ DepXB N B false i → τ.v i = vRhs N τ i) :
    ∀ n b i, rk b i < n → i < N.length → ¬ DepXB N B b i → valB σ b i = valB τ b i := by
  intro n
  induction n with
  | zero => intro b i h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro b i hrk hi hnd
    obtain ⟨hrv, hrc, hr1⟩ := hR i hi
    cases b with
    | true =>
      simp only [valB, cond_true]
      rw [(hC i hi).1, hτo i hi hnd]
      apply oRhs_congr
      · have := ih false i (by omega) hi (fun hd => hnd (DepXB.ov hd))
        simpa [valB] using this
      · intro c hc hb hu
        have := ih true c (by have := hrc c hc hb hu; omega) (mem_children hc).2
          (fun hd => hnd (DepXB.ochild hc hb hu hd))
        simpa [valB] using this
    | false =>
      simp only [valB, cond_false]
      rw [(hC i hi).2, hτv i hi hnd]
      apply vRhs_congr
      · intro m h1 hm
        have hmi := par_lt N 1 i m hm
        have := ih false m (by have := (hr1 h1).1 m hm; omega) (by omega)
          (fun hd => hnd (DepXB.vpar h1 hm hd))
        simpa [valB] using this
      · intro k h1 h2 hk
        have := ih false k (by have := (hr1 h1).2.1 h2 k hk; omega) (upg_lt hi hk)
          (fun hd => hnd (DepXB.vupg h1 h2 hk hd))
        simpa [valB] using this
      · intro j hj h1 h2 hb k hk
        have := ih true k (by have := (hr1 h1).2.2 h2 j hj hb k hk; omega) (mem_children hk).2
          (fun hd => hnd (DepXB.vbump h1 h2 hj hb hk hd))
        simpa [valB] using this

/-- **(E1) in the form of `AgreeOffB`** (on the columns of `N`). -/
theorem agreeOffB_of_eqs {N : Mat} {σ τ : Valn} {rk : Bool → Nat → Nat} {B : Nat → Prop}
    (hC : Cons N σ) (hR : Rk N rk)
    (hτo : ∀ i, i < N.length → ¬ DepXB N B true i → τ.o i = oRhs N τ i)
    (hτv : ∀ i, i < N.length → ¬ DepXB N B false i → τ.v i = vRhs N τ i) :
    (∀ i, i < N.length → ¬ DepXB N B true i → σ.o i = τ.o i) ∧
    (∀ i, i < N.length → ¬ DepXB N B false i → σ.v i = τ.v i) := by
  refine ⟨fun i hi hnd => ?_, fun i hi hnd => ?_⟩
  · have := agree_off_rk hC hR hτo hτv (rk true i + 1) true i (Nat.lt_succ_self _) hi hnd
    simpa [valB] using this
  · have := agree_off_rk hC hR hτo hτv (rk false i + 1) false i (Nat.lt_succ_self _) hi hnd
    simpa [valB] using this

/-- **Uniqueness**: two solutions agree everywhere (the case `B = ∅`). -/
theorem cons_unique {N : Mat} {σ τ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hR : Rk N rk)
    (hτ : Cons N τ) : ∀ i, i < N.length → σ.o i = τ.o i ∧ σ.v i = τ.v i := by
  have h := agreeOffB_of_eqs (B := fun _ => False) hC hR (fun i hi _ => (hτ i hi).1)
    (fun i hi _ => (hτ i hi).2)
  exact fun i hi => ⟨h.1 i hi DepXB.empty, h.2 i hi DepXB.empty⟩

end Ytosk.WfQnL2
