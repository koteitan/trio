/-
**WfQrL8 (2026-11-01): the local equations of `hLoc` are free for the true valuation.**

Let `σ` be any solution of `N = M[n]` (it exists: `cons_of_rk` with `rk_N_t1`) and put
`τ = glueQ M x ρ (shiftV ρP L) σ.o σ.v` (the true values on `D`, `ρ` off `D` below `x`, the shifted `M[n-1]`
values from `x` on).  Then `τ` satisfies the equations of `N` off `D` (`cons_glueQ_off` below `x`, `cons_copy`
from `x` on) and equals `σ` on `D`; by induction on the rank `σ = τ` everywhere (`agree_of_eqs`).  Hence
`Cons N τ`, and the local equations `oRhs M τ i = σ.o i`, `vRhs M τ i = σ.v i` hold on `D` (`true_glue`).

So the only content left in `hLoc` of `qr_chainQ` is about the values of `σ` on `D`: the next chain term at `r`,
the root drop, `≤ o(c)`, `≠ 0`, standard form (`qr_chainT`).  With `σ.o = DQ(o)` (the engine statement) the drop
and the bound are `DQ.lt`.
-/
import Ytosk.WfQrL7
import Ytosk.V3Rank

namespace Ytosk.WfQrL8
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL7

/-- **Agreement from the equations off a set where the values are already equal**, by rank. -/
theorem agree_of_eqs {N : Mat} {σ τ : Valn} {rk : Bool → Nat → Nat} (S : Bool → Nat → Prop)
    (hC : Cons N σ) (hR : Rk N rk)
    (hS : ∀ b i, i < N.length → S b i → valB σ b i = valB τ b i)
    (hτo : ∀ i, i < N.length → ¬ S true i → τ.o i = oRhs N τ i)
    (hτv : ∀ i, i < N.length → ¬ S false i → τ.v i = vRhs N τ i) :
    ∀ n b i, rk b i < n → i < N.length → valB σ b i = valB τ b i := by
  intro n
  induction n with
  | zero => intro b i h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro b i hrk hi
    by_cases hSi : S b i
    · exact hS b i hi hSi
    obtain ⟨hrv, hrc, hr1⟩ := hR i hi
    cases b with
    | true =>
      simp only [valB, cond_true]
      rw [(hC i hi).1, hτo i hi hSi]
      apply oRhs_congr
      · have := ih false i (by omega) hi
        simpa [valB] using this
      · intro c hc hb hu
        have := ih true c (by have := hrc c hc hb hu; omega) (mem_children hc).2
        simpa [valB] using this
    | false =>
      simp only [valB, cond_false]
      rw [(hC i hi).2, hτv i hi hSi]
      apply vRhs_congr
      · intro m h1 hm
        have hmi := par_lt N 1 i m hm
        have := ih false m (by have := (hr1 h1).1 m hm; omega) (by omega)
        simpa [valB] using this
      · intro k h1 h2 hk
        have := ih false k (by have := (hr1 h1).2.1 h2 k hk; omega) (upg_lt hi hk)
        simpa [valB] using this
      · intro j hj h1 h2 hb k hk
        have := ih true k (by have := (hr1 h1).2.2 h2 j hj hb k hk; omega) (mem_children hk).2
        simpa [valB] using this

/-- Two valuations equal on the columns are both solutions. -/
theorem cons_of_agree {N : Mat} {σ τ : Valn} (hC : Cons N σ)
    (h : ∀ i, i < N.length → σ.o i = τ.o i ∧ σ.v i = τ.v i) : Cons N τ := by
  intro i hi
  rw [← (h i hi).1, ← (h i hi).2, (hC i hi).1, (hC i hi).2]
  refine ⟨?_, ?_⟩
  · apply oRhs_congr
    · exact (h i hi).2
    · intro c hc _ _; exact (h c (mem_children hc).2).1
  · apply vRhs_congr
    · intro m _ hm; exact (h m (by have := par_lt N 1 i m hm; omega)).2
    · intro k _ _ hk; exact (h k (upg_lt hi hk)).2
    · intro j _ _ _ _ k hk; exact (h k (mem_children hk).2).1

section
variable {M : Mat} {x : Nat} {ρ ρN : Valn} {oq vq : Nat → T}

/-- **The glue satisfies the equations of `N` off `D` below `x`** (the off-`D` half of `cons_glueQ_lt`). -/
theorem cons_glueQ_off {N : Mat} (hx : x + 1 = M.length) (hC : Cons M ρ) (hS : ∀ i, i < x → SameAt M N i)
    (hvx : ∀ i, i < x → ¬ DepX M x false i → ∀ m, entry M 1 i ≠ 0 →
      (par M 1 i = some m ∨ (entry M 2 i = 0 ∧ upg M i = some m)) → m < x) :
    ∀ i, i < x →
      (¬ DepX M x true i → (glueQ M x ρ ρN oq vq).o i = oRhs N (glueQ M x ρ ρN oq vq) i) ∧
      (¬ DepX M x false i → (glueQ M x ρ ρN oq vq).v i = vRhs N (glueQ M x ρ ρN oq vq) i) := by
  intro i hi
  have hiM : i < M.length := by omega
  rw [oRhs_same (hS i hi), vRhs_same (hS i hi)]
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [glueQ_o_lt hi hd, (hC i hiM).1]
    apply oRhs_congr
    · have hv : ¬ DepX M x false i := fun hv => hd (DepX.ov hv)
      rw [glueQ_v_lt hi hv]
    · intro c hc hb hu
      have hcd : ¬ DepX M x true c := fun h => hd (DepX.ochild hc hb hu h)
      have hcl := (mem_children hc).2
      have hcx : c < x := by
        rcases Nat.lt_or_ge c x with h | h
        · exact h
        · have : c = x := by omega
          subst this; exact absurd DepX.leaf hcd
      rw [glueQ_o_lt hcx hcd]
  · rw [glueQ_v_lt hi hd, (hC i hiM).2]
    apply vRhs_congr
    · intro m h1 hm
      have hmd : ¬ DepX M x false m := fun h => hd (DepX.vpar h1 hm h)
      rw [glueQ_v_lt (hvx i hi hd m h1 (Or.inl hm)) hmd]
    · intro k h1 h2 hk
      have hkd : ¬ DepX M x false k := fun h => hd (DepX.vupg h1 h2 hk h)
      rw [glueQ_v_lt (hvx i hi hd k h1 (Or.inr ⟨h2, hk⟩)) hkd]
    · intro j hj h1 h2 hb k hk
      have hkd : ¬ DepX M x true k := fun h => hd (DepX.vbump h1 h2 hj hb hk h)
      have hkl := (mem_children hk).2
      have hkx : k < x := by
        rcases Nat.lt_or_ge k x with h | h
        · exact h
        · have : k = x := by omega
          subst this; exact absurd DepX.leaf hkd
      rw [glueQ_o_lt hkx hkd]

end

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The true valuation is the glue of its own `D` values**, and the local equations hold. -/
theorem true_glue (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP σ : Valn} {rkN : Bool → Nat → Nat} (hC : Cons M ρ) (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v).v g = ρP.v g) :
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v) ∧
    ∀ i, i < r + L →
      (DepX M (r + L) true i → oRhs M (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v) i = σ.o i) ∧
      (DepX M (r + L) false i → vRhs M (glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v) i = σ.v i) := by
  have hlN := len_N (d0 := d0) hlen hn
  set τ := glueQ M (r + L) ρ (shiftV ρP L) σ.o σ.v with hτ
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hoff := cons_glueQ_off (ρ := ρ) (ρN := shiftV ρP L) (oq := σ.o) (vq := σ.v)
    (N := TRIO.gexp M r L d0 0 n) (by omega) hC hSA (fun i hi _ m _ hm => reads_lt_x hlen hx2 hi hm)
  have hcopy : ∀ i, r + L ≤ i → i < (TRIO.gexp M r L d0 0 n).length →
      τ.o i = oRhs (TRIO.gexp M r L d0 0 n) τ i ∧ τ.v i = vRhs (TRIO.gexp M r L d0 0 n) τ i := by
    intro i h hi
    rw [hτ, glueQ_eq_glueZ M (r + L) ρ (shiftV ρP L) σ.o σ.v (fun _ => z)] at hagree ⊢
    have := cons_copy hlen hL hA hd0e hn hpath hz2 hCP hagree (i - (r + L)) (by omega)
    rw [show r + L + (i - (r + L)) = i by omega] at this
    exact this
  let S : Bool → Nat → Prop := fun b i => i < r + L ∧ DepX M (r + L) b i
  have hS : ∀ b i, i < (TRIO.gexp M r L d0 0 n).length → S b i → valB σ b i = valB τ b i := by
    intro b i _ ⟨hi, hd⟩
    cases b with
    | true => simp only [valB, cond_true]; rw [hτ, glueQ_o_dep hi hd]
    | false => simp only [valB, cond_false]; rw [hτ, glueQ_v_dep hi hd]
  have hτo : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ S true i →
      τ.o i = oRhs (TRIO.gexp M r L d0 0 n) τ i := by
    intro i hi hn'
    rcases Nat.lt_or_ge i (r + L) with h | h
    · exact (hoff i h).1 (fun hd => hn' ⟨h, hd⟩)
    · exact (hcopy i h hi).1
  have hτv : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ S false i →
      τ.v i = vRhs (TRIO.gexp M r L d0 0 n) τ i := by
    intro i hi hn'
    rcases Nat.lt_or_ge i (r + L) with h | h
    · exact (hoff i h).2 (fun hd => hn' ⟨h, hd⟩)
    · exact (hcopy i h hi).2
  have hag : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → σ.o i = τ.o i ∧ σ.v i = τ.v i := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have := agree_of_eqs S hCN hRN hS hτo hτv (rkN true i + 1) true i (Nat.lt_succ_self _) hi
      simpa [valB] using this
    · have := agree_of_eqs S hCN hRN hS hτo hτv (rkN false i + 1) false i (Nat.lt_succ_self _) hi
      simpa [valB] using this
  have hCτ := cons_of_agree hCN hag
  refine ⟨hCτ, fun i hi => ⟨fun hd => ?_, fun hd => ?_⟩⟩
  · rw [← oRhs_same (hSA i hi), ← (hCτ i (by omega)).1, hτ, glueQ_o_dep hi hd]
  · rw [← vRhs_same (hSA i hi), ← (hCτ i (by omega)).2, hτ, glueQ_v_dep hi hd]

end

end Ytosk.WfQrL8
