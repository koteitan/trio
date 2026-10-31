/-
**WfQnL4 (2026-11-01): (E1) for the generalized t = 1, q ≠ r engine.**
- `depX_rk`: along `DepX` the rank does not drop below `rk true x`; hence `¬ DepX M x false x` (`not_depX_vx`)
  and every call of a closure of bad calls lies below `x` (`depXB_lt`).
- `cons_glue_ltB`: `cons_glue_lt` (V3Dep) with the exchange `hF` asked only off `DepXB M B`.
- `depXB_N_of_M`: below `x` the closure in `M` is contained in the closure in `N = M[n]`.
- `E1_N`: the true valuation of `N` (any solution with a ranking) equals the glue at every call outside the
  closure `DepXB N B` (the glue satisfies the equations there: `cons_glue_ltB` below `x`, `cons_copy` from `x` on).
-/
import Ytosk.WfQnL2
import Ytosk.WfQnL3
import Ytosk.V3T1
import Ytosk.V3Rank

namespace Ytosk.WfQnL4
open T Ytosk Ytosk.WfQnE3

theorem entry_ge {M : Mat} {y i : Nat} (hi : M.length ≤ i) : entry M y i = 0 := by
  unfold entry
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  split_ifs <;> rfl

/-- **Ranks along `DepX`.** -/
theorem depX_rk {M : Mat} {x : Nat} {rk : Bool → Nat → Nat} (hR : Rk M rk) (hx : x < M.length) :
    ∀ {b i}, DepX M x b i → i < M.length ∧ rk true x ≤ rk b i := by
  intro b i h
  induction h with
  | leaf => exact ⟨hx, le_refl _⟩
  | @ochild i c hc hb hu _ ih =>
    have hic := (mem_children hc)
    have := (hR i (by omega)).2.1 c hc hb hu
    exact ⟨by omega, by omega⟩
  | @ov i _ ih =>
    have := (hR i ih.1).1
    exact ⟨ih.1, by omega⟩
  | @vpar i m h1 hm _ ih =>
    have hi : i < M.length := by
      by_contra hc; exact h1 (entry_ge (by omega))
    have := ((hR i hi).2.2 h1).1 m hm
    exact ⟨hi, by omega⟩
  | @vupg i k h1 h2 hk _ ih =>
    have hi : i < M.length := by
      by_contra hc; exact h1 (entry_ge (by omega))
    have := ((hR i hi).2.2 h1).2.1 h2 k hk
    exact ⟨hi, by omega⟩
  | @vbump i j k h1 h2 hj hb hk _ ih =>
    have hi : i < M.length := by
      by_contra hc; exact h1 (entry_ge (by omega))
    have := ((hR i hi).2.2 h1).2.2 h2 j hj hb k hk
    exact ⟨hi, by omega⟩

theorem not_depX_vx {M : Mat} {x : Nat} {rk : Bool → Nat → Nat} (hR : Rk M rk) (hx : x < M.length) :
    ¬ DepX M x false x := by
  intro h
  have h1 := (depX_rk hR hx h).2
  have h2 := (hR x hx).1
  omega

/-- **The closure of bad calls lies below `x`** (`x` the last column). -/
theorem depXB_lt {M : Mat} {x : Nat} {rk : Bool → Nat → Nat} (hR : Rk M rk) (hx : x + 1 = M.length)
    {B : Nat → Prop} (hB : ∀ i, B i → DepX M x false i) : ∀ {b i}, DepXB M B b i → i < x := by
  intro b i h
  have hD := DepXB.sub hB h
  have hl := (depX_rk hR (by omega) hD).1
  rcases Nat.lt_or_ge i x with h' | h'
  · exact h'
  · exfalso
    have hix : i = x := by omega
    subst hix
    have hv : ¬ DepXB M B false i := fun hv => not_depX_vx hR (by omega) (DepXB.sub hB hv)
    cases b with
    | false => exact hv h
    | true =>
      cases h with
      | ochild hc _ _ _ => have := mem_children hc; omega
      | ov h0 => exact hv h0

/-- **Gluing off the closure** (`cons_glue_lt` with `hF` only off `DepXB M B`). -/
theorem cons_glue_ltB {M N : Mat} {x : Nat} (hx : x + 1 = M.length) {ρ ρN : Valn} {Z : Nat → T}
    {B : Nat → Prop}
    (hC : Cons M ρ) (hS : ∀ i, i < x → SameAt M N i)
    (hvx : ∀ i, i < x → ¬ DepX M x false i → ∀ m, entry M 1 i ≠ 0 →
      (par M 1 i = some m ∨ (entry M 2 i = 0 ∧ upg M i = some m)) → m < x)
    (hF : ∀ i, i < x →
      (DepX M x true i → ¬ DepXB M B true i → oRhs M (glueZ M x ρ ρN Z) i = fsD (ρ.o i) (Z i)) ∧
      (DepX M x false i → ¬ DepXB M B false i → vRhs M (glueZ M x ρ ρN Z) i = fsD (ρ.v i) (Z i))) :
    ∀ i, i < x → (¬ DepXB M B true i → (glueZ M x ρ ρN Z).o i = oRhs N (glueZ M x ρ ρN Z) i) ∧
      (¬ DepXB M B false i → (glueZ M x ρ ρN Z).v i = vRhs N (glueZ M x ρ ρN Z) i) := by
  intro i hi
  have hiM : i < M.length := by omega
  rw [oRhs_same (hS i hi), vRhs_same (hS i hi)]
  refine ⟨fun hnb => ?_, fun hnb => ?_⟩
  · by_cases hd : DepX M x true i
    · rw [glueZ_o_dep ρ ρN Z hi hd, (hF i hi).1 hd hnb]
    · rw [glueZ_o_lt ρ ρN Z hi hd, (hC i hiM).1]
      apply oRhs_congr
      · have hv : ¬ DepX M x false i := fun hv => hd (DepX.ov hv)
        rw [glueZ_v_lt ρ ρN Z hi hv]
      · intro c hc hb hu
        have hcd : ¬ DepX M x true c := fun h => hd (DepX.ochild hc hb hu h)
        have hcl := (mem_children hc).2
        have hcx : c < x := by
          rcases Nat.lt_or_ge c x with h | h
          · exact h
          · have : c = x := by omega
            subst this; exact absurd DepX.leaf hcd
        rw [glueZ_o_lt ρ ρN Z hcx hcd]
  · by_cases hd : DepX M x false i
    · rw [glueZ_v_dep ρ ρN Z hi hd, (hF i hi).2 hd hnb]
    · rw [glueZ_v_lt ρ ρN Z hi hd, (hC i hiM).2]
      apply vRhs_congr
      · intro m h1 hm
        have hmd : ¬ DepX M x false m := fun h => hd (DepX.vpar h1 hm h)
        rw [glueZ_v_lt ρ ρN Z (hvx i hi hd m h1 (Or.inl hm)) hmd]
      · intro k h1 h2 hk
        have hkd : ¬ DepX M x false k := fun h => hd (DepX.vupg h1 h2 hk h)
        rw [glueZ_v_lt ρ ρN Z (hvx i hi hd k h1 (Or.inr ⟨h2, hk⟩)) hkd]
      · intro j hj h1 h2 hb k hk
        have hkd : ¬ DepX M x true k := fun h => hd (DepX.vbump h1 h2 hj hb hk h)
        have hkl := (mem_children hk).2
        have hkx : k < x := by
          rcases Nat.lt_or_ge k x with h | h
          · exact h
          · have : k = x := by omega
            subst this; exact absurd DepX.leaf hkd
        rw [glueZ_o_lt ρ ρN Z hkx hkd]

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0)
  (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
  (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
  {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
include hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB

/-- **Below `x` the closure in `M` is inside the closure in `N = M[n]`.** -/
theorem depXB_N_of_M : ∀ {b i}, DepXB M B b i → DepXB (TRIO.gexp M r L d0 0 n) B b i := by
  have hlt : ∀ {b i}, DepXB M B b i → i < r + L := fun h => depXB_lt hRM (by omega) hB h
  have hbN : ∀ i, i < r + L → bump (TRIO.gexp M r L d0 0 n) i = bump M i := by
    intro i hi
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  intro b i h
  have hix := hlt h
  induction h with
  | leaf h0 => exact DepXB.leaf h0
  | @ochild i c hc hb hu hd ih =>
    have hcx := hlt hd
    refine DepXB.ochild (by rw [children_N_lt hlen hL hA hd0e hn hix]; exact hc) ?_ ?_ (ih hcx)
    · rw [col_gexp_pre hlen (by omega) hcx, hbN i hix]; exact hb
    · rw [hiu c hcx, topped_N_lt hlen hL hA hd0e hn hpath hx2 hxnb hcx]; exact hu
  | @ov i hd ih => exact DepXB.ov (ih hix)
  | @vpar i m h1 hm hd ih =>
    refine DepXB.vpar (by rw [entry_gexp_pre hlen (by omega) 1 hix]; exact h1)
      (by rw [par_gexp_pre hlen (by omega) 1 hix]; exact hm) (ih (hlt hd))
  | @vupg i k h1 h2 hk hd ih =>
    have SA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux i hix
    refine DepXB.vupg (by rw [SA.e1]; exact h1) (by rw [SA.e2]; exact h2) (by rw [SA.upg]; exact hk)
      (ih (hlt hd))
  | @vbump i j k h1 h2 hj hb hk hd ih =>
    have hkx := hlt hd
    have hjk := (mem_children hk).1
    have hjx : j < r + L := by omega
    refine DepXB.vbump (by rw [entry_gexp_pre hlen (by omega) 1 hix]; exact h1)
      (by rw [entry_gexp_pre hlen (by omega) 2 hix]; exact h2)
      (by rw [children_N_lt hlen hL hA hd0e hn hix]; exact hj)
      (by rw [col_gexp_pre hlen (by omega) hjx, hbN i hix]; exact hb)
      (by rw [children_N_lt hlen hL hA hd0e hn hjx]; exact hk) (ih hkx)

/-- **(E1)**: a solution of the equations of `N = M[n]` equals the glue outside the closure `DepXB N B`,
when the glue's exchange `hF` holds outside the closure `DepXB M B`. -/
theorem E1_N (hz2 : entry M 2 r ≤ 1) {ρ ρP : Valn} {Z : Nat → T} (hC : Cons M ρ)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v g = ρP.v g)
    (hF : ∀ i, i < r + L →
      (DepX M (r + L) true i → ¬ DepXB M B true i →
        oRhs M (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (ρ.o i) (Z i)) ∧
      (DepX M (r + L) false i → ¬ DepXB M B false i →
        vRhs M (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (ρ.v i) (Z i)))
    {σ : Valn} {rkN : Bool → Nat → Nat} (hCN : Cons (TRIO.gexp M r L d0 0 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN) :
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ DepXB (TRIO.gexp M r L d0 0 n) B true i →
      σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) Z).o i) ∧
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ DepXB (TRIO.gexp M r L d0 0 n) B false i →
      σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) Z).v i) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hG := cons_glue_ltB (N := TRIO.gexp M r L d0 0 n) (by omega) hC
    (sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux)
    (fun i hi _ m _ hm => reads_lt_x hlen hx2 hi hm) hF
  have hcp := cons_copy hlen hL hA hd0e hn hpath hz2 hCP hagree
  apply WfQnL2.agreeOffB_of_eqs (B := B) hCN hRN
  · intro i hi hnb
    rcases Nat.lt_or_ge i (r + L) with h | h
    · exact (hG i h).1 (fun hd => hnb (depXB_N_of_M hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hd))
    · have := (hcp (i - (r + L)) (by omega)).1
      rwa [show r + L + (i - (r + L)) = i by omega] at this
  · intro i hi hnb
    rcases Nat.lt_or_ge i (r + L) with h | h
    · exact (hG i h).2 (fun hd => hnb (depXB_N_of_M hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hd))
    · have := (hcp (i - (r + L)) (by omega)).2
      rwa [show r + L + (i - (r + L)) = i by omega] at this

end

end Ytosk.WfQnL4
