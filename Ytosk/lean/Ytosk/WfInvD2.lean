/-
**WfInvD2: `BumpAbsC` with the bad shape alternative (2026-10-31).**

On graftM36 a `t = 2` matrix outside `Bad2` (37 columns, …(13,1,0)(14,2,1)(15,2,1)) fails `BumpAbsC` at `i = 32`,
so the second conjunct of `HDropUg` is false too. At every failure of `BumpAbsC` measured outside `Bad2`
the column has the shape `WfAbsW.BadAbsShape M (M.take x)` (the same shape as the failures of `AbsWN M M[n]`).
`BumpAbsCX` adds it as an alternative; `absWNx_of_absCX` gives what `t2_absWN_take` should read, `AbsWNx`.
-/
import Ytosk.WfInvD1
import Ytosk.WfAbsWEta
import Ytosk.V3T2Top
import Ytosk.V3T0AbW

namespace Ytosk

open T

/-- **`BumpAbsC` or the bad shape** at every bump-type column. -/
def BumpAbsCX (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ σ', Cons (M.take x) σ' → ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    (∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z) →
    (StrongG M x ρ i ∨ XParNB M x ∨ ρ.v x = z) →
    (∀ r ∈ summands (vOpt ρ (par M 1 i)), ¬ r < bumpW (M.take x) σ' i → r < bumpW M ρ i →
      Lhd z r (bumpW M ρ i)) ∨ WfAbsW.BadAbsShape M (M.take x) ρ σ' i

theorem BumpAbsC.toX {M : Mat} {x : Nat} {ρ : Valn} (h : BumpAbsC M x ρ) : BumpAbsCX M x ρ :=
  fun σ' hσ i h1 h2 hx hg => Or.inl (h σ' hσ i h1 h2 hx hg)

/-- **`AbsWNx` for the drop** from `BumpAbsCX` (as `absWN_of_absC`). -/
theorem absWNx_of_absCX {M : Mat} {x q : Nat} {ρ σ' : Valn} (hAbsC : BumpAbsCX M x ρ)
    (hσ' : Cons (M.take x) σ') (hpx : par M 0 x = some q)
    (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i) : WfAbsW.AbsWNx M (M.take x) x ρ σ' := by
  intro i _ h1 h2
  have g1 : ∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z := by
    intro j hj hjb hjx
    exfalso
    have hxj : x ∈ children M j := by rw [hjx]; simp
    have hpx' := (mem_children_iff.mp hxj).2
    rw [hpx] at hpx'; cases hpx'
    exact hqb i (mem_children_iff.mp hj).2 hjb
  have g2 : XParNB M x := by
    intro q' i' hq' hi'
    rw [hpx] at hq'; cases hq'; exact hqb i' hi'
  rcases hAbsC σ' hσ' i h1 h2 g1 (Or.inr (Or.inl g2)) with h | h
  · exact Or.inl fun s hs _ hn hlt => h s hs hn hlt
  · exact Or.inr h

/-- **`AbsWNx` for the drop at `t = 0`** from `BumpAbsCX` (as `absWN_take_t0`). -/
theorem absWNx_take_t0 {M : Mat} {x bnd : Nat} {ρ τ : Valn} (hAbsC : BumpAbsCX M x ρ) (hC : Cons M ρ)
    (hx : x < M.length) (he1 : entry M 1 x = 0) (hτ : Cons (M.take x) τ) :
    WfAbsW.AbsWNx M (M.take x) bnd ρ τ := by
  have hvx : ρ.v x = z := by rw [(hC x hx).2]; unfold vRhs; rw [if_pos he1]
  intro i _ h1 h2
  rcases hAbsC τ hτ i h1 h2 (fun _ _ _ _ => hvx) (Or.inr (Or.inr hvx)) with h | h
  · exact Or.inl fun q hq _ hn hlt => h q hq hn hlt
  · exact Or.inr h

/-- **The repaired drop residual with the bad shape** (2026-10-31): `DropResHBg` everywhere, and `BumpAbsCX` at
`t = 0` and at `t = 2` outside `Bad2`. -/
def HDropUx : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResHBg M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧
      (entry M 1 (M.length - 1) = 0 ∨ (entry M 2 (M.length - 1) ≠ 0 ∧ ¬ Bad2 M) →
        BumpAbsCX M (M.length - 1) ρ)

theorem hDropUx_of_g (h : HDropUg) : HDropUx := fun M ρ rk hM hS hE I =>
  ⟨(h M ρ rk hM hS hE I).1, fun hc => ((h M ρ rk hM hS hE I).2 hc).toX⟩

theorem hDropUx_of_U (h : HDropU) : HDropUx := hDropUx_of_g (hDropUg_of_U h)

/-- The drop conclusion from `HDropUx` (its first conjunct is that of `HDropUg`). -/
theorem hdrop_of_Ux (h : HDropUx) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk) :
    ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i := by
  have hE : M ≠ [] := by intro he; rw [he] at hl; simp at hl
  obtain ⟨R, _⟩ := h M ρ rk hM hS hE I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  exact drop_all_hardW hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs R.vst I.fc I.fo
    R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td R.ab R.ws) R.ua.x1

/-- **The absorption at `x − 1` without the component condition** (what every drop lemma reads). -/
def UAw (N : Mat) (x : Nat) (σ : Valn) : Prop :=
  ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt σ (par N 1 i)), r < W → Lhd z r W) ∨ WCSP N σ i (add (vOpt σ (par N 1 i)) one)

theorem UAg.toW {N : Mat} {x : Nat} {σ : Valn} (h : UAg N x σ) : UAw N x σ := h.x1

/-- **`DropResHB` with `UAw`.** -/
structure DropResHBw (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  hard : HardArg N x σ σ'
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrcB N x σ σ'
  ua : UAw N x σ
  ab : BumpAbsCB N x σ

/-- **The weakest measured form** (2026-10-31): `DropResHBw` and `BumpAbsCX` at every standard matrix, with no
`Bad2` or type guard (on the families every failure of `BumpAbsC`, also on `Bad2` and at `t = 1`, has the bad
shape). The `t = 1` readers of the component condition (`qr_dropSeed`, `frameMapT1_take`) then need their own
residual. -/
def HDropUw : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResHBw M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧ BumpAbsCX M (M.length - 1) ρ

theorem hdrop_of_Uw (h : HDropUw) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk) :
    ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i := by
  have hE : M ≠ [] := by intro he; rw [he] at hl; simp at hl
  obtain ⟨R, _⟩ := h M ρ rk hM hS hE I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  exact drop_all_hardW hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs R.vst I.fc I.fo
    R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td R.ab R.ws) R.ua

end Ytosk
