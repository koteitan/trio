/-
**3 行・t = 2: x より前の弱い吸収 AbsWN を、落とし側（BumpAbsC）と bumpW の単調性に分ける（2026-10-17、t2）。**

t0 の V3T0AbW と同じ形。AbsWN M N bnd の前件「bumpW N σ i に吸収されない」は bumpW (M.take x) τ i ≤ bumpW N σ i
なら M.take x でも立つ（`absWN_mono`）。
- 落とし側 AbsWN M (M.take x) x ρ τ は落としの残り BumpAbsC（Res3W の drop.ab）から（`absWN_of_absC`）。
  その側条件「x の親 q は bump の子でない」は t = 2 ではいつも立つ（`t2_xparNB`: q = r なら行 2 が 0、
  q ≠ r なら t2_qn_struct）。
- 展開側: i < x（行 1・2 が 0 でない列）で bumpW (M.take x) τ i ≤ bumpW M[n] σ i（残り `T2BumpMono`）。
-/
import Ytosk.V3T0AbW
import Ytosk.V3T2Top
import Ytosk.V3ExpT2BA
import Ytosk.V3T2SeedQNV

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The parent of `x` is not a bump child** (`t = 2`). -/
theorem t2_xparNB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
  intro i hi hb
  by_cases hqr : q = r
  · rw [hqr] at hb
    have h0 := (par2_facts I.z2 (show r + L < M.length by omega) hr).1
    have h1 := e2_of_col (show col M r = (entry M 0 i + 1, entry M 1 i, 1) from hb)
    omega
  · obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
    have hpq := par0_q_t2 hM hS I hlen hr hq hqr
    have hrq : r < q := par_lt M 0 q r hpq
    rw [hpq] at hi; cases hi
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
    obtain ⟨_, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
    rw [show r + (q - r) = q by omega] at Tqb
    exact Tqb hb

/-- **The weak absorption for the drop** (`t = 2`, outside `Bad2`), from the drop residual `BumpAbsC`. On `Bad2` it
is false (graftBb2St: 3 standard matrices), while `AbsWN M M[n]` holds there (the residual `T2AbsNBad`, V3T2BelowR). -/
theorem t2_absWN_take {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hNB : ¬ Bad2 M) {r L : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    AbsWN M (M.take (r + L)) (r + L) ρ τ := by
  have hA := anc0_of_par M 2 r (r + L) hr
  have hrx : r < r + L := par_lt M 2 _ _ hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hnb := t2_xparNB hM hS I hlen hr hq
  have hab := R.ab hNB (by
    intro q' i hq' hi
    rw [show M.length - 1 = r + L by omega, hq] at hq'
    cases hq'
    exact hnb i hi)
  rw [show M.length - 1 = r + L by omega] at hab
  exact absWN_of_absC hab hτ hq hnb

/-- **The monotonicity of the bump term** from `M.take x` to `M[n]` (`t = 2`, columns before `x`). -/
def T2BumpMono (M : Mat) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ n, 2 ≤ n →
    ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      bumpW (M.take (r + L)) τ i ≤
        bumpW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ i

/-- **AbsWN for `t = 2`** from the drop and `T2BumpMono`. -/
theorem t2_absWN {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hNB : ¬ Bad2 M) {r L : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hm : T2BumpMono M r L) {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) :
    AbsWN M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
      (r + L) ρ σ := by
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  exact absWN_mono (t2_absWN_take hM hS I R hNB hlen hr hC0) (hm _ hC0 n hn σ hCN)

end Ytosk
