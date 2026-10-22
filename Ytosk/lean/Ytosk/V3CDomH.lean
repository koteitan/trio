/-
**3 行・t = 2・C: 種の残り T2SeedCDom1 を証明する（`t2SeedCDom1_holds`）。**

C（q が r の最後の数える子でない）でも P_0(q) = r（`par0_q_t2`）と x = bump(q)（`t2_qn_struct`）が成り立つ。
すると qn の場合と同じ `qn_omega_lev` で ω^{W₀} の頭の添字は V 以下（W₀ = 1 + q の x より前の bump 項の和）。
`qn_omega_lev` は q の bump 子 j (< x) の子 c について v(c) ≤ v(r)（`qn_kid_v`: BumpLeaf で e1 c < e1 q、
RowJ で e2 c = 0、守られない子孫の `v_le_unguarded`）から出ていて、CL の形を使わない。
残り `T2SeedDomV2B` は qn の欄だけの `T2SeedDomV2Q` になる。
-/
import Ytosk.V3T2SeedQNK
import Ytosk.V3QNFC
import Ytosk.V3T2SeedQNV

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **`T2SeedCDom1` holds** at every `t = 2` matrix with `q ≠ r` (no condition on `CL M r`). -/
theorem t2SeedCDom1_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) : T2SeedCDom1 M ρ r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, -⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  exact qn_omega_lev hX hJ I.cons I.good I.rank (by omega) hr hq hpq Txb

/-- **Residual (t2): the qn part of `T2SeedDomV2B`** (the C part is `t2SeedCDom1_holds`). -/
def T2SeedDomV2Q : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom1 M ρ r L q Lc

theorem t2SeedDomV2B_of_Q (h : T2SeedDomV2Q) : T2SeedDomV2B := fun M ρ rk C hz h2 =>
  ⟨h M ρ rk C hz h2, fun _ _ _ hlen hr hq hqr _ =>
    t2SeedCDom1_holds C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr⟩

end Ytosk
