/-
**落とす補題の残りの仮定を HardArg に狭める（`DropResH`）。**

`DropRes.argT`（M.take x のすべての枠で、新しい最後の数える子の引数の成分が状態以下）は、
`drop_all_hard` で M.take x の Good3 が出ると `argT_std` で導ける。したがって 1 回の落としの残りの仮定は
`DropResH`（argT を `HardArg` に替えたもの）で足りる（`DropRes.ofH`）。逆に `DropRes` は `DropResH` を含む
（`hardArg_of_argT`）。

- `Res3H`: `Res3A` の drop を `DropResH` に替えたもの。`Res3A.ofH` で戻る。
- `hLast_of_H`: hLast の残りを `Res3H (M.take x)` で述べた形。
- `trio_terminates_main_H`: 最上位の hLast・hExp の結論を `Res3H` にした形。
-/
import Ytosk.V3DropStrong
import Ytosk.V3Main

namespace Ytosk

open T

/-- The remaining hypotheses of one drop, with `argT` narrowed to `HardArg`. -/
structure DropResH (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  hard : HardArg N x σ σ'
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrc N x σ σ'
  ua : UpgAbsXW N x σ
  ab : BumpAbsC N x σ

/-- **`DropResH` with `UpgAbsXW0`** (no row-1 condition on the weak alternative, 2026-10-17). -/
structure DropResH0 (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  hard : HardArg N x σ σ'
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrc N x σ σ'
  ua : UpgAbsXW0 N x σ
  ab : BumpAbsC N x σ

theorem DropResH0.toH {N : Mat} {x : Nat} {σ σ' : Valn} (h : DropResH0 N x σ σ')
    (h0 : entry N 1 x = 0 → ¬ T0Easy N x → UpgAbsX N x σ) : DropResH N x σ σ' :=
  ⟨h.hard, h.vst, h.ws, UpgAbsXW.of0 h.ua h0, h.ab⟩

/-- **The drop lemma from `DropResH`.** -/
theorem drop_all_H {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hD : DropResH N x σ σ')
    (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) :
    ∀ i, i < x → PO σ σ' i ∧ PV N σ σ' i :=
  drop_all_hard hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.vs hD.vst hI.fc hI.fo hD.hard
    (bump_drop hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.kd hI.td hD.ab hD.ws) hD.ua

/-- **`DropRes` from `DropResH`**: `argT` from the standardness of `N.take x` (`drop_all_H`, `good3_take`,
`argT_std`). -/
theorem DropRes.ofH {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hD : DropResH N x σ σ')
    (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) : DropRes N x σ σ' := by
  have hdrop := drop_all_H hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI hD hC' hRk'
  have hGT := good3_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop
  exact ⟨argT_std hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hGT, hD.vst, hD.ws, hD.ua, hD.ab⟩

/-- `argT` gives `HardArg` (both rewrite, so the new state is `H s y′`). -/
theorem hardArg_of_argT {N : Mat} {x : Nat} {σ σ' : Valn}
    (h : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (N.take x) i = Lc ++ [cs] →
      ∀ s y, σ'.o cs = psi s y z → ¬ lt s (σ.v i) = true →
      ∀ g ∈ comps (σ.v i) y, g ≤ step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y z) :
    HardArg N x σ σ' := by
  intro i hi Lc cs hcl s y' y ho' _ has ht' _ _ g hg
  have hst : step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y' z = H s y' := by
    unfold step; rw [if_pos ht']
  have hns : ¬ lt s (σ.v i) = true := fun h => lt_irrefl' _ (lt_trans (show σ.v i < s from has) h)
  rw [← hst]
  exact h i hi Lc cs hcl s y' ho' hns g hg

theorem DropRes.toH {N : Mat} {x : Nat} {σ σ' : Valn} (h : DropRes N x σ σ') : DropResH N x σ σ' :=
  ⟨hardArg_of_argT h.argT, h.vst, h.ws, h.ua, h.ab⟩

/-- `Res3A` with the drop part narrowed to `DropResH`. -/
structure Res3H (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropResH M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  seed : ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    lt (sf ((drop1 M (M.length - 1) rk).v r)) (ρ.v r) = true →
    ∀ a', ¬ lt (ρ.v r) a' = true →
    isOT (psi a' (app (qrB M ρ r (M.length - 1)) (psi (succ (ρ.v r)) z z)) z) = true →
    ∀ g ∈ comps a' ((drop1 M (M.length - 1) rk).o r),
      g < app (qrB M ρ r (M.length - 1)) ((drop1 M (M.length - 1) rk).o r)
  /-- the strong absorption at `t = 2` and `t = 0` (`AbsSR`, 2026-10-11) -/
  abS : AbsSR M ρ

/-- **`Res3A` from `Res3H`** on a nonempty matrix with the structural invariants and the value part. -/
theorem Res3A.ofH {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hne : M ≠ []) (S : SInv M)
    (V : Inv3V M ρ rk) (h : Res3H M ρ rk) : Res3A M ρ rk := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h0 | h0
    · exact absurd (List.length_eq_zero_iff.mp h0) hne
    · exact h0
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) hl S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) V.rank hcnt
  exact ⟨DropRes.ofH hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab V.cons
    ⟨V.good, V.vs, V.fc, V.fo, V.kd, V.td⟩ h.drop (cons_of_rk hRk1) hRk1, h.seed, h.abS⟩

theorem Res3A.toH {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : Res3A M ρ rk) : Res3H M ρ rk :=
  ⟨h.drop.toH, h.seed, h.abS⟩

/-- **The top theorem with the narrowed residual**: `hLast` and `hExp` only have to give `Res3H`. -/
theorem trio_terminates_main_H
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3H (M.take (M.length - 1)) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3H (expand M n) ρN rkN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' := by
  apply trio_terminates_main_T2 _ _ hR2
  · intro M ρ rk hM hS hl I R
    obtain ⟨ρ', rk', V, R'⟩ := hLast M ρ rk hM hS hl I R
    have hne : M.take (M.length - 1) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_take] at this; simp at this; omega
    have hS' : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V.rank
    exact ⟨ρ', rk', V, Res3A.ofH hne (sInv_std (std_take hM _ (by omega)) hS') V R'⟩
  · intro M ρ rk hM hS hE I R hz n hn hNS hNE
    obtain ⟨ρN, rkN, V, R'⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
    exact ⟨ρN, rkN, V, Res3A.ofH hNE (sInv_std (Std.exp n hM) hNS) V R'⟩

end Ytosk
