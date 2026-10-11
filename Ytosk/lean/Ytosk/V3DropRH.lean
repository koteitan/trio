/-
**落とす補題の残りから HardArg を外した形を最上位までつなぐ。**

- `DropResR`: 1 回の落としの残りの仮定。`argT` も `HardArg` もなく、代わりに `VSmallNewR`・`ShadowC`・`TailNR`。
- `DropRes.ofR`: `drop_all_R`（関係 `RelR` を運ぶ落とす補題）→ `good3_take` → `argT_std` で `DropRes`。
  1 行列の値の不変条件 `VSmallR` を使う。
- `Res3R`・`Res3A.ofR`、最上位 `trio_terminates_main_R`: hLast・hExp は `Inv3V ∧ Res3R` を出せばよく、
  `VSmallR` はすべての標準形について成り立つことを仮定 `hVSR` にする。
-/
import Ytosk.V3DropR
import Ytosk.V3DropH
import Ytosk.V3HLast

namespace Ytosk

open T

/-- The remaining hypotheses of one drop, without `argT` and `HardArg`. -/
structure DropResR (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrc N x σ σ'
  ua : UpgAbsX N x σ
  ab : BumpAbsC N x σ
  vnr : VSmallNewR N x σ σ'
  sh : ShadowC N x σ σ'
  tnr : TailNR N x σ

/-- **The drop lemma from `DropResR`.** -/
theorem drop_all_RR {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hVR : VSmallR N σ)
    (hD : DropResR N x σ σ') (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) :
    ∀ i, i < x → PO σ σ' i ∧ PV N σ σ' i := by
  intro i hi
  have h := drop_all_R hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.vs hD.vst hI.fc hI.fo hVR hD.vnr
    hD.sh hD.tnr (bump_drop hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.kd hI.td hD.ab hD.ws) hD.ua i hi
  exact ⟨h.1.1, h.2⟩

/-- **`DropRes` from `DropResR`** and `VSmallR`. -/
theorem DropRes.ofR {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hVR : VSmallR N σ)
    (hD : DropResR N x σ σ') (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) : DropRes N x σ σ' := by
  have hdrop := drop_all_RR hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI hVR hD hC' hRk'
  have hGT := good3_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hdrop
  exact ⟨argT_std hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hGT, hD.vst, hD.ws, hD.ua, hD.ab⟩

/-- `Res3A` with the drop part replaced by `DropResR`. -/
structure Res3R (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropResR M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  seed : ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    lt (sf ((drop1 M (M.length - 1) rk).v r)) (ρ.v r) = true →
    ∀ a', ¬ lt (ρ.v r) a' = true →
    isOT (psi a' (app (qrB M ρ r (M.length - 1)) (psi (succ (ρ.v r)) z z)) z) = true →
    ∀ g ∈ comps a' ((drop1 M (M.length - 1) rk).o r),
      g < app (qrB M ρ r (M.length - 1)) ((drop1 M (M.length - 1) rk).o r)

/-- **`Res3A` from `Res3R`** (and `VSmallR` of `M`). -/
theorem Res3A.ofR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hne : M ≠ []) (S : SInv M)
    (V : Inv3V M ρ rk) (hVR : VSmallR M ρ) (h : Res3R M ρ rk) : Res3A M ρ rk := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h0 | h0
    · exact absurd (List.length_eq_zero_iff.mp h0) hne
    · exact h0
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) hl S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) V.rank hcnt
  exact ⟨DropRes.ofR hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab V.cons
    ⟨V.good, V.vs, V.fc, V.fo, V.kd, V.td⟩ hVR h.drop (cons_of_rk hRk1) hRk1, h.seed⟩

/-- **The top theorem without `HardArg`**: `VSmallR` on every standard matrix (`hVSR`), and `hLast`・`hExp`
give `Inv3V ∧ Res3R`. -/
theorem trio_terminates_main_R
    (hVSR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → VSmallR M ρ)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3R (M.take (M.length - 1)) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3R (expand M n) ρN rkN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' := by
  apply trio_terminates_main_T2 _ _ hR2
  · intro M ρ rk hM hS hl I R
    obtain ⟨ρ', rk', V, R'⟩ := hLast M ρ rk hM hS hl I R
    have hne : M.take (M.length - 1) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_take] at this; simp at this; omega
    have hS' : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V.rank
    have hM' := std_take hM (M.length - 1) (by omega)
    exact ⟨ρ', rk', V, Res3A.ofR hne (sInv_std hM' hS') V (hVSR (M.take (M.length - 1)) ρ' rk' hM' hS' hne V) R'⟩
  · intro M ρ rk hM hS hE I R hz n hn hNS hNE
    obtain ⟨ρN, rkN, V, R'⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
    have hMN := Std.exp n hM
    exact ⟨ρN, rkN, V, Res3A.ofR hNE (sInv_std hMN hNS) V (hVSR (expand M n) ρN rkN hMN hNS hNE V) R'⟩

/-- The seed condition of `Res3A` as a property of one matrix. -/
def SeedR (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    lt (sf ((drop1 M (M.length - 1) rk).v r)) (ρ.v r) = true →
    ∀ a', ¬ lt (ρ.v r) a' = true →
    isOT (psi a' (app (qrB M ρ r (M.length - 1)) (psi (succ (ρ.v r)) z z)) z) = true →
    ∀ g ∈ comps a' ((drop1 M (M.length - 1) rk).o r),
      g < app (qrB M ρ r (M.length - 1)) ((drop1 M (M.length - 1) rk).o r)

/-- **The value part of the one-column drop**: the drop lemma gives all fields of `Inv3V (M.take x)` except
the eleven hole fields (`hRest`). `RootP` at a root column `x` is `rootP_take_root`. -/
theorem inv3V_take_of
    (hRest : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      let x := M.length - 1
      let σ := drop1 M x rk
      AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
      TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
      TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ) :
    ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      Inv3V (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk := by
  intro M ρ rk hM hS hl I R
  obtain ⟨had, hau, htp1, htplo, htp1w, htplow, hauw, hadw, htrig, htplon, hadn⟩ :=
    hRest M ρ rk hM hS hl I R
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V := valInv_drop1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI R.drop
  have hRP : RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
    by_cases h0 : entry M 0 (M.length - 1) = 0
    · exact rootP_take_root hx (col_root_of_e0 I.r01 I.r12 h0) I.cons hC1 hRk1 I.rootP
    · exact rootP_drop1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 h0 I.cons I.rank hVI R.drop
        I.rootP
  exact ⟨hC1, V.g, hRk1, V.vs, V.fc, V.fo, V.kd, V.td, had, hau, htp1, htplo, htp1w, htplow,
    hauw, hadw, htrig, htplon, hadn, rootS_of_good hC1 V.g, hRP⟩

/-- **The top theorem with the per-matrix residuals made global.** The drop residual `DropResR`, the seed
condition and `VSmallR` are hypotheses on every standard matrix; the one-column drop needs only the eleven
hole fields of `M.take x` (`hRest`), and an expansion only `Inv3V` of `M[n]`. -/
theorem trio_terminates_main_G
    (hVSR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → VSmallR M ρ)
    (hDR : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk →
      DropResR M (M.length - 1) ρ (drop1 M (M.length - 1) rk))
    (hSeed : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → SeedR M ρ rk)
    (hRest : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      let x := M.length - 1
      let σ := drop1 M x rk
      AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
      TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
      TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ)
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' := by
  apply trio_terminates_main_R hVSR _ _ hR2
  · intro M ρ rk hM hS hl I R
    have V := inv3V_take_of hRest M ρ rk hM hS hl I R
    have hne : M.take (M.length - 1) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_take] at this; simp at this; omega
    have hS' : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V.rank
    have hM' := std_take hM (M.length - 1) (by omega)
    exact ⟨_, rk, V, hDR _ _ _ hM' hS' hne V, hSeed _ _ _ hM' hS' hne V⟩
  · intro M ρ rk hM hS hE I R hz n hn hNS hNE
    obtain ⟨ρN, rkN, V⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
    have hMN := Std.exp n hM
    exact ⟨ρN, rkN, V, hDR _ _ _ hMN hNS hNE V, hSeed _ _ _ hMN hNS hNE V⟩

end Ytosk
