/-
**落とす補題の残りから HardArg を外した形を最上位までつなぐ。**

- `DropResR`: 1 回の落としの残りの仮定。`argT` も `HardArg` もなく、代わりに `VSmallNewR`・`ShadowC`・`TailNR`。
- `DropRes.ofR`: `drop_all_R`（関係 `RelR` を運ぶ落とす補題）→ `good3_take` → `argT_std` で `DropRes`。
  1 行列の値の不変条件 `VSmallR` を使う。
- `Res3R`・`Res3A.ofR`、最上位 `trio_terminates_main_R`: hLast・hExp は `Inv3V ∧ Res3R` を出せばよく、
  `VSmallR` はすべての標準形について成り立つことを仮定 `hVSR` にする。
-/
import Ytosk.V3DropR
import Ytosk.V3TailNR
import Ytosk.V3DropH
import Ytosk.V3HLast

namespace Ytosk

open T

/-- The remaining hypotheses of one drop, without `argT` and `HardArg`. -/
structure DropResR (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrc N x σ σ'
  ua : UpgAbsXW N x σ
  ab : BumpAbsC N x σ
  vnr : VSmallNewR N x σ σ'
  sh : ShadowC N x σ σ'
  /-- `TailNR` narrowed to `y ≤ ψ_s(y)` in the tail without `x` (`tailNR_of`, `tailNRL_of`) -/
  tnr : TailY N x σ

/-- **The drop lemma from `DropResR`.** -/
theorem drop_all_RR {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hVR : VSmallR N σ)
    (hD : DropResR N x σ σ') (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) :
    ∀ i, i < x → PO σ σ' i ∧ PV N σ σ' i := by
  intro i hi
  have h := drop_all_R hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.vs hD.vst hI.fc hI.fo hVR hD.vnr
    hD.sh (tailNR_of hx hC hI.g (tailNRL_of hx hC hI.g hD.tnr)) (bump_drop hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.kd hI.td hD.ab hD.ws) hD.ua i hi
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
  /-- the strong absorption at `t = 2` and `t = 0` (`AbsSR`, 2026-10-11) -/
  abS : AbsSR M ρ

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
    ⟨V.good, V.vs, V.fc, V.fo, V.kd, V.td⟩ hVR h.drop (cons_of_rk hRk1) hRk1, h.seed, h.abS⟩

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
    (hAbS : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V M ρ rk → AbsSR M ρ)
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
    exact ⟨_, rk, V, hDR _ _ _ hM' hS' hne V, hSeed _ _ _ hM' hS' hne V, hAbS _ _ _ hM' hS' hne V⟩
  · intro M ρ rk hM hS hE I R hz n hn hNS hNE
    obtain ⟨ρN, rkN, V⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
    have hMN := Std.exp n hM
    exact ⟨ρN, rkN, V, hDR _ _ _ hMN hNS hNE V, hSeed _ _ _ hMN hNS hNE V, hAbS _ _ _ hMN hNS hNE V⟩

/-- **`VSmallR` passes to `M.take x`** (no extra hypothesis): a changed last child with the same
subscript rewrites only if the old one does, and a changed subscript comes with the argument `0`. -/
theorem vsmallR_take {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i) (hVR : VSmallR M ρ) : VSmallR (M.take x) ρ' := by
  intro i hi L c R h s' y' hc' ht' hhz' u hu g hg
  rw [lenT hx] at hi
  have hiM : i < M.length := by omega
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  rw [hv, hL] at ht'
  rw [hv] at hu ⊢
  rw [hL]
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcc := cl_mem_children hcT
  have hcx : c < x := by have := (mem_children hcc).2; rw [lenT hx] at this; exact this
  have hcM : c < M.length := by omega
  have hcxT : c < (M.take x).length := by rw [lenT hx]; exact hcx
  obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
  have hy'z : y' ≠ z := ne_z_of_lt ht'.1
  -- the subscript does not change
  have hss : s' = s := by
    have hvM : s = ρ.v c := by
      obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
      rw [hsy] at hy0; simp only [psi.injEq] at hy0
      rw [hy0.1, sf_ot (hG.ot_v c hcM)]
    have hvT : s' = ρ'.v c := by
      obtain ⟨y0, hy0⟩ := o_psi_sub hC' hcxT
      rw [hc'] at hy0; simp only [psi.injEq] at hy0
      rw [hy0.1, sf_ot (hdrop c hcx).2.2]
    rw [hvM, hvT]
    by_contra hvs
    have hCv : ChgX M x false c := by
      by_contra hn; exact hvs ((chg_off hx hC hG hC' hRk' c hcx).2 hn)
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hcx
    have ho := o_of_no_counted hC' hcxT (hdrop c hcx).2.2 hT.2.1
    rw [hc'] at ho; simp only [psi.injEq] at ho
    exact hy'z ho.2.1
  subst hss
  -- `y′ ≤ y`
  have hyy : y' ≤ y := by
    rcases (hdrop c hcx).1.1 with hle | ⟨⟨w1, _, _, e1, _, _⟩, _⟩
    · rw [hc', hsy] at hle
      rcases (le_iff _ _).mp hle.le with h' | h'
      · rcases psi_lt_psi_z_iff.mp h' with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl' _)
        · exact le_of_lt h'
      · simp only [psi.injEq] at h'; rw [h'.2.1]
    · rw [hc'] at e1; simp only [psi.injEq] at e1; exact absurd e1.2.1 hy'z
  have ht : lt (spArg (ρ.v i) z (sumN (L.map ρ.o))) y = true ∧
      lt (psi (ρ.v i) z z) (psi s' y z) = true :=
    ⟨lt_of_lt_of_le (show _ < y' from ht'.1) hyy,
      lt_of_lt_of_le (show psi (ρ.v i) z z < psi s' y' z from ht'.2) (psi_le_psi_arg hyy)⟩
  have hhz : (split y (psi (succ s') z z)).1 ≠ z := by
    rcases (le_iff _ _).mp hyy with hlt | rfl
    · rcases split_mono (psi (succ s') z z) hlt with h' | ⟨h', _⟩
      · intro h0; rw [h0] at h'; exact T.not_lt_z _ h'
      · rw [← h']; exact hhz'
    · exact hhz'
  exact hVR i hiM L c (R ++ Tl) hM s' y hsy ht hhz u hu g hg

end Ytosk
