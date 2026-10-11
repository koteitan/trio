/-
**`VSmallR` を帰納法で一緒に運ぶ最上位（大域の仮定 `hVSR` を外す）。**

`trio_terminates_main_G` の `hVSR`（すべての標準形で `VSmallR`）は、`Inv3 ∧ Res3A` と一緒に運べば仮定でなくなる:
- 基底 SRO[n]: 書き換える枠がない（`no_trig`）ので `VSmallR` は自明（`base_vsmallR`）。
- 1 列落とし: `vsmallR_take`（追加の仮定なし）。
- 展開 `M → M[n]`（n ≥ 2）: 仮定 `hVSRexp`（展開の担当が `VSmallF` と同じ仕組みで示す）。
-/
import Ytosk.V3DropRH
import Ytosk.V3BaseInd
import Ytosk.V3T2Fin

namespace Ytosk

open T

theorem base_vsmallR {L : Nat} {β : T} (hF : BaseFit L β) : VSmallR (Mlen L) (bval L β) := by
  intro i hi L' c R h s y ho htr
  obtain ⟨_, hc, _⟩ := CL_split hF h
  exact absurd (no_trig hF (by simpa using hi) hc ho htr.1 htr.2) id

/-- The base with `VSmallR`. -/
theorem hBaseVR_holds : ∀ n, expand SRO n ≠ [] →
    ∃ ρ rk, Inv3V (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk ∧ VSmallR (expand SRO n) ρ := by
  intro n _
  rw [expand_SRO_eq]
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  have hL : 1 ≤ 1 + 3 * n := by omega
  exact ⟨bval (1 + 3 * n) one, brk (1 + 3 * n), ⟨bval_cons hF, base_good3 hF, brk_rk le_rfl,
    base_vsmallF hF, base_frameClosed hF, base_frameOT hF, base_kd hF, base_td hF, base_ad hF,
    base_au hF, base_tp1 hF, base_tplo hF, base_tp1w hF, base_tplow hF, base_auw hF, base_adw hF,
    base_trig hF, base_tplon hF, base_adn hF, base_rootS hF hL, base_rootP hF hL⟩, base_res3A,
    base_vsmallR hF⟩

/-- `HInvE` with `VSmallR`. -/
def HInvER : Prop :=
  ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3 M ρ rk ∧ Res3A M ρ rk ∧ VSmallR M ρ

/-- **`HInvER` by induction on `Std`**, from the base and a step. -/
theorem hInvER_of_step
    (hBase : ∀ n, expand SRO n ≠ [] →
      ∃ ρ rk, Inv3 (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk ∧ VSmallR (expand SRO n) ρ)
    (hStep : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      ∀ n, expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3 (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN ∧ VSmallR (expand M n) ρN) :
    HInvER := by
  intro M hM
  induction hM with
  | sro => intro h; exact absurd rfl h
  | @exp M n hM ih =>
    intro hS hE
    by_cases hMS : M = SRO
    · subst hMS; exact hBase n hE
    by_cases hME : M = []
    · subst hME; exact absurd rfl hE
    obtain ⟨ρ, rk, I, R, P⟩ := ih hMS hME
    exact hStep M ρ rk hM hMS hME I R P n hS hE

/-- **The prefix step with `VSmallR`**, from the one-column drop. -/
theorem hTakeR_of_last
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk' ∧
        VSmallR (M.take (M.length - 1)) ρ') :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
        ∃ ρ' rk', Inv3 (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk' ∧ VSmallR (M.take j) ρ' := by
  have key : ∀ m M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      ∀ j, 1 ≤ j → j < M.length → M.length - j ≤ m →
        ∃ ρ' rk', Inv3 (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk' ∧ VSmallR (M.take j) ρ' := by
    intro m
    induction m with
    | zero => intro M ρ rk _ _ _ _ _ j _ hj hm; omega
    | succ m ih =>
      intro M ρ rk hM hS I R P j hj1 hj hm
      obtain ⟨ρ1, rk1, V1, R1, P1⟩ := hLast M ρ rk hM hS (by omega) I R P
      have hM1 : Std (M.take (M.length - 1)) := std_take hM _ (by omega)
      have hS1 : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V1.rank
      have I1 := Inv3.ofV (sInv_std hM1 hS1) V1
      by_cases hjx : j = M.length - 1
      · subst hjx; exact ⟨ρ1, rk1, I1, R1, P1⟩
      have hl1 : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
      obtain ⟨ρ', rk', I', R', P'⟩ := ih _ ρ1 rk1 hM1 hS1 I1 R1 P1 j hj1 (by omega) (by omega)
      rw [List.take_take, Nat.min_eq_left (by omega)] at I' R' P'
      exact ⟨ρ', rk', I', R', P'⟩
  intro M ρ rk hM hS _ I R P j hj _ hjE
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; exact absurd List.take_zero hjE
    · exact h0
  exact key _ M ρ rk hM hS I R P j hj1 hj (le_refl _)

/-- **The top theorem carrying `VSmallR`.** As `trio_terminates_main_G`, with the global `hVSR` replaced by
its preservation under the expansions `M → M[n]`, `n ≥ 2` (`hVSRexp`). -/
theorem trio_terminates_main_GP
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
    (hVSRexp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' := by
  -- the one-column drop, with `VSmallR`
  have hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk' ∧
        VSmallR (M.take (M.length - 1)) ρ' := by
    intro M ρ rk hM hS hl I R P
    have V := inv3V_take_of hRest M ρ rk hM hS hl I R
    have hx : M.length - 1 + 1 = M.length := by omega
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
    have hC1 := cons_of_rk hRk1
    have hdrop := drop_all hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
      I.fc I.fo R.drop.argT
      (bump_drop hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
      R.drop.ua
    have P' := vsmallR_take hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop P
    have hne : M.take (M.length - 1) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_take] at this; simp at this; omega
    have hS' : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V.rank
    have hM' := std_take hM (M.length - 1) (by omega)
    exact ⟨_, rk, V, Res3A.ofR hne (sInv_std hM' hS') V P' ⟨hDR _ _ _ hM' hS' hne V, hSeed _ _ _ hM' hS' hne V⟩,
      P'⟩
  have hTake := hTakeR_of_last hLast
  -- the step
  have hStep : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      ∀ n, expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3 (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN ∧ VSmallR (expand M n) ρN := by
    intro M ρ rk hM hS hE I R P n hNS hNE
    have hlen : 0 < M.length := by
      cases M with
      | nil => exact absurd rfl hE
      | cons _ _ => simp
    by_cases hz : col M (M.length - 1) = (0, 0, 0)
    · have he := expand_zero_last hE hz n
      rw [he] at hNS hNE ⊢
      exact hTake M ρ rk hM hS hE I R P _ (by omega) hNS hNE
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rcases Nat.lt_or_ge n 1 with hn0 | hn1
      · obtain rfl : n = 0 := by omega
        obtain ⟨j, hj, he⟩ := expand_zero_take hE
        rw [he] at hNS hNE ⊢
        exact hTake M ρ rk hM hS hE I R P j hj hNS hNE
      · obtain rfl : n = 1 := by omega
        rw [expand_one] at hNS hNE ⊢
        exact hTake M ρ rk hM hS hE I R P _ (by omega) hNS hNE
    · obtain ⟨ρN, rkN, V⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
      have hMN := Std.exp n hM
      have PN := hVSRexp M ρ rk hM hS hE I R P hz n hn hNS hNE ρN rkN V
      exact ⟨ρN, rkN, Inv3.ofV (sInv_std hMN hNS) V,
        Res3A.ofR hNE (sInv_std hMN hNS) V PN ⟨hDR _ _ _ hMN hNS hNE V, hSeed _ _ _ hMN hNS hNE V⟩, PN⟩
  have hER : HInvER := hInvER_of_step (fun n hE => by
    obtain ⟨ρ, rk, V, R, P⟩ := hBaseVR_holds n hE
    have hSRO : expand SRO n ≠ SRO := by
      intro h
      have := congrArg List.length h
      rw [expand_SRO_length] at this
      simp [SRO] at this
      omega
    exact ⟨ρ, rk, Inv3.ofV (sInv_std (Std.exp n Std.sro) hSRO) V, R, P⟩) hStep
  have hE : HInvE := fun M hM hS hE' => by
    obtain ⟨ρ, rk, I, R, _⟩ := hER M hM hS hE'
    exact ⟨ρ, rk, I, R⟩
  exact trio_terminatesE hE (t2_hT2E hR2)

end Ytosk
