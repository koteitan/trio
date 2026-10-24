/-
**行列ごとの共通の残り（2026-10-16、top）。**

最後の列の枠の 10 欄（TakeFrameV2）と葉の条件（TP1LeafG・TP1WLeafG）は、どれも行列ごとの主張。
drop（M.take x）・t0（M[n]）・t1（各コピー）・t2（M[n]）が同じ種類の残りを持つので、
「どの標準形でも、Cons・Rk・Good3 を満たす評価で成り立つ」という共通の残りを 1 つずつ置く。

- `HFrameV2`: 枠の 10 欄。`HLeafV2`: 葉の 2 条件。
- 変換: `hTake_of_glob`（drop の HTakeV2）、`t0Frame_of_glob`・`t0Leaf_of_glob`（t0 の T0NRes）。

注意: 共通の形は前件が弱い（親の行列の Inv3V2 を使えない）ので、担当ごとの形より強い主張。
担当ごとの形（TakeResV2・T0NRes TakeFrameV2 など）で示してもよい。
-/
import Ytosk.V3MainV2
import Ytosk.V3BumpDropB

namespace Ytosk

open T

/-- **The last-column frame fields of every standard matrix.** -/
def HFrameV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → N ≠ [] → Cons N σ → Rk N rk → Good3 N σ → TakeFrameV2 N σ rk

/-- **The two leaf conditions of every standard matrix.** -/
def HLeafV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → N ≠ [] → Cons N σ → Rk N rk → Good3 N σ →
    TP1LeafG N σ ∧ TP1WLeafG N σ

/-- `HTakeV2` from the two shared residuals. -/
theorem hTake_of_glob (hF : HFrameV2) (hL : HLeafV2) : HTakeV2 := by
  intro M ρ rk hM hS hl I R
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have V := valInv_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.rank
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ R.drop
  have hM1 := std_take hM (M.length - 1) (by omega)
  have hS1 := ne_SRO_of_rk hRk1
  have hE1 := take_ne_nil_of (M := M) (j := M.length - 1) (by omega) (by omega)
  obtain ⟨h1, h2⟩ := hL _ _ rk hM1 hS1 hE1 hC1 hRk1 V.g
  exact ⟨hF _ _ rk hM1 hS1 hE1 hC1 hRk1 V.g, h1, h2⟩

/-- **Residual: the conclusion of the drop lemma at a `Bad2` matrix** (2026-10-25): `PO ∧ PV` at every column (with
the third case of `CntX`), `VSmallNew`, and the strict descent of the root. On `Bad2` the hypotheses of the drop
lemma fail, but its conclusion holds (graftB, desc). -/
def DropBadV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Bad2 M → Inv3V2 M ρ rk →
    (∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i) ∧
    VSmallNew M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ

/-- **The hypotheses of the drop lemma in the `Bad2` form** (2026-10-25): `HardArg`, `VSmallNew`, the weak sources
`BumpWeakSrcB`, the absorption at `x − 1` with the weak alternative `WCSP ∧ SmallSelf` (no parent condition), and the
bump absorption `BumpAbsCB`. -/
structure DropResB (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  argT : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (N.take x) i = Lc ++ [cs] →
    ∀ s y, σ'.o cs = psi s y z → ¬ lt s (σ.v i) = true →
    ∀ g ∈ comps (σ.v i) y, g ≤ step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y z
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrcB N x σ σ'
  ua : ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt σ (par N 1 i)), r < W → Lhd z r W) ∨
      (WCSP N σ i (add (vOpt σ (par N 1 i)) one) ∧
        (∀ g ∈ comps z (add (vOpt σ (par N 1 i)) one), g < psi (add (vOpt σ (par N 1 i)) one) z z))
  ab : BumpAbsCB N x σ

/-- **Residual: the drop hypotheses at a `Bad2` matrix** (2026-10-25), with the strict descent of the root. -/
def DropBadV2B : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Bad2 M → Inv3V2 M ρ rk →
    DropResB M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ

/-- **`DropBadV2` from the drop lemma in the `Bad2` form** (`drop_allB`, `bump_dropB`). -/
theorem dropBad_of_B (h : DropBadV2B) : DropBadV2 := by
  intro M ρ rk hM hS hl hB I
  obtain ⟨R, hlt⟩ := h M ρ rk hM hS hl hB I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  refine ⟨drop_allB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs R.vst I.fc I.fo R.argT
    (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td R.ab R.ws) R.ua,
    R.vst, hlt⟩

/-- **The hypotheses of the drop lemma in the `Bad2` form with `HardArg`** (2026-10-25). -/
structure DropResHB (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  hard : HardArg N x σ σ'
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrcB N x σ σ'
  ua : ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt σ (par N 1 i)), r < W → Lhd z r W) ∨
      (WCSP N σ i (add (vOpt σ (par N 1 i)) one) ∧
        (∀ g ∈ comps z (add (vOpt σ (par N 1 i)) one), g < psi (add (vOpt σ (par N 1 i)) one) z z))
  ab : BumpAbsCB N x σ

/-- **Residual: the drop hypotheses of every standard matrix** (2026-10-25): the `Bad2` form `DropResHB` everywhere,
and `BumpAbsC` outside `Bad2`. Measured on the 11 sets and the grafted sets with no exception (desc). It replaces
`HDropV2W` (outside `Bad2`) and the drop part of `DropBadV2B` (on `Bad2`). -/
def HDropU : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResHB M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧
      (¬ Bad2 M → BumpAbsC M (M.length - 1) ρ)

/-- **`HDropV2W` from `HDropU`**: outside `Bad2` the weak sources have the old shape (`noBad3_of_nb2`), and a weak
alternative at `x − 1` with a bump parent has `x` above the grandparent and row 2 = 0 (else `Bad2`). -/
theorem hDropV2W_of_U (h : HDropU) : HDropV2W := by
  intro M ρ rk hM hS hE hNB I
  obtain ⟨R, hab⟩ := h M ρ rk hM hS hE I
  have h3 := noBad3_of_nb2 hNB I.cons
  refine ⟨R.hard, R.vst, ⟨fun i h1 h2 j hj hjb k hk ⟨w, hw, hok⟩ hcase => ?_, R.ws.2, h3⟩, ?_, hab hNB⟩
  · obtain ⟨hsh, hhead⟩ := R.ws.1 i h1 h2 j hj hjb k hk ⟨w, z, hw, hok⟩ hcase
    rcases hsh with hsh | ⟨_, hu, hb⟩
    · exact ⟨hsh, hhead⟩
    · exact absurd ⟨hu, hb⟩ h3
  · intro i k W hix hu hvk hW
    rcases R.ua i k W hix hu hvk hW with hs | ⟨hwc, hss⟩
    · exact Or.inl hs
    by_cases hs : ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W
    · exact Or.inl hs
    refine Or.inr ⟨hwc, hss, fun p g hp hg hb => ?_⟩
    by_contra hc
    apply hNB
    have hi2 : M.length - 2 = i := by omega
    refine ⟨⟨k, by rw [hi2]; exact hu⟩, p, g, by rw [hi2]; exact hp, hg, hb, Or.inl ⟨?_, ρ, I.cons, ?_⟩⟩
    · by_contra hn
      push Not at hn
      exact hc ⟨hn.1, hn.2⟩
    · intro hS'
      exact hs (hS' i k W (by omega) hu hvk hW)

/-- **The strict descent of the root at the one-column drop of a `Bad2` matrix** (2026-10-25). -/
def RootBadV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Bad2 M → Inv3V2 M ρ rk →
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ

/-- **Residual: `RootBadV2` when `x` has row 2 ≠ 0** (`t = 2`; the other types follow from the drop lemma,
`root_drop_e2z`). -/
def RootBadV2T2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Bad2 M → Inv3V2 M ρ rk → entry M 2 (M.length - 1) ≠ 0 →
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ

/-- **The conclusion of the drop lemma from `HDropU`** (`drop_all_hardB`, `bump_dropB`), for every standard matrix. -/
theorem hdrop_of_U (h : HDropU) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk) :
    ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i := by
  have hE : M ≠ [] := by intro he; rw [he] at hl; simp at hl
  obtain ⟨R, _⟩ := h M ρ rk hM hS hE I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  exact drop_all_hardB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs R.vst I.fc I.fo
    R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td R.ab R.ws) R.ua

/-- **The strict descent of the root at the one-column drop when `x` has row 2 = 0** (`t = 0, 1`), from the
conclusion of the drop lemma alone (`dep_strict0`, `root_take_lt`), for any standard matrix. -/
theorem root_drop_e2z {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk)
    (hdrop : ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i)
    (hx2 : entry M 2 (M.length - 1) = 0) :
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ := by
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  refine (root_take_lt hx S.r01 S.r12 S.e00 I.cons I.good (fun i hi => (hdrop i hi).1.2.1)
    (fun i hi => (hdrop i hi).1.le) ?_).2
  intro R hR hRA _
  obtain ⟨q, hq⟩ := par0_of_anc hRA (by omega)
  have hnx : ¬ DepX M (M.length - 1) false (M.length - 1) := by
    by_cases he1 : entry M 1 (M.length - 1) = 0
    · intro h
      cases h with
      | vpar h1 _ _ => exact h1 he1
      | vupg h1 _ _ _ => exact h1 he1
      | vbump h1 _ _ _ _ _ => exact h1 he1
    · obtain ⟨r, hr⟩ := par1_exists S.e00 S.r01 (by omega : 0 < entry M 1 (M.length - 1))
      have hrx : r < M.length - 1 := par_lt M 1 _ r hr
      obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
      have hlen : r + L + 1 = M.length := by omega
      have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) (by rw [← hL]; exact hr)
      rw [hL] at hr hq hx2 ⊢
      intro h
      cases h with
      | vpar _ hp hdm =>
        rw [hr] at hp; cases hp
        by_cases hqr : q = r
        · subst hqr
          exact (qr_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hr hx2 hq).2.1 hdm
        · exact v_r_not_chg hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hA (by omega)
            (fun h' => hqr (Option.some.inj (hq.symm.trans h')))
            (hpath_of_par1 hr hA (by omega)) (depX_chgX hdm)
      | vupg _ _ hu _ => have := upg_succ_lt hu; omega
      | vbump _ h2 _ _ _ _ => exact h2 hx2
  have hD := dep_strict0 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop hx2 hq hnx
  exact hD true R (dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hx hx2 hRA) hR

/-- **`RootBadV2` from `HDropU` and the `t = 2` part.** -/
theorem rootBad_of_T2 (h : HDropU) (h2 : RootBadV2T2) : RootBadV2 := by
  intro M ρ rk hM hS hl hB I
  by_cases hx2 : entry M 2 (M.length - 1) = 0
  · exact root_drop_e2z hM hS hl I (hdrop_of_U h hM hS hl I) hx2
  · exact h2 M ρ rk hM hS hl hB I hx2

/-- **`DropBadV2B` from `HDropU` and `RootBadV2`**: `argT` from the standardness of `M.take x` (`drop_all_hardB`,
`good3_take`, `argT_std`). -/
theorem dropBadB_of_U (h : HDropU) (hR : RootBadV2) : DropBadV2B := by
  intro M ρ rk hM hS hl hB I
  have hE : M ≠ [] := by intro he; rw [he] at hl; simp at hl
  obtain ⟨R, _⟩ := h M ρ rk hM hS hE I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all_hardB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs R.vst I.fc I.fo
    R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td R.ab R.ws) R.ua
  have hGT := good3_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop
  exact ⟨⟨argT_std hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hGT, R.vst, R.ws, R.ua, R.ab⟩,
    hR M ρ rk hM hS hl hB I⟩

/-- **`TakeBadV2` from the drop conclusion and the two shared residuals.** -/
theorem takeBad_of_drop (hDB : DropBadV2) (hF : HFrameV2) (hL : HLeafV2) : TakeBadV2 := by
  intro M ρ rk hM hS hl hB I
  obtain ⟨hdrop, hvst, hlt⟩ := hDB M ρ rk hM hS hl hB I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have V := drop_presD hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdrop hvst hC1 hRk1
  have hM1 := std_take hM (M.length - 1) (by omega)
  have hS1 := ne_SRO_of_rk hRk1
  have hE1 := take_ne_nil_of (M := M) (j := M.length - 1) (by omega) (by omega)
  obtain ⟨h1, h2⟩ := hL _ _ rk hM1 hS1 hE1 hC1 hRk1 V.g
  exact ⟨inv3V2_takeD S I hl hdrop hvst (hF _ _ rk hM1 hS1 hE1 hC1 hRk1 V.g) h1 h2
    (fun h0 => rootP0_take S I hl h0), hlt⟩

theorem gexp_t0_facts {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (C : StepCtxV2 M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0) (n : Nat) (hn : 2 ≤ n) :
    Std (TRIO.gexp M r L 0 0 n) ∧ TRIO.gexp M r L 0 0 n ≠ [] := by
  refine ⟨std_gexp_t0C C.std (Inv3V2.toC C.S C.I) hlen hL hp he1 n, ?_⟩
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen (show 1 ≤ n by omega)
  apply List.ne_nil_of_length_pos
  have : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  omega

theorem t0Frame_of_glob (hF : HFrameV2) : T0NRes TakeFrameV2 := by
  intro M ρ rk r L C hlen hL hp he1 n hn σ rkN hCN hRN hGN
  obtain ⟨hStd, hE⟩ := gexp_t0_facts C hlen hL hp he1 n hn
  exact hF _ σ rkN hStd (ne_SRO_of_rk hRN) hE hCN hRN hGN

theorem t0Leaf_of_glob (hL0 : HLeafV2) : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ) := by
  intro M ρ rk r L C hlen hL hp he1 n hn σ rkN hCN hRN hGN
  obtain ⟨hStd, hE⟩ := gexp_t0_facts C hlen hL hp he1 n hn
  exact hL0 _ σ rkN hStd (ne_SRO_of_rk hRN) hE hCN hRN hGN

end Ytosk
