/-
**接ぎ木の悪い形 `Bad2` の M[n]（n ≥ 2）を t = 0 と残りに分ける（2026-10-25）。**

- `BadOutT0`: `Bad2` で最後の列の行 0 の親で展開する場合（`srow = 0`）。`badOutT0_of` で、落とす補題の結論
  （`HDropU` から、`T0DropF.of_U`）・1 列落としの Inv3V2（`TakeBadV2`）・共有の残り `HFrameV2`・`HLeafV2` と、
  `HBumpExt`（`T0AbsW` は `t0AbsW_of_U`）と新しい残り `T0BadSeeds`（種の事実 `T0SeedsN`）から、V3T0Bad のエンジンで証明する。
- `BadOutRest`: 残りの場合（t = 1・t = 2、最後の列が 0）。`badOutV2_of` で 2 つから `BadOutV2`。
-/
import Ytosk.V3T0Bad
import Ytosk.V3GlobV2
import Ytosk.V3BumpExt

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The drop facts of every standard matrix** from `HDropU` (also on `Bad2`). -/
theorem T0DropF.of_U (h : HDropU) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk) : T0DropF M ρ rk := by
  have hE : M ≠ [] := by intro he; rw [he] at hl; simp at hl
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := hdrop_of_U h hM hS hl I
  exact ⟨hdrop, drop_presD hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdrop (h M ρ rk hM hS hE I).1.vst hC1 hRk1⟩

/-- **The weak absorption at `t = 0`** from `HDropU` (its `BumpAbsC` at `t = 0`, also on `Bad2`) and `HBumpExt`. -/
theorem t0AbsW_of_U (hDU : HDropU) (hBE : HBumpExt) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3V2 M ρ rk) {r L : Nat} (hlen : r + L + 1 = M.length)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) : T0AbsW M r L ρ := by
  have S := sInv_std hM hS
  have hE : M ≠ [] := by intro he; rw [he] at hlen; simp at hlen
  have hxl : M.length - 1 = r + L := by omega
  have hab := (hDU M ρ rk hM hS hE I).2 (Or.inr (by rw [hxl]; exact he1))
  rw [hxl] at hab
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [hxl] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hτ := cons_of_rk hRk1
  exact t0AbsW_of hτ (absWN_take_t0 hab I.cons (by omega) he1 hτ)
    (t0BumpMono_of_ext hBE hM hlen hp he1 (S.r12 _ he1))

/-- **Residual: the seed facts of a `Bad2` matrix at `t = 0`** (2026-10-25): the seeds S1・S2・S3 of every `M[n]`
(`T0SeedsN`). On graftB's 108 such matrices (`r = P_0(x)` is `g`, `p` or `x − 1`, 36 each) all seeds hold for
`n = 2, 3` (tmp: t0seed.py, t0cls.py). -/
def T0BadSeeds : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ

/-- **The `t = 0` part of `BadOutV2`.** -/
def BadOutT0 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Bad2 M → Inv3V2 M ρ rk →
    col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
    ∀ n, 2 ≤ n → (∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ DropsAt M ρ n

/-- **Residual: the rest of `BadOutV2`** (`t = 1`, `t = 2`, and a zero last column). -/
def BadOutRest : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Bad2 M → Inv3V2 M ρ rk →
    ¬ (col M (M.length - 1) ≠ (0, 0, 0) ∧ TRIO.srow M (M.length - 1) = 0) →
    ∀ n, 2 ≤ n → (∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ DropsAt M ρ n

theorem badOutV2_of (h0 : BadOutT0) (h1 : BadOutRest) : BadOutV2 := by
  intro M ρ rk hM hS hE hB I n hn
  by_cases h : col M (M.length - 1) ≠ (0, 0, 0) ∧ TRIO.srow M (M.length - 1) = 0
  · exact h0 M ρ rk hM hS hE hB I h.1 h.2 n hn
  · exact h1 M ρ rk hM hS hE hB I h n hn

/-- **`BadOutT0` from the drop residual, the one-column drop of `Bad2`, the shared residuals and the seeds.** -/
theorem badOutT0_of (hDU : HDropU) (hBE : HBumpExt) (hTB : TakeBadV2) (hF : HFrameV2) (hLf : HLeafV2)
    (hSe : T0BadSeeds) :
    BadOutT0 := by
  intro M ρ rk hM hS hE hB I hz hs0 n hn2
  have S := sInv_std hM hS
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shapeS S hz hs0
  have hl2 : 2 ≤ M.length := by omega
  have D := T0DropF.of_U hDU hM hS hl2 I
  obtain ⟨I1, _⟩ := hTB M ρ rk hM hS hl2 hB I
  rw [show M.length - 1 = r + L by omega] at I1
  have hSd := hSe M ρ rk hM hS hB I r L hlen hL hp he1
  have hAbW := t0AbsW_of_U hDU hBE hM hS I hlen hp he1
  have hDF := t0DF_ofG hM hS (I.toC S) D I.ph I.vra.toLast
    (fun r' L' hl' hp' he' => t0AbsW_of_U hDU hBE hM hS I hl' hp' he')
    (fun r' L' hl' hL' hp' he' => hSe M ρ rk hM hS hB I r' L' hl' hL' hp' he')
  have hNs : ∀ n, 1 ≤ n → TRIO.gexp M r L 0 0 n ≠ [] := fun n hn he => by
    have h1 := congrArg List.length he
    have h2 : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
    have h3 : L ≤ n * L := Nat.le_mul_of_pos_left L hn
    simp only [List.length_nil] at h1
    omega
  obtain ⟨ρN, rkN, IN, hot, hlt⟩ := t0_final_inv3V2G hM hS S I hlen hL hp he1 D hAbW hSd I1 hDF
    (fun n hn σ rkN hC hR hG => hLf _ σ rkN (std_gexp_t0C hM (I.toC S) hlen hL hp he1 n) (ne_SRO_of_rk hR)
      (hNs n (by omega)) hC hR hG)
    (fun n hn σ rkN hC hR hG => hF _ σ rkN (std_gexp_t0C hM (I.toC S) hlen hL hp he1 n) (ne_SRO_of_rk hR)
      (hNs n (by omega)) hC hR hG)
    n hn2
  exact ⟨⟨ρN, rkN, by rw [hexp n]; exact IN⟩, dropsAt_of (hexp n) ⟨ρN, rkN, IN.cons, IN.rank, hot, hlt⟩⟩

/-- **The last column of a `Bad2` matrix is not `(0,0,0)`**: `x` lies under `g`, or has row 2 ≠ 0, or row 1 ≠ 0. -/
theorem bad2_col_ne_zero {M : Mat} (hB : Bad2 M) : col M (M.length - 1) ≠ (0, 0, 0) := by
  intro h0
  have hc : M.getD (M.length - 1) (0, 0, 0) = (0, 0, 0) := h0
  have e1 : entry M 1 (M.length - 1) = 0 := by unfold entry; rw [hc]; rfl
  have e2 : entry M 2 (M.length - 1) = 0 := by unfold entry; rw [hc]; rfl
  have e0 : entry M 0 (M.length - 1) = 0 := by unfold entry; rw [hc]; rfl
  obtain ⟨⟨k, hu⟩, p, g, hp, hg, hb, hcase⟩ := hB
  rcases hcase with ⟨hA | hA, _⟩ | ⟨_, hA, _⟩
  · have hpl := par_lt M 0 _ _ hp
    have hgl := par_lt M 0 _ _ hg
    have := anc0_e0_lt hA (by omega)
    omega
  · exact hA e2
  · exact hA e1

/-- **Residual: `BadOutV2` at `t = 1` and `t = 2`** (2026-10-25; the zero last column does not occur in `Bad2`). -/
def BadOutT12 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Bad2 M → Inv3V2 M ρ rk → TRIO.srow M (M.length - 1) ≠ 0 →
    ∀ n, 2 ≤ n → (∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ DropsAt M ρ n

theorem badOutRest_of (h : BadOutT12) : BadOutRest := by
  intro M ρ rk hM hS hE hB I hn0 n hn
  exact h M ρ rk hM hS hE hB I (fun h0 => hn0 ⟨bad2_col_ne_zero hB, h0⟩) n hn

end Ytosk
