/-
**Inv3V の作り直し `Inv3V2`（2026-10-12）。**

偽だった欄を、使う所（消費者）が本当に要る形に替える。
V3BaseInv2 と V3TakeInv2 で基底と 1 列落としに使用。既存の最上位と展開側への移行は未完。

- `AbsUW`（T2Ext で偽）→ `AbsUWL`（最後の列の枠、鎖の下限 gamS μ b_r 1 (max 1 d_i)）＋ `AbsUW0`（添字 0 = 種）。
- `AbsD`（ext1 で偽、t = 1・q ≠ r の DepX の枠）→ `AbsDS`（q ≠ r の最後の列の枠、種 o_{M.take x}(r) での吸収）。
- `TPLo`（ext1 で偽、同じ枠）→ `TPLoS`（q ≠ r の最後の列の枠、種での TPL の比較）。
- `AbsU`（偽ではないが生産者 absU_of_absD・absU_of_phiX の元が偽）→ `AbsUS`（q ≠ r の最後の列の枠、種での吸収）。
  本当に使うのは vlocal_t1 の上げの枠だけ。
- `TrigOmC` → `TrigS0`（種 < ψ_μ(1)、子の持ち上げ回数 = 0 の枠で状態 < b + 種）。
  子の持ち上げ回数を制限しない `TrigS` は T2Ext で偽。
- 新しい欄: `PH3cG`・`FC3`（closure、今は最上位の大域の仮定 hPH）、`VSmallRAll`（t0-exp の V3VSRAll、全部の数える子の枠。t2 の VSmallRA は VSmallRAll.toLast）。
- そのまま: Cons・Good3・Rk・VSmallF・FrameClosed・FrameOT・BumpKidsDec・BumpTermDec・TP1C・TP1WC・
  TPLoW・AbsDW・TPLoN・AbsDN・rootS・rootP。

種 o_{M.take x}(r) は drop1 M x rk の値（AbsUW0 と同じ）。

欄ごとの生産者と消費者の表は desc.md「Inv3V2 の下書き」の節。
-/
import Ytosk.V3IndV
import Ytosk.V3QRFinal4
import Ytosk.V3PDef
import Ytosk.V3DepRWU
import Ytosk.V3VSRAll
import Ytosk.V3TrigSeed
import Ytosk.V3SeedFields

namespace Ytosk

open T

/-- **The trigger at the seed** (`hYBs` of `qr_final3`; t1-exp の trigs.py): in the frame of the last column `x`
(`t = 1`, `q = r`, `o(r) = ψ_μ(b + Ω_{μ+1})`) with the seed `o_{M.take x}(r) < ψ_μ(1)`, at a frame `i` of `D`
whose counted child `c` of `D` is `ψ_s(b + Ω_{μ+1})` and rewrites, the state is below `b + seed`. `TrigOmC`
(state `= 0`) is false on T2Ext (2 matrices, this frame); its only real use is this frame and the carries. -/
def TrigS (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
    (drop1 M (M.length - 1) rk).o r < psi μ one z →
    ∀ i L' c R, i < M.length - 1 → DepX M (M.length - 1) true i → children M i = L' ++ c :: R →
    Counted M i c → DepX M (M.length - 1) true c → ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
    lt (preState M ρ i L') (app b (psi (succ μ) z z)) = true →
    lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
    lt (preState M ρ i L') (app b ((drop1 M (M.length - 1) rk).o r)) = true

/-- Exhaustive success of the older, stronger test also validates TrigS0.
This implication is only for comparing the measurements; production uses TrigS0. -/
theorem trigS0_of_trigS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (h : TrigS M ρ rk) : TrigS0 M ρ rk :=
  fun r μ b h1 h0 h2 hro hs i L' c R hi hd hch hcnt hdc _ =>
    h r μ b h1 h0 h2 hro hs i L' c R hi hd hch hcnt hdc

/-- **The grafted bad shape** (2026-10-24): the column `x − 1` (`x` the last column) has an upgrade target, its
parent `p` is the bump child of `g`, and either the strong absorption at `x − 1` fails while `x` lies under `g` or has
row 2 ≠ 0, or `x` is the child of `x − 1` with row 1 ≠ 0 and `BumpAbsC` fails. On standard matrices of this shape the frame fields
`TPLoW`・`AbsDW` and the drop fields `BumpWeakSrc`・`UpgAbsXW0`・`BumpAbsC` can fail (grafted sets graftA・graftB,
desc); outside it they hold. (The same day it was narrowed twice from "upgrade target ∧ bump parent": when `x` lies
above `g` the fields hold with `NBParX` in place of `NBPar` in `UpgAbsXW0`; at `t = 2` the engines need
`NBPar M (x − 1)` only when the strong absorption fails; under `g` with the strong absorption the fields fail only
when `x` is the child of `x − 1` with row 1 ≠ 0; after `TPLoWs`・`AbsDWs` replaced `TPLoW`・`AbsDW` only `BumpAbsC`
fails there.) -/
def Bad2 (M : Mat) : Prop :=
  (∃ k, upg M (M.length - 2) = some k) ∧
    ∃ p g, par M 0 (M.length - 2) = some p ∧ par M 0 p = some g ∧ col M p = bump M g ∧
      (((Anc0 M g (M.length - 1) ∨ entry M 2 (M.length - 1) ≠ 0) ∧
          ∃ ρ, Cons M ρ ∧ ¬ UpgAbsX M (M.length - 1) ρ) ∨
        (par M 0 (M.length - 1) = some (M.length - 2) ∧ entry M 1 (M.length - 1) ≠ 0 ∧
          ∃ ρ, Cons M ρ ∧ ¬ BumpAbsC M (M.length - 1) ρ))

/-- **Outside `Bad2` the third case of `CntX` does not occur**: a failed upgrade of `x − 1` at the bad position is
`Bad2`. -/
theorem noBad3_of_nb2 {M : Mat} {ρ : Valn} (hNB : ¬ Bad2 M) (hC : Cons M ρ) : NoBad3 M ρ := by
  rintro ⟨⟨k, W, hi2, hu, hvk, hWz, hn⟩, ⟨p, g, hp, hg, hb, hA⟩⟩
  exact hNB ⟨⟨k, hu⟩, p, g, hp, hg, hb,
    Or.inl ⟨Or.inl hA, ρ, hC, fun hS => hn (hS _ k W (by omega) hu hvk hWz)⟩⟩

/-- **`TPLoW` at the chain terms of the seed `o_{M.take x}(r)`** (2026-10-24). Unlike `TPLoW` (at the lower
bound `gamS μ b_r 1 (max 1 d)`), it holds on every grafted standard matrix (graftA・graftB, including `Bad2`). -/
def TPLoWs (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  TPLoWAt M ρ (fun r => (drop1 M (M.length - 1) rk).o r)

/-- **`AbsDW` at the chain terms of the seed `o_{M.take x}(r)`** (2026-10-24), as `TPLoWs`. -/
def AbsDWs (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  AbsDWAt M ρ (fun r => (drop1 M (M.length - 1) rk).o r)

/-- **The redesigned value part**. -/
structure Inv3V2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  ph : PH3cG M ρ
  fc3 : FC3 M ρ
  vra : VSmallRAll M ρ
  ads : AbsDS M ρ rk
  aus : AbsUS M ρ rk
  tp1 : TP1C M ρ
  tplos : TPLoS M ρ rk
  tp1w : TP1WC M ρ
  tplow : TPLoWs M ρ rk
  auwl : AbsUWL M ρ
  auw0 : AbsUW0 M ρ rk
  adw : AbsDWs M ρ rk
  trigs : TrigS0 M ρ rk
  tplon : TPLoN M ρ
  adn : AbsDN M ρ
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- `TPLoWs` at the frame of `x = r + L` with its row-1 parent `r`, the seed as a constant. -/
theorem Inv3V2.tplowAt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (I : Inv3V2 M ρ rk)
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) :
    TPLoWAt M ρ (fun _ => (drop1 M (r + L) rk).o r) := by
  have h := I.tplow.const (r := r) (by rw [show M.length - 1 = r + L by omega]; exact h1)
  rwa [show M.length - 1 = r + L by omega] at h

/-- `AbsDWs` at the frame of `x = r + L`, the seed as a constant. -/
theorem Inv3V2.adwAt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (I : Inv3V2 M ρ rk)
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) :
    AbsDWAt M ρ (fun _ => (drop1 M (r + L) rk).o r) := by
  have h := I.adw.const (r := r) (by rw [show M.length - 1 = r + L by omega]; exact h1)
  rwa [show M.length - 1 = r + L by omega] at h

/-- The `t = 1`, `q = r` expansion engine with Inv3V2 as its input.
The drop residual, the smaller matrix, the seed components, and preservation
of Inv3V2 in one expansion step remain explicit obligations. -/
theorem qr_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2 M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) (hNB : ¬ Bad2 M)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hPs : ExpStepT1 (fun N σ => ∃ rkN, Inv3V2 N σ rkN) M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (TRIO.gexp M r L d0 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  intro n hn
  obtain ⟨ρN, _, _, _, _, ⟨rkN, IN⟩, hot, hlt⟩ :=
    qr_final4S hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hq I.cons I.good I.rank I.vs I.fc I.fo R.argT I.kd I.td R.ab R.ws R.vst R.ua
      I.tp1w (I.tplowAt hlen h1) I.auwl I.auw0 (I.adwAt hlen h1) I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
      (fun N σ => ∃ rkN, Inv3V2 N σ rkN) ⟨rk, I1⟩ hPs n hn
  exact ⟨ρN, rkN, IN, hot, hlt⟩

/-- The `t = 1`, `q != r` expansion engine with Inv3V2 as its input.
Its remaining obligations are the drop, the prefix, and one-copy preservation.
The seed-local fields replace the false global AbsD and TPLo. -/
theorem qn_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2 M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hqr : par M 0 (r + L) ≠ some r)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hPs : ExpStepT1 (fun N σ => ∃ rkN, Inv3V2 N σ rkN) M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (TRIO.gexp M r L d0 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hrM : r < M.length := by omega
  obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
  rw [sf_ot (I.good.ot_v r hrM)] at hro
  have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
    I.vs R.vst I.fc I.fo R.argT
    (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
      I.kd I.td R.ab R.ws) R.ua
  have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
    ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
      h1 hx2 hqr I.cons I.good I1.cons I1.rank hdrop)
  intro n hn
  obtain ⟨ρN, _, _, _, _, ⟨rkN, IN⟩, hot, hlt⟩ :=
    t1_main_vlocS hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hqr I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus R.argT
      I.kd I.td R.ab R.ws R.vst R.ua hne rfl hro I.rootS I.rootP I1.good
      (fun N σ => ∃ rkN, Inv3V2 N σ rkN) ⟨rk, I1⟩ hPs n hn
  exact ⟨ρN, rkN, IN, hot, hlt⟩

end Ytosk
