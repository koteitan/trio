/-
**Inv3V の作り直しの下書き `Inv3V2`（2026-10-12、t1-exp）。**

偽だった欄を、使う所（消費者）が本当に要る形に替える。共有の定義は変えない（この版はまだどこからも使われない）。

- `AbsUW`（T2Ext で偽）→ `AbsUWL`（最後の列の枠、鎖の下限 gamS μ b_r 1 (max 1 d_i)）＋ `AbsUW0`（添字 0 = 種）。
- `AbsD`（ext1 で偽、t = 1・q ≠ r の DepX の枠）→ `AbsDS`（q ≠ r の最後の列の枠、種 o_{M.take x}(r) での吸収）。
- `TPLo`（ext1 で偽、同じ枠）→ `TPLoS`（q ≠ r の最後の列の枠、種での TPL の比較）。
- `AbsU`（偽ではないが生産者 absU_of_absD・absU_of_phiX の元が偽）→ `AbsUS`（q ≠ r の最後の列の枠、種での吸収）。
  本当に使うのは vlocal_t1 の上げの枠だけ。
- `TrigOmC`（T2Ext で 2 行列偽、t = 1・q = r の DepX）→ `TrigS`（qr_final3 の hYBs の形: 種 < ψ_μ(1) のとき状態 < b + 種）。
- 新しい欄: `PH3cG`・`FC3`（closure、今は最上位の大域の仮定 hPH）、`VSmallRA`（t2・t0-exp、今は大域の仮定）。
- そのまま: Cons・Good3・Rk・VSmallF・FrameClosed・FrameOT・BumpKidsDec・BumpTermDec・TP1C・TP1WC・
  TPLoW・AbsDW・TPLoN・AbsDN・rootS・rootP。

種 o_{M.take x}(r) は drop1 M x rk の値（AbsUW0 と同じ）。

欄ごとの生産者と消費者の表は desc.md「Inv3V2 の下書き」の節。
-/
import Ytosk.V3IndV
import Ytosk.V3QRFinal4
import Ytosk.V3PDef
import Ytosk.V3DepRWU

namespace Ytosk

open T

/-- **AbsD at the seed** (t1-exp の absds.py): in the frame of the last column `x` (`t = 1`, `q ≠ r`,
`o(r) = ψ_μ(b)`), at a bump call `i` of `D` whose bump term `W` has a hole at the level `μ`, the summands of
`v(P_1 i)` absorbed by `W` stay absorbed by `fsD(W, o_{M.take x}(r))`. Every chain index `ζ` is at least the
seed, so this gives the hypothesis `hADζ` of `vlocal_t1` by `fsD_mono_eta`. -/
def AbsDS (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) ≠ some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ b z →
    ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    OHole (bumpW M ρ i) → holeLev (bumpW M ρ i) = μ →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
      q < fsD (bumpW M ρ i) ((drop1 M (M.length - 1) rk).o r)

/-- `AbsDS` gives `hADζ` of `vlocal_t1` at every index `ζ` above the seed. -/
theorem hADζ_of_absDS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : AbsDS M ρ rk) {r : Nat} {μ b ζ : T}
    (h1 : par M 1 (M.length - 1) = some r) (h0 : par M 0 (M.length - 1) ≠ some r)
    (h2 : entry M 2 (M.length - 1) = 0) (hro : ρ.o r = psi μ b z)
    (hζ : (drop1 M (M.length - 1) rk).o r ≤ ζ) :
    ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      OHole (bumpW M ρ i) → holeLev (bumpW M ρ i) = μ → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
        q < bumpW M ρ i → q < fsD (bumpW M ρ i) ζ :=
  fun i hi hv he1 he2 hO hl q hq hlt =>
    lt_of_lt_of_le (h r μ b h1 h0 h2 hro i hi hv he1 he2 hO hl q hq hlt) (fsD_mono_eta hO hζ)

/-- **TPLo at the seed** (t1-exp の tplos.py): in the frame of the last column `x` (`t = 1`, `q ≠ r`,
`o(r) = ψ_μ(b)`), at an `o` call `c` of `D` with `o(c) = ψ_s(y)`, `y` without a part below `Ω_{s+1}`, ending with
`Ω_a` (`a` a limit with a hole) and the hole at the level `μ`, the comparison holds at the seed
`o_{M.take x}(r)`. `TPLo` (at `ψ_μ(Ω_{μ+1})`) is false here on ext1 (1 matrix). -/
def TPLoS (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) ≠ some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ b z →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c →
    ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → holeLev y = μ →
    ¬ psi (fsD a ((drop1 M (M.length - 1) rk).o r)) z z < psi (succ s) z z

/-- **AbsU at the seed** (t1-exp の absus.py): in the frame of the last column `x` (`t = 1`, `q ≠ r`,
`o(r) = ψ_μ(b)`), at a `v` call `i` of `D` upgrading to `k` with a hole of `last v(k)` at the level `μ`, the
summands of `v(P_1 i)` below `last v(k)` stay below `fsD(last v(k), o_{M.take x}(r))`. The only real use of
`AbsU` is this frame in `vlocal_t1`, at `ζ ≥` the seed. -/
def AbsUS (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) ≠ some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ b z →
    ∀ i k, i < M.length - 1 → DepX M (M.length - 1) false i → upg M i = some k →
    OHole (last (ρ.v k)) → holeLev (last (ρ.v k)) = μ →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) →
      q < fsD (last (ρ.v k)) ((drop1 M (M.length - 1) rk).o r)

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

/-- **The redesigned value part** (draft). -/
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
  vra : VSmallRA M ρ
  ads : AbsDS M ρ rk
  aus : AbsUS M ρ rk
  tp1 : TP1C M ρ
  tplos : TPLoS M ρ rk
  tp1w : TP1WC M ρ
  tplow : TPLoW M ρ
  auwl : AbsUWL M ρ
  auw0 : AbsUW0 M ρ rk
  adw : AbsDW M ρ
  trigs : TrigS M ρ rk
  tplon : TPLoN M ρ
  adn : AbsDN M ρ
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

end Ytosk
