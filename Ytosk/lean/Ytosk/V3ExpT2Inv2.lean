/-
**t = 2 の展開を Inv3V2 に接続（2026-10-16、t2）。**

`hExp_t2_inv3V2`: M の Inv3V2・落とす補題の残り DropRes・M.take x の Inv3V2 から、n ≥ 2 の M[n] の
Inv3V2、値の標準性、値の下降を出す。t = 2 のエンジンは `Inv3W`（V3InvW）で動くので、偽の旧欄
（AbsD・AbsU・TPLo・AbsUW・TrigOmC）を仮定しない。

証明済みで出る欄: Cons・Good3・Rk・FrameOT・BumpKidsDec・BumpTermDec・PH3cG・FC3・rootS・rootP、
および TP1C・TP1WC（PH3cG と葉の条件から、`tp1C_of_ph3cG`）。
名前つきの残り:
- `T2BelowXRes`（x より前の Good3 の残り、旧来）
- `T2SeedFrames QFO M`・`G.T2SeedPRes M ρ`（種の列の枠、旧来）
- `T2NRes`: M[n] の VSmallF・FrameClosed・VSmallRAll、最後の列の枠の欄（`TakeFrameV2`、1 列落としと同じ束）、
  葉の条件 TP1LeafG・TP1WLeafG。
-/
import Ytosk.V3Inv2
import Ytosk.V3TakeInv2
import Ytosk.V3ExpT2M3
import Ytosk.V3PSeedAllG
import Ytosk.V3T2R3
import Ytosk.V3PIntG
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- `Inv3W` from the structural invariants and `Inv3V2`. -/
theorem Inv3W.ofV2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V2 M ρ rk) :
    Inv3W M ρ rk :=
  Inv3W.mk' S I.cons I.good I.rank I.vs I.fc I.fo I.kd I.td I.rootS I.rootP

/-- **The fields of `Inv3V2 (M[n])` not yet produced at `t = 2`** (named residuals). -/
structure T2NRes (N : Mat) (σ : Valn) (rkN : Bool → Nat → Nat) : Prop where
  vs : VSmallF N σ
  fc : FrameClosed N σ
  vra : VSmallRAll N σ
  frame : TakeFrameV2 N σ rkN
  tp1 : TP1LeafG N σ
  tp1w : TP1WLeafG N σ

/-- The valuation of `M[n]` (`n ≥ 2`, `t = 2`) with its ranking and `Good3`. -/
theorem t2_val_expand {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (n : Nat) (hn : 2 ≤ n) :
    ∃ σ rkN, Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧ Good3 (expand M n) σ := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  have hCN := cons_of_rk hRN
  exact ⟨_, rkN, hCN, hRN, good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2) n (by omega) _ hCN⟩

/-- **The `t = 2` expansion with `Inv3V2`**: from `Inv3V2` of `M` and of `M.take x`, the drop residual, and
the named residuals, every `M[n]` (`n ≥ 2`) has `Inv3V2`, a standard value, and a smaller value. -/
theorem hExp_t2_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk)
    (RW : Res3W M ρ rk)
    (I1 : Inv3V2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hFO : T2SeedFrames QFO M) (hPR : G.T2SeedPRes M ρ)
    (hN : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      PH3cG (expand M n) σ → T2NRes (expand M n) σ rkN) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ := by
  intro n hn
  have S := sInv_std hM hS
  have IW : Inv3W M ρ rk := Inv3W.ofV2 S I
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  have hCN := cons_of_rk hRN
  set σ := rhsIt (expand M n) (rkBound (expand M n) rkN) with hσ
  have hGN := good3_expand_t2 hM hS IW RW hz h2 (t2BelowXE_of hB hM hS IW RW hz h2)
    (t2CopyResAll_holds M ρ rk hM hS IW RW hz h2) n (by omega) σ hCN
  -- the prefix `M.take x`
  have hAg : ∀ τ', Cons (M.take (M.length - 1)) τ' →
      Agree (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) τ' :=
    fun τ' h => agree_of_cons I1.cons h I1.rank
  have hfo := frameOT_expand_t2 hB hM hS IW RW hz h2
    (fun τ' h => clField_congr (Q := QFO) I1.fo (hAg τ' h)) hFO n (by omega) σ hCN
  have hbd := bumpFields_expand_t2 hB hM hS IW RW hz h2
    (fun τ' h => ⟨bumpKidsDec_congr I1.kd (hAg τ' h), bumpTermDec_congr I1.td (hAg τ' h)⟩)
    (t2SeedBump_holds hM hS IW hz h2) n (by omega) σ hCN
  have hrp := rootP_expand_t2 hB hM hS IW RW hz h2 n hn σ hCN
  have hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ :=
    fun τ h => ⟨clField_congr (Q := QFO) I1.fo (hAg τ h), G.ph3c_congr I1.ph (hAg τ h),
      G.fc3_congr I1.fc3 (hAg τ h)⟩
  have hph := G.ph3c_expand_t2S hB hM hS IW RW I.ph I.fc3 hz h2 hT hFO hPR n (by omega) σ hCN
  have hfc3 := G.fc3_expand_t2S hB hM hS IW RW I.ph I.fc3 hz h2 hT hFO hPR n (by omega) σ hCN
  have NR := hN n hn σ rkN hCN hRN hGN hph
  refine ⟨σ, rkN, ⟨hCN, hGN, hRN, NR.vs, NR.fc, hfo, hbd.1, hbd.2, hph, hfc3, NR.vra,
    NR.frame.ads, NR.frame.aus, tp1C_of_ph3cG hCN hGN.toOT hph NR.tp1, NR.frame.tplos,
    tp1WC_of_ph3cG hCN hGN.toOT hph NR.tp1w, NR.frame.tplow, NR.frame.auwl, NR.frame.auw0,
    NR.frame.adw, NR.frame.trigs, NR.frame.tplon, NR.frame.adn, rootS_of_good hCN hGN, hrp⟩, ?_⟩
  -- the drop of the value
  have R2 := hR2_t2_ofW hB hM IW RW hz h2
  have hge := t2_drops_ge2 IW RW R2 hX hJ hz h2
    (fun m hm _ _ => t2_val_expand hB hM hS IW RW hz h2 m hm)
  obtain ⟨t', ⟨ρ', rk', hC', hR', hroot⟩, hot, hlt⟩ := hge n hn
  have heq : root (expand M n) σ = t' := by
    rw [← hroot]
    exact root_congr (fun i hi => (agree_of_cons hCN hC' hRN i hi).1)
  rw [heq]
  exact ⟨hot, hlt⟩

end Ytosk
