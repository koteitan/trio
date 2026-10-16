/-
**RwClosed は t = 1 の展開の各段で保たれる（2026-10-17、t0）。**

closure の `G.expStep_ph3c_t1S`（V3PT1G）と同じ組み立てで、書き換える枠の性質を
`RC′`（B < hi(y) なら B は閉じている）にしたもの。
- (d) 引数が下がる: hi は単調（split_mono）なので B < hi(y′) ≤ hi(y)。
- x の枠（新しい引数が b + δ、b = 状態、0 < δ < Ω_{s+1}）: hi = b = B なので前提が立たない。
-/
import Ytosk.V3RwClT0
import Ytosk.V3PT1G

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The rewriting-frame property of `RwClosed`. -/
abbrev RC' (a : T) (Lv : List T) (s y : T) : Prop :=
  spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 → ClosedA a (spArg a z (sumN Lv))

theorem rwClosed_iffQR {M : Mat} {ρ : Valn} : RwClosed M ρ ↔ ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat)
    (R : List Nat), CL M i = Lc ++ c :: R → G.QR RC' (ρ.v i) (Lc.map ρ.o) (ρ.o c) :=
  ⟨fun h i hi Lc c R hCL s y hsy ht hB => h i hi Lc c R hCL s y hsy ht hB,
   fun h i hi Lc c R hCL s y hsy ht hB => h i hi Lc c R hCL s y hsy ht hB⟩

theorem rc'_drop {a : T} {Lv : List T} {s y y' : T} (hyy : y' ≤ y)
    (_ht : lt (spArg a z (sumN Lv)) y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (h : RC' a Lv s y) : RC' a Lv s y' :=
  fun hB => h (lt_of_lt_of_le hB (hi_le_of_le hyy))

theorem rc'_app {a : T} {Lv : List T} {s b δ : T} (hb : spArg a z (sumN Lv) = b)
    (hge : AllGeT (psi (succ s) z z) b) (_hδz : δ ≠ z) (hδ : δ < psi (succ s) z z) : RC' a Lv s (app b δ) := by
  intro hB
  have hsplit : split (app b δ) (psi (succ s) z z) = (b, δ) :=
    split_app_of hge (Or.inr (lt_of_le_of_lt (head_le_self δ) hδ))
  rw [hsplit, hb] at hB
  exact absurd hB (lt_irrefl' _)

/-- **RwClosed is carried** (`t = 1`). -/
theorem expStep_rwClosed_t1S {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ)
    (hG : Good3 M ρ) (hRM : Rk M rk) (hP : RwClosed M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 (fun N σ => RwClosed N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hPP _ hGN _ _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  exact rwClosed_iffQR.mpr (G.frameQR_N_t1 hlen hL hA hd0e hn RC' (fun _ _ _ _ _ hyy ht h => rc'_drop hyy ht h)
    hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS hC (rwClosed_iffQR.mp hP)
    (G.frameQROmN_t1S RC' (fun _ _ _ _ _ hb hge hδz hδ => rc'_app hb hge hδz hδ) S hC hG hRM hlen hL hd0e h1 hx2 hn hGN
      hlex hH)
    (rwClosed_iffQR.mp hPP) (fun c hc hd => (hle c hc hd).1) hlex.1 hox)

end Ytosk
