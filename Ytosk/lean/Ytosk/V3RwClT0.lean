/-
**RwClosed は t = 0 の展開で保たれる（2026-10-17、t0）。**

RwClosed（V3T0DepS: 書き換える枠で B < hi(y) なら状態 B は閉じている）は枠の性質 `QRC` で、
- (d) 子の値が添字を保って下がっても保たれる: 新しい枠が書き換えて B < hi(y′) なら、古い枠も書き換え、
  hi は単調（split_mono）なので B < hi(y′) ≤ hi(y)。B は子に依らない。
- (nr) 書き換えない枠では前提が立たない。
よって closure の `G.frameQd_N_t0` で M と M.take x の RwClosed から N = M[n] の RwClosed が出る。
-/
import Ytosk.V3T0DepS
import Ytosk.V3PT0G

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The frame property of `RwClosed`. -/
abbrev QRC (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 → Closed a (spArg a z (sumN Lv))

theorem rwClosed_iff {M : Mat} {ρ : Valn} : RwClosed M ρ ↔ ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat)
    (R : List Nat), CL M i = Lc ++ c :: R → QRC (ρ.v i) (Lc.map ρ.o) (ρ.o c) :=
  ⟨fun h i hi Lc c R hCL s y hsy ht hB => h i hi Lc c R hCL s y hsy ht hB,
   fun h i hi Lc c R hCL s y hsy ht hB => h i hi Lc c R hCL s y hsy ht hB⟩

/-- `hi` is monotone. -/
theorem hi_le_of_le {t y' y : T} (h : y' ≤ y) : (split y' t).1 ≤ (split y t).1 := by
  rcases (le_iff _ _).mp h with h | rfl
  · rcases split_mono t h with h1 | ⟨h1, -⟩
    · exact le_of_lt h1
    · rw [h1]
  · exact le_refl _

/-- (d) for `QRC`. -/
theorem qrc_drop {a : T} {Lv : List T} {s s' y y' : T} (hle : psi s' y' z ≤ psi s y z)
    (hss : y' ≠ z → s' = s) (hM : QRC a Lv (psi s y z)) : QRC a Lv (psi s' y' z) := by
  intro s1 y1 h ht hB
  obtain ⟨h1, h2, -⟩ := T.psi.inj h
  subst h1; subst h2
  have hy0 : y' ≠ z := ne_z_of_lt ht.1
  have hs := hss hy0
  subst hs
  have hyy : y' ≤ y := by
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  have ht0 : lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s' y z) = true := by
    refine ⟨lt_of_lt_of_le (show spArg a z (sumN Lv) < y' from ht.1) hyy, ?_⟩
    exact lt_of_lt_of_le (show psi a z z < psi s' y' z from ht.2)
      (by rcases (le_iff _ _).mp hyy with h | h
          · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
          · rw [h])
  exact hM s' y rfl ht0 (lt_of_lt_of_le hB (hi_le_of_le hyy))

theorem qrc_nr {a : T} {Lv : List T} {s y : T}
    (h : ¬ (lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true)) :
    QRC a Lv (psi s y z) := by
  intro s1 y1 e ht
  simp only [psi.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e
  exact absurd ht h

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **RwClosed of `N = M[n]`** (`t = 0`). -/
theorem rwClosed_N_t0 {ρ' : Valn} (hF : RwClosed M ρ) (hFT : RwClosed (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hlr : ρ'.o r ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z) :
    RwClosed (TRIO.gexp M r L 0 0 n) σ :=
  rwClosed_iff.mpr (G.frameQd_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN QRC
    (fun _ _ _ _ _ _ hle hss h => qrc_drop hle hss h) (fun _ _ _ _ h => qrc_nr h)
    (rwClosed_iff.mp hF) (rwClosed_iff.mp hFT) hσB hoffD hσmid hσlast hLast hC1 hGT hlr hO'le hy' hdl hss)

end

end Ytosk
