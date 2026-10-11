/-
**3 行・t = 2: x より前の残り T2BelowXRes から、証明済みの種の ◁ を外す（`t2BelowXRes_of_L`）。**

T2BelowResL は T2BelowRes の種の欄の ◁ を、次の 2 つの場合を除く形に弱めたもの（`T2SeedDone`）。
- q = r で x への上げがない: seedL_qr（V3T2SeedQRL）、M と M.take x だけの残り T2SeedQRRes から。
- q ≠ r で q が r の最後の数える子: seedL_qn（V3T2SeedQNV）、残り T2SeedQNRes から。
- sv（q = r で x − 1 が x へ上げる）: seedL_sv（V3T2SeedSV）、残り T2SeedSVRes から。
残る種の ◁ は C（q ≠ r で q が r で数えられない）だけ。
-/
import Ytosk.V3T2SeedSV

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- `q = r` and nothing upgrades into `x`. -/
def T2QRNoUpg (M : Mat) (r L : Nat) : Prop := par M 0 (r + L) = some r ∧ ∀ i, upg M i ≠ some (r + L)

/-- `q ≠ r` and `q` is the last counted child of `r`. -/
def T2QNLast (M : Mat) (r L : Nat) : Prop :=
  ∃ q Lc, par M 0 (r + L) = some q ∧ q ≠ r ∧ CL M r = Lc ++ [q]

/-- `q = r` and `x − 1` upgrades to `x` (the sv case). -/
def T2SVCase (M : Mat) (r L : Nat) : Prop := par M 0 (r + L) = some r ∧ upg M (r + L - 1) = some (r + L)

/-- The seed cases whose ◁ is proved from residuals of `M` and `M.take x`. -/
def T2SeedDone (M : Mat) (r L : Nat) : Prop := T2QRNoUpg M r L ∨ T2QNLast M r L ∨ T2SVCase M r L

/-- **`T2BelowRes` without the ◁ of the seed in the cases `T2SeedDone`.** -/
def T2BelowResL (M : Mat) (ρ : Valn) (r L d0 d1 : Nat) : Prop :=
  ∀ n, 2 ≤ n → (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L d0 d1 m) τ → Good3 (TRIO.gexp M r L d0 d1 m) τ) →
    ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true) →
    T2VSN (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ ∧ T2HardR M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ (T2Seed M r L) ∧
    (∀ p, T2Seed M r L p → (¬ T2SeedDone M r L → Lhd z (σ.o p) (ρ.o p)) ∧ isOT (σ.o p) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ p).Pairwise (fun a b => b ≤ a)) ∧
    (∀ q, par M 0 (r + L) = some q → q ≠ r → isOT (σ.o q) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ q).Pairwise (fun a b => b ≤ a))

/-- `T2BelowResL` for every standard `M` of type `t = 2`. -/
def T2BelowXResL : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2BelowResL M ρ r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r)

/-- The seed residual of `q = r` without an upgrade into `x`, for every standard `M` of type `t = 2`. -/
def T2SeedQRAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2QRNoUpg M r L → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRRes M ρ r L Lc

/-- The seed residual of `q ≠ r` with `q` the last counted child of `r`, for every standard `M` of type `t = 2`. -/
def T2SeedQNAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      ∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNRes M ρ r L q Lc

/-- The seed residual of the sv case, for every standard `M` of type `t = 2`. -/
def T2SeedSVAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2SVCase M r L → T2SeedSVRes M ρ r L

/-- `x` is the last counted child of `r` (`q = r`, nothing upgrades into `x`). -/
theorem cl_r_split {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hq : par M 0 (r + L) = some r)
    (hXu : ∀ i, upg M i ≠ some (r + L)) (hxb : col M (r + L) ≠ bump M r) :
    ∃ Lc, CL M r = Lc ++ [r + L] := by
  have hxc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hcnt : Counted M r (r + L) := ⟨hxb, by
    have : isUpg M (r + L) = false := by
      unfold isUpg; rw [List.any_eq_false]; intro k _ hk; exact hXu k (of_decide_eq_true hk)
    rw [this]; simp⟩
  have hsplit := children_split_x hlen hxc
  refine ⟨(children M r).filter (fun d => decide (d < r + L)) |>.filter (fun c => decide (Counted M r c)), ?_⟩
  unfold CL
  rw [hsplit, List.filter_append]
  simp [hcnt]

/-- **`T2BelowXRes` from `T2BelowXResL` and the seed residuals of `q = r` and `q ≠ r`.** -/
theorem t2BelowXRes_of_L (hL : T2BelowXResL) (hQR : T2SeedQRAll) (hQN : T2SeedQNAll) (hSV : T2SeedSVAll) :
    T2BelowXRes := by
  intro M ρ rk hM hS I R hz h2 r L hlen hr n hn hGlow σ hCN hOT
  obtain ⟨h1, h2', h3, h4⟩ := hL M ρ rk hM hS I R hz h2 r L hlen hr n hn hGlow σ hCN hOT
  refine ⟨h1, h2', fun p hp => ?_, h4⟩
  obtain ⟨hl, hot, hdec⟩ := h3 p hp
  refine ⟨?_, hot, hdec⟩
  by_cases hqn : T2QNLast M r L
  · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hqn
    have hpq : par M 0 q = some r := by
      have hqcl : q ∈ CL M r := by rw [hCLM]; simp
      exact (mem_children_iff.mp (cl_mem_children hqcl)).2
    have hp' : p = r := by
      rcases hp with ⟨hq', _⟩ | ⟨q', hq', _, hpq'⟩
      · rw [hq] at hq'; cases hq'; exact absurd rfl hqr
      · rw [hq] at hq'; cases hq'; rw [hpq] at hpq'; cases hpq'; rfl
    subst p
    exact seedL_qn hM hS I R hz h2 hlen hr hq hqr hCLM (hQN M ρ rk hM hS I R hz h2 r L hlen hr q Lc hq hqr hCLM)
      n hn hGlow σ hCN (h4 q hq hqr).1 (by rw [← cvals_eq_mapC hCN]; exact hdec)
  by_cases hsv : T2SVCase M r L
  · obtain ⟨hq, hux⟩ := hsv
    have hp' : p = r := by
      rcases hp with ⟨_, rfl⟩ | ⟨q, hq', hqr, _⟩
      · rfl
      · rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    subst p
    exact seedL_sv hM hS I R hz h2 hlen hr hq hux (hSV M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hux⟩)
      n hn hGlow σ hCN (by rw [← cvals_eq_mapC hCN]; exact hdec)
  by_cases hnu : T2QRNoUpg M r L
  · obtain ⟨hq, hXu⟩ := hnu
    have hp' : p = r := by
      rcases hp with ⟨_, rfl⟩ | ⟨q, hq', hqr, _⟩
      · rfl
      · rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    subst p
    obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
    have hxb : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
    exact seedL_qr hM hS I R hz h2 hlen hr hq hXu hCLM
      (hQR M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hXu⟩ Lc hCLM) n hn hGlow σ hCN
  · exact hl (fun h => h.elim hnu (fun h' => h'.elim hqn hsv))

end Ytosk
