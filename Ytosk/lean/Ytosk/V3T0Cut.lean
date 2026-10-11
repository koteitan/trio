/-
**3 行・t = 0: T0Shape (i)（B ≠ 0）を PH3c と「右端だけ違う」(RE) に帰着。**

(i) の枠では両方の低い部分が 0 なので、M の PH3c から枠の種類は pre（y = B + R）か cut（B ∈ cutsNS s y）。
新しい引数が y = P + t（t は 1 項）と最後の加数だけ違う y′ = P + T′（T′ ≠ 0）なら:
- pre: B は P の頭の部分なので B ≤ P < y′。
- cut が P の中: 切り口は元の項以下なので B ≤ P < y′。
- cut が t の中（B = P + κ）: 残り κ < T′。
実測（T0Ext 3 万行列、(i) の枠 10812 件）: pre 1456、P の中の cut 2906、t の中の cut 6450（どれも κ < T′）。
RE（最後の加数だけが変わり T′ ≠ 0）は同じ v の D の列 34.6 万件で例外 0。
-/
import Ytosk.V3PSh
import Ytosk.V3T0NoVB

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **A cut is at most the term.** -/
theorem cutsNS_le {s : T} : ∀ {h t : T}, t ∈ cutsNS s h → t ≤ h
  | z, _, ht => by simp [cutsNS] at ht
  | psi a x c, t, ht => by
    simp only [cutsNS, List.mem_append, List.mem_map] at ht
    rcases ht with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
    · exact psi_le_psi_any (scuts_le hu)
    · rcases (le_iff _ _).mp (cutsH_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩))
      · rcases (le_iff _ _).mp (z_le c) with h | h
        · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
        · rw [h]
    · rcases (le_iff _ _).mp (cutsNS_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
      · exact le_refl _

/-- **A cut of `P + t`** is a cut of `P` or `P` followed by a cut of `t`. -/
theorem cutsNS_split {s t : T} : ∀ {P B : T}, B ∈ cutsNS s (app P t) →
    B ∈ cutsNS s P ∨ ∃ κ ∈ cutsNS s t, B = app P κ
  | z, B, h => Or.inr ⟨B, by simpa using h, by simp [app]⟩
  | psi a x c, B, h => by
    simp only [app, cutsNS, List.mem_append, List.mem_map] at h
    rcases h with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
    · left; simp only [cutsNS, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨u, hu, rfl⟩)
    · left; simp only [cutsNS, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
    · rcases cutsNS_split hu with h' | ⟨κ, hκ, rfl⟩
      · left; simp only [cutsNS, List.mem_append, List.mem_map]; exact Or.inr ⟨u, h', rfl⟩
      · right; exact ⟨κ, hκ, rfl⟩

/-- **A proper prefix before the last summand** is a prefix of the part before it. -/
theorem prefix_of_app_single {a x : T} : ∀ {B R P : T}, app B R = app P (psi a x z) → R ≠ z →
    ∃ R0, P = app B R0
  | z, R, P, _, _ => ⟨P, rfl⟩
  | psi b1 b2 b3, R, z, h, hR => by
    simp only [app, psi.injEq] at h
    exact absurd (app_eq_z h.2.2).2 hR
  | psi b1 b2 b3, R, psi p1 p2 p3, h, hR => by
    simp only [app, psi.injEq] at h
    obtain ⟨rfl, rfl, h3⟩ := h
    obtain ⟨R0, hR0⟩ := prefix_of_app_single h3 hR
    exact ⟨R0, by rw [hR0]; rfl⟩

theorem lt_app_ne {P T' : T} (h : T' ≠ z) : P < app P T' := by
  have := app_lt_app_left P (show z < T' by cases T' with
    | z => exact absurd rfl h
    | psi _ _ _ => exact T.z_lt_psi _ _ _)
  rwa [app_z_right] at this

/-- **The new argument stays above the state**: a rewriting frame of kind pre or cut (low part `0`) whose
argument changes only in its last summand. -/
theorem lt_new_of_kind {B s P a x T' : T} (hT : T' ≠ z)
    (hK : PH3cKind B (app P (psi a x z)) z s)
    (hcut : ∀ κ ∈ cutsNS s (psi a x z), B = app P κ → κ < T') : B < app P T' := by
  rcases hK with ⟨_, hlo⟩ | ⟨_, (⟨R, hR, hhi⟩ | ⟨_, hc⟩)⟩
  · exact absurd rfl hlo
  · obtain ⟨R0, rfl⟩ := prefix_of_app_single hhi.symm hR
    rw [app_assoc]
    exact lt_app_ne (fun h => hT (app_eq_z h).2)
  · rcases cutsNS_split hc with h | ⟨κ, hκ, rfl⟩
    · exact lt_of_le_of_lt (cutsNS_le h) (lt_app_ne hT)
    · exact app_lt_app_left P (hcut κ hκ rfl)

/-- **Residual RE** (`t = 0`): a `D` column before `r` whose argument drops by `◁` with the same subscript
changes only in the last summand of its argument, and the new tail is nonzero. -/
def T0RERes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ c, c < r → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
        ∃ P a x T', y = app P (psi a x z) ∧ y' = app P T' ∧ T' ≠ z

/-- **Residual: the cut in the changed summand** (the frames of (i) whose state cuts the last summand). -/
def T0CutRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      ∀ P a x T', y = app P (psi a x z) → y' = app P T' →
      ∀ κ ∈ cutsNS s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ → κ < T'

/-- **(i) from PH3c of `M`, RE and the cut residual.** -/
theorem t0ShapeR3_of (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hRE : T0RERes) (hCut : T0CutRes) : T0ShapeR3 := by
  intro M ρ rk r L hM hS I R hlen hL hp he1 n hn σ hCN i c Lc hi hc hCL hD s y y' hy hy' hl hlo' hlo hB htr
  have hK := hPH M ρ rk hM hS I R i (by omega) Lc c [] hCL s y hy hB htr
  have hhi : (split y (psi (succ s) z z)).1 = y := by
    have e := split_app (psi (succ s) z z) y
    rw [hlo, app_z_right] at e; exact e
  rw [hhi, hlo] at hK
  obtain ⟨P, a, x, T', rfl, rfl, hT⟩ := hRE M ρ rk r L hM hS I R hlen hL hp he1 n hn σ hCN c hc hD s _ _ hy hy' hl
  exact lt_new_of_kind hT hK (hCut M ρ rk r L hM hS I R hlen hL hp he1 n hn σ hCN i c Lc hi hc hCL hD s _ _
    hy hy' hl hlo' hlo hB htr P a x T' rfl rfl)

end Ytosk
