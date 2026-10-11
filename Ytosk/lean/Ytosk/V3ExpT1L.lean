/-
**3 行・t = 1: 種の条件の残り（AbsDRes・AbsUWRes）を groupA の LevFree に帰着する。**

種の条件で効く部分項は Ω_μ ≤ u < ψ_μ(Ω_{μ+1}) のものだけ（u < Ω_μ なら fsD(ζ, θ) ≥ Ω_μ で自動）。
groupA の `LevFree μ V`（V に添字 μ の ψ がない）はこの帯を空にする（`lt_Om_of_levFree`）。
鎖の 1 項目以降 ζ = ψ_μ(b[γ]) では fsD(ζ, θ) ≥ Ω_μ（`om_le_gamS_succ`）。
残りは 3 つに分かれる:
- 段 μ ≠ 0: LevFree μ v(P_1 i)（groupA が運ぶ不変条件。C′ で例外 0）。
- 段 μ ≠ 0 で添字が種そのもの（q = r・n = 2 で種の添字が μ より小さい場合だけ問題になる）: 新しい値での欄。
- 段 0: もとの種の条件か新しい値での欄（groupA の PhiX0R と同じ種類）。
-/
import Ytosk.V3ExpT1A
import Ytosk.V3PhiGapT2
import Ytosk.V3DropH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem om_le_psi (μ Y c : T) : psi μ z z ≤ psi μ Y c := by
  cases Y with
  | z =>
    cases c with
    | z => exact (le_iff _ _).mpr (Or.inr rfl)
    | psi _ _ _ => exact (le_iff _ _).mpr (Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩))))
  | psi _ _ _ => exact (le_iff _ _).mpr (Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, T.z_lt_psi _ _ _⟩))))

/-- `fsD(ψ_μ(X), θ)` keeps the head subscript `μ` when `X ≠ 0`. -/
theorem om_le_fsD_psi {μ X θ : T} (hX : X ≠ z) (hθ : θ ≠ z) : psi μ z z ≤ fsD (psi μ X z) θ := by
  unfold fsD
  rw [if_neg hX]
  split
  · obtain ⟨k, hk⟩ : ∃ k, count θ = k + 1 := ⟨count θ - 1, by have := count_pos hθ; omega⟩
    rw [hk]
    show psi μ z z ≤ app (psi μ (init X) z) (mulT (psi μ (init X) z) k)
    exact om_le_psi μ (init X) _
  · split
    · exact om_le_psi μ _ z
    · exact om_le_psi μ _ z

/-- **The chain terms after the seed keep the level**: `Ω_μ ≤ fsD(γ_{k+1}, θ)`. -/
theorem om_le_gamS_succ {μ b seed θ : T} (hcb : cof b = .big μ) (hs : seed ≠ z) (hθ : θ ≠ z) (k : Nat) :
    psi μ z z ≤ fsD (gamS μ b seed (k + 1)) θ :=
  om_le_fsD_psi (fs_ne_z_big hcb (gamS_ne_z_gen hs k)) hθ

/-- **The seed condition from `LevFree`.** -/
theorem seedCond_of_levFree {μ V ζ θ : T} (hL : LevFree μ V) (hz : psi μ z z ≤ fsD ζ θ) :
    SeedCond V ζ (etaOm μ) θ :=
  fun _ hu _ h0 => lt_of_lt_of_le (lt_Om_of_levFree hL hu h0) hz

/-- **The AbsD residual in the `LevFree` form.**
- `lf`: at a positive level, `LevFree` of `v(P_1 i)` at the hole level of `W`;
- `seed`: at a positive level, when the index is the seed itself, the field at the new value;
- `zero`: at the level `0`, the former residual. -/
structure AbsDResL (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop where
  lf : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 → holeLev (bumpW M ρ i) ≠ z →
    LevFree (holeLev (bumpW M ρ i)) (vOpt ρ (par M 1 i))
  seed : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 → holeLev (bumpW M ρ i) ≠ z →
    (∃ μ br vr seed, HoleData M (r + L) ρ μ br vr seed ∧ Z i = seed) →
    (isSucc (Z i) = false ∧
      SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) (etaOm (holeLev (Z i)))) ∨
    (OHole (fsD (bumpW M ρ i) (Z i)) → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (bumpW M ρ i) (Z i) →
      q < fsD (fsD (bumpW M ρ i) (Z i)) (etaOm (holeLev (fsD (bumpW M ρ i) (Z i)))))
  zero : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 → holeLev (bumpW M ρ i) = z →
    (isSucc (Z i) = false ∧
      SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) (etaOm (holeLev (Z i)))) ∨
    (OHole (fsD (bumpW M ρ i) (Z i)) → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (bumpW M ρ i) (Z i) →
      q < fsD (fsD (bumpW M ρ i) (Z i)) (etaOm (holeLev (fsD (bumpW M ρ i) (Z i)))))

/-- The hole of `W` at a bump column of `D` is at the chain level. -/
theorem holeLev_bumpW_D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {μ br vr seed : T} (hHD : HoleData M (r + L) ρ μ br vr seed)
    {i : Nat} (hi : i < r + L) (hv : DepX M (r + L) false i) (h2 : entry M 2 i ≠ 0) :
    holeLev (bumpW M ρ i) = μ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by have := par_lt M 1 _ r h1; omega)
  have hHv := hHD.hole false i hv hi
  simp only [valB, cond_false] at hHv
  obtain ⟨he1, _, _⟩ := dv_shape hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq hi hv
  have hiM : i < M.length := by omega
  -- `v(i) = add V W` with `W` single, so `last v(i) = W`
  have hv' := (I.cons i hiM).2
  unfold vRhs at hv'
  rw [if_neg he1, if_neg h2] at hv'
  have hY : isOT (sumN (one :: (children M i).map (bumpTerm M ρ i))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm_of (fun k hk => I.good.ot_o k hk) i j
  obtain ⟨_, sW, yW, hW⟩ := single_omega hY
  have hW0 : bumpW M ρ i = psi sW yW z := hW
  rw [hW, sf_ot (isOT_add (vOpt_ot I.good hiM) (by rw [← hW]; exact isOT_omega hY))] at hv'
  have hl : last (ρ.v i) = bumpW M ρ i := by rw [hv', hW0]; exact last_add_single _
  rw [← hl]
  exact holeLev_holeT (holeT_last hHv)

/-- **`AbsDRes` from the `LevFree` form.** -/
theorem absDRes_of_L {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hL : AbsDResL M r L d0 ρ) : AbsDRes M r L d0 ρ := by
  intro n hn ρP Z hH hCN i hi hv h2
  by_cases hμ : holeLev (bumpW M ρ i) = z
  · exact hL.zero n hn ρP Z hH hCN i hi hv h2 hμ
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, _, _, _, _⟩ := hH
  have hHlev := holeLev_bumpW_D I hlen h1 hx2 hHD hi hv h2
  obtain ⟨k, _, hZe⟩ := hZk i
  cases k with
  | zero =>
    exact hL.seed n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, by assumption, by assumption, by assumption,
      by assumption⟩ hCN i hi hv h2 hμ ⟨μ, br, vr, seed, hHD, hZe⟩
  | succ k' =>
    left
    have hLF := hL.lf n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, by assumption, by assumption, by assumption,
      by assumption⟩ hCN i hi hv h2 hμ
    have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
    have hμz : μ ≠ z := by rw [← hHlev]; exact hμ
    refine ⟨by rw [hZe]; exact isSucc_psi_z (Or.inl hμz), ?_⟩
    apply seedCond_of_levFree hLF
    rw [hHlev, hZe]
    exact om_le_gamS_succ hHD.cb hseedz (by simp [etaOm]) k'

/-- **The AbsUW residual in the `LevFree` form** (as `AbsDResL`, at an upgrade `i → k` with `k` in `D`). -/
structure AbsUWResL (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop where
  lf : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i k, i < r + L → upg M i = some k → DepX M (r + L) false k → holeLev (last (ρ.v k)) ≠ z →
    LevFree (holeLev (last (ρ.v k))) (vOpt ρ (par M 1 i))
  seed : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i k, i < r + L → upg M i = some k → DepX M (r + L) false k → holeLev (last (ρ.v k)) ≠ z →
    (∃ μ br vr seed, HoleData M (r + L) ρ μ br vr seed ∧ Z k = seed) →
    (isSucc (Z k) = false ∧ SeedCond (vOpt ρ (par M 1 i)) (Z k) (etaOm (holeLev (last (ρ.v k)))) one) ∨
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (last (ρ.v k)) (Z k) →
        q < fsD (fsD (last (ρ.v k)) (Z k)) one
  zero : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i k, i < r + L → upg M i = some k → DepX M (r + L) false k → holeLev (last (ρ.v k)) = z →
    (isSucc (Z k) = false ∧ SeedCond (vOpt ρ (par M 1 i)) (Z k) (etaOm (holeLev (last (ρ.v k)))) one) ∨
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (last (ρ.v k)) (Z k) →
        q < fsD (fsD (last (ρ.v k)) (Z k)) one

/-- **`AbsUWRes` from the `LevFree` form.** -/
theorem absUWRes_of_L {M : Mat} {ρ : Valn} {r L d0 : Nat} (hx2 : entry M 2 (r + L) = 0)
    (hL : AbsUWResL M r L d0 ρ) : AbsUWRes M r L d0 ρ := by
  intro n hn ρP Z hH hCN i k hi hu hkv
  by_cases hμ : holeLev (last (ρ.v k)) = z
  · exact hL.zero n hn ρP Z hH hCN i k hi hu hkv hμ
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, h5, h6⟩ := hH
  have hkx : k < r + L := by
    have hk1 := upg_le hu
    have hk2 := upg_target_e2 hu
    rcases Nat.lt_or_ge k (r + L) with h | h
    · exact h
    · exfalso
      have : k = r + L := by omega
      rw [this, hx2] at hk2; omega
  have hHv := hHD.hole false k hkv hkx
  simp only [valB, cond_false] at hHv
  have hHlev : holeLev (last (ρ.v k)) = μ := holeLev_holeT (holeT_last hHv)
  obtain ⟨kk, _, hZe⟩ := hZk k
  cases kk with
  | zero =>
    exact hL.seed n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, h5, h6⟩ hCN i k hi hu hkv hμ
      ⟨μ, br, vr, seed, hHD, hZe⟩
  | succ k' =>
    left
    have hLF := hL.lf n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, h5, h6⟩ hCN i k hi hu hkv hμ
    have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
    have hμz : μ ≠ z := by rw [← hHlev]; exact hμ
    refine ⟨by rw [hZe]; exact isSucc_psi_z (Or.inl hμz), ?_⟩
    apply seedCond_of_levFree hLF
    rw [hHlev, hZe]
    exact om_le_gamS_succ hHD.cb hseedz (by simp [one]) k'

/-- **The `t = 1` part of `hExp` for `trio_terminates_main_H`** (`Res3H` for `M[n]`), with the seed residuals of
AbsD・AbsUW in the `LevFree` form. -/
theorem hExp_t1L
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hQs : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      ExpStepT1 QV2 M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      AbsDResL M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsUWResL M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ VSFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hRes : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → ∀ n, 2 ≤ n →
      ∀ σ rkN, Inv3 (expand M n) σ rkN → Res3H (expand M n) σ rkN) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3H (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn hNS _
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  rw [h1t] at hr
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1A I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (hQs M ρ rk hM hS I R r L hlen hr hx2)
      (hResN M ρ rk hM hS I R r L hlen hr hx2).1
      (absDRes_of_L I hlen hr hx2 (hResN M ρ rk hM hS I R r L hlen hr hx2).2.1)
      (absUWRes_of_L hx2 (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.1)
      (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.2.1
      (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.2.2 n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V, hRes M ρ rk hM hS I R hz h1t n hn ρN rkN
    (Inv3.ofV (sInv_std (Std.exp n hM) hNS) V)⟩


end Ytosk
