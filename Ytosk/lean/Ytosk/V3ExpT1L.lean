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

/-- **The TPLo residual in the `LevFree` form** (the seed condition of `TPLoRes` is on the subterms of the
subscript `s₀` of `o(c)`; at a positive hole level it follows from `LevFree μ s₀`). -/
structure TPLoResL (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop where
  deg : DegRes TPLoAt M r L d0 ρ
  lf : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    GoodIdx (Z c) → TPLoPatN s0 y0 (Z c) → holeLev y0 ≠ z → LevFree (holeLev y0) s0
  seed : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    GoodIdx (Z c) → TPLoPatN s0 y0 (Z c) → holeLev y0 ≠ z →
    (∃ μ br vr seed, HoleData M (r + L) ρ μ br vr seed ∧ Z c = seed) →
    SeedCond s0 (Z c) (etaOm (holeLev y0)) (etaOm (holeLev (Z c)))
  zero : ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    GoodIdx (Z c) → TPLoPatN s0 y0 (Z c) → holeLev y0 = z →
    SeedCond s0 (Z c) (etaOm (holeLev y0)) (etaOm (holeLev (Z c)))

/-- **`TPLoRes` from the `LevFree` form.** -/
theorem tploRes_of_L {M : Mat} {ρ : Valn} {r L d0 : Nat} (hL : TPLoResL M r L d0 ρ) : TPLoRes M r L d0 ρ := by
  refine ⟨hL.deg, ?_⟩
  intro n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat
  by_cases hμ : holeLev y0 = z
  · exact hL.zero n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, h5, h6⟩ := hH
  have hHc := hHD.hole true c hd hc
  simp only [valB, cond_true] at hHc
  rw [h0] at hHc
  have hHlev : holeLev y0 = μ := by rw [← holeLev_psi_arg (a := s0) hy0]; exact holeLev_holeT hHc
  obtain ⟨kk, _, hZe⟩ := hZk c
  cases kk with
  | zero =>
    exact hL.seed n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, h5, h6⟩ hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ
      ⟨μ, br, vr, seed, hHD, hZe⟩
  | succ k' =>
    have hLF := hL.lf n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, h5, h6⟩ hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ
    have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
    apply seedCond_of_levFree hLF
    rw [hHlev, hZe]
    exact om_le_gamS_succ hHD.cb hseedz (by simp [etaOm]) k'

/-! ## 最後の列の枠の欄を TPLo・AbsD と LevFree から（段 μ ≠ 0） -/

/-- `last v(i) = W_i` at a column with rows 1, 2 nonzero. -/
theorem last_v_bumpW {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat} (hiM : i < M.length)
    (he1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) : last (ρ.v i) = bumpW M ρ i := by
  have hv' := (hC i hiM).2
  unfold vRhs at hv'
  rw [if_neg he1, if_neg h2] at hv'
  have hY : isOT (sumN (one :: (children M i).map (bumpTerm M ρ i))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm_of (fun k hk => hG.ot_o k hk) i j
  obtain ⟨_, sW, yW, hW⟩ := single_omega hY
  have hW0 : bumpW M ρ i = psi sW yW z := hW
  rw [hW, sf_ot (isOT_add (vOpt_ot hG hiM) (by rw [← hW]; exact isOT_omega hY))] at hv'
  rw [hv', hW0]; exact last_add_single _

/-- The residual `hLF` of `tplow_of_lf`. -/
def TPLoWLF (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
      entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
      ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
      y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega → μ ≠ z → LevFree μ s

/-- The residual `h0` of `tplow_of_lf`. -/
def TPLoW0 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
      entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
      ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
      y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega → μ = z →
      ¬ psi (fsD a (gamS μ (app b (psi (succ μ) z z)) one
        (max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c)))) z z < psi (succ s) z z

/-- The residual `hLF` of `absDW_of_lf`. -/
def AbsDWLF (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
      entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
      ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      OHole (bumpW M ρ i) → cof (bumpW M ρ i) = .omega → μ ≠ z → LevFree μ (vOpt ρ (par M 1 i))

/-- The residual `h0` of `absDW_of_lf`. -/
def AbsDW0 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
      entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
      ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      OHole (bumpW M ρ i) → cof (bumpW M ρ i) = .omega → μ = z →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) (gamS μ (app b (psi (succ μ) z z)) one
          (max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i)))

/-- The value data a frame field needs (a sub-bundle of `Inv3`, available before `Inv3` of `M[n]` is
assembled). -/
structure FrameV (M : Mat) (ρ : Valn) : Prop where
  s : SInv M
  cons : Cons M ρ
  good : Good3 M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  ad : AbsD M ρ
  tplo : TPLo M ρ

theorem FrameV.ofInv3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) : FrameV M ρ :=
  ⟨⟨I.r0p, I.z2, I.sd, I.z1, I.uat, I.uab, I.r12, I.be, I.r01, I.e00⟩, I.cons, I.good, I.kd, I.td, I.ad, I.tplo⟩

/-- The frame data of the last column (`t = 1`, `q = r`): `μ = v(r)`, the hole of the `D` values is at `μ`. -/
theorem frame_hole {M : Mat} {ρ : Valn} (I : FrameV M ρ) {r : Nat} {μ b : T}
    (h1 : par M 1 (M.length - 1) = some r) (hq : par M 0 (M.length - 1) = some r)
    (hx2 : entry M 2 (M.length - 1) = 0) (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z) :
    ∀ bb i, DepX M (M.length - 1) bb i → i < M.length - 1 →
      HoleT μ (app b (psi (succ μ) z z)) μ (valB ρ bb i) := by
  intro bb i hd hi
  have hx : M.length - 1 + 1 = M.length := by omega
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  have hμ : μ = ρ.v r := by
    obtain ⟨y, hy⟩ := o_psi_sub I.cons hrM
    rw [hro] at hy
    rw [(T.psi.inj hy).1, sf_ot (I.good.ot_v r hrM)]
  have hx1 : entry M 1 (M.length - 1) ≠ 0 := by have := par1_entry_lt h1; omega
  have hox : ρ.o (M.length - 1) = psi (succ μ) z z := by
    rw [hμ]; exact o_last_t1 hx I.cons I.good h1 hx1 hx2
  exact (qr_holeD hx I.s.r0p I.s.z2 I.s.sibDec I.s.z1c I.s.uat I.s.uab hx2 h1 hq I.cons I.good I.kd I.td I.ad hro hox
    (hOS_t1 hx I.s.r0p I.s.z2 I.s.sibDec I.s.z1c I.s.uat I.s.uab hx2 hq) bb i hd hi).1

/-- **TPLoW from TPLo and `LevFree`** at a positive level; the level `0` is the residual `h0`. -/
theorem tplow_of_lf {M : Mat} {ρ : Valn} (I : FrameV M ρ)
    (hLF : TPLoWLF M ρ)
    (h0 : TPLoW0 M ρ) :
    TPLoW M ρ := by
  intro r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca
  by_cases hμ : μ = z
  · exact h0 r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ
  have hLFs := hLF r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ
  have hH := frame_hole I h1 hq hx2 hro true c hd hc
  simp only [valB, cond_true] at hH
  rw [ho] at hH
  have hyz : y ≠ z := by intro h; rw [h] at hla; simp [last] at hla
  have hlev : holeLev y = μ := by rw [← holeLev_psi_arg (a := s) hyz]; exact holeLev_holeT hH
  have hT := tpl_iff.mp (I.tplo c (by omega) s y ho hspl a hla hns hOa)
  rw [hlev] at hT
  apply tpl_iff.mpr
  obtain ⟨k, hk⟩ : ∃ k, max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c) = k + 1 :=
    ⟨max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c) - 1, by
      have := le_max_left 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c); omega⟩
  rw [hk]
  refine fsD_transfer (subClosed_subS s) (fun u hu h1' _ => ?_) hOa s (subT_subS (.refl s)) hT hT
  exact lt_of_lt_of_le (lt_Om_of_levFree hLFs hu h1') (om_le_psi μ _ z)

/-- **AbsDW from AbsD and `LevFree`** at a positive level; the level `0` is the residual `h0`. -/
theorem absDW_of_lf {M : Mat} {ρ : Valn} (I : FrameV M ρ)
    (hLF : AbsDWLF M ρ)
    (h0 : AbsDW0 M ρ) :
    AbsDW M ρ := by
  intro r μ b h1 hq hx2 hro i hi hd he1 he2 hO hcof q hqm hlt
  by_cases hμ : μ = z
  · exact h0 r μ b h1 hq hx2 hro i hi hd he1 he2 hO hcof hμ q hqm hlt
  have hLFs := hLF r μ b h1 hq hx2 hro i hi hd he1 he2 hO hcof hμ
  have hH := frame_hole I h1 hq hx2 hro false i hd hi
  simp only [valB, cond_false] at hH
  have hiM : i < M.length := by omega
  have hlev : holeLev (bumpW M ρ i) = μ := by
    rw [← last_v_bumpW I.cons I.good hiM he1 he2]; exact holeLev_holeT (holeT_last hH)
  have hA := I.ad i hiM he1 he2 hO q hqm hlt
  rw [hlev] at hA
  obtain ⟨k, hk⟩ : ∃ k, max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i) = k + 1 :=
    ⟨max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i) - 1, by
      have := le_max_left 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i); omega⟩
  rw [hk]
  refine fsD_transfer (subClosed_subS _) (fun u hu h1' _ => ?_) hO q (summand_subS hqm) hA hA
  exact lt_of_lt_of_le (lt_Om_of_levFree hLFs hu h1') (om_le_psi μ _ z)


/-! ## 組み立て: 最後の列の枠の欄を M[n] 自身の欄と LevFree から -/

/-- **The property carried along the `t = 1` chain** (`PT1A` with only TPLoN among the frame fields). -/
def PT1B (M : Mat) (r : Nat) (ρ : Valn) (N : Mat) (σ : Valn) : Prop :=
  FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ ∧ FrameClosed N σ ∧ TrigOmC N σ ∧ TP1C N σ ∧ TP1WC N σ ∧
    TPLo N σ ∧ (AgrT1 M r ρ N σ ∧ AbsD N σ) ∧ (AgrT1 M r ρ N σ ∧ AbsUW N σ) ∧
    (AgrT1 M r ρ N σ ∧ AbsDN N σ) ∧ (VrLe r ρ N σ ∧ VSmallF N σ) ∧ TPLoN N σ

theorem inv3V_of_PT1B {M N : Mat} {r : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ)
    (hR : Rk N rk) (hG : Good3 N σ) (hP : PT1B M r ρ N σ) (hF : TPLoW N σ ∧ AbsDW N σ) : Inv3V N σ rk :=
  let ⟨fo, rp, ⟨kd, td⟩, fc, trig, tp1, tp1w, tplo, ⟨_, ad⟩, ⟨_, auw⟩, ⟨_, adn⟩, ⟨_, vs⟩, tplon⟩ := hP
  ⟨hC, hG, hR, vs, fc, fo, kd, td, ad, absU_of_absD hC hG ad, tp1, tplo, tp1w, hF.1, auw, hF.2, trig, tplon, adn,
    rootS_of_good hC hG, rp⟩

theorem inv3V_N_t1B {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hQs : ExpStepT1 TPLoN M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResL : TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResD : AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResU : AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResDN : AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResV : VSFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hFr : ∀ n σ rkN, 2 ≤ n → Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN →
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpKidsDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpTermDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      AbsD (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLo (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLoW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧
      AbsDW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN,
      Inv3V (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  intro n hn
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; have := par_lt M 1 _ r hr; omega
    · exact h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hdr := R.drop
  have hsd := R.seed
  rw [show M.length - 1 = r + L by omega] at hdr hsd
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V1 := valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI hdr
  have hx0 : entry M 0 (r + L) ≠ 0 := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  have hRP1 := rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 hx0 I.cons I.rank hVI hdr
    I.rootP
  have hRT' := hRT
  simp only [RestT] at hRT'
  rw [show M.length - 1 = r + L by omega] at hRT'
  obtain ⟨ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hRT'
  have hAg := agr_base hlen hL0 hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 I.cons I.good I.rank
  have hP1 : PT1B M r ρ (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, tp1, tp1w, tplo, ⟨hAg, ad⟩, ⟨hAg, auw⟩, ⟨hAg, adn⟩,
      ⟨vrle_base I R hlen hr, V1.vs⟩, tplon⟩
  have hPs : ExpStepT1 (PT1B M r ρ) M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1' I hlen hL0 hd0e hr hx2)
            (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2)
              (expStep_and (expStep_tp1C I hlen hL0 hd0e hr hx2)
                (expStep_and (expStep_tp1WC I hlen hL0 hd0e hr hx2)
                  (expStep_and (expStep_tplo I hlen hL0 hd0e hr hx2 hResL)
                    (expStep_and (expStep_absD I hlen hL0 hd0e hr hx2 hResD)
                      (expStep_and (expStep_absUW I hlen hL0 hd0e hr hx2 hResU)
                        (expStep_and (expStep_absDN I hlen hL0 hd0e hr hx2 hResDN)
                          (expStep_and (expStep_vsmallF I hlen hL0 hd0e hr hx2 (vsfRes_of I hResV)) hQs)))))))))))
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) (PT1B M q ρ) hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1B hCN hRN hGN hPN (hFr n ρN rkN hn hRN hCN hGN hPN.2.2.1.1 hPN.2.2.1.2 hPN.2.2.2.2.2.2.2.2.1.2 hPN.2.2.2.2.2.2.2.1), hot, hlt⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g (PT1B M r ρ) hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1B hCN hRN hGN hPN (hFr n ρN rkN hn hRN hCN hGN hPN.2.2.1.1 hPN.2.2.1.2 hPN.2.2.2.2.2.2.2.2.1.2 hPN.2.2.2.2.2.2.2.1), hot, hlt⟩


/-- **The `t = 1` part of `hExp` for `trio_terminates_main_H`** (`Res3H` for `M[n]`). The seed residuals of
TPLo・AbsD・AbsUW are in the `LevFree` form; of the frame fields only TPLoN is carried (`hQs`), TPLoW・AbsDW of
`M[n]` come from its own TPLo・AbsD and `LevFree` at a positive level (`tplow_of_lf`・`absDW_of_lf`), with the
residual `hFrm` (`LevFree` and the level-0 parts, on the standard matrix `M[n]`). -/
theorem hExp_t1L
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hQs : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      ExpStepT1 TPLoN M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → TPLoWLF N σ ∧ TPLoW0 N σ ∧ AbsDWLF N σ ∧ AbsDW0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      TPLoResL M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
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
  have hexpA := fun n' => expand_eq_gexp_t1 M n' hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hexpA hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp hexpA
  have hlen : r + L + 1 = M.length := by omega
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1B I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (hQs M ρ rk hM hS I R r L hlen hr hx2)
      (tploRes_of_L (hResN M ρ rk hM hS I R r L hlen hr hx2).1)
      (absDRes_of_L I hlen hr hx2 (hResN M ρ rk hM hS I R r L hlen hr hx2).2.1)
      (absUWRes_of_L hx2 (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.1)
      (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.2.1
      (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.2.2
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h3, h4⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ h1 h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ h3 h4⟩) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V, hRes M ρ rk hM hS I R hz h1t n hn ρN rkN
    (Inv3.ofV (sInv_std (Std.exp n hM) hNS) V)⟩


end Ytosk
