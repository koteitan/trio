/-
**WfSdP3: the carried-property interface shared by both `t = 1` chains (2026-11-01).**

`ExpStepT1W` (WfSdH1) gives a producer `HoleDataW`: `SeedOK v(r)` and the descent `HokQ` of `fsD`. The live producer
`vsf_frameS` (V3ExpT1V, under `expStep_vsmallF2S`) reads the old `hS` through `hole_dom`, which needs the
domination `fsD(t, γ_k) ◁ t` at the diagonal points, not only the descent; `HokQ` does not give it. So the
interface is strengthened:
- `OkD μ br vr seed`: at a diagonal point `a′ ≤ vr` of `t`, `fsD(t, γ_k)` is standard and `◁ t`, at index `0`
  under `SeedOK a′` at the seed.
- `ExpStepT1D`: `ExpStepT1` over `HoleDataW ∧ OkD`, with the index-0 condition of each column in the form
  "the seed is good at every diagonal point of the `D` values" (`q = r`: the only point is `v(r)`, `SeedOK v(r)`;
  `q ≠ r`: the old `hS`).
- `expStepT1_of_D`: a producer over `ExpStepT1D` is a producer over the old `ExpStepT1` (so the `q ≠ r` chain
  `t1_chain` uses the same producers; it has no index-0 witness but has the old `hS` at every point).
- `okD_of_S` (old `hS`), `okD_of_S1` (`SeedOK` at `γ_1` everywhere: the weak branch of `SeedC2`), `okD_of_seedC2W`,
  `hokQ_of_okD`, `hole_domD` (`hole_dom` over `OkD`).
-/
import Ytosk.WfSdP1
import Ytosk.V3ExpT1V

namespace Ytosk

open T

/-- **The domination of `fsD` at the diagonal points**, at index `0` under `SeedOK` at the seed. -/
def OkD (μ br vr seed : T) : Prop :=
  ∀ a' t k, ¬ lt vr a' = true → DiagAt a' br μ t → isOT t = true → (k = 0 → SeedOK a' br μ seed) →
    isOT (fsD t (gamS μ br seed k)) = true ∧ Lhd z (fsD t (gamS μ br seed k)) t

/-- `OkD` from the old seed condition at every diagonal point. -/
theorem okD_of_S {μ br vr seed : T}
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed) : OkD μ br vr seed :=
  fun a' _ k ha hD hot _ => fsD_seed (hS a' ha (DiagAt.ot_node hD hot)) hD hot k

/-- `OkD` from `SeedOK` at `γ_1` at every diagonal point (index `0` from the premise). -/
theorem okD_of_S1 {μ br vr seed : T}
    (hS1 : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ (gamS μ br seed 1)) :
    OkD μ br vr seed := by
  intro a' t k ha hD hot h0
  cases k with
  | zero => exact fsD_seed (h0 rfl) hD hot 0
  | succ m =>
    rw [gamS_shift]
    exact fsD_seed (hS1 a' ha (DiagAt.ot_node hD hot)) hD hot m

/-- **`OkD` from `SeedC2`** at the `q = r` frame `b_r = b + Ω_{μ+1}` (the strong branch as the old `hS`). -/
theorem okD_of_seedC2W {μ b seed : T}
    (hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hS : Lhd z seed (psi μ (app b (psi (succ μ) z z)) z) →
      ∀ a', ¬ lt μ a' = true → isOT (psi a' (app b (psi (succ μ) z z)) z) = true →
        SeedOK a' (app b (psi (succ μ) z z)) μ seed)
    (h : SeedC2 μ b seed) : OkD μ (app b (psi (succ μ) z z)) μ seed := by
  rcases h with hl | ⟨_, _, _, hSr, hl⟩
  · exact okD_of_S (hS hl)
  · have hμ : ¬ lt μ μ = true := lt_irrefl' μ
    have hs1 := gamS_ot hrot cof_br hμ hSr 1
    have hsot : isOT (psi μ (app b seed) z) = true := by
      have e : gamS μ (app b (psi (succ μ) z z)) seed 1 = psi μ (app b seed) z := by
        show psi μ (fs _ seed) z = _; rw [fs_br]
      rw [← e]; exact hs1
    exact okD_of_S1 (fun a' ha hot' => seedOK1_of_lhd hot' ha hsot hl)

/-- **The descent from `OkD`** for a hole term whose diagonal points are good at index `0`. -/
theorem hokQ_of_okD {μ br vr seed t : T} (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ)
    (hμ : ¬ lt μ vr = true) (hSr : SeedOK vr br μ seed) (hok : OkD μ br vr seed)
    (hot : isOT t = true) (hH : HoleT μ br vr t) (k : Nat)
    (h0 : k = 0 → ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → DiagAt a' br μ t →
      SeedOK a' br μ seed) :
    isOT (fsD t (gamS μ br seed k)) = true ∧ fsD t (gamS μ br seed k) < t := by
  rcases hH with hc | ⟨a', ha', hD⟩
  · rw [fsD_eq_fs hc]
    exact fs_ot_lt hot ⟨gamS_ot hrot hcb hμ hSr k, by rw [hc]; exact gamS_lt_om hrot hcb hμ hSr k⟩
  · obtain ⟨h1, h2⟩ := hok a' t k ha' hD hot (fun hk => h0 hk a' ha' (DiagAt.ot_node hD hot) hD)
    exact ⟨h1, h2.1⟩

/-- **`hole_dom` over `OkD`.** -/
theorem hole_domD {μ br vr seed W : T} (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ)
    (hμ : ¬ lt μ vr = true) (hSr : SeedOK vr br μ seed) (hok : OkD μ br vr seed)
    (hot : isOT W = true) (hH : HoleT μ br vr W) (m : Nat)
    (h0 : m = 0 → ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → DiagAt a' br μ W →
      SeedOK a' br μ seed) (u : T) :
    ∀ g ∈ comps u (fsD W (gamS μ br seed m)), ∃ y, (y ∈ comps u W ∨ y = z ∨
      (cof W = .big μ ∧ y ∈ comps u (gamS μ br seed m))) ∧ g ≤ y := by
  rcases hH with hc | ⟨a', ha', hD⟩
  · rw [fsD_eq_fs hc]
    have hV : ValidLt W (gamS μ br seed m) := by
      unfold ValidLt; rw [hc]; exact gamS_lt_om hrot hcb hμ hSr m
    have hl := lhd_fs hot hV
    intro g hg
    obtain ⟨y, hy, hgy⟩ := hl.2 u W hl.1 (le_refl _) g hg
    refine ⟨y, ?_, hgy⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact Or.inl hy
    · simp only [Gc, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hc, hy⟩)
  · have hnode := DiagAt.ot_node hD hot
    obtain ⟨_, hl⟩ := hok a' W m ha' hD hot (fun hk => h0 hk a' ha' hnode hD)
    intro g hg
    obtain ⟨y, hy, hgy⟩ := hl.2 u W hl.1 (le_refl _) g hg
    refine ⟨y, ?_, hgy⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact Or.inl hy
    · simp [Gc, comps] at hy; exact Or.inr (Or.inl hy)

/-- **`ExpStepT1At` over `HoleDataW ∧ OkD`**, with the index-0 condition at the diagonal points of the `D` values. -/
def ExpStepT1AtD (Pn : Mat → Valn → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) (n : Nat) : Prop :=
  ∀ (ρP : Valn) (Z : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    (∀ i, i < r + L → DepX M (r + L) true i → isOT (fsD (ρ.o i) (Z i)) = true) →
    (∀ i, i < r + L → DepX M (r + L) false i → isOT (fsD (ρ.v i) (Z i)) = true) →
    (∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c ∧ fsD (ρ.o c) (Z c) ≠ z) →
    (ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z) →
    (∃ μ br vr seed k0, HoleDataW M (r + L) ρ μ br vr seed ∧ OkD μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k ∧
        (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → ∀ a', ¬ lt vr a' = true →
          isOT (psi a' br z) = true → DiagAt a' br μ (valB ρ bb i) → SeedOK a' br μ seed)) ∧
      ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧ μ = vr ∧ ρ.o r = psi vr br z) →
    Pn (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z)

/-- `ExpStepT1AtD` at every `n ≥ 2`. -/
def ExpStepT1D (Pn : Mat → Valn → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ExpStepT1AtD Pn M r L d0 ρ n

/-- **A producer over `ExpStepT1D` is a producer over the old `ExpStepT1`** (the `q ≠ r` chain): the old hole data
gives `HoleDataW`, `OkD` and the index-0 condition from `hS`. -/
theorem expStepT1_of_D {Pn : Mat → Valn → Prop} {M : Mat} {r L d0 : Nat} {ρ : Valn}
    (h : ExpStepT1D Pn M r L d0 ρ) : ExpStepT1 Pn M r L d0 ρ := by
  intro n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex hH
  obtain ⟨μ, br, vr, seed, k0, hHD, hZ, hPr, hk0, hμv, hro⟩ := hH
  refine h n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex
    ⟨μ, br, vr, seed, k0, hHD.toW, okD_of_S hHD.S, fun i => ?_, hPr, hk0, hμv, hro⟩
  obtain ⟨k, hk, hZe⟩ := hZ i
  exact ⟨k, hk, hZe, fun _ _ _ _ a' ha hot _ => hHD.S a' ha hot⟩

/-- `expStep_and` over `ExpStepT1D`. -/
theorem expStepD_and {P Q : Mat → Valn → Prop} {M : Mat} {r L d0 : Nat} {ρ : Valn}
    (hP : ExpStepT1D P M r L d0 ρ) (hQ : ExpStepT1D Q M r L d0 ρ) :
    ExpStepT1D (fun N σ => P N σ ∧ Q N σ) M r L d0 ρ :=
  fun n hn ρP Z hCP hGP hPQ hCN hGN ho hv hle hlex hH =>
    ⟨hP n hn ρP Z hCP hGP hPQ.1 hCN hGN ho hv hle hlex hH, hQ n hn ρP Z hCP hGP hPQ.2 hCN hGN ho hv hle hlex hH⟩

end Ytosk
