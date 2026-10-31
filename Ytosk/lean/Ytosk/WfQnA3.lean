/-
**WfQnA3 (2026-11-01): the `◁` engine instantiated for the t = 1, q ≠ r frame (closure of the bad calls).**
- `seed_lhd_val`: the value lemma of a bad leaf: `V < A`, `A[ζ] ◁ A` and the window absorption
  (`q ∈ summands V`, `A[ζ] ≤ q < A` ⇒ `q ◁ A`) give `sf(V + A[ζ]) ◁ A`.
- `seed_bad_t1`: `hSeed` of the engine at a bad leaf `i` (from `WfQnH4.leaf_E3`, `v_bad_M` and the diagonal
  point `A = o(r) = ψ_μ(b_r)` with `ζ = gamS μ b_r seed m`: `fsD_seed` / `lhd_diag_seed`).
- `hOTD_of_hole`: the standard form of the glue values on `D` from the holes and `hok`.
- `engine_t1B`: `WfQnA1.deps_lhd_otUD` with `S = SB B`, `U = off D`, `bnd = x`, structural hypotheses from
  WfQnA2, `hoff`/`hOTn` from (E1) (`WfQnH8`).  Left as hypotheses: `hVSN`, `hHard`, `hAbsW` (all only in the
  closure), `hOTout` (`N` from `x` on), and the seeds.
-/
import Ytosk.WfQnA2

namespace Ytosk.WfQnA3
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad

/-- **The value lemma at a bad leaf.** -/
theorem seed_lhd_val {V A Az : T} (hV : isOT V = true) (hVlt : V < A) (hA : Single A) (hAz : Single Az)
    (hl : Lhd z Az A) (hR : ∀ q ∈ summands V, ¬ q < Az → q < A → Lhd z q A)
    (hlt : sf (add V Az) < A) : Lhd z (sf (add V Az)) A ∧ isOT (sf (add V Az)) = true := by
  have hot : isOT (add V Az) = true := isOT_add hV hAz.1
  have hE := v_strong hV hAz hA (Or.inr hl) hR
  obtain ⟨_, a, b, hAe⟩ := hA
  have hA' : add V A = A := by rw [hAe]; exact WfQnE2.add_absorb (by rw [← hAe]; exact hVlt)
  rw [hA'] at hE
  rw [sf_ot hot] at hlt ⊢
  exact ⟨lhd_of_lhdE_lt hE hlt, hot⟩

/-- **`hSeed` at a bad leaf** (t = 1, q ≠ r).  Residuals: `V < A` (`hVlt`), no nested bad call (`hnest`),
the window absorption (`hR`), and the `ζ`-data `BumpNA` at `i`. -/
theorem seed_bad_t1 {M N : Mat} {x r : Nat} {ρ ρN σ : Valn} {B : Nat → Prop} {μ br seed : T} {m i : Nat}
    (hx : x + 1 = M.length) (hxN' : x < N.length) (hC : Cons M ρ) (hCN : Cons N σ) (hS : SameAt M N i)
    (hxN : ρN.o x = fsD (ρ.o x) (gamS μ br seed m)) (hi : i < x) (h1 : entry M 1 i ≠ 0)
    (h2 : entry M 2 i ≠ 0)
    (hpd : ∀ m', par M 1 i = some m' → ¬ DepX M x false m')
    (hna : WfQnL6.BumpNA M x ρ (gamS μ br seed m) i)
    (hW : bumpW M ρ i = ρ.o r) (hro : ρ.o r = psi μ br z) (hAot : isOT (ρ.o r) = true)
    (hcb : cof br = .big μ) (hSd : SeedOK μ br μ seed)
    (hVot : isOT (vOpt ρ (par M 1 i)) = true) (hVlt : vOpt ρ (par M 1 i) < psi μ br z)
    (hB : ∀ j, B j → DepX M x false j)
    (hE1o : ∀ k, k < N.length → ¬ (k < x ∧ DepXB M B true k) →
      σ.o k = (glueZ M x ρ ρN (fun _ => gamS μ br seed m)).o k)
    (hE1v : ∀ k, k < N.length → ¬ (k < x ∧ DepXB M B false k) →
      σ.v k = (glueZ M x ρ ρN (fun _ => gamS μ br seed m)).v k)
    (hnest : ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, ¬ DepXB M B true k)
    (hR : ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < fsD (ρ.o r) (gamS μ br seed m) → q < ρ.o r →
      Lhd z q (ρ.o r)) :
    Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true := by
  have hrot : isOT (psi μ br z) = true := by rw [← hro]; exact hAot
  have hbr : br ≠ z := by intro h; rw [h] at hcb; simp [cof] at hcb
  have hμ : ¬ lt μ μ = true := lt_irrefl' μ
  have hfe : fsD (psi μ br z) (gamS μ br seed m) = psi μ (fs br (gamS μ br seed m)) z := fsD_here hbr hcb
  have hfot : isOT (fsD (psi μ br z) (gamS μ br seed m)) = true := by
    rw [hfe]; exact isOT_diag_seed hrot hcb hμ hSd m
  have hfl : Lhd z (fsD (psi μ br z) (gamS μ br seed m)) (psi μ br z) := by
    rw [hfe]; exact lhd_diag_seed hrot hcb hμ hSd m
  obtain ⟨hσ, hlt, _⟩ := WfQnH4.leaf_E3 hx hxN' hC hCN hS hxN hi h1 h2 hpd hna hW hro hAot hVot hfot hVlt
    hfl.1 hB hE1o hE1v hnest
  have hvi := WfQnH4.v_bad_M hC (by omega) h1 h2 hW hro hAot hVlt
  rw [hvi] at hlt ⊢
  rw [hσ] at hlt ⊢
  rw [hro] at hlt hR ⊢
  exact seed_lhd_val hVot hVlt ⟨hrot, μ, br, rfl⟩ ⟨hfot, by rw [hfe]; exact ⟨_, _, rfl⟩⟩ hfl hR hlt

/-- **`hOTD`** (the glue values on `D` are standard) from the holes and `hok`. -/
theorem hOTD_of_hole {M : Mat} {x : Nat} {ρ : Valn} {μ br vr ζ : T} (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hH : ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) → HoleT μ br vr (valB ρ b i))
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true) :
    ∀ b j, j < x → DepX M x b j → isOT (fsD (valB ρ b j) ζ) = true := by
  intro b j hj hd
  apply hok _ _ (hH b j hd (Or.inl hj))
  cases b
  · exact hG.ot_v j (by omega)
  · exact hG.ot_o j (by omega)

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
  {q : Nat} (hq : par M 0 (r + L) = some q)
  {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
include hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq hB

/-- **The `◁` engine on the closure of the bad calls** (t = 1, q ≠ r). -/
theorem engine_t1B {ρ ρN σ : Valn} {rk : Bool → Nat → Nat} {ζ : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRM : Rk M rk)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hE1o : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B true i) →
      σ.o i = (glueZ M (r + L) ρ ρN (fun _ => ζ)).o i)
    (hE1v : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B false i) →
      σ.v i = (glueZ M (r + L) ρ ρN (fun _ => ζ)).v i)
    (hOTD : ∀ b j, j < r + L → DepX M (r + L) b j → isOT (fsD (valB ρ b j) ζ) = true)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 0 n).length → isOT (valB σ b j) = true)
    (hSeedB : ∀ i, B i → i < r + L → Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true)
    (hVSN : ∀ i (Lc : List Nat) c, i < r + L → DepXB M B true i → CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] →
      σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hHard : ∀ i (Lc : List Nat) c s y y', i < r + L → DepXB M B true i →
      CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] → ρ.o c = psi s y z →
      σ.o c = psi s y' z → lt (ρ.v i) s = true →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
      ∀ g ∈ comps (ρ.v i) y', g ≤ H s y')
    (hAbsW : ∀ i, i < r + L → DepXB M B false i → ¬ B i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z →
        ¬ q < bumpW (TRIO.gexp M r L d0 0 n) σ i → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    ∀ b i, DepXB M B b i → i < r + L → Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true := by
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hxN : r + L < (TRIO.gexp M r L d0 0 n).length := by rw [hlN]; have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simp at this; omega
  have hoff := WfQnH8.hoff_of_E1 hB hxN hE1o hE1v
  have hσo : ∀ e, e < r + L → ¬ DepX M (r + L) true e → σ.o e = ρ.o e :=
    fun e he hn' => (hoff e he).1 hn'
  have hOTn := WfQnH8.hOTn_of_E1 hB hxN hE1o hE1v hG hlen hOTD
  have key := WfQnA1.deps_lhd_otUD (S := WfQnH8.SB B) (U := fun b i => ¬ DepX M (r + L) b i) (bnd := r + L)
    hC hG hCN hRM (by omega) (by omega) hF hFO hVS hTD hKD
    (fun i Lc c hi hD hcl hne => hVSN i Lc c hi (WfQnH8.depS_iff.mp hD) hcl hne)
    (fun i Lc c s y y' hi hD => hHard i Lc c s y y' hi (WfQnH8.depS_iff.mp hD))
    hoff hOTn hOTout
    (fun b i hs hi _ _ => by
      obtain ⟨rfl, hBi⟩ := hs
      exact hSeedB i hBi hi)
    (fun c hc hd => WfQnA2.hDvNilB hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hB c hc
      (WfQnH8.depS_iff.mp hd))
    (WfQnA2.hCLnilB hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2)
    (fun i hi _ hD hv => by
      obtain ⟨Lc, c, h1', h2', h3, h4, h5, h6, h7⟩ := WfQnA2.hOcB hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2
        hqr hq hB i hi (WfQnH8.depS_iff.mp hD) (fun h => hv (WfQnH8.depS_iff.mpr h))
      exact ⟨Lc, c, h1', h2', WfQnH8.depS_iff.mpr h3, h4, h5, h6,
        fun h => h7 (fun h' => h (WfQnH8.depS_iff.mpr h'))⟩)
    (fun i hi hs hD => by
      obtain ⟨he1, he2, hp1, hpm, hup, hupb, hbsh⟩ := WfQnA2.hVcB hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1
        hx2 hqr hq hB hσo i hi (fun h => hs ⟨rfl, h⟩) (WfQnH8.depS_iff.mp hD)
      refine ⟨he1, he2, hp1, fun m hm => ⟨fun h => (hpm m hm).1 (WfQnH8.depS_iff.mp h), (hpm m hm).2⟩, hup,
        fun k hk hdk => hupb k hk (WfQnH8.depS_iff.mp hdk), fun h2 => ?_⟩
      obtain ⟨Lb, Kb, j, k, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hbsh h2
      exact ⟨Lb, Kb, j, k, a1, a2, a3, a4, a5, a6, a7, a8,
        fun d hd => ⟨fun h => (a9 d hd).1 (WfQnH8.depS_iff.mp h), (a9 d hd).2⟩,
        fun d hd e he h => a10 d hd e he (WfQnH8.depS_iff.mp h), a11,
        fun h => a12 (fun h' => h (WfQnH8.depS_iff.mpr h'))⟩)
    (WfQnA2.hupgKB hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2)
    (fun i hi hD hs => hAbsW i hi (WfQnH8.depS_iff.mp hD) (fun h => hs ⟨rfl, h⟩))
  exact fun b i hD hi => key b i (WfQnH8.depS_iff.mpr hD) hi

end

end Ytosk.WfQnA3
