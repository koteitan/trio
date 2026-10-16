/-
**t = 1・q != r の始点での値の条件と、実際の添字で使うための補題。**
Inv3V2 と展開側で同じ定義を共用する。
-/
import Ytosk.V3FrameT1

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

/-- The upgrade absorption needed by `vlocal_t1`, at any index above the seed.
Unlike `AbsU`, this only asks about dependent calls in the last-column frame. -/
theorem hAUζ_of_absUS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (h : AbsUS M ρ rk) {r : Nat} {μ b ζ : T}
    (h1 : par M 1 (M.length - 1) = some r)
    (h0 : par M 0 (M.length - 1) ≠ some r)
    (h2 : entry M 2 (M.length - 1) = 0) (hro : ρ.o r = psi μ b z)
    (hζ : (drop1 M (M.length - 1) rk).o r ≤ ζ) :
    ∀ i k, i < M.length - 1 → DepX M (M.length - 1) false i → upg M i = some k →
      OHole (last (ρ.v k)) → holeLev (last (ρ.v k)) = μ →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) →
        q < fsD (last (ρ.v k)) ζ :=
  fun i k hi hd hu hO hl q hq hlt =>
    lt_of_lt_of_le (h r μ b h1 h0 h2 hro i k hi hd hu hO hl q hq hlt)
      (fsD_mono_eta hO hζ)

/-- The low-part comparison needed by the dependent `o` calls, at any index
above the seed. A smaller replacement index gives the stronger comparison. -/
theorem hTPLζ_of_tplos {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (h : TPLoS M ρ rk) {r : Nat} {μ b ζ : T}
    (h1 : par M 1 (M.length - 1) = some r)
    (h0 : par M 0 (M.length - 1) ≠ some r)
    (h2 : entry M 2 (M.length - 1) = 0) (hro : ρ.o r = psi μ b z)
    (hζ : (drop1 M (M.length - 1) rk).o r ≤ ζ) :
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c →
      ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a → holeLev y = μ →
        ¬ psi (fsD a ζ) z z < psi (succ s) z z := by
  intro c hc hd s y hcy hy a hya hns hO hl hlt
  exact h r μ b h1 h0 h2 hro c hc hd s y hcy hy a hya hns hO hl
    (lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hO hζ)) hlt)

/-- `lo_keep_of_TPL` with the comparison at any index `η ≤ ζ` (for `TPLoS`: `η` = the seed). -/
theorem lo_keep_of_TPLη {μ br vr s y η ζ : T} (hTPLf : (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a →
      ¬ psi (fsD a η) z z < psi (succ s) z z)
    (hy : y ≠ z) (hH : HoleT μ br vr (psi s y z)) (hcb : cof br = .big μ)
    (hbrl : last br ≠ psi (succ μ) z z) (hζΩ : η ≤ ζ)
    (hl : (split y (psi (succ s) z z)).2 = z) :
    (split (fsD y ζ) (psi (succ s) z z)).2 = z := by
  have hHy := holeT_arg hy hH hcb
  apply lo_z_keep hy hl
  have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
    intro q hq
    have e := split_app (psi (succ s) z z) y
    rw [hl, app_z_right] at e
    rw [← e] at hq
    exact split_fst_ge _ y q hq
  have hHl := holeT_last hHy
  have hlh := hyall _ (last_mem hy)
  obtain ⟨a, b, hlc⟩ := last_psi_form hy
  rw [hlc] at hlh hHl ⊢
  by_cases hb : b = z
  · subst hb
    by_cases ha : isSucc a = true
    · -- the last summand is `Ω_{μ+1}`
      exfalso
      have haz : a ≠ z := by
        intro h; subst h
        have h1 : isSucc (z : T) = false := rfl
        rw [h1] at ha; cases ha
      have hcf : cof (psi a z z) = .big (init a) := by
        unfold cof; rw [if_pos rfl, if_neg haz, if_pos ha]
      have hia : init a = μ := by
        rcases hHl with h | ⟨_, _, hD⟩
        · rw [hcf] at h; cases h; rfl
        · rw [hD.not_omega_succ] at ha; cases ha
      have hsa : succ μ = a := by rw [← hia]; unfold succ; exact init_app_one ha
      rcases hH with hcof | ⟨a', _, hD⟩
      · have hμs := (cof_psi_inv hy hcof).2
        apply hlh
        rw [← hsa, psi_lt_psi_z_iff]
        left
        exact lt_of_le_of_lt (le_refl _) (show succ μ < succ s from by
          rw [lt_succ_iff]; exact succ_le_of_lt (show μ < s from hμs))
      · cases hD with
        | here _ _ _ => exact hbrl (by rw [hlc, ← hsa])
        | arg _ _ hDy =>
          have := hDy.last'
          rw [hlc] at this
          rw [this.not_omega_succ] at ha; cases ha
        | sub _ _ _ => exact hy rfl
    · have haz : a ≠ z := by
        intro h; subst h
        have := holeT_not_succ hHl
        have h1 : isSucc (psi z z z) = true := rfl
        rw [h1] at this; cases this
      have hns : isSucc a = false := by simpa using ha
      have hOa : OHole a := by
        have h := ohole_of_holeT hHl
        unfold OHole at h
        rw [if_pos rfl] at h
        rcases h.2 with h' | h'
        · rw [hns] at h'; cases h'
        · exact h'
      rw [fsD_sub haz hns]
      intro q hq
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
      subst hq
      intro hlt
      apply hTPLf hl a hlc hns hOa
      exact lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hOa hζΩ)) hlt
  · intro q hq
    obtain ⟨b', rfl⟩ := summands_fsD_psi hb q hq
    intro hlt
    apply hlh
    rw [psi_lt_psi_z_iff] at hlt ⊢
    rcases hlt with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact absurd h' (T.not_lt_z _)

/-- `hLo_of_TPL` with the last-column seed condition instead of global `TPLo`.
The child cannot be the last column: its argument would be zero and could
not trigger. Thus the local condition `TPLoS` covers every frame used here. -/
theorem hLo_of_TPLS {M : Mat} {x r : Nat} {ρ : Valn} {rk : Bool → Nat → Nat}
    {μ br vr seed ζ0 : T} (hx : x + 1 = M.length)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrx : r < x) (hAr : Anc0 M r x)
    (h1 : par M 1 x = some r) (h0 : par M 0 x ≠ some r) (h2 : entry M 2 x = 0)
    (hro : ρ.o r = psi vr br z) (hcb : cof br = .big μ) (hμr : μ = vr)
    (hbr : br ≠ z) (hox : ρ.o x = psi (succ μ) z z)
    (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
    (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ0 μ i)
    (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
    (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
      DepX M x true k → k ≤ r)
    (hTPL : TPLoS M ρ rk) (hbrl : last br ≠ psi (succ μ) z z)
    (hζseed : ∀ m, (drop1 M x rk).o r ≤ gamS μ br seed m)
    (hζz : ∀ m, gamS μ br seed m ≠ z) :
    ∀ m i L' c R, i < x → DepX M x true i → children M i = L' ++ c :: R →
      DepX M x true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2 (gamS μ br seed m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br seed m)) (psi (succ s) z z)).2 = z) := by
  have hH := t1_hole hC hG hx hrx hAr hro hcb hμr hbr
    (Or.inl (by rw [hox]; exact cof_omega_succ μ)) hF1 hOS hV hS2 hS3
  have hlast : M.length - 1 = x := by omega
  intro m i L' c R hi hd hch hdc s y hcv hlt1 _
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hcL := (mem_children hcM).2
  have hy : y ≠ z := by
    intro h; rw [h] at hlt1; exact T.not_lt_z _ hlt1
  have hcx : c < x := by
    by_contra hn
    have he : c = x := by omega
    subst c
    rw [hox] at hcv
    cases hcv
    exact hy rfl
  obtain ⟨hHc, _⟩ := hH true c hdc (Or.inl hcx)
  simp only [valB, cond_true] at hHc
  rw [hcv] at hHc
  have hHy := holeT_arg hy hHc hcb
  refine ⟨lo_ne_z_of_holeT (hζz m) hHy, fun hl => ?_⟩
  have hTf := hTPL r μ br (by simpa [hlast] using h1) (by simpa [hlast] using h0)
    (by simpa [hlast] using h2) (by simpa [hμr] using hro) c
    (by simpa [hlast] using hcx) (by simpa [hlast] using hdc) s y hcv
  have hTPLf : (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a →
        ¬ psi (fsD a ((drop1 M x rk).o r)) z z < psi (succ s) z z := by
    intro hs a ha hns hO
    simpa [hlast] using hTf hs a ha hns hO (holeLev_holeT hHy)
  exact lo_keep_of_TPLη hTPLf hy hHc hcb hbrl (hζseed m) hl

end Ytosk
