/-
**WfQrE1: the q = r engine without absorption (2026-10-31).**

On M13 = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,0) the value of
`N = M[2]` at the `v` call `9` is `q + W'` (`q = v(8)`, `W' = fsD(W, gamS 2)`), not `fsD(v 9, gamS 2) = W'`.
The summand `q` of `v(P_1 i)` was absorbed by `W` in `M` and is not absorbed by `W'` in `N`.

The general form of a `v` call (upgrade or bump frame): with `W' ≤ W`,
  `A + W = B ++ W` and `A + W' = B ++ Q ++ W'`, every summand of `Q` in `[W', W)`
(`add_exchangeQ`). `Q = []` is the old `add_exchange` (absorption `AbsUW`/`AbsDW`).
The engine then carries, at every column of `D`, the relation `DQ η t tN` (`tN` is `t` with the hole path followed
as in `fsD`, and at each sum level on the path some summands `Q` inserted before the new last summand, each in
`[new last, old last)`); `DQ` with all `Q = []` is `fsD`.
-/
import Ytosk.V3QRLocV
import Ytosk.V3StepVG

namespace Ytosk

open T

/-- `add X W` keeps exactly the leading summands of `X` that are not below `W`. -/
theorem add_eq_app_split (s y : T) : ∀ X : T,
    add X (psi s y z) = app (split X (psi s y z)).1 (psi s y z)
  | z => rfl
  | psi a b c => by
    rw [add_psi_psi]
    by_cases h : psi a b z < psi s y z
    · rw [if_pos h]
      simp only [split]
      rw [if_pos (show lt (psi a b z) (psi s y z) = true from h)]
      rfl
    · rw [if_neg h]
      simp only [split]
      rw [if_neg (show ¬ lt (psi a b z) (psi s y z) = true from h)]
      simp only [app_psi]
      rw [add_eq_app_split s y c]

/-- The summands kept by `split` are summands of `X`, not below `t`. -/
theorem split_fst_mem (t : T) : ∀ X q, q ∈ summands (split X t).1 → q ∈ summands X ∧ ¬ q < t
  | z, q, hq => by simp [split, summands] at hq
  | psi a b c, q, hq => by
    simp only [split] at hq
    by_cases h : lt (psi a b z) t = true
    · rw [if_pos h] at hq; simp [summands] at hq
    · rw [if_neg h] at hq
      simp only [summands, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨by simp [summands], h⟩
      · obtain ⟨h1, h2⟩ := split_fst_mem t c q hq
        exact ⟨by simp [summands, h1], h2⟩

/-- Adding to `B ++ X` where no summand of `B` is below the principal `W'` adds to `X`. -/
theorem add_app_keep {s y : T} : ∀ {B : T} (X : T), (∀ q ∈ summands B, ¬ q < psi s y z) →
    add (app B X) (psi s y z) = app B (add X (psi s y z))
  | z, X, _ => rfl
  | psi a1 b1 B', X, hB => by
    simp only [app_psi]
    rw [add_psi_psi, if_neg (hB _ (by simp [summands]))]
    rw [add_app_keep X (fun q hq => hB q (by simp [summands, hq]))]

/-- A term below a single term has its head below it. -/
theorem head_lt_of_lt_single {s y : T} : ∀ {X : T}, X < psi s y z → head X < psi s y z
  | z, h => h
  | psi a b c, h => by
    show lt (psi a b z) (psi s y z) = true
    have h' : lt (psi a b c) (psi s y z) = true := h
    by_cases h1 : a = s
    · by_cases h2 : b = y
      · subst h1; subst h2
        exfalso
        have : lt (psi a b c) (psi a b z) = lt c z := by simp [lt]
        rw [this] at h'; cases c <;> simp [lt] at h'
      · have e1 : lt (psi a b c) (psi s y z) = lt b y := by simp [lt, h1, h2]
        have e2 : lt (psi a b z) (psi s y z) = lt b y := by simp [lt, h1, h2]
        rw [e2, ← e1]; exact h'
    · have e1 : lt (psi a b c) (psi s y z) = lt a s := by simp [lt, h1]
      have e2 : lt (psi a b z) (psi s y z) = lt a s := by simp [lt, h1]
      rw [e2, ← e1]; exact h'

/-- **The `v` frame without absorption**: `A + W = B ++ W` and `A + W' = B ++ Q ++ W'` with every summand of `Q`
in `[W', W)`. (`add_exchange` is the case where the absorption hypothesis forces `Q = []`.) -/
theorem add_exchangeQ {A W' s y : T} (hAot : isOT A = true) (hW' : Single W') (hle : W' ≤ psi s y z) :
    ∃ B Q, add A (psi s y z) = app B (psi s y z) ∧ add A W' = app B (app Q W') ∧
      ∀ q ∈ summands Q, W' ≤ q ∧ q < psi s y z := by
  obtain ⟨_, s', y', rfl⟩ := hW'
  obtain ⟨B, X, hAB, hX, hadd⟩ := add_prefix s y A
  have hBge : ∀ q ∈ summands B, ¬ q < psi s y z := by
    intro q hq hlt
    have hq' : q ∈ summands (add A (psi s y z)) := by
      rw [hadd, summands_app]; exact List.mem_append_left _ hq
    exact lt_irrefl' _ (lt_of_le_of_lt (add_summands_ge A q hq') hlt)
  refine ⟨B, (split X (psi s' y' z)).1, hadd, ?_, ?_⟩
  · rw [hAB, add_app_keep X (fun q hq hlt => hBge q hq (lt_of_lt_of_le hlt hle)),
      add_eq_app_split s' y' X]
  · intro q hq
    obtain ⟨hqX, hnq⟩ := split_fst_mem _ X q hq
    refine ⟨not_lt.mp hnq, ?_⟩
    have hXot : isOT X = true := by rw [hAB] at hAot; exact isOT_app_right hAot
    exact lt_of_le_of_lt (summands_le_head hXot q hqX) (head_lt_of_lt_single hX)

/-- **One upgrade frame without absorption** (generalizes `qr_v_upg`): if the new valuation `σ` keeps
`v(P_1 i)` and replaces `last v(k)` by a smaller single `W'`, then `v_σ(i) = B ++ Q ++ W'` where
`v(i) = B ++ last v(k)` and every summand of `Q` is in `[W', last v(k))`. -/
theorem v_upgQ {M : Mat} {ρ σ : Valn} (hC : Cons M ρ) {i k : Nat} (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hA : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i)) (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hV : Single (last (ρ.v k))) (hV' : Single (last (σ.v k))) (hle : last (σ.v k) ≤ last (ρ.v k)) :
    ∃ B Q, ρ.v i = app B (last (ρ.v k)) ∧ vRhs M σ i = app B (app Q (last (σ.v k))) ∧
      ∀ q ∈ summands Q, last (σ.v k) ≤ q ∧ q < last (ρ.v k) := by
  obtain ⟨hVot, s, y, hsy⟩ := hV
  rw [hsy] at hle ⊢
  obtain ⟨B, Q, hB, hB', hQ⟩ := add_exchangeQ hAot hV' hle
  refine ⟨B, Q, ?_, ?_, hQ⟩
  · rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu]
    simp only
    rw [hsy, sf_ot (isOT_add hAot (by rw [← hsy]; exact hVot)), hB]
  · unfold vRhs
    rw [if_neg h1, if_pos h2, hu, hA]
    simp only
    rw [sf_ot (isOT_add hAot hV'.1), hB']

/-- **One bump frame without absorption** (the absorption conjunct of `VLocZ` dropped): if `σ` keeps `v(P_1 i)`
and its bump term `W_σ = bumpW M σ i` is single and at most `W = bumpW M ρ i`, then `v_σ(i) = B ++ Q ++ W_σ` where
`v(i) = B ++ W` and every summand of `Q` is in `[W_σ, W)`. -/
theorem v_bumpQ {M : Mat} {ρ σ : Valn} (hC : Cons M ρ) {i : Nat} (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hA : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i)) (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hW : Single (bumpW M ρ i)) (hW' : Single (bumpW M σ i)) (hle : bumpW M σ i ≤ bumpW M ρ i) :
    ∃ B Q, ρ.v i = app B (bumpW M ρ i) ∧ vRhs M σ i = app B (app Q (bumpW M σ i)) ∧
      ∀ q ∈ summands Q, bumpW M σ i ≤ q ∧ q < bumpW M ρ i := by
  obtain ⟨hWot, s, y, hsy⟩ := hW
  rw [hsy] at hle ⊢
  obtain ⟨B, Q, hB, hB', hQ⟩ := add_exchangeQ hAot hW' hle
  refine ⟨B, Q, ?_, ?_, hQ⟩
  · rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_neg h2]
    have e : omega (sumN (one :: (children M i).map (bumpTerm M ρ i))) = psi s y z := hsy
    rw [e, sf_ot (isOT_add hAot (by rw [← hsy]; exact hWot)), hB]
  · unfold vRhs
    rw [if_neg h1, if_neg h2, hA]
    have e : omega (sumN (one :: (children M i).map (bumpTerm M σ i))) = bumpW M σ i := rfl
    rw [e, sf_ot (isOT_add hAot hW'.1), hB']

/-- **The substitution with re-exposed summands** `DQ η k t tN` (`k = true`: a sum, `k = false`: a single term).
`tN` is `t` with the hole path followed as in `fsD`; at every sum level on the path, summands `Q` in
`[new last, old last)` are inserted before the new last summand. At the end of the path the step of `fsD` is taken
(`base`). With every `Q = z` this is `fsD` along the path. On M13 (`N = M[2]`) the true values of `N` at the
columns `9, 8, 4, 0` of `D` are `DQ (gamS 2)` of the values of `M` with `Q = ψ(ψ(ψ(1)))` at the depth of `v(9)`
(tmp/wf/WfQrE/cmpq.py). -/
inductive DQ (η : T) : Bool → T → T → Prop
  | mk {B l lN Q s y : T} : l = psi s y z → DQ η false l lN →
      (∀ q ∈ summands Q, lN ≤ q ∧ q < l) → DQ η true (app B l) (app B (app Q lN))
  | base {l : T} : fsD l η < l → DQ η false l (fsD l η)
  | sub {a aN : T} : DQ η true a aN → DQ η false (psi a z z) (psi aN z z)
  | arg {a b bN : T} : DQ η true b bN → DQ η false (psi a b z) (psi a bN z)

/-- **`DQ` decreases** (no standard-form hypothesis: the order is lexicographic). -/
theorem DQ.lt {η : T} : ∀ {k : Bool} {t tN : T}, DQ η k t tN → tN < t := by
  intro k t tN h
  induction h with
  | @mk B l lN Q s y hl _ hQ ih =>
    apply app_lt_app_left B
    subst hl
    cases hQc : Q with
    | z => simpa using ih
    | psi a b c =>
      simp only [app_psi]
      apply lt_of_head_lt
      exact (hQ (psi a b z) (by rw [hQc]; simp [summands])).2
  | base h => exact h
  | sub _ ih => rw [psi_lt_psi_z_iff]; exact Or.inl ih
  | arg _ ih => rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, ih⟩)

/-- The source of a low part: the `v` frame output `B ++ Q ++ W'` is a `DQ` of `B ++ W`. -/
theorem DQ.source {η B Q W W' : T} (hW : ∃ s y, W = psi s y z) (h : DQ η false W W')
    (hQ : ∀ q ∈ summands Q, W' ≤ q ∧ q < W) : DQ η true (app B W) (app B (app Q W')) := by
  obtain ⟨s, y, hs⟩ := hW
  exact DQ.mk hs h hQ

/-- The subscript frame `o = Ω_v = ψ_v(0)` carries `DQ`. -/
theorem DQ.om {η v vN : T} (h : DQ η true v vN) : DQ η true (psi v z z) (psi vN z z) := by
  have := DQ.mk (B := z) (Q := z) (s := v) (y := z) rfl (DQ.sub h) (by simp [summands])
  simpa using this

/-- **(L)(ii) with the re-exposed summands** (`TPLoQ`, replaces `TPLoW`): at an `o` call `c` with
`o(c) = ψ_s(y)`, `last y = Ω_a`, `a = v(i) = P + W` (`P = v(P_1 i)`), the value of `a` in `N` is `P + W'`
(`v_bumpQ` / `v_upgQ`). If `s ≤ P`, then `Ω_{P + W'} ≥ Ω_{s+1}`, whatever `W'` is: the low part of the argument
stays empty. (On M13, `c = 4`: `s = P = ψ(ψ(ψ(1)))`, `W' = ψ(ψ(ψ(1)))`; `TPLoW` asks `W' > s` and fails.) -/
theorem tpLoQ_of_le {P s a b : T} (hP : s ≤ P) :
    ¬ psi (add P (psi a b z)) z z < psi (succ s) z z := by
  have h1 : s < add P (psi a b z) := lt_of_le_of_lt hP (lt_add_principal a b P)
  intro h
  rcases psi_lt_psi_z_iff.mp h with h2 | ⟨_, h3⟩
  · exact lt_irrefl' _ (lt_of_lt_of_le h1 (lt_succ_iff.mp h2))
  · exact absurd h3 (T.not_lt_z z)

/-- **VLocQ, upgrade frame**: the new value of a `v` call is a `DQ` of the old one as soon as the last summand of
`v(k)` is (no absorption hypothesis). -/
theorem v_upgDQ {M : Mat} {ρ σ : Valn} (hC : Cons M ρ) {i k : Nat} (hiM : i < M.length) {η : T}
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hA : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i)) (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hV : Single (last (ρ.v k))) (hV' : Single (last (σ.v k)))
    (hD : DQ η false (last (ρ.v k)) (last (σ.v k))) :
    DQ η true (ρ.v i) (vRhs M σ i) := by
  obtain ⟨B, Q, hB, hB', hQ⟩ := v_upgQ hC hiM h1 h2 hu hA hAot hV hV' (le_of_lt hD.lt)
  rw [hB, hB']
  exact DQ.source hV.2 hD hQ

/-- **VLocQ, bump frame**: as `v_upgDQ` with the bump term `bumpW`. -/
theorem v_bumpDQ {M : Mat} {ρ σ : Valn} (hC : Cons M ρ) {i : Nat} (hiM : i < M.length) {η : T}
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hA : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i)) (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hW : Single (bumpW M ρ i)) (hW' : Single (bumpW M σ i))
    (hD : DQ η false (bumpW M ρ i) (bumpW M σ i)) :
    DQ η true (ρ.v i) (vRhs M σ i) := by
  obtain ⟨B, Q, hB, hB', hQ⟩ := v_bumpQ hC hiM h1 h2 hA hAot hW hW' (le_of_lt hD.lt)
  rw [hB, hB']
  exact DQ.source hW.2 hD hQ

end Ytosk
