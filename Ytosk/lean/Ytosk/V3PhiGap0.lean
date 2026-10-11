/-
**段 0 の穴の PhiX を値の不変条件から。**

- NoGap0Pos V: V の部分項 ψ_a(b) + c で、a の加数、または a ≠ 0 のときの b の加数に [ψ_0(Ω_1), Ω_1) の項がない
  （行 1 の子を持つ列 p の v(p) について C′ で 226 万件、T0Ext で 107 万件、例外 0。**ただし標準形で偽**:
  d3s・deep3 で 6 件、v(p) = ψ_0(ψ_1(ψ_0(Ω_1))) のように ψ_a（a ≠ 0）の引数の加数がちょうど ψ_0(Ω_1)。
  reach_z0 は補題として正しいが、NoGap0PosP は不変条件として使えない。）
- Z0Hole X: fsD の経路で、段 0 の穴 Ω_1 の直前の（残りでない）段階が添字か ψ_a（a ≠ 0）の引数、
  または穴の節点が ψ_μ(Ω_{μ+1}) そのもの（EtaHole の終端）。
- reach_z0: 標準形の V で NoGap0Pos V なら、Z0Hole X（段 0）について Reach (SubS V) X ψ_0(Ω_1)。
- C′ の段 0 の場面で Z0Hole でないもの（W = Ω_1 か ψ_0 の引数で前置きのある Ω_1）は、すべて v(p) が
  NoGap0（210826 件）。したがって段 0 の PhiX は NoGap0Pos と「Z0Hole W ∨ NoGap0 v(p)」に帰着。
-/
import Ytosk.V3PhiGapT2

namespace Ytosk

open T

/-- `t` lies in `[ψ_0(Ω_1), Ω_1)`. -/
def Gap0 (t : T) : Prop := etaOm z ≤ t ∧ t < psi (succ z) z z

/-- **No level-0 gap term in a subscript or in the argument of `ψ_a`, `a ≠ 0`.** -/
def NoGap0Pos (V : T) : Prop :=
  ∀ a b c, SubT (psi a b c) V → (∀ q ∈ summands a, ¬ Gap0 q) ∧ (a ≠ z → ∀ q ∈ summands b, ¬ Gap0 q)

mutual
/-- The level-0 hole is reached in a safe context (general position). -/
def Z0Hole : T → Prop
  | z => False
  | psi _ _ (psi c d e) => Z0Hole (psi c d e)
  | psi a b z =>
    if b = z then (isSucc a = false ∧ Z0Ctx a)
    else if b = psi (succ a) z z then True
    else (isSucc b = false ∧ (if a = z then Z0Hole b else Z0Ctx b))
/-- The same inside a subscript or the argument of `ψ_a`, `a ≠ 0` (the base `Ω` may come directly). -/
def Z0Ctx : T → Prop
  | z => False
  | psi _ _ (psi c d e) => Z0Ctx (psi c d e)
  | psi a b z =>
    if b = z then (isSucc a = true ∨ Z0Ctx a)
    else if b = psi (succ a) z z then True
    else (isSucc b = false ∧ (if a = z then Z0Hole b else Z0Ctx b))
end

section
variable {V : T}

/-- Sets of subterms. -/
def GenS (V : T) (S : T → Prop) : Prop := ∀ u, S u → u = z ∨ SubS V u
/-- Sets of clean tails (no summand in the level-0 gap). -/
def CleanS (V : T) (S : T → Prop) : Prop := ∀ u, S u → u = z ∨ (SubS V u ∧ ∀ q ∈ summands u, ¬ Gap0 q)

theorem subS_node {V a b c : T} (h : SubS V (psi a b c)) : ∃ c', SubT (psi a b c') V := by
  obtain ⟨w, hw, hu⟩ := h
  rcases hu with rfl | ⟨a', b', c', rfl, he⟩
  · exact ⟨c, hw⟩
  · cases he; exact ⟨c', hw⟩

theorem subS_rest {V a b c : T} (h : SubS V (psi a b c)) : SubS V c := by
  obtain ⟨w, hw, hu⟩ := h
  rcases hu with rfl | ⟨a', b', c', rfl, he⟩
  · exact ⟨c, (SubT.rest (.refl c)).trans hw, Or.inl rfl⟩
  · cases he; exact ⟨z, (subT_z c').trans ((SubT.rest (.refl c')).trans hw), Or.inl rfl⟩

theorem subS_sub {V a b c : T} (h : SubS V (psi a b c)) : SubS V a := by
  obtain ⟨c', hc'⟩ := subS_node h
  exact ⟨a, (SubT.sub (.refl a)).trans hc', Or.inl rfl⟩

theorem subS_arg {V a b c : T} (h : SubS V (psi a b c)) : SubS V b := by
  obtain ⟨c', hc'⟩ := subS_node h
  exact ⟨b, (SubT.arg (.refl b)).trans hc', Or.inl rfl⟩

theorem genS_rest {S : T → Prop} (h : GenS V S) (a b : T) : GenS V (ImRest S a b) := by
  intro u hu
  rcases h _ hu with he | he
  · cases he
  · exact Or.inr (subS_rest he)

theorem cleanS_rest {S : T → Prop} (h : CleanS V S) (a b : T) : CleanS V (ImRest S a b) := by
  intro u hu
  rcases h _ hu with he | ⟨he, hq⟩
  · cases he
  · exact Or.inr ⟨subS_rest he, fun q hq' => hq q (by simp [summands, hq'])⟩

theorem cleanS_sub (hP : NoGap0Pos V) {S : T → Prop} (h : GenS V S) : CleanS V (ImSub S) := by
  rintro u ⟨b, c, hu⟩
  rcases h _ hu with he | he
  · cases he
  · obtain ⟨c', hc'⟩ := subS_node he
    exact Or.inr ⟨subS_sub he, (hP _ _ _ hc').1⟩

theorem cleanS_arg (hP : NoGap0Pos V) {S : T → Prop} (h : GenS V S) {a : T} (ha : a ≠ z) : CleanS V (ImArg S a) := by
  rintro u ⟨c, hu⟩
  rcases h _ hu with he | he
  · cases he
  · obtain ⟨c', hc'⟩ := subS_node he
    exact Or.inr ⟨subS_arg he, (hP _ _ _ hc').2 ha⟩

theorem genS_sub {S : T → Prop} (h : GenS V S) : GenS V (ImSub S) := by
  rintro u ⟨b, c, hu⟩
  rcases h _ hu with he | he
  · cases he
  · exact Or.inr (subS_sub he)

theorem genS_arg {S : T → Prop} (h : GenS V S) (a : T) : GenS V (ImArg S a) := by
  rintro u ⟨c, hu⟩
  rcases h _ hu with he | he
  · cases he
  · exact Or.inr (subS_arg he)

theorem CleanS.gen {S : T → Prop} (h : CleanS V S) : GenS V S := fun u hu =>
  (h u hu).imp id And.left

theorem ot_of_gen (hV : isOT V = true) {S : T → Prop} (h : GenS V S) : ∀ u, S u → isOT u = true := by
  intro u hu
  rcases h u hu with rfl | he
  · rfl
  · exact isOT_of_subS hV he

theorem lt_E0_of_clean {S : T → Prop} (h : CleanS V S) :
    ∀ u, S u → u < psi (succ z) z z → u < etaOm z := by
  intro u hu hlt
  rcases h u hu with rfl | ⟨_, hq⟩
  · exact T.z_lt_psi _ _ _
  · cases u with
    | z => exact T.z_lt_psi _ _ _
    | psi a b c =>
      have hhead : psi a b z < psi (succ z) z z := by
        rw [T.psi_lt_psi] at hlt ⊢
        rcases hlt with h1 | ⟨h1, h2⟩ | ⟨_, _, h3⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact absurd h3 (T.not_lt_z _)
      have hn := hq (psi a b z) (by simp [summands])
      have hlt' : psi a b z < etaOm z := by
        by_contra hc; exact hn ⟨le_of_not_gt hc, hhead⟩
      unfold etaOm at hlt' ⊢
      rw [T.psi_lt_psi] at hlt' ⊢
      rcases hlt' with h1 | ⟨h1, h2⟩ | ⟨_, _, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact absurd h3 (T.not_lt_z _)

theorem succ_z_of_holeLev {a : T} (hs : isSucc a = true) (h : holeLev (psi a z z) = z) :
    a = succ z := by
  have h1 : holeLev (psi a z z) = init a := by simp [holeLev, hs]
  rw [h1] at h
  rw [← init_app_one hs, h]; rfl

/-- **Reach at a safe level-0 hole.** -/
theorem reach_z0 (hV : isOT V = true) (hP : NoGap0Pos V) : ∀ (X : T) {S : T → Prop}, holeLev X = z →
    (Z0Hole X → GenS V S → Reach S X (etaOm z)) ∧ (Z0Ctx X → CleanS V S → Reach S X (etaOm z))
  | z, _, _ => ⟨fun h => absurd h (by simp [Z0Hole]), fun h => absurd h (by simp [Z0Ctx])⟩
  | psi a b (psi c d e), S, hl => by
    have hl' : holeLev (psi c d e) = z := by rw [← hl]; rfl
    refine ⟨fun h hS => ?_, fun h hS => ?_⟩
    · exact reach_rest (by simp) ((reach_z0 hV hP (psi c d e) hl').1 h (genS_rest hS a b))
    · exact reach_rest (by simp) ((reach_z0 hV hP (psi c d e) hl').2 h (cleanS_rest hS a b))
  | psi a b z, S, hl => by
    by_cases hb : b = z
    · subst hb
      have hrec : ∀ {S' : T → Prop}, isSucc a = false → Z0Ctx a → CleanS V S' →
          Reach S' (psi a z z) (etaOm z) := by
        intro S' hs hc hS'
        have ha : a ≠ z := by rintro rfl; exact absurd hc (by simp [Z0Ctx])
        have hla : holeLev a = z := by rw [← holeLev_sub' hs]; exact hl
        exact reach_sub ha hs ((reach_z0 hV hP a hla).2 hc (cleanS_sub hP hS'.gen))
      refine ⟨fun h hS => ?_, fun h hS => ?_⟩
      · have h' : isSucc a = false ∧ Z0Ctx a := by simpa [Z0Hole] using h
        have ha : a ≠ z := by rintro rfl; exact absurd h'.2 (by simp [Z0Ctx])
        have hla : holeLev a = z := by rw [← holeLev_sub' h'.1]; exact hl
        exact reach_sub ha h'.1 ((reach_z0 hV hP a hla).2 h'.2 (cleanS_sub hP hS))
      · have h' : isSucc a = true ∨ Z0Ctx a := by simpa [Z0Ctx] using h
        by_cases hs : isSucc a = true
        · have ha := succ_z_of_holeLev hs hl
          subst ha
          exact reach_base (succ_ne_z z) hs (lt_E0_of_clean hS)
        · have hs' : isSucc a = false := by simpa using hs
          rcases h' with h' | h'
          · exact absurd h' hs
          · exact hrec hs' h' hS
    by_cases he : b = psi (succ a) z z
    · subst he
      have ha : a = z := by
        have := hl; change holeLev (etaOm a) = z at this; rwa [holeLev_etaOm] at this
      subst ha
      have hE : ∀ {S' : T → Prop}, GenS V S' → Reach S' (psi z (psi (succ z) z z) z) (etaOm z) :=
        fun hS' => reach_etaOm (ot_of_gen hV hS') z
      exact ⟨fun _ hS => hE hS, fun _ hS => hE hS.gen⟩
    · have hlb : holeLev b = z := by rw [← holeLev_arg hb]; exact hl
      have key : isSucc b = false ∧ (if a = z then Z0Hole b else Z0Ctx b) → GenS V S →
          Reach S (psi a b z) (etaOm z) := by
        rintro ⟨hs, hc⟩ hS
        by_cases ha : a = z
        · rw [if_pos ha] at hc
          exact reach_arg hb hs ((reach_z0 hV hP b hlb).1 hc (genS_arg hS a))
        · rw [if_neg ha] at hc
          exact reach_arg hb hs ((reach_z0 hV hP b hlb).2 hc (cleanS_arg hP hS ha))
      refine ⟨fun h hS => ?_, fun h hS => ?_⟩
      · unfold Z0Hole at h; rw [if_neg hb, if_neg he] at h; exact key h hS
      · unfold Z0Ctx at h; rw [if_neg hb, if_neg he] at h; exact key h hS.gen

end

/-- **The level-0 PhiX instance** from `NoGap0Pos` and a safe hole. -/
theorem reach_z0_inst {V X : T} (hV : isOT V = true) (hP : NoGap0Pos V) (hX : Z0Hole X)
    (hl : holeLev X = z) : Reach (SubS V) X (etaOm (holeLev X)) := by
  rw [hl]
  exact (reach_z0 hV hP X hl).1 hX (fun u hu => Or.inr hu)

/-! ## 段 0 を値の不変条件で -/

/-- **Not an invariant**: false on 6 standard matrices (d3s・deep3、引数の加数が ψ_0(Ω_1) そのもの). -/
def NoGap0PosP (M : Mat) (ρ : Valn) : Prop := VP NoGap0Pos M ρ

/-- **The level-0 link**: an unsafe level-0 hole (`W = Ω_1`, or `Ω_1` after a prefix in a `ψ_0` argument)
only occurs with `v(p)` free of `[ψ_0(Ω_1), Ω_1)` (C′ で 210826 件、例外 0). -/
def Z0Link (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p, c < M.length → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c → OHole (bumpW M ρ c) →
    holeLev (bumpW M ρ c) = z → ¬ Z0Hole (bumpW M ρ c) → NoGap0 (ρ.v p)

theorem phiX0_of_z0 {M : Mat} {ρ : Valn} (hG : Good3 M ρ) (hP : NoGap0PosP M ρ) (hL : Z0Link M ρ) :
    PhiX0 M ρ := by
  intro c p hc h1 h2 hch hO hμ
  obtain ⟨c', hc', hp⟩ := hch.has_child hc
  have hpM : p < M.length := by have := par_lt M 1 c' p hp; omega
  by_cases hZ : Z0Hole (bumpW M ρ c)
  · exact reach_z0_inst (hG.ot_v p hpM) (hP c' p hc' hp) hZ hμ
  · exact reach_of_noGap0 hO hμ (hL c p hc h1 h2 hch hO hμ hZ)

/-- **PhiX from value invariants and the level-0 link.** -/
theorem phiX_of_z0 {M : Mat} {ρ : Valn} (hG : Good3 M ρ) (hN : NoGapP M ρ) (hP : NoGap0PosP M ρ)
    (hL : Z0Link M ρ) : PhiX M ρ :=
  phiX_of_noGap hN (phiX0_of_z0 hG hP hL)

end Ytosk
