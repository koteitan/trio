/-
**落とす補題: のりしろの v の枠（`drop_all` の仮定 `hBump`）。**

行 2 が 0 でない列 i の v は v(i) = V + ω^p、p = 1 + Σ_j ω^{G_j}（j はのりしろの子、G_j = Σ_k o(k)）。
M′ = M.take x では、変わりうるのは最後ののりしろの子 jl の最後の子 kl だけ（`chg_only_last`）。

関係 `BRelS`（⊴ に「ω^ を通せる形」を添えたもの）を G → ω^G → p → ω^p の順に運ぶ:
- 両方 ψ_0(Ω_1) 未満（small）、先頭の添字が同じ（same）、ψ_0(Ω_1) をまたいで添字 0（mixed）、
  ψ_{w′}(0) と ψ_w(…)（fix、ω^ の不動点）。
弱い関係 `BWk`（≤ と、小さいか ψ_{w′}(0) の形）は崩れ（jl の子が x だけ）と、弱い子から出る。
弱い場合は値の仮定 `BumpWeakShape` で i の子は jl だけ・V の成分は可算になる。

値の仮定（SRO より下の L9 網羅で例外 0）:
- `BumpKidsDec`: のりしろの子の子の o は減少列。
- `BumpTermDec`: のりしろの項 ω^{G_j} は減少列。
- `BumpAbs`: V の加数で ω^2 以上かつ w より下のものは w に対して ◁。
- `BumpWeakShape`: のりしろの子の子 k の o が ψ_w(0)（w ≠ 0）なら、子は 1 つだけ・k は最初の子・V の成分は可算。
-/
import Ytosk.V3DropMain

namespace Ytosk

open T

/-! ## 項の段: ψ_0(Ω_1) より下かどうかは先頭の加数で決まる -/

theorem E0_lt_Om_one : E0 < Om one := by
  rw [E0, Om, T.psi_lt_psi]; exact Or.inl (T.z_lt_psi _ _ _)

theorem lt_E0_iff {s b c : T} : psi s b c < E0 ↔ s = z ∧ b < Om one := by
  unfold E0
  rw [psi_lt_psi_z_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (T.not_lt_z _)
    · exact h
  · intro h; exact Or.inr h

theorem lt_E0_rest {s b c c' : T} (h : psi s b c < E0) : psi s b c' < E0 :=
  lt_E0_iff.mpr (lt_E0_iff.mp h)

theorem psi_z_lt_E0 {X : T} (h : X < E0) : psi z X z < E0 :=
  lt_E0_iff.mpr ⟨rfl, lt_trans h E0_lt_Om_one⟩

/-- `1 + 1`. -/
def two : T := psi z z one

theorem two_lt_E0 : two < E0 := lt_E0_iff.mpr ⟨rfl, T.z_lt_psi _ _ _⟩

theorem one_lt_two : one < two := by
  unfold one two; rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, T.z_lt_psi _ _ _⟩)

theorem one_lt_E0 : one < E0 := lt_trans one_lt_two two_lt_E0

theorem isOT_two : isOT two = true := by decide

/-- A single summand above `1` is above `1 + 1`. -/
theorem two_lt_of_one_lt {s y : T} (h : one < psi s y z) : two < psi s y z := by
  unfold one at h; unfold two
  rw [psi_lt_psi_z_iff] at h
  rw [psi_lt_psi_z_iff]
  exact h

theorem comps_two (u : T) : ∀ g ∈ comps u two, g = z := by
  intro g hg
  unfold two one at hg
  simp only [comps, List.mem_append] at hg
  split at hg <;> simp at hg <;> tauto

theorem lhd_two {l : T} (hl : two < l) : Lhd z two l := by
  refine ⟨hl, fun u c _ _ g hg => ?_⟩
  rw [comps_two u g hg]
  exact ⟨z, by simp [Gc], le_refl _⟩

theorem closed_two : Closed z two := by
  intro u _ g hg
  rw [comps_two u g hg]; exact z_le _

theorem closed_one : Closed z one := by
  intro u _ g hg
  simp only [one, comps, List.append_nil] at hg
  split at hg
  · simp at hg
  · simp at hg; rw [hg]; exact z_le _

/-! ## 関係 -/

/-- **The strong relation** carried through the bump frame: `⊴` together with a shape that lets it pass
through `ω^`. -/
def BRelS (X' X : T) : Prop :=
  (LhdE X' X ∧ X < E0) ∨
  (LhdE X' X ∧ ¬ X' < E0 ∧ ∃ s b' c' b c, X' = psi s b' c' ∧ X = psi s b c) ∨
  (LhdE X' X ∧ X' < E0 ∧ Closed z X' ∧ ¬ X < E0 ∧ ∃ b c, X = psi z b c) ∨
  (∃ w' w Y c, X' = psi w' z z ∧ X = psi w Y c ∧ LhdE w' w ∧ one ≤ w')

/-- **The weak relation**: `≤`, with the new side below `ψ_0(Ω_1)` or a `ψ_{w′}(0)` with countable
components. -/
def BWk (X' X : T) : Prop :=
  X' ≤ X ∧ (X' < E0 ∨ ∃ w', X' = psi w' z z ∧ one ≤ w' ∧ CS w')

theorem one_le_psi_sub {w Y c : T} (h : one ≤ w) : ¬ psi w Y c < E0 := by
  intro hE
  have := (lt_E0_iff.mp hE).1
  subst this
  exact absurd h (not_le_of_gt (T.z_lt_psi _ _ _))

theorem brelS_lhdE {X' X : T} (h : BRelS X' X) : LhdE X' X := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨w', w, Y, c, rfl, rfl, hw, _⟩
  · exact h
  · exact h
  · exact h
  · have h1 := lhdE_prefix (psi w Y z) c
    simp only [app_psi, app_z] at h1
    exact LhdE.trans (lhdE_oq_v hw) h1

theorem brelS_refl {X : T} : BRelS X X := by
  by_cases hE : X < E0
  · exact Or.inl ⟨Or.inl rfl, hE⟩
  · cases X with
    | z => exact absurd (T.z_lt_psi _ _ _) hE
    | psi s b c => exact Or.inr (Or.inl ⟨Or.inl rfl, hE, s, b, c, b, c, rfl, rfl⟩)

theorem not_lt_E0_mono {X' X : T} (hle : X' ≤ X) (h : ¬ X' < E0) : ¬ X < E0 :=
  fun hX => h (lt_of_le_of_lt hle hX)

theorem not_lt_E0_omega {X : T} (hX : isOT X = true) (h : ¬ X < E0) : ¬ omega X < E0 := by
  cases X with
  | z => exact absurd (T.z_lt_psi _ _ _) h
  | psi s b c => exact not_lt_E0_mono (le_omega_big hX h) h

/-- **`ω^` preserves the strong relation.** -/
theorem brelS_omega {X' X : T} (hX' : isOT X' = true) (hX : isOT X = true) (h : BRelS X' X) :
    BRelS (omega X') (omega X) := by
  rcases h with ⟨hl, hE⟩ | ⟨hl, hE', s, b', c', b, c, rfl, rfl⟩ | ⟨hl, hE', hcl, hE, b, c, rfl⟩ |
      ⟨w', w, Y, c, rfl, rfl, hw, h1⟩
  · have hE' := lt_of_le_of_lt hl.le hE
    rw [omega_small hE', omega_small hE]
    exact Or.inl ⟨lhdE_psi z hl, psi_z_lt_E0 hE⟩
  · have hE := not_lt_E0_mono hl.le hE'
    refine Or.inr (Or.inl ⟨omega_lhd_same hX' hX hE' hl, not_lt_E0_omega hX' hE', ?_⟩)
    rw [omega_big hX' hE', omega_big hX hE]
    exact ⟨_, _, _, _, _, rfl, rfl⟩
  · refine Or.inr (Or.inr (Or.inl ⟨omega_lhd_mixed0 hE' hcl hX hE, ?_, ?_, not_lt_E0_omega hX hE, ?_⟩))
    · rw [omega_small hE']; exact psi_z_lt_E0 hE'
    · have hot := isOT_omega hX'
      rw [omega_small hE'] at hot ⊢
      exact closed_psi0 hot (psi_z_lt_E0 hE')
    · rw [omega_big hX hE]; exact ⟨_, _, rfl⟩
  · have hw1 : one ≤ w := le_trans h1 hw.le
    rw [omega_psi_fix (isOT_sub hX') (one_le_psi_sub h1), omega_big hX (one_le_psi_sub hw1)]
    exact Or.inr (Or.inr (Or.inr ⟨w', w, _, z, rfl, rfl, hw, h1⟩))

/-- **`ω^` preserves the weak relation.** -/
theorem bwk_omega {X' X : T} (hX' : isOT X' = true) (hX : isOT X = true) (h : BWk X' X) :
    BWk (omega X') (omega X) := by
  obtain ⟨hle, hs⟩ := h
  refine ⟨?_, ?_⟩
  · rcases (le_iff _ _).mp hle with h | h
    · exact le_of_lt (omega_lt_omega hX' hX h)
    · rw [h]
  · rcases hs with hE | ⟨w', rfl, h1, hcs⟩
    · left; rw [omega_small hE]; exact psi_z_lt_E0 hE
    · right
      rw [omega_psi_fix (isOT_sub hX') (one_le_psi_sub h1)]
      exact ⟨w', rfl, h1, hcs⟩

/-! ## p の段: 1 + t と末尾の 1 -/

theorem sumN_pair_one {t : T} (ht : Single t) :
    sumN [one, t] = if one < t then t else psi z z t := by
  obtain ⟨hot, s, y, rfl⟩ := ht
  have h1 : isOT one = true := rfl
  show sf (add (sf (add z one)) (psi s y z)) = _
  rw [add_z_left, sf_ot h1, sf_ot (isOT_add h1 hot)]
  unfold one
  rw [add_psi_psi]
  simp

theorem onep_self {t : T} (ht : Single t) (h : one < t) : sumN [one, t] = t := by
  rw [sumN_pair_one ht, if_pos h]

theorem onep_two {t : T} (ht : Single t) (h : ¬ one < t) : t = one ∧ sumN [one, t] = two := by
  have h1 : one ≤ t := one_le_of_ne_z (single_ne_z ht)
  have he : t = one := by
    rcases (le_iff _ _).mp h1 with h' | h'
    · exact absurd h' h
    · exact h'.symm
  refine ⟨he, ?_⟩
  rw [sumN_pair_one ht, if_neg h, he]; rfl

theorem one_ne_psi_pos {w' : T} (h : one ≤ w') : one ≠ psi w' z z := by
  intro he
  unfold one at he
  simp only [psi.injEq] at he
  rw [← he.1] at h
  exact absurd h (not_le_of_gt (T.z_lt_psi _ _ _))

/-- **`1 + ·` preserves the strong relation.** -/
theorem brelS_onep {t' t : T} (ht' : Single t') (ht : Single t) (h : BRelS t' t) :
    BRelS (sumN [one, t']) (sumN [one, t]) := by
  have hle := (brelS_lhdE h).le
  by_cases h1 : one < t'
  · rw [onep_self ht' h1, onep_self ht (lt_of_lt_of_le h1 hle)]; exact h
  · obtain ⟨rfl, e'⟩ := onep_two ht' h1
    rw [e']
    by_cases h2 : one < t
    · rw [onep_self ht h2]
      obtain ⟨_, s, y, rfl⟩ := ht
      have h2' := two_lt_of_one_lt h2
      rcases h with ⟨_, hE⟩ | ⟨_, hE', _⟩ | ⟨_, _, _, hE, b, c, hb⟩ | ⟨w', w, Y, c, he, _, _, hw1⟩
      · exact Or.inl ⟨Or.inr (lhd_two h2'), hE⟩
      · exact absurd one_lt_E0 hE'
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (lhd_two h2'), two_lt_E0, closed_two, hE, b, c, hb⟩))
      · exact absurd he (one_ne_psi_pos hw1)
    · rw [(onep_two ht h2).2]; exact brelS_refl

/-- **`1 + ·` preserves the weak relation.** -/
theorem bwk_onep {t' t : T} (ht' : Single t') (ht : Single t) (h : BWk t' t) :
    BWk (sumN [one, t']) (sumN [one, t]) := by
  obtain ⟨hle, hs⟩ := h
  by_cases h1 : one < t'
  · rw [onep_self ht' h1, onep_self ht (lt_of_lt_of_le h1 hle)]; exact ⟨hle, hs⟩
  · obtain ⟨rfl, e'⟩ := onep_two ht' h1
    rw [e']
    refine ⟨?_, Or.inl two_lt_E0⟩
    by_cases h2 : one < t
    · rw [onep_self ht h2]; obtain ⟨_, s, y, rfl⟩ := ht; exact le_of_lt (two_lt_of_one_lt h2)
    · rw [(onep_two ht h2).2]

theorem add_one_eq_app (X : T) : add X one = app X one :=
  add_eq_app_of_ge ⟨z, z, rfl⟩ X (fun q hq => by
    obtain ⟨s, y, rfl⟩ := mem_summands hq; exact one_le_of_ne_z (by simp))

/-- **A final `+1` on the old side** (the bump child `x`). -/
theorem brelS_tail {X' X : T} (h : BRelS X' X) (hne : X ≠ z) : BRelS X' (app X one) := by
  cases X with
  | z => exact absurd rfl hne
  | psi a b c =>
    have hl : LhdE X' (app (psi a b c) one) := LhdE.trans (brelS_lhdE h) (lhdE_prefix _ one)
    simp only [app_psi] at hl ⊢
    rcases h with ⟨_, hE⟩ | ⟨_, hE', s, b', c', b0, c0, rfl, he⟩ | ⟨_, hE', hcl, hE, b0, c0, he⟩ |
        ⟨w', w, Y, c0, rfl, he, hw, h1⟩
    · exact Or.inl ⟨hl, lt_E0_rest hE⟩
    · simp only [psi.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr (Or.inl ⟨hl, hE', _, _, _, _, _, rfl, rfl⟩)
    · simp only [psi.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr (Or.inr (Or.inl ⟨hl, hE', hcl, fun h' => hE (lt_E0_rest h'), _, _, rfl⟩))
    · simp only [psi.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr (Or.inr (Or.inr ⟨w', a, b, _, rfl, rfl, hw, h1⟩))

theorem bwk_tail {X' X : T} (h : BWk X' X) : BWk X' (app X one) := ⟨le_trans h.1 (le_app_self _ _), h.2⟩

/-! ## v の段: V + W -/

theorem add_le_add_single : ∀ (V : T) {W' W : T}, (∃ s y, W' = psi s y z) → (∃ s y, W = psi s y z) →
    W' ≤ W → add V W' ≤ add V W
  | z, _, _, _, _, hle => by simpa using hle
  | psi a b c, _, _, ⟨s', y', rfl⟩, ⟨s, y, rfl⟩, hle => by
    rw [add_psi_psi, add_psi_psi]
    by_cases h1 : psi a b z < psi s' y' z
    · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 hle)]; exact hle
    · rw [if_neg h1]
      by_cases h2 : psi a b z < psi s y z
      · rw [if_pos h2]; apply le_of_lt; rw [psi_lt_psi_z_iff] at h2 ⊢; exact h2
      · rw [if_neg h2]; exact psi_le_psi_rest (add_le_add_single c ⟨s', y', rfl⟩ ⟨s, y, rfl⟩ hle)

theorem le_add_single : ∀ (V : T) {W : T}, (∃ s y, W = psi s y z) → W ≤ add V W
  | z, _, _ => by simp
  | psi a b c, _, ⟨s, y, rfl⟩ => by
    rw [add_psi_psi]
    split
    · exact le_refl _
    · rename_i h
      exact le_trans (not_lt.mp h) (psi_le_psi_rest (z_le _))

theorem comps_add (u : T) : ∀ (V W : T), ∀ g ∈ comps u (add V W), g ∈ comps u V ∨ g ∈ comps u W
  | z, W, g, hg => by simp at hg; exact Or.inr hg
  | psi a b c, z, g, hg => by simp at hg; exact Or.inl hg
  | psi a b c, psi d e f, g, hg => by
    rw [add_psi_psi] at hg
    split at hg
    · exact Or.inr hg
    · simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · left; simp only [comps, List.mem_append]; exact Or.inl hg
      · rcases comps_add u c (psi d e f) g hg with h | h
        · left; simp only [comps, List.mem_append]; exact Or.inr h
        · exact Or.inr h

theorem cs_add {V W : T} (hV : CS V) (hW : CS W) : CS (add V W) :=
  fun g hg => (comps_add z V W g hg).elim (hV g) (hW g)

theorem bwk_cs {X' X : T} (hX' : isOT X' = true) (h : BWk X' X) : CS X' := by
  rcases h.2 with hE | ⟨w', rfl, _, hcs⟩
  · intro g hg; exact lt_trans (lt_trans (comps_z_lt_of_lt_E0 hX' hE g hg) hE) E0_lt_Om_one
  · intro g hg
    have hnz : lt w' z = false := by cases w' <;> rfl
    simp only [comps, hnz, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | h | h) | h
    · unfold Om; exact T.z_lt_psi _ _ _
    · simp at h
    · exact hcs g h
    · simp at h

theorem vsmall_of_cs {t : T} (hcs : CS t) (h1 : one ≤ t) : VSmallV t := by
  intro u g hg
  exact le_of_lt (lt_of_lt_of_le (hcs g (comps_sub_z u t g hg)) (Om_one_le_psi h1))

/-! ## p の段（前の兄弟つき）と G の段の形 -/

theorem sumN_ne_z {l : List T} (hs : ∀ t ∈ l, Single t) (hp : l.Pairwise (fun a b => b ≤ a))
    (hne : l ≠ []) : sumN l ≠ z := by
  intro h
  have := (sumN_dec l hs hp).2
  rw [h] at this
  simp only [summands] at this
  exact hne this.symm

theorem sumN_one_cons_gt {q : T} {l : List T} (hq : Single q) (h : one < q) :
    sumN (one :: q :: l) = sumN (q :: l) := by
  unfold sumN
  simp only [List.foldl_cons]
  congr 1
  obtain ⟨hot, s, y, rfl⟩ := hq
  have h1 : isOT one = true := rfl
  rw [add_z_left, sf_ot h1, add_z_left]
  unfold one at h ⊢
  rw [add_psi_psi, if_pos h]

/-- **A common nonzero prefix**: `S + a′` against `S + a + R`. -/
theorem brelS_app_same {S a' a : T} (hS : S ≠ z) (h : LhdE a' a) (R : T) :
    BRelS (app S a') (app (app S a) R) := by
  cases S with
  | z => exact absurd rfl hS
  | psi s b c =>
    have hl : LhdE (app (psi s b c) a') (app (app (psi s b c) a) R) :=
      LhdE.trans (lhdE_app _ h) (lhdE_prefix _ R)
    simp only [app_psi] at hl ⊢
    by_cases hE : psi s b (app (app c a) R) < E0
    · exact Or.inl ⟨hl, hE⟩
    · exact Or.inr (Or.inl ⟨hl, fun h' => hE (lt_E0_rest h'), _, _, _, _, _, rfl, rfl⟩)

/-- **The `p` level**: `1 + P + t′` against `1 + P + t` (the terms of `P` are at least `t`). -/
theorem brelS_p {Pl : List T} {t' t : T} (hsP : ∀ q ∈ Pl, Single q)
    (hpP : Pl.Pairwise (fun a b => b ≤ a)) (hPt : ∀ q ∈ Pl, t ≤ q) (ht' : Single t') (ht : Single t)
    (h : BRelS t' t) : BRelS (sumN (one :: Pl ++ [t'])) (sumN (one :: Pl ++ [t])) := by
  have hle := (brelS_lhdE h).le
  cases Pl with
  | nil => simpa using brelS_onep ht' ht h
  | cons q Pr =>
    have hq := hsP q (by simp)
    by_cases hq1 : one < q
    · simp only [List.cons_append]
      rw [sumN_one_cons_gt hq hq1, sumN_one_cons_gt hq hq1]
      have hsl : ∀ c, Single c → c ≤ t → (∀ u ∈ (q :: Pr) ++ [c], Single u) ∧
          ((q :: Pr) ++ [c]).Pairwise (fun a b => b ≤ a) := by
        intro c hc hct
        refine ⟨fun u hu => ?_, List.pairwise_append.mpr ⟨hpP, by simp, fun a ha b hb => ?_⟩⟩
        · rcases List.mem_append.mp hu with hu | hu
          · exact hsP u hu
          · simp at hu; rw [hu]; exact hc
        · simp at hb; rw [hb]; exact le_trans hct (hPt a ha)
      obtain ⟨hs1, hp1⟩ := hsl t' ht' hle
      obtain ⟨hs2, hp2⟩ := hsl t ht (le_refl _)
      rw [← List.cons_append, ← List.cons_append, sumN_snoc_dec hs1 hp1, sumN_snoc_dec hs2 hp2]
      have hS : sumN (q :: Pr) ≠ z := sumN_ne_z hsP hpP (by simp)
      have := brelS_app_same hS (brelS_lhdE h) z
      simpa using this
    · have hq0 : q = one := (onep_two hq hq1).1
      have ht1 : t = one := le_antisymm (hq0 ▸ hPt q (by simp)) (one_le_of_ne_z (single_ne_z ht))
      have ht1' : t' = one :=
        le_antisymm (ht1 ▸ hle) (one_le_of_ne_z (single_ne_z ht'))
      rw [ht1, ht1']; exact brelS_refl

/-- `ψ_s(y′) ⊴ ψ_s(y)` with the same subscript, against `ψ_s(y) + R`. -/
theorem brelS_single_same {s y' y : T} (R : T) (h : LhdE (psi s y' z) (psi s y z))
    (hot' : isOT (psi s y' z) = true) : BRelS (psi s y' z) (psi s y R) := by
  have hl : LhdE (psi s y' z) (psi s y R) := LhdE.trans h (by
    have := lhdE_prefix (psi s y z) R; simpa using this)
  by_cases hE : psi s y R < E0
  · exact Or.inl ⟨hl, hE⟩
  · by_cases hE' : psi s y' z < E0
    · obtain ⟨rfl, _⟩ := lt_E0_iff.mp hE'
      exact Or.inr (Or.inr (Or.inl ⟨hl, hE', closed_psi0 hot' hE', hE, _, _, rfl⟩))
    · exact Or.inr (Or.inl ⟨hl, hE', _, _, _, _, _, rfl, rfl⟩)

theorem brelS_fix {w' w Y R : T} (h : LhdE w' w) (h1 : one ≤ w') : BRelS (psi w' z z) (psi w Y R) :=
  Or.inr (Or.inr (Or.inr ⟨w', w, Y, R, rfl, rfl, h, h1⟩))

theorem bwk_fix {w' X : T} (hle : psi w' z z ≤ X) (h1 : one ≤ w') (hcs : CS w') :
    BWk (psi w' z z) X := ⟨hle, Or.inr ⟨w', rfl, h1, hcs⟩⟩

/-! ## v の段のまとめ -/

/-- **The strong case**: `V + W′ ⊴ V + W` with absorption. -/
theorem v_strong {V W' W : T} (hV : isOT V = true) (hW' : Single W') (hW : Single W)
    (h : LhdE W' W) (hR : ∀ r ∈ summands V, ¬ r < W' → r < W → Lhd z r W) :
    LhdE (add V W') (add V W) := by
  obtain ⟨hot', s', y', rfl⟩ := hW'
  obtain ⟨_, s, y, rfl⟩ := hW
  exact lhdE_add_absorb h V hV (isOT_add hV hot') hR

/-- **The weak case**: `V + W′ = V + W` or weakly below. -/
theorem v_weak {V W' W : T} (hV : isOT V = true) (hcsV : CS V) (hW' : Single W') (hW : Single W)
    (h : BWk W' W) : add V W' = add V W ∨ WkV (add V W') (add V W) := by
  rcases (le_iff _ _).mp (add_le_add_single V hW'.2 hW.2 h.1) with hlt | heq
  · right
    exact ⟨hlt, cs_add hcsV (bwk_cs hW'.1 h),
      le_trans (one_le_of_ne_z (single_ne_z hW')) (le_add_single V hW'.2), isOT_add hV hW'.1⟩
  · left; exact heq

/-! ## 0 でない値と 2 以上の p -/

theorem add_ne_z_right : ∀ (x : T) {y : T}, y ≠ z → add x y ≠ z
  | z, _, h => by simpa using h
  | psi a b c, z, _ => by simp
  | psi a b c, psi d e f, _ => by
    rw [add_psi_psi]; split <;> simp

theorem sp_ne_z (a : T) : ∀ (c b : T), sp a b c ≠ z
  | z, b => by simp [sp]
  | psi s y c, b => by
    unfold sp
    split
    · exact sp_ne_z a c _
    · exact sp_ne_z a c _

theorem sf_ne_z : ∀ {t : T}, t ≠ z → sf t ≠ z
  | z, h => absurd rfl h
  | psi a b c, _ => by
    simp only [sf]
    cases hc : sf c with
    | z => rw [add_z_right]; exact sp_ne_z _ _ _
    | psi => exact add_ne_z_right _ (by simp)

theorem last_ne_z_bd : ∀ {t : T}, t ≠ z → last t ≠ z
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last]
  | psi a b (psi c d e), _ => by
    show last (psi c d e) ≠ z
    exact last_ne_z_bd (by simp)

theorem vbump_ne_z {N : Mat} {σ : Valn} (hC : Cons N σ) {k : Nat} (hk : k < N.length)
    (h1 : entry N 1 k ≠ 0) (h2 : entry N 2 k ≠ 0) : σ.v k ≠ z := by
  rw [(hC k hk).2]; unfold vRhs
  rw [if_neg h1, if_neg h2]
  exact sf_ne_z (add_ne_z_right _ (omega_ne_z _))

/-- **`v ≠ 0` where row 1 is nonzero.** -/
theorem v_ne_z_of_e1 {N : Mat} {σ : Valn} (hC : Cons N σ) {k : Nat} (hk : k < N.length)
    (h1 : entry N 1 k ≠ 0) : σ.v k ≠ z := by
  by_cases h2 : entry N 2 k = 0
  · rw [(hC k hk).2]; unfold vRhs
    rw [if_neg h1, if_pos h2]
    apply sf_ne_z
    apply add_ne_z_right
    cases hu : upg N k with
    | none => simp [one]
    | some k2 =>
      simp only
      obtain ⟨m, _, _, hcol, _⟩ := upg_spec hu
      have hk2 := upg_lt hk hu
      have e1 : entry N 1 k2 ≠ 0 := by
        have : entry N 1 k2 = (col N k2).2.1 := rfl
        rw [this, hcol]; exact h1
      have e2 : entry N 2 k2 ≠ 0 := by
        have : entry N 2 k2 = (col N k2).2.2 := rfl
        rw [this, hcol]; simp
      exact last_ne_z_bd (vbump_ne_z hC hk2 e1 e2)
  · exact vbump_ne_z hC hk h1 h2

theorem v_z_of_e1 {N : Mat} {σ : Valn} (hC : Cons N σ) {k : Nat} (hk : k < N.length)
    (h1 : entry N 1 k = 0) : σ.v k = z := by
  rw [(hC k hk).2]; unfold vRhs; rw [if_pos h1]

theorem le_add_of_single : ∀ (X : T) {c : T}, (∃ s y, c = psi s y z) → X ≤ add X c
  | z, _, _ => z_le _
  | psi a b c0, _, ⟨s, y, rfl⟩ => by
    rw [add_psi_psi]
    split
    · rename_i h
      exact le_of_lt (lt_of_head_lt (by simpa [head] using h))
    · exact psi_le_psi_rest (le_add_of_single c0 ⟨s, y, rfl⟩)

theorem foldl_ge : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, Single t) →
    acc ≤ l.foldl (fun a b => sf (add a b)) acc
  | [], _, _, _ => le_refl _
  | t :: l, acc, h, hs => by
    simp only [List.foldl_cons]
    have ht := hs t (by simp)
    have hot : isOT (add acc t) = true := isOT_add h ht.1
    rw [sf_ot hot]
    exact le_trans (le_add_of_single acc ht.2)
      (foldl_ge l _ hot (fun u hu => hs u (List.mem_cons_of_mem _ hu)))

/-- **`1 + Σ ≥ 2`** for a nonempty sum. -/
theorem two_le_sumN_one_cons {l : List T} (hne : l ≠ []) (hs : ∀ t ∈ l, Single t) :
    two ≤ sumN (one :: l) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c l' =>
    have hc := hs c (by simp)
    have e : sumN (one :: c :: l') = l'.foldl (fun a b => sf (add a b)) (sumN [one, c]) := by
      unfold sumN; simp only [List.foldl_cons, List.foldl_nil]
    have h2 : two ≤ sumN [one, c] := by
      by_cases h : one < c
      · rw [onep_self hc h]; obtain ⟨_, s, y, rfl⟩ := hc; exact le_of_lt (two_lt_of_one_lt h)
      · rw [(onep_two hc h).2]
    have hot : isOT (sumN [one, c]) = true :=
      isOT_sumN _ (fun t ht => by simp at ht; rcases ht with rfl | rfl; rfl; exact hc.1)
    rw [e]
    exact le_trans h2 (foldl_ge l' _ hot (fun u hu => hs u (List.mem_cons_of_mem _ hu)))

/-! ## 値の仮定 -/

/-- **Value hypothesis**: under a column with rows 1 and 2 nonzero, the `o` values of the children of a
bump child do not increase (SRO より下の L9 網羅で 57 万件、例外 0). -/
def BumpKidsDec (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ j ∈ children M i, col M j = bump M i →
    ((children M j).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- **Value hypothesis**: the bump terms `ω^{G_j}` do not increase (L9 網羅で 57 万件、例外 0). -/
def BumpTermDec (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    (nzs ((children M i).map (bumpTerm M ρ i))).Pairwise (fun a b => b ≤ a)

/-- The bump term `ω^p` of `v(i)`. -/
def bumpW (M : Mat) (ρ : Valn) (i : Nat) : T := omega (sumN (one :: (children M i).map (bumpTerm M ρ i)))

/-- **Value hypothesis**: a summand of `v(P_1 i)` at least `ω^2` and below the bump term `w` is `◁ w`
(L9 網羅: そのような加数は 1 つもない。`ω^2` 未満では `ω ◁ Ω_1` が偽になる例がある). -/
def BumpAbs (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ r ∈ summands (vOpt ρ (par M 1 i)),
    ¬ r < psi z two z → r < bumpW M ρ i → Lhd z r (bumpW M ρ i)

/-- **Value hypothesis** (the shape of the weak sources): if a child `k` of a bump child `j` has
`o(k) = ψ_w(0)` with `w ≠ 0`, then `j` is the only child, `k` is its first child, and the components of
`v(P_1 i)` are countable (L9 網羅で 3256 件、例外 0). -/
def BumpWeakShape (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ j ∈ children M i, col M j = bump M i →
    ∀ k ∈ children M j, (∃ w, w ≠ z ∧ ρ.o k = psi w z z) →
      children M i = [j] ∧ (children M j).head? = some k ∧ CS (vOpt ρ (par M 1 i))

@[simp] theorem sumN_nil : sumN [] = z := rfl

/-! ## 行列の段: M.take x の子 -/

/-- The children of `i` in `M` are those in `M.take x`, then possibly `x`. -/
theorem children_M_eq {M : Mat} {x : Nat} (hx : x + 1 = M.length) (i : Nat) :
    ∃ XI, children M i = children (M.take x) i ++ XI ∧ (XI = [] ∨ (XI = [x] ∧ x ∈ children M i)) := by
  by_cases hxi : x ∈ children M i
  · exact ⟨[x], by rw [children_take]; exact children_split_x hx hxi, Or.inr ⟨rfl, hxi⟩⟩
  · exact ⟨[], by rw [children_take, children_filter_x hx hxi]; simp, Or.inl rfl⟩

theorem mem_children_take {M : Mat} {x i k : Nat} (h : k ∈ children (M.take x) i) :
    k < x ∧ k ∈ children M i := by
  rw [children_take, List.mem_filter] at h
  exact ⟨by simpa using h.2, h.1⟩

/-- **The children of a changed bump-type column in `M.take x` are bump columns.** -/
theorem bump_children_take {M : Mat} {x : Nat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M)
    (hZ1 : Z1C M) {i : Nat} (hi : i < x) (he2 : entry M 2 i = 1) (hT : TopC M x i) :
    ∀ c ∈ children (M.take x) i, col M c = bump M i := by
  intro c hc
  have htop := hT.1
  unfold topped at htop
  cases hl : (children (M.take x) i).getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hc; simp at hc
  | some ℓ =>
    rw [hl] at htop
    simp only [decide_eq_true_eq] at htop
    have hlast : children (M.take x) i = (children (M.take x) i).dropLast ++ [ℓ] := by
      rw [List.dropLast_append_getLast? _ hl]
    have hall := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x)
      (Z1C_take hZ1 x) (by rw [entry_take M 2 hi]; exact he2) hlast htop c hc
    have hcx := (mem_children_take hc).1
    rwa [col_take M hcx, bump_take M hi] at hall

theorem e2_of_bump {M : Mat} {i j : Nat} (h : col M j = bump M i) : entry M 2 j = 1 := by
  have : entry M 2 j = (col M j).2.2 := rfl
  rw [this, h]; rfl

/-! ## G の段: のりしろの子 jl の子の和 -/

/-- **The `G` level.** For the last bump child `jl` of a changed column (its children in `M.take x`
change only at the last one), `G′ = Σ o′` against `G = Σ o` is in the strong relation, or weakly below
with a weak source `o(k) = ψ_w(0)` among the children of `jl`. -/
theorem g_level {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hWS : BumpWeakShape M ρ)
    {i jl : Nat} (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hjlM : jl ∈ children M i) (hjlx : jl < x) (hjlb : col M jl = bump M i)
    (hIH : ∀ k ∈ children M jl, k < x → PO ρ ρ' k ∧ PV M ρ ρ' k) :
    (∀ t ∈ (children (M.take x) jl).map ρ'.o, Single t) ∧
    (BRelS (sumN ((children (M.take x) jl).map ρ'.o)) (sumN ((children M jl).map ρ.o)) ∨
      (BWk (sumN ((children (M.take x) jl).map ρ'.o)) (sumN ((children M jl).map ρ.o)) ∧
        ∃ k ∈ children M jl, ∃ w, w ≠ z ∧ ρ.o k = psi w z z)) := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have he2jl : entry M 2 jl ≠ 0 := by rw [e2_of_bump hjlb]; simp
  have hoff := chg_off hx hC hG hC' hRk'
  obtain ⟨XJ, hXJ, hXJc⟩ := children_M_eq hx jl
  have hdec := hKD i h1 h2 jl hjlM hjlb
  rcases List.eq_nil_or_concat (children (M.take x) jl) with hnil | ⟨K0, kl, hKT⟩
  · -- no child in `M.take x`
    rw [hnil] at hXJ ⊢
    simp only [List.map_nil, List.nil_append] at hXJ ⊢
    refine ⟨by simp, ?_⟩
    rcases hXJc with rfl | ⟨rfl, hxjl⟩
    · rw [hXJ]; left; exact brelS_refl
    · rw [hXJ]
      have hox : ρ.o x = psi (ρ.v x) z z := o_of_no_counted hC (by omega) (hG.ot_v x (by omega))
        (fun c hc => by have := mem_children hc; omega)
      have hsx : Single (ρ.o x) := single_o hC hG (by omega)
      simp only [List.map_cons, List.map_nil]
      rw [sumN_singleton hsx, hox]
      by_cases hvx : ρ.v x = z
      · left; rw [hvx]
        exact Or.inl ⟨Or.inr (lhd_zero (by simp)), one_lt_E0⟩
      · right; exact ⟨⟨z_le _, Or.inl (T.z_lt_psi _ _ _)⟩, x, by simp, _, hvx, hox⟩
  · rw [List.concat_eq_append] at hKT
    have hklT : kl ∈ children (M.take x) jl := by rw [hKT]; simp
    obtain ⟨hklx, hklM⟩ := mem_children_take hklT
    have hklL : kl < M.length := by omega
    have hklLT : kl < (M.take x).length := by omega
    obtain ⟨hPO, hPV⟩ := hIH kl hklM hklx
    have hK0lt : ∀ k ∈ K0, k < kl := by
      have hs := children_sorted (M.take x) jl
      rw [hKT] at hs
      exact fun k hk => (List.pairwise_append.mp hs).2.2 k hk kl (by simp)
    have hK0T : ∀ k ∈ K0, k ∈ children (M.take x) jl := fun k hk => by rw [hKT]; simp [hk]
    have hsame : ∀ k ∈ K0, ρ'.o k = ρ.o k := by
      intro k hk
      obtain ⟨hkx', hkM⟩ := mem_children_take (hK0T k hk)
      apply (hoff k hkx').1
      intro hCk
      exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB he2jl hkM hklT (hK0lt k hk) hCk (Anc0.refl k)
    have hchM : children M jl = K0 ++ [kl] ++ XJ := by rw [hXJ, hKT]
    rw [hchM] at hdec
    simp only [List.map_append, List.map_cons, List.map_nil] at hdec
    have hmapT : (children (M.take x) jl).map ρ'.o = K0.map ρ.o ++ [ρ'.o kl] := by
      rw [hKT, List.map_append, List.map_singleton]
      congr 1; exact List.map_congr_left hsame
    have hlekl : ρ'.o kl ≤ ρ.o kl := hPO.1.elim (fun h => h.le) (fun h => DRelO.le (Or.inr h.1))
    have hsM : ∀ k ∈ children M jl, Single (ρ.o k) := fun k hk => single_o hC hG (mem_children hk).2
    have hsAll : ∀ t ∈ K0.map ρ.o ++ [ρ.o kl] ++ XJ.map ρ.o, Single t := by
      intro t ht
      have : t ∈ (children M jl).map ρ.o := by rw [hchM]; simpa using ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp this
      exact hsM k hk
    have hp1 := List.pairwise_append.mp hdec
    have hp0 := List.pairwise_append.mp hp1.1
    have hsK0 : ∀ t ∈ K0.map ρ.o, Single t := fun t ht => hsAll t (by simp [ht])
    have hsT : ∀ t ∈ K0.map ρ.o ++ [ρ'.o kl], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hsK0 t ht
      · simp at ht; rw [ht]; exact hPO.2
    have eG' : sumN (K0.map ρ.o ++ [ρ'.o kl]) = app (sumN (K0.map ρ.o)) (ρ'.o kl) :=
      sumN_snoc_dec hsT (List.pairwise_append.mpr ⟨hp0.1, by simp, fun a ha b hb => by
        simp at hb; rw [hb]; exact le_trans hlekl (hp0.2.2 a ha _ (by simp))⟩)
    have eG : sumN (K0.map ρ.o ++ [ρ.o kl] ++ XJ.map ρ.o) =
        app (app (sumN (K0.map ρ.o)) (ρ.o kl)) (sumN (XJ.map ρ.o)) := by
      rw [sumN_append_dec hsAll hdec, sumN_snoc_dec (fun t ht => hsAll t (List.mem_append_left _ ht)) hp1.1]
    refine ⟨by rw [hmapT]; exact hsT, ?_⟩
    rw [hmapT, hchM]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [eG', eG]
    by_cases hK0 : K0 = []
    · subst hK0
      simp only [List.map_nil, sumN_nil, app_z]
      obtain ⟨y0, hy0⟩ := o_psi_sub hC hklL
      rw [sf_ot (hG.ot_v kl hklL)] at hy0
      rw [hy0]
      simp only [app_psi, app_z]
      by_cases hv : ρ'.v kl = ρ.v kl
      · obtain ⟨y1, hy1⟩ := o_psi_sub hC' hklLT
        rw [sf_ot hPV.2.1, hv] at hy1
        rcases hPO.1 with hl | ⟨⟨w1, w2, X, e1, e2, hWk⟩, _⟩
        · left
          rw [hy1, hy0] at hl
          rw [hy1]
          exact brelS_single_same _ hl (hy1 ▸ hPO.2.1)
        · exfalso
          rw [hy1] at e1; rw [hy0] at e2
          simp only [psi.injEq] at e1 e2
          rw [← e1.1, ← e2.1] at hWk
          exact lt_irrefl' _ hWk.1
      · have hCk : ChgX M x false kl := by
          by_contra hn; exact hv ((hoff kl hklx).2 hn)
        have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl hklx
        have ho' : ρ'.o kl = psi (ρ'.v kl) z z := o_of_no_counted hC' hklLT hPV.2.1 hT.2.1
        have he1 : entry M 1 kl ≠ 0 := by
          intro he; apply hv
          rw [v_z_of_e1 hC hklL he, v_z_of_e1 hC' hklLT (by rw [entry_take M 1 hklx]; exact he)]
        have hv'z : ρ'.v kl ≠ z := v_ne_z_of_e1 hC' hklLT (by rw [entry_take M 1 hklx]; exact he1)
        rw [ho']
        rcases hPV.1 with hl | ⟨hWk, hnc⟩
        · left; exact brelS_fix hl (one_le_of_ne_z hv'z)
        · right
          refine ⟨bwk_fix (le_trans (psi_le_psi_z (le_of_lt hWk.1)) (psi_le_psi_rest (z_le _)))
            hWk.2.2.1 hWk.2.1, kl, by simp, ρ.v kl, ?_, o_of_no_counted hC hklL (hG.ot_v kl hklL) hnc⟩
          intro hz; rw [hz] at hWk; exact T.not_lt_z _ hWk.1
    · have hS0 : sumN (K0.map ρ.o) ≠ z := sumN_ne_z hsK0 hp0.1 (by simpa using hK0)
      rcases hPO.1 with hl | ⟨⟨w1, w2, X, _, e2, hWk⟩, ⟨w, hw⟩⟩
      · left; exact brelS_app_same hS0 hl _
      · exfalso
        rw [hw] at e2
        simp only [psi.injEq] at e2
        have hw2 : w ≠ z := by
          rw [e2.1]; intro hz; rw [hz] at hWk; exact T.not_lt_z _ hWk.1
        obtain ⟨_, hhead, _⟩ := hWS i h1 h2 jl hjlM hjlb kl hklM ⟨w, hw2, hw⟩
        rw [hchM] at hhead
        obtain ⟨k0, K0', rfl⟩ := List.exists_cons_of_ne_nil hK0
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hhead
        have := hK0lt k0 (by simp)
        omega

end Ytosk
