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

end Ytosk
