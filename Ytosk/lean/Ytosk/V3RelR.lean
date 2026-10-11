/-
**HardArg の順序数の核: ◁ から「b より小さい成分」を除いた関係 `RelR` と Buchholz の補題 3.4。**

`RelR q b A`: 段 u ≤ q と b < c ≤ A のすべての c で、G_u b の元は b より小さいか、
G°_u c = {0} ∪ G_u c か G_u q の元以下。Buchholz（1986）の b ◁_z A で、z の役を「b より小さいもの」と
親の添字 q の成分にしたもの。

- `closed_of_relR`（補題 3.4 の形）: b ≤ A、`RelR q b A`、G_q A < A、G_q q < b なら G_q b < b。
  証明は 3.4 と同じ: b 以上の成分のうち大きさが最小のもの g を試す元にとる。
- `hard_of_relR`: 落とす補題の難しい場合（`HardArg`）の結論 comps_a y′ ≤ H(s, y′) は、
  `RelR a (H s y′) (H s y)` と古い枠の標準形 ψ_a(H(s, y)) から出る。

純粋な枠 1 段の仮定（◁・標準形・高い部分の違い）だけでは HardArg は偽（desc.md の反例
a = 0、s = 1、y = ψ_2(Ω_1)、y′ = ψ_2(ψ_0(ψ_2(Ω_1)))）。`RelR` は変化の鎖にそって運ぶ。
-/
import Ytosk.V3DropStrong

namespace Ytosk

open T

/-- **`◁` with the components below `b` exempted**, at the levels `u ≤ q`; the components of `q` also
dominate. -/
def RelR (q b A : T) : Prop :=
  ∀ u, ¬ lt q u = true → ∀ c, b < c → c ≤ A →
    ∀ g ∈ comps u b, g < b ∨ ∃ d ∈ Gc u c ++ comps u q, g ≤ d

/-- **Buchholz's Lemma 3.4 for `RelR`.** -/
theorem closed_of_relR {q b A : T} (hbA : b ≤ A) (hR : RelR q b A)
    (hA : ∀ g ∈ comps q A, g < A) (hq : ∀ d ∈ comps q q, d < b) :
    ∀ g ∈ comps q b, g < b := by
  rcases (le_iff _ _).mp hbA with hbA | rfl
  swap
  · exact hA
  have hq0 : ¬ lt q q = true := lt_irrefl' q
  -- strong induction on the size of the component
  have key : ∀ n, ∀ g ∈ comps q b, size g < n → g < b := by
    intro n
    induction n with
    | zero => intro g _ h; omega
    | succ n ih =>
      intro g hg hn
      by_contra hgb
      have hbg : b ≤ g := not_lt.mp hgb
      have hbg' : b < g := by
        rcases (le_iff _ _).mp hbg with h | h
        · exact h
        · exfalso; have := size_comps hg; rw [← h] at this; omega
      have hz : ∀ d, g ≤ d → d = z → False := by
        intro d hgd hd; subst hd
        exact absurd (lt_of_lt_of_le hbg' hgd) (T.not_lt_z _)
      -- the test `A`: `g < A`
      have hgA : g < A := by
        rcases hR q hq0 A hbA (le_refl _) g hg with h | ⟨d, hd, hgd⟩
        · exact absurd h hgb
        · simp only [Gc, List.mem_append, List.mem_cons] at hd
          rcases hd with (rfl | hd) | hd
          · exact (hz _ hgd rfl).elim
          · exact lt_of_le_of_lt hgd (hA d hd)
          · exact absurd (lt_of_le_of_lt hgd (hq d hd)) hgb
      -- the test `g` itself
      rcases hR q hq0 g hbg' (le_of_lt hgA) g hg with h | ⟨d, hd, hgd⟩
      · exact hgb h
      · simp only [Gc, List.mem_append, List.mem_cons] at hd
        rcases hd with (rfl | hd) | hd
        · exact hz _ hgd rfl
        · have hdb : d < b := ih d (comps_trans hg d hd) (by have := size_comps hd; omega)
          exact hgb (lt_of_le_of_lt hgd hdb)
        · exact hgb (lt_of_le_of_lt hgd (hq d hd))
  exact fun g hg => key _ g hg (Nat.lt_succ_self _)

/-- The components of `y` at a level `a ≤ s` are components of `H s y` or `y` itself. -/
theorem comps_y_sub_H {a s y : T} (hc : isOT (psi s y z) = true) (has : ¬ lt s a = true) :
    ∀ g ∈ comps a y, g ∈ comps a (H s y) ∨ (H s y = y) := by
  intro g hg
  rw [H_eq hc]
  have ey := split_app (psi (succ s) z z) y
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · right; rw [if_pos hlo, app_z_right]; rw [hlo, app_z_right] at ey; exact ey
  · left
    rw [if_neg hlo, comps_app, comps_psi_z_of_ge has]
    simp [hg]

/-- **The hard case from `RelR`**: if the new state `H s y′` is in the relation `RelR a` with the old state
`H s y` and `ψ_a(H(s, y))` is standard, then the components of `y′` at the level `a` are at most `H s y′`. -/
theorem hard_of_relR {a s y y' : T} (hc' : isOT (psi s y' z) = true) (has : lt a s = true)
    (haot : isOT a = true) (hot : isOT (psi a (H s y) z) = true) (hle : H s y' ≤ H s y)
    (hR : RelR a (H s y') (H s y)) :
    ∀ g ∈ comps a y', g ≤ H s y' := by
  have hA : ∀ g ∈ comps a (H s y), g < H s y := ((isOT_psi_iff).mp hot).2.2.2.2
  have hq : ∀ d ∈ comps a a, d < H s y' := by rw [comps_self_nil haot]; simp
  have hcl := closed_of_relR hle hR hA hq
  have hsa : ¬ lt s a = true := fun h => lt_irrefl' _ (lt_trans (show a < s from has) h)
  intro g hg
  rcases comps_y_sub_H hc' hsa g hg with h | h
  · exact le_of_lt (hcl g h)
  · rw [← h] at hg; exact le_of_lt (hcl g hg)

/-! ## 一般の補題 -/

theorem relR_refl (q b : T) : RelR q b b :=
  fun _ _ c h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

/-- **Changing the parent subscript**: a relation with the components of `p` as extra dominators gives one
with those of `q ≤ p`, when the components of `p` are below `b` or dominated by those of `q`. -/
theorem relR_of_le_q {p q b A : T} (hqp : ¬ lt p q = true) (hR : RelR p b A)
    (hconv : ∀ u, ¬ lt q u = true → ∀ d ∈ comps u p, d < b ∨ ∃ d' ∈ comps u q, d ≤ d') : RelR q b A := by
  intro u hu c h1 h2 g hg
  have hpu : ¬ lt p u = true := by
    intro h
    have hq : q ≤ p := not_lt.mp hqp
    exact hu (lt_of_le_of_lt hq h)
  rcases hR u hpu c h1 h2 g hg with h | ⟨d, hd, hgd⟩
  · exact Or.inl h
  · rcases List.mem_append.mp hd with hd | hd
    · exact Or.inr ⟨d, List.mem_append_left _ hd, hgd⟩
    · rcases hconv u hu d hd with h | ⟨d', hd', hdd'⟩
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩

theorem gc_app_left {u P c0 : T} : ∀ d ∈ comps u P, d ∈ Gc u (app P c0) := by
  intro d hd
  unfold Gc; rw [comps_app]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)

theorem gc_app_right {u P c0 : T} : ∀ d ∈ Gc u c0, d ∈ Gc u (app P c0) := by
  intro d hd
  unfold Gc at hd ⊢
  rcases List.mem_cons.mp hd with rfl | hd
  · exact List.mem_cons_self
  · rw [comps_app]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hd)

/-- **`◁` after a common prefix gives `RelR`** (no exemption needed). -/
theorem relR_prefix_lhd {q P b0 A0 : T} (h : Lhd z b0 A0) : RelR q (app P b0) (app P A0) := by
  intro u _ c h1 h2 g hg
  obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
  · obtain ⟨d, hd, hgd⟩ := h.2 u c0 hc1 hc2 g hg
    right
    refine ⟨d, List.mem_append_left _ ?_, hgd⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact gc_app_right d (List.mem_cons_of_mem _ hd)
    · simp [Gc, comps] at hd; subst hd; exact gc_app_right _ List.mem_cons_self

theorem relR_prefix_lhdE {q P b0 A0 : T} (h : LhdE b0 A0) : RelR q (app P b0) (app P A0) := by
  rcases h with rfl | h
  · exact relR_refl _ _
  · exact relR_prefix_lhd h

/-- **Extending the top**: tests above `A` start with some `P ∈ (b, A]`. -/
theorem relR_ext_prefix {q b A P A' : T} (hR : RelR q b A) (hbP : b < P) (hPA : P ≤ A)
    (hA' : ∀ c, A < c → c ≤ A' → ∃ c0, c = app P c0) : RelR q b A' := by
  intro u hu c h1 h2 g hg
  by_cases hcA : c ≤ A
  · exact hR u hu c h1 hcA g hg
  · obtain ⟨c0, rfl⟩ := hA' c (lt_of_not_ge hcA) h2
    rcases hR u hu P hbP hPA g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · rcases List.mem_append.mp hd with hd | hd
      · refine Or.inr ⟨d, List.mem_append_left _ ?_, hgd⟩
        unfold Gc at hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact gc_app_left d hd
      · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩

/-- `H s y = y` when `y` has no part below `Ω_{s+1}`. -/
theorem H_of_lo_z {s y : T} (hc : isOT (psi s y z) = true) (hlo : (split y (psi (succ s) z z)).2 = z) :
    H s y = y := by
  rw [H_eq hc, if_pos hlo, app_z_right]
  have e := split_app (psi (succ s) z z) y
  rw [hlo, app_z_right] at e; exact e

/-- **Extending the top by domination**: every test above `A` dominates the components of `A`. -/
theorem relR_ext_dom {q b A A' : T} (hR : RelR q b A) (hb : b ≤ A)
    (hdom : ∀ u c, A < c → c ≤ A' → ∀ d ∈ Gc u A, ∃ d' ∈ Gc u c, d ≤ d') : RelR q b A' := by
  intro u hu c h1 h2 g hg
  by_cases hcA : c ≤ A
  · exact hR u hu c h1 hcA g hg
  have hAc : A < c := lt_of_not_ge hcA
  rcases (le_iff _ _).mp hb with hbA | rfl
  · rcases hR u hu A hbA (le_refl _) g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨d', hd', hdd'⟩ := hdom u c hAc h2 d hd
        exact Or.inr ⟨d', List.mem_append_left _ hd', le_trans hgd hdd'⟩
      · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩
  · obtain ⟨d', hd', hgd'⟩ := hdom u c hAc h2 g (List.mem_cons_of_mem _ hg)
    exact Or.inr ⟨d', List.mem_append_left _ hd', hgd'⟩

/-- **Raising the bottom**: the new components are below `b`, components of `b0`, or dominated by `q`. -/
theorem relR_of_sub {q b0 b A : T} (hR : RelR q b0 A) (hle : b0 ≤ b)
    (hsub : ∀ u, ¬ lt q u = true → ∀ g ∈ comps u b, g < b ∨ g ∈ comps u b0 ∨ ∃ d ∈ comps u q, g ≤ d) :
    RelR q b A := by
  intro u hu c h1 h2 g hg
  rcases hsub u hu g hg with h | h | ⟨d, hd, hgd⟩
  · exact Or.inl h
  · rcases hR u hu c (lt_of_le_of_lt hle h1) h2 g h with h' | h'
    · exact Or.inl (lt_of_lt_of_le h' hle)
    · exact Or.inr h'
  · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩

theorem split_app_hi {θ : T} : ∀ {B : T} (r : T), (∀ q ∈ summands B, ¬ q < θ) →
    split (app B r) θ = (app B (split r θ).1, (split r θ).2)
  | z, r, _ => by simp [app]
  | psi a b c, r, h => by
    simp only [app, split]
    rw [if_neg (show ¬ lt (psi a b z) θ = true from h _ (by simp [summands]))]
    rw [split_app_hi r (fun q hq => h q (by simp [summands, hq]))]

theorem split_low {θ : T} {r : T} (hr : r = z ∨ head r < θ) : split r θ = (z, r) := by
  rcases hr with rfl | hr
  · rfl
  · cases r with
    | z => rfl
    | psi a b c => simp only [split]; rw [if_pos (show lt (psi a b z) θ = true from hr)]

/-- `H p X = X` when every summand of `X` is at least `Ω_{p+1}`. -/
theorem H_all_hi {p X : T} (hX : isOT (psi p X z) = true)
    (hall : ∀ q ∈ summands X, ¬ q < psi (succ p) z z) : H p X = X :=
  H_of_lo_z hX (by
    have := split_app_hi (θ := psi (succ p) z z) (B := X) z hall
    rw [app_z_right] at this; rw [this]; rfl)

/-- `H p (P + r) = P + ψ_p(P + r)` when `P` is all high and `r ≠ 0` is low. -/
theorem H_hi_low {p P r : T} (hX : isOT (psi p (app P r) z) = true)
    (hP : ∀ q ∈ summands P, ¬ q < psi (succ p) z z) (hr : r ≠ z) (hrl : head r < psi (succ p) z z) :
    H p (app P r) = app P (psi p (app P r) z) := by
  rw [H_eq hX, split_app_hi r hP, split_low (Or.inr hrl), if_neg hr, app_z_right]

theorem head_app_low {θ L r : T} (hL : L = z ∨ head L < θ) (hr : head r < θ) (hrz : r ≠ z) :
    app L r ≠ z ∧ head (app L r) < θ := by
  rcases hL with rfl | hL
  · simpa using ⟨hrz, hr⟩
  · cases L with
    | z => simpa using ⟨hrz, hr⟩
    | psi a b c => exact ⟨by simp [app], by simpa [app, head] using hL⟩

/-- **The removed last child `x` (`o(x) = Ω_w`) only raises the top.** -/
theorem relR_tl {q p b Y0 w : T} (hR : RelR q b (H p Y0)) (hb : b ≤ H p Y0)
    (hY0 : isOT (psi p Y0 z) = true) (hY : isOT (psi p (app Y0 (psi w z z)) z) = true)
    (hge : ∀ q' ∈ summands Y0, psi w z z ≤ q') :
    RelR q b (H p (app Y0 (psi w z z))) := by
  apply relR_ext_dom hR hb
  intro u c h1 h2 d hd
  set θ := psi (succ p) z z with hθ
  by_cases hw : psi w z z < θ
  · set P := (split Y0 θ).1 with hPdef
    set L := (split Y0 θ).2 with hLdef
    have eY0 : app P L = Y0 := split_app θ Y0
    have hP : ∀ q ∈ summands P, ¬ q < θ := split_fst_ge θ Y0
    have hL : L = z ∨ head L < θ := split_snd_head θ Y0
    have eY : app Y0 (psi w z z) = app P (app L (psi w z z)) := by rw [← eY0, app_assoc]
    obtain ⟨hr0, hrl⟩ := head_app_low (r := psi w z z) hL (by simpa [head] using hw) (by simp)
    have hHY : H p (app Y0 (psi w z z)) = app P (psi p (app Y0 (psi w z z)) z) := by
      rw [eY] at hY ⊢; exact H_hi_low hY hP hr0 hrl
    rw [hHY] at h2
    have hHY0 := H_eq hY0
    rw [← hPdef, ← hLdef] at hHY0
    by_cases hL0 : L = z
    · rw [if_pos hL0] at hHY0
      rw [hHY0] at h1 hd
      obtain ⟨c0, rfl, _, _⟩ := between_app h1 h2
      unfold Gc at hd
      rw [app_z_right] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨z, List.mem_cons_self, le_refl _⟩
      · exact ⟨d, gc_app_left d hd, le_refl _⟩
    · rw [if_neg hL0] at hHY0
      rw [hHY0] at h1 hd
      obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
      obtain ⟨W, c1, rfl, hW1, hW2⟩ := between_psi hc1 hc2
      unfold Gc at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨z, List.mem_cons_self, le_refl _⟩
      rw [comps_app] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ⟨d, gc_app_left d hd, le_refl _⟩
      simp only [comps, List.mem_append] at hd
      rcases hd with hd | hd
      swap
      · simp at hd
      split at hd
      · simp at hd
      rename_i hpu
      have hmem : ∀ e ∈ W :: (comps u W ++ comps u p), e ∈ Gc u (app P (psi p W c1)) := by
        intro e he
        apply gc_app_right
        unfold Gc; apply List.mem_cons_of_mem
        simp only [comps]; rw [if_neg hpu]
        exact List.mem_append_left _ he
      simp only [List.mem_cons, List.mem_append] at hd
      rcases hd with rfl | hd | hd
      · exact ⟨W, hmem W List.mem_cons_self, hW1⟩
      · rcases (le_iff _ _).mp hW1 with hlt | rfl
        · obtain ⟨W0, rfl, _, _⟩ := between_app (A := Y0) (x := z) (by rw [app_z_right]; exact hlt) hW2
          refine ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_left _ ?_)), le_refl _⟩
          rw [comps_app]; exact List.mem_append_left _ hd
        · exact ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_left _ hd)), le_refl _⟩
      · exact ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_right _ hd)), le_refl _⟩
  · have hall : ∀ q' ∈ summands Y0, ¬ q' < θ :=
      fun q' hq' => not_lt.mpr (le_trans (not_lt.mp hw) (hge q' hq'))
    have hHY0 : H p Y0 = Y0 := H_all_hi hY0 hall
    have hallY : ∀ q' ∈ summands (app Y0 (psi w z z)), ¬ q' < θ := by
      intro q' hq'
      rw [summands_app, List.mem_append] at hq'
      rcases hq' with hq' | hq'
      · exact hall q' hq'
      · simp [summands] at hq'; subst hq'; exact hw
    rw [H_all_hi hY hallY] at h2
    rw [hHY0] at h1 hd
    obtain ⟨c0, rfl, _, _⟩ := between_app (A := Y0) (x := z) (by rw [app_z_right]; exact h1) h2
    unfold Gc at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨z, List.mem_cons_self, le_refl _⟩
    · exact ⟨d, gc_app_left d hd, le_refl _⟩

/-! ## 両方書き換える枠（子の主張から） -/

/-- A term starting with `P` is in the relation with every longer term starting with `P`. -/
theorem relR_self_prefix {q P A : T} (hA : ∀ c, P < c → c ≤ A → ∃ c0, c = app P c0) : RelR q P A := by
  intro u _ c h1 h2 g hg
  obtain ⟨c0, rfl⟩ := hA c h1 h2
  exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩

theorem prefix_tests {P e E : T} : ∀ c, app P e < c → c ≤ app P E → ∃ c0, c = app P c0 := by
  intro c h1 h2
  obtain ⟨c0, h, _, _⟩ := between_app h1 h2
  exact ⟨c0, h⟩

/-- `Ω_p < H p X` for `X ≠ 0`. -/
theorem om_lt_H {p X : T} (hX : isOT (psi p X z) = true) (hXz : X ≠ z) : psi p z z < H p X := by
  rw [H_eq hX]
  set θ := psi (succ p) z z
  by_cases hlo : (split X θ).2 = z
  · rw [if_pos hlo, app_z_right]
    have e := split_app θ X
    rw [hlo, app_z_right] at e
    have hne : (split X θ).1 ≠ z := by rw [e]; exact hXz
    have h1 := le_hi (θ := θ) (y := X) hne
    exact lt_of_lt_of_le (show psi p z z < θ from psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self p))) h1
  · rw [if_neg hlo]
    have h1 : psi p z z < psi p X z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hXz)⟩)
    refine lt_of_lt_of_le h1 ?_
    cases hP : (split X θ).1 with
    | z => exact le_refl _
    | psi a b c =>
      apply le_of_lt
      have hall := split_fst_ge θ X
      rw [hP] at hall
      have ha : ¬ psi a b z < θ := hall _ (by simp [summands])
      have : psi p X z < psi a b z := lt_of_lt_of_le (show psi p X z < θ from
        psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self p))) (not_lt.mp ha)
      simp only [app]
      exact lt_of_lt_of_le this (psi_le_psi_rest (z_le _))

/-- **Both rewrite, `p < s`**: the new and old states are all high, so the claim at the child (taken at the
parent level `p`) passes up; the components of `p` are converted by the hypothesis on `q`. -/
theorem rc_tt_gt {q p s y y' : T} (hps : lt p s = true) (hc' : isOT (psi s y' z) = true)
    (hc : isOT (psi s y z) = true) (hy' : y' ≠ z)
    (hX' : isOT (psi p (H s y') z) = true) (hY : isOT (psi p (H s y) z) = true)
    (hRcs : RelR p (H s y') (H s y)) (hqp : ¬ lt p q = true)
    (hyp : ∀ u, ¬ lt q u = true → ∀ d ∈ comps u p, d ≤ psi p z z ∨ d < H p (H s y') ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelR q (H p (H s y')) (H p (H s y)) := by
  have hθ : psi (succ p) z z ≤ psi s z z := by
    rcases (le_iff _ _).mp (succ_le_of_lt (show p < s from hps)) with h | h
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
    · rw [h]
  have hall : ∀ {w : T}, isOT (psi s w z) = true → ∀ q' ∈ summands (H s w), ¬ q' < psi (succ p) z z := by
    intro w hw q' hq'
    exact not_lt.mpr (le_trans hθ (le_trans (psi_le_psi_arg (z_le _)) (H_summands_ge hw q' hq')))
  rw [H_all_hi hX' (hall hc'), H_all_hi hY (hall hc)]
  rw [H_all_hi hX' (hall hc')] at hyp
  apply relR_of_le_q hqp hRcs
  intro u hu d hd
  rcases hyp u hu d hd with h | h | h
  · left
    refine lt_of_le_of_lt h (lt_of_lt_of_le ?_ (om_le_H hc' hy'))
    exact psi_lt_psi_z_iff.mpr (Or.inl hps)
  · exact Or.inl h
  · exact Or.inr h

theorem head_psi_lt_succ (p y : T) : head (psi p y z) < psi (succ p) z z := by
  show psi p y z < psi (succ p) z z
  exact psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self p))

/-- `H p (H p y)`: unchanged without a low part, else the high part and `ψ_p(H p y)`. -/
theorem HH_form {p y : T} (hc : isOT (psi p y z) = true) (hX : isOT (psi p (H p y) z) = true) :
    H p (H p y) = if (split y (psi (succ p) z z)).2 = z then H p y
      else app (split y (psi (succ p) z z)).1 (psi p (H p y) z) := by
  have e := H_eq hc
  split_ifs with hlo
  · rw [e, if_pos hlo, app_z_right] at hX ⊢
    exact H_all_hi hX (split_fst_ge _ y)
  · rw [e, if_neg hlo] at hX ⊢
    exact H_hi_low hX (split_fst_ge _ y) (by simp) (head_psi_lt_succ p y)

theorem y_lt_H {p y : T} (hc : isOT (psi p y z) = true) (hlo : (split y (psi (succ p) z z)).2 ≠ z) :
    y < H p y := by
  rw [H_eq hc, if_neg hlo]
  conv => lhs; rw [← split_app (psi (succ p) z z) y]
  exact app_lt_app_left _ (split_lo_lt hc hlo)

/-- Raising the bottom from `H p y′` to `hi′ + ψ_p(H p y′)` (a low part present). -/
theorem relR_HH_sub {p y' A : T} (hc' : isOT (psi p y' z) = true)
    (hlo : (split y' (psi (succ p) z z)).2 ≠ z) (hR : RelR p (H p y') A) :
    RelR p (app (split y' (psi (succ p) z z)).1 (psi p (H p y') z)) A := by
  have e := H_eq hc'
  rw [if_neg hlo] at e
  have hlt := y_lt_H hc' hlo
  have hb0 : H p y' < app (split y' (psi (succ p) z z)).1 (psi p (H p y') z) := by
    conv => lhs; rw [e]
    exact app_lt_app_left _ (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hlt⟩))
  apply relR_of_sub hR (le_of_lt hb0)
  intro u hu g hg
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · right; left; rw [e, comps_app]; exact List.mem_append_left _ hg
  · simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · rw [if_neg hu] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact Or.inl hb0
      · exact Or.inr (Or.inl hg)
      · exact Or.inr (Or.inr ⟨g, hg, le_refl _⟩)
    · simp at hg

/-- **Both rewrite, `s = p`**: the double `H` keeps the relation (at the level `p`). -/
theorem relR_HH {p y y' : T} (hc' : isOT (psi p y' z) = true) (hc : isOT (psi p y z) = true)
    (hX' : isOT (psi p (H p y') z) = true) (hY : isOT (psi p (H p y) z) = true) (hyy : y' < y)
    (hR : RelR p (H p y') (H p y)) (hL : LhdE (psi p (H p y') z) (psi p (H p y) z)) :
    RelR p (H p (H p y')) (H p (H p y)) := by
  rw [HH_form hc' hX', HH_form hc hY]
  set θ := psi (succ p) z z with hθ
  have ey' := H_eq hc'
  have ey := H_eq hc
  rcases split_mono θ hyy with hhi | ⟨hhi, hlo⟩
  · split_ifs with h1 h2 h2
    · exact hR
    · rw [if_pos h1, app_z_right] at ey'
      rw [if_neg h2] at ey
      refine relR_ext_prefix hR (P := (split y θ).1) (by rw [ey']; exact hhi)
        (by rw [ey]; exact le_app_self _ _) ?_
      intro c hc1 hc2
      rw [ey] at hc1
      exact prefix_tests c hc1 hc2
    · rw [if_pos h2, app_z_right] at ey
      rw [ey]; rw [ey] at hR
      exact relR_HH_sub hc' h1 hR
    · rw [if_neg h2] at ey
      have h1' := relR_HH_sub hc' h1 hR
      refine relR_ext_prefix h1' (P := (split y θ).1) ?_ (by rw [ey]; exact le_app_self _ _) ?_
      · exact app_lt_of_lt_hi hhi (split_fst_ge θ y) (Or.inr (head_psi_lt_succ p _))
      · intro c hc1 hc2
        rw [ey] at hc1
        exact prefix_tests c hc1 hc2
  · have hloz : (split y θ).2 ≠ z := by intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
    rw [if_neg hloz]
    by_cases h1 : (split y' θ).2 = z
    · rw [if_pos h1]
      rw [if_pos h1, app_z_right] at ey'
      rw [ey', hhi]
      apply relR_self_prefix
      intro c hc1 hc2
      exact prefix_tests (e := z) c (by rw [app_z_right]; exact hc1) hc2
    · rw [if_neg h1, hhi]
      exact relR_prefix_lhdE hL

/-! ## 古い方だけ書き換える枠（B が hi(y) の先頭部分） -/

theorem succ_le_succ' {p s : T} (h : p ≤ s) : succ p ≤ succ s := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (lt_of_le_of_lt (succ_le_of_lt h) (lt_succ_self s))
  · exact le_refl _

theorem mem_comps_one {u d : T} (h : d ∈ comps u one) : d = z := by
  unfold one at h
  simp only [comps, List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp at h
    · simpa [comps] using h
  · simp at h

theorem one_lt_om_succ (p : T) : one < psi (succ p) z z := by
  unfold one
  rw [psi_lt_psi_z_iff]; left
  exact lt_of_le_of_lt (z_le p) (lt_succ_self p)

/-- **Only the old child rewrites, `B` a prefix of `hi(y)`.** The tests start with `B`; the components of
the new child are dominated through the test `ψ_s(B + 1)` of `ψ_s(y′) ◁ ψ_s(y)`, and the components of the
subscripts `s` and `p` are bounded by hypothesis. -/
theorem rc_tn_prefix {q p B s y s' y' R : T}
    (hc : isOT (psi s y z) = true)
    (hl : Lhd z (psi s' y' z) (psi s y z))
    (hss : y' ≠ z → s' = s)
    (hn' : ¬ (lt B y' = true ∧ lt (psi p z z) (psi s' y' z) = true))
    (ht : lt B y = true ∧ lt (psi p z z) (psi s y z) = true)
    (hpre : (split y (psi (succ s) z z)).1 = app B R)
    (hX' : isOT (psi p (app B (psi s' y' z)) z) = true) (hY0 : isOT (psi p (H s y) z) = true)
    (hsubS : ∀ u, ¬ lt q u = true → ∀ g ∈ comps u s,
      g < H p (app B (psi s' y' z)) ∨ ∃ d ∈ comps u q, g ≤ d)
    (hyp : ∀ u, ¬ lt q u = true → ∀ d ∈ comps u p,
      d < H p (app B (psi s' y' z)) ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelR q (H p (app B (psi s' y' z))) (H p (H s y)) := by
  have has : p ≤ s := le_of_trig ht.2
  set c' := psi s' y' z with hc'def
  have hBhi : ∀ r ∈ summands B, ¬ r < psi (succ p) z z := by
    intro r hr h
    have h1 : ¬ r < psi (succ s) z z :=
      split_fst_ge _ y r (by rw [hpre, summands_app]; exact List.mem_append_left _ hr)
    have hθ : psi (succ p) z z ≤ psi (succ s) z z := psi_le_psi_z (succ_le_succ' has)
    exact h1 (lt_of_lt_of_le h hθ)
  -- `y′ = 0` or `y′ ≤ B`
  have hy'B : y' = z ∨ y' ≤ B := by
    by_cases hy : y' = z
    · exact Or.inl hy
    · right
      obtain rfl := hss hy
      have htr : lt (psi p z z) (psi s' y' z) = true := by
        show psi p z z < psi s' y' z
        rcases (le_iff _ _).mp has with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hy)⟩)
      exact not_lt.mp (fun h => hn' ⟨h, htr⟩)
  have hc'z : c' ≠ z := by simp [hc'def]
  have hy'lt : y' < app B c' := by
    rcases hy'B with rfl | h
    · cases B <;> simp [app, hc'def]
    · exact lt_of_le_of_lt h (lt_app_of hc'z)
  -- the form of the new state
  obtain ⟨e, hb, he⟩ : ∃ e, H p (app B c') = app B e ∧
      ((e = c' ∧ ¬ c' < psi (succ p) z z) ∨ (e = psi p (app B c') z ∧ c' < psi (succ p) z z)) := by
    by_cases hcθ : c' < psi (succ p) z z
    · exact ⟨_, H_hi_low hX' hBhi hc'z (by simpa [hc'def, head] using hcθ), Or.inr ⟨rfl, hcθ⟩⟩
    · refine ⟨c', H_all_hi hX' ?_, Or.inl ⟨rfl, hcθ⟩⟩
      intro r hr; rw [summands_app] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hBhi r hr
      · simp [summands, hc'def] at hr; rw [hr]; exact hcθ
  -- the form of the old state
  have eH := H_eq hc
  have ey : y = app B (app R (split y (psi (succ s) z z)).2) := by
    rw [← app_assoc, ← hpre]; exact (split_app _ y).symm
  obtain ⟨E, hA⟩ : ∃ E, H p (H s y) = app B E := by
    rcases (le_iff _ _).mp has with hps | rfl
    · have hθ : psi (succ p) z z ≤ psi s z z := by
        rcases (le_iff _ _).mp (succ_le_of_lt hps) with h | h
        · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
        · rw [h]
      have hall : ∀ r ∈ summands (H s y), ¬ r < psi (succ p) z z := fun r hr =>
        not_lt.mpr (le_trans hθ (le_trans (psi_le_psi_arg (z_le _)) (H_summands_ge hc r hr)))
      rw [H_all_hi hY0 hall, eH, hpre, app_assoc]; exact ⟨_, rfl⟩
    · rw [HH_form hc hY0]
      split_ifs
      · rw [eH, hpre, app_assoc]; exact ⟨_, rfl⟩
      · rw [hpre, app_assoc]; exact ⟨_, rfl⟩
  rw [hb, hA]
  rw [hb] at hsubS hyp
  -- the test `ψ_s(B + 1)`
  have hRne : app R (split y (psi (succ s) z z)).2 ≠ z := by
    intro h; rw [h, app_z_right] at ey
    have := ht.1; rw [← ey] at this; exact lt_irrefl' _ this
  have hone : app B one ≤ y := by
    rw [ey]; exact app_le_app_left B (one_le_of_ne_z hRne)
  have htest : c' < psi s (app B one) z := by
    rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨rfl, _⟩
    · exact psi_lt_psi_z_iff.mpr (Or.inl h)
    · rcases hy'B with rfl | h
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, by cases B <;> simp [app, one]⟩)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt h (lt_app_of (by simp [one]))⟩)
  have htest2 : psi s (app B one) z ≤ psi s y z := psi_le_psi_arg hone
  have hone_e : one < e := by
    rcases he with ⟨rfl, hcθ⟩ | ⟨rfl, _⟩
    · exact lt_of_lt_of_le (one_lt_om_succ p) (not_lt.mp hcθ)
    · unfold one
      rcases lt_trichotomy' z p with h | rfl | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le _) (lt_app_of hc'z)⟩)
      · exact absurd h (T.not_lt_z _)
  have hb1 : app B one < app B e := app_lt_app_left B hone_e
  intro u hu cst h1 h2 g hg
  obtain ⟨c0, rfl, _, _⟩ := between_app h1 h2
  have hz : ∀ g, g ≤ z → ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d :=
    fun g h => ⟨z, List.mem_append_left _ List.mem_cons_self, h⟩
  have key : ∀ g ∈ comps u c', g < app B e ∨ ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d := by
    intro g hg
    obtain ⟨d, hd, hgd⟩ := hl.2 u _ htest htest2 g hg
    rcases List.mem_append.mp hd with hd | hd
    · simp only [comps, List.mem_append] at hd
      rcases hd with hd | hd
      · split at hd
        · simp at hd
        simp only [List.mem_cons, List.mem_append] at hd
        rcases hd with rfl | hd | hd
        · exact Or.inl (lt_of_le_of_lt hgd hb1)
        · rw [comps_app] at hd
          rcases List.mem_append.mp hd with hd | hd
          · exact Or.inr ⟨d, List.mem_append_left _ (gc_app_left d hd), hgd⟩
          · rw [mem_comps_one hd] at hgd; exact Or.inr (hz g hgd)
        · rcases hsubS u hu d hd with h | ⟨d', hd', hdd'⟩
          · exact Or.inl (lt_of_le_of_lt hgd h)
          · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩
      · simp at hd
    · simp [Gc, comps] at hd; subst hd; exact Or.inr (hz g hgd)
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
  rcases he with ⟨rfl, _⟩ | ⟨rfl, hcθ⟩
  · exact key g hg
  · simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · left
        apply app_lt_app_left
        have hs'p : s' ≤ p := by
          have := lt_om_iff.mp hcθ
          rcases this with h | h
          · simp [hc'def] at h
          · simpa [lev, hc'def] using lt_succ_iff.mp h
        rcases (le_iff _ _).mp hs'p with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hy'lt⟩)
      · rw [comps_app] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
        · exact key g hg
      · rcases hyp u hu g hg with h | ⟨d', hd', hdd'⟩
        · exact Or.inl h
        · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩
    · simp at hg

/-! ## 新旧とも書き換えない枠 -/

/-- **Neither child rewrites.** `X′ = B + c′`, `Y₀ = B + c`. Below `Ω_{p+1}` the parent relation `hN` gives
the claim after the high part of `B`; above, the tests start with `B` and the child relation `hchild`
dominates the components of `c′`. -/
theorem rc_nn {q p B s y s' y' : T}
    (hc'c : psi s' y' z < psi s y z) (hBc : ∀ r ∈ summands B, psi s y z ≤ r)
    (hX' : isOT (psi p (app B (psi s' y' z)) z) = true) (hY0 : isOT (psi p (app B (psi s y z)) z) = true)
    (hN : LhdE (psi p (app B (psi s' y' z)) z) (psi p (app B (psi s y z)) z))
    (hchild : ∀ c0, psi s' y' z < c0 → c0 ≤ psi s y z → ∀ u, ∀ g ∈ comps u (psi s' y' z),
      g < app B (psi s' y' z) ∨ ∃ d ∈ Gc u c0, g ≤ d)
    (hc'p : psi s' y' z < psi (succ p) z z → psi s' y' z < psi p (app B (psi s' y' z)) z)
    (hyp : ∀ u, ¬ lt q u = true → ∀ d ∈ comps u p,
      d < H p (app B (psi s' y' z)) ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelR q (H p (app B (psi s' y' z))) (H p (app B (psi s y z))) := by
  set θ := psi (succ p) z z with hθ
  set c := psi s y z with hcdef
  set c' := psi s' y' z with hc'def
  by_cases hcθ : c < θ
  · -- below `Ω_{p+1}`: after the high part of `B`
    have hc'θ : c' < θ := lt_trans hc'c hcθ
    set P := (split B θ).1
    set L := (split B θ).2
    have eB : app P L = B := split_app θ B
    have hP : ∀ r ∈ summands P, ¬ r < θ := split_fst_ge θ B
    have hL : L = z ∨ head L < θ := split_snd_head θ B
    have hform : ∀ {t : T}, t = psi s' y' z ∨ t = psi s y z → t < θ → isOT (psi p (app B t) z) = true →
        H p (app B t) = app P (psi p (app B t) z) := by
      intro t ht htθ hot
      have ht0 : t ≠ z := by rcases ht with rfl | rfl <;> simp
      have htl : head t < θ := by rcases ht with rfl | rfl <;> simpa [head] using htθ
      obtain ⟨hr0, hrl⟩ := head_app_low hL htl ht0
      have e : app B t = app P (app L t) := by rw [← eB, app_assoc]
      rw [e] at hot ⊢
      exact H_hi_low hot hP hr0 hrl
    rw [hform (Or.inl rfl) hc'θ hX', hform (Or.inr rfl) hcθ hY0]
    exact relR_prefix_lhdE hN
  · -- above: `B` is all high and `H p (B + c) = B + c`
    have hcθ' : θ ≤ c := not_lt.mp hcθ
    have hBhi : ∀ r ∈ summands B, ¬ r < θ := fun r hr => not_lt.mpr (le_trans hcθ' (hBc r hr))
    have hallY : ∀ r ∈ summands (app B c), ¬ r < θ := by
      intro r hr; rw [summands_app] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hBhi r hr
      · simp [summands, hcdef] at hr; rw [hr]; exact hcθ
    rw [H_all_hi hY0 hallY]
    -- the tests start with `B` and their tail is above `c′`
    have hdomc' : ∀ u (c0 : T), c' < c0 → c0 ≤ c → ∀ g ∈ comps u c',
        g < app B c' ∨ ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d := by
      intro u c0 h1 h2 g hg
      rcases hchild c0 h1 h2 u g hg with h | ⟨d, hd, hgd⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_append_left _ (gc_app_right d hd), hgd⟩
    by_cases hc'θ : c' < θ
    · have hc'z : c' ≠ z := by simp [hc'def]
      have hb : H p (app B c') = app B (psi p (app B c') z) :=
        H_hi_low hX' hBhi hc'z (by simpa [hc'def, head] using hc'θ)
      rw [hb]; rw [hb] at hyp
      have hc'p' := hc'p hc'θ
      have hXb : app B c' < app B (psi p (app B c') z) := app_lt_app_left B hc'p'
      intro u hu cst h1 h2 g hg
      obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
      have hc0 : c' < c0 := lt_trans hc'p' hc1
      rw [comps_app] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · split at hg
        · simp at hg
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact Or.inl hXb
        · rw [comps_app] at hg
          rcases List.mem_append.mp hg with hg | hg
          · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
          · rcases hdomc' u c0 hc0 hc2 g hg with h | h
            · exact Or.inl (lt_trans h hXb)
            · exact Or.inr h
        · rcases hyp u hu g hg with h | ⟨d', hd', hdd'⟩
          · exact Or.inl h
          · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩
      · simp at hg
    · have hallX : ∀ r ∈ summands (app B c'), ¬ r < θ := by
        intro r hr; rw [summands_app] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hBhi r hr
        · simp [summands, hc'def] at hr; rw [hr]; exact hc'θ
      rw [H_all_hi hX' hallX]
      intro u hu cst h1 h2 g hg
      obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
      rw [comps_app] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
      · exact hdomc' u c0 hc1 hc2 g hg

end Ytosk
