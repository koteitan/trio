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

end Ytosk
