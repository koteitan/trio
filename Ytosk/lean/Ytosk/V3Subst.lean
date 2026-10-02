/-
**添字の置き換え σ（V を V′ に深く替える）。**

t = 2 の M[n] の写しの列 x + a と M[n − 1] の r + a の値の関係（実測: C′ の t = 2 の 3000 行列 × n = 2..4 で例外 0）。
V = v(r)、V′ = v_N(x′)、V < V′。

- f(s) = V′ + σ(s − V)（s ≥ V、s − V = sub s V。f(V) = V′）。
- σ(0) = 0、σ(ψ_s(y) + c) = ψ_{f(s)}(σ y) + σ c（V < s のとき）、ψ_s(y) + σ c（s ≤ V のとき。y の中には入らない）。

守られた列（行 1 の祖先に r がある）は v_N = f(v_P)、o_N = ψ_{f(s)}(σ y)（o_P = ψ_s(y)）、守られない列は等しい。
値だけの関数では書けない（V = 0 で e1 = 0 の列の下の守られない値が守られた値と一致する）。「s ≤ V の項の中に
入らない」がちょうどその区別になる。

この節は行列によらない項の補題: σ は加数ごと、標準形の上で順序を保つ埋め込み、t ≤ σ t、標準形を保つ、
和・last・sumN・ω・sp と交換する。
-/
import Ytosk.SP
import Ytosk.TwoRow

namespace Ytosk

open T

/-! ## 大きさ -/

theorem size_sub_le : ∀ x y : T, size (sub x y) ≤ size x
  | z, _ => by simp [sub, size]
  | psi a b c, z => by simp [sub]
  | psi a b c, psi d e f => by
    simp only [sub]
    split
    · exact Nat.le_refl _
    · have := size_sub_le c f; simp [size]; omega

/-! ## 定義 -/

/-- **The substitution `σ`**: subscripts `s > V` become `V′ + σ(s − V)`; summands with `s ≤ V` are kept whole. -/
def sh (V V' : T) : T → T
  | z => z
  | psi s y c =>
    if lt V s = true then psi (add V' (sh V V' (sub s V))) (sh V V' y) (sh V V' c)
    else psi s y (sh V V' c)
termination_by t => size t
decreasing_by
  all_goals (have := size_sub_le s V; simp only [size]; omega)

/-- **The subscript map** `f(s) = V′ + σ(s − V)`. -/
def shf (V V' s : T) : T := add V' (sh V V' (sub s V))

section
variable {V V' : T}

@[simp] theorem sh_z : sh V V' z = z := by rw [sh]

theorem sh_psi_gt {s y c : T} (h : V < s) :
    sh V V' (psi s y c) = psi (shf V V' s) (sh V V' y) (sh V V' c) := by
  rw [sh, if_pos (show lt V s = true from h)]; rfl

theorem sh_psi_le {s y c : T} (h : ¬ V < s) :
    sh V V' (psi s y c) = psi s y (sh V V' c) := by
  rw [sh, if_neg (show ¬ lt V s = true from h)]

/-- `σ` acts summand by summand. -/
theorem sh_psi_app (s y c : T) : sh V V' (psi s y c) = app (sh V V' (psi s y z)) (sh V V' c) := by
  by_cases h : V < s
  · rw [sh_psi_gt h, sh_psi_gt h]; simp
  · rw [sh_psi_le h, sh_psi_le h]; simp

theorem sh_single (s y : T) : ∃ a b, sh V V' (psi s y z) = psi a b z := by
  by_cases h : V < s
  · rw [sh_psi_gt h, sh_z]; exact ⟨_, _, rfl⟩
  · rw [sh_psi_le h, sh_z]; exact ⟨_, _, rfl⟩

theorem sh_ne_z {t : T} (h : t ≠ z) : sh V V' t ≠ z := by
  cases t with
  | z => exact absurd rfl h
  | psi s y c =>
    by_cases hs : V < s
    · rw [sh_psi_gt hs]; simp
    · rw [sh_psi_le hs]; simp

theorem sh_eq_z_iff {t : T} : sh V V' t = z ↔ t = z :=
  ⟨fun h => by by_contra hne; exact sh_ne_z hne h, fun h => by subst h; simp⟩

theorem shf_self : shf V V' V = V' := by
  have : sub V V = z := by
    induction V with
    | z => rfl
    | psi a b c _ _ ihc =>
      simp only [sub]; rw [if_neg (show ¬ lt (psi a b z) (psi a b z) = true from lt_irrefl' _)]; exact ihc
  simp [shf, this]

theorem sh_one : sh V V' one = one := by
  rw [one, sh_psi_le (T.not_lt_z V)]; simp

end

/-! ## `sub` の分解（行列によらない） -/

theorem sub_z_right : ∀ x : T, sub x z = x
  | z => rfl
  | psi _ _ _ => rfl

theorem sub_psi_psi (a b c d e f : T) :
    sub (psi a b c) (psi d e f) = if psi d e z < psi a b z then psi a b c else sub c f := by
  simp only [sub, lt_iff_lt]

theorem sub_psi_self (a b c f : T) : sub (psi a b c) (psi a b f) = sub c f := by
  rw [sub_psi_psi, if_neg (lt_irrefl' _)]

/-- `sub x y` is a suffix of `x`. -/
theorem sub_suffix : ∀ x y : T, ∃ Q, x = app Q (sub x y)
  | z, _ => ⟨z, by simp [sub]⟩
  | psi a b c, z => ⟨z, by simp [sub]⟩
  | psi a b c, psi d e f => by
    simp only [sub]
    split
    · exact ⟨z, by simp⟩
    · obtain ⟨Q, hQ⟩ := sub_suffix c f
      exact ⟨psi a b Q, by simp [← hQ]⟩

theorem isOT_sub_sfx {x : T} (hx : isOT x = true) (y : T) : isOT (sub x y) = true := by
  obtain ⟨Q, hQ⟩ := sub_suffix x y
  rw [hQ] at hx; exact isOT_app_right hx

theorem head_sub_le {x : T} (hx : isOT x = true) (y : T) : head (sub x y) ≤ head x := by
  obtain ⟨Q, hQ⟩ := sub_suffix x y
  generalize hS : sub x y = S at hQ
  cases S with
  | z => exact z_le _
  | psi a b c =>
    have hm : psi a b z ∈ summands x := by
      rw [hQ, summands_app]; simp [summands]
    exact summands_le_head hx _ hm

/-- Lexicographic `≤` from the parts. -/
theorem psi_le_psi_of {a b c a' b' c' : T}
    (h : a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c ≤ c')))) : psi a b c ≤ psi a' b' c' := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inl h)
  · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩))
  · rcases (le_iff _ _).mp h with h | rfl
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
    · exact le_refl _

/-- From `psi d e f ≤ psi a b c` and equal heads: `f ≤ c`. -/
theorem rest_le_of_le_head {a b c d e f : T} (h : psi d e f ≤ psi a b c)
    (hh : ¬ psi d e z < psi a b z) : d = a ∧ e = b ∧ f ≤ c := by
  rw [psi_lt_psi_z_iff] at hh
  rcases (le_iff _ _).mp h with h1 | h1
  · rw [T.psi_lt_psi] at h1
    rcases h1 with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
    · exact absurd (Or.inl h2) hh
    · exact absurd (Or.inr ⟨rfl, h2⟩) hh
    · exact ⟨rfl, rfl, le_of_lt h2⟩
  · cases h1; exact ⟨rfl, rfl, le_refl _⟩

theorem head_lt_of_le_of_lt {d e f a b c : T} (h : psi d e f ≤ psi a b c) :
    psi d e z ≤ psi a b z := by
  have := head_le_of_lt' h
  simpa [head] using this
where
  head_le_of_lt' {x y : T} (h : x ≤ y) : head x ≤ head y := by
    rcases (le_iff _ _).mp h with h | rfl
    · exact head_le_of_lt h
    · exact le_refl _

/-- `add x y = y` when the head of `x` is below that of `y`. -/
theorem add_eq_right_of_head_lt {x d e f : T} (h : head x < psi d e z) : add x (psi d e f) = psi d e f := by
  cases x with
  | z => rfl
  | psi a b c => rw [add_psi_psi, if_pos (by simpa [head] using h)]

/-- **`V + (s − V) = s`** for standard `V ≤ s`. -/
theorem add_sub_cancel' : ∀ {V s : T}, isOT V = true → isOT s = true → V ≤ s → add V (sub s V) = s
  | z, s, _, _, _ => by simp [sub_z_right]
  | psi d e f, z, _, _, h => absurd h (not_le_of_gt (T.z_lt_psi _ _ _))
  | psi d e f, psi a b c, hV, hs, h => by
    rw [sub_psi_psi]
    by_cases hh : psi d e z < psi a b z
    · rw [if_pos hh, add_psi_psi, if_pos hh]
    · rw [if_neg hh]
      obtain ⟨rfl, rfl, hfc⟩ := rest_le_of_le_head h hh
      have ih := add_sub_cancel' (isOT_rest hV) (isOT_rest hs) hfc
      generalize hX : sub c f = X at ih
      cases X with
      | z => simp at ih; subst ih; simp
      | psi g k m =>
        have hX1 : head (psi g k m) ≤ psi d e z := by
          rw [← hX]
          exact le_trans (head_sub_le (isOT_rest hs) f) (isOT_psi_iff.mp hs).2.2.2.1
        rw [add_psi_psi, if_neg (not_lt_of_ge (by simpa [head] using hX1)), ih]

/-- **`(A + Y) − V = (A − V) + Y`** for standard `V ≤ A`. -/
theorem sub_add_dist : ∀ {V A : T} (Y : T), isOT V = true → isOT A = true → V ≤ A →
    sub (add A Y) V = add (sub A V) Y
  | z, A, Y, _, _, _ => by simp [sub_z_right]
  | psi d e f, z, _, _, _, h => absurd h (not_le_of_gt (T.z_lt_psi _ _ _))
  | psi d e f, psi a b c, Y, hV, hA, h => by
    cases Y with
    | z => simp
    | psi g k m =>
      by_cases hh : psi d e z < psi a b z
      · have hsA : sub (psi a b c) (psi d e f) = psi a b c := by rw [sub_psi_psi, if_pos hh]
        rw [hsA, add_psi_psi]
        split
        · rename_i hY
          rw [sub_psi_psi, if_pos (lt_trans hh hY)]
        · rw [sub_psi_psi, if_pos hh]
      · obtain ⟨rfl, rfl, hfc⟩ := rest_le_of_le_head h hh
        rw [sub_psi_self, add_psi_psi]
        split
        · rename_i hY
          rw [sub_psi_psi, if_pos hY]
          symm; apply add_eq_right_of_head_lt
          exact lt_of_le_of_lt (le_trans (head_sub_le (isOT_rest hA) f) (isOT_psi_iff.mp hA).2.2.2.1) hY
        · rw [sub_psi_self]
          exact sub_add_dist (psi g k m) (isOT_rest hV) (isOT_rest hA) hfc

/-- **`s − V` is strictly monotone** on standard `s ≥ V`. -/
theorem sub_lt_sub : ∀ {V s t : T}, isOT V = true → isOT s = true → isOT t = true → V ≤ s → s < t →
    sub s V < sub t V
  | z, s, t, _, _, _, _, h => by simpa [sub_z_right] using h
  | psi d e f, z, _, _, _, _, h, _ => absurd h (not_le_of_gt (T.z_lt_psi _ _ _))
  | psi d e f, psi a b c, z, _, _, _, _, h => absurd h (T.not_lt_z _)
  | psi d e f, psi a b c, psi a' b' c', hV, hs, ht, hVs, hst => by
    have hht : psi a b z ≤ psi a' b' z := by simpa [head] using head_le_of_lt hst
    by_cases hh : psi d e z < psi a b z
    · have hh' : psi d e z < psi a' b' z := lt_of_lt_of_le hh hht
      rw [sub_psi_psi, sub_psi_psi, if_pos hh, if_pos hh']; exact hst
    · obtain ⟨rfl, rfl, hfc⟩ := rest_le_of_le_head hVs hh
      by_cases hh' : psi d e z < psi a' b' z
      · rw [sub_psi_self, sub_psi_psi, if_pos hh']
        apply lt_of_head_lt
        exact lt_of_le_of_lt (le_trans (head_sub_le (isOT_rest hs) f) (isOT_psi_iff.mp hs).2.2.2.1) hh'
      · have he : psi d e z = psi a' b' z := le_antisymm hht (le_of_not_gt hh')
        cases he
        rw [sub_psi_self, sub_psi_self]
        have hcc : c < c' := by
          rw [T.psi_lt_psi] at hst
          rcases hst with h | ⟨_, h⟩ | ⟨_, _, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact absurd h (lt_irrefl' _)
          · exact h
        exact sub_lt_sub (isOT_rest hV) (isOT_rest hs) (isOT_rest ht) hfc hcc

theorem sub_ne_z_of_lt {V s : T} (hV : isOT V = true) (hs : isOT s = true) (h : V < s) : sub s V ≠ z := by
  intro h0
  have := add_sub_cancel' hV hs (le_of_lt h)
  rw [h0, add_z_right] at this
  exact lt_irrefl' _ (this ▸ h)

/-! ## 順序の埋め込み -/

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V ≤ V')
include hV hV' hVV

theorem sh_lt_aux : ∀ n (a b : T), size a + size b < n → isOT a = true → isOT b = true → a < b →
    sh V V' a < sh V V' b
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, b, hn, ha, hb, hab => by
    cases b with
    | z => exact absurd hab (T.not_lt_z _)
    | psi d e f =>
      cases a with
      | z => rw [sh_z]; exact lt_of_le_of_ne (z_le _) (Ne.symm (sh_ne_z (by simp)))
      | psi s y c =>
        have hsz : ∀ x, size x ≤ size s → size x + size (sub d V) < n := by
          intro x hx; have := size_sub_le d V; simp [size] at hn; omega
        have shf_lt : V ≤ s → s < d → shf V V' s < shf V V' d := by
          intro hVs hsd
          unfold shf
          apply add_lt_add_left
          exact sh_lt_aux n _ _ (hsz _ (size_sub_le s V)) (isOT_sub_sfx (isOT_sub ha) V)
            (isOT_sub_sfx (isOT_sub hb) V) (sub_lt_sub hV (isOT_sub ha) (isOT_sub hb) hVs hsd)
        have hVf : ∀ {w : T}, isOT w = true → V < w → V < shf V V' w := by
          intro w hw hVw
          refine lt_of_le_of_lt hVV ?_
          unfold shf
          have h1 := add_lt_add_left V' (show z < sh V V' (sub w V) from
            lt_of_le_of_ne (z_le _) (Ne.symm (sh_ne_z (sub_ne_z_of_lt hV hw hVw))))
          simpa using h1
        rw [T.psi_lt_psi] at hab
        have ihy : y < e → sh V V' y < sh V V' e := fun h =>
          sh_lt_aux n y e (by simp [size] at hn; omega) (isOT_arg ha) (isOT_arg hb) h
        have ihc : c < f → sh V V' c < sh V V' f := fun h =>
          sh_lt_aux n c f (by simp [size] at hn; omega) (isOT_rest ha) (isOT_rest hb) h
        by_cases hs : V < s <;> by_cases hd : V < d
        · rw [sh_psi_gt hs, sh_psi_gt hd, T.psi_lt_psi]
          rcases hab with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
          · exact Or.inl (shf_lt (le_of_lt hs) h)
          · exact Or.inr (Or.inl ⟨rfl, ihy h⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl, ihc h⟩)
        · exfalso
          rcases hab with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
          · exact hd (lt_trans hs h)
          · exact hd hs
          · exact hd hs
        · rw [sh_psi_le hs, sh_psi_gt hd, T.psi_lt_psi]
          exact Or.inl (lt_of_le_of_lt (le_of_not_gt hs) (hVf (isOT_sub hb) hd))
        · rw [sh_psi_le hs, sh_psi_le hd, T.psi_lt_psi]
          rcases hab with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, h⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl, ihc h⟩)

/-- **`σ` is strictly monotone** on standard terms. -/
theorem sh_lt_sh {a b : T} (ha : isOT a = true) (hb : isOT b = true) (h : a < b) :
    sh V V' a < sh V V' b :=
  sh_lt_aux hV hV' hVV _ a b (Nat.lt_succ_self _) ha hb h

theorem sh_le_sh {a b : T} (ha : isOT a = true) (hb : isOT b = true) (h : a ≤ b) :
    sh V V' a ≤ sh V V' b := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (sh_lt_sh hV hV' hVV ha hb h)
  · exact le_refl _

theorem sh_lt_iff {a b : T} (ha : isOT a = true) (hb : isOT b = true) :
    sh V V' a < sh V V' b ↔ a < b := by
  refine ⟨fun h => ?_, sh_lt_sh hV hV' hVV ha hb⟩
  by_contra hn
  exact absurd h (not_lt_of_ge (sh_le_sh hV hV' hVV hb ha (le_of_not_gt hn)))

theorem sh_inj {a b : T} (ha : isOT a = true) (hb : isOT b = true) (h : sh V V' a = sh V V' b) :
    a = b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact absurd h (ne_of_lt (sh_lt_sh hV hV' hVV ha hb h1))
  · exact h1
  · exact absurd h.symm (ne_of_lt (sh_lt_sh hV hV' hVV hb ha h1))

/-- **`f` is strictly monotone** on standard `s ≥ V`. -/
theorem shf_lt_shf {s t : T} (hs : isOT s = true) (ht : isOT t = true) (hVs : V ≤ s) (h : s < t) :
    shf V V' s < shf V V' t :=
  add_lt_add_left V' (sh_lt_sh hV hV' hVV (isOT_sub_sfx hs V) (isOT_sub_sfx ht V)
    (sub_lt_sub hV hs ht hVs h))

theorem shf_lt_iff {s t : T} (hs : isOT s = true) (ht : isOT t = true) (hVs : V ≤ s) (hVt : V ≤ t) :
    shf V V' s < shf V V' t ↔ s < t := by
  refine ⟨fun h => ?_, shf_lt_shf hV hV' hVV hs ht hVs⟩
  by_contra hn
  rcases (le_iff _ _).mp (le_of_not_gt hn) with h1 | h1
  · exact absurd h (not_lt_of_gt (shf_lt_shf hV hV' hVV ht hs hVt h1))
  · subst h1; exact lt_irrefl' _ h

/-- `V′ < f(s)` for `V < s`. -/
theorem lt_shf {s : T} (hs : isOT s = true) (h : V < s) : V' < shf V V' s := by
  unfold shf
  have h1 := add_lt_add_left V' (show z < sh V V' (sub s V) from
    lt_of_le_of_ne (z_le _) (Ne.symm (sh_ne_z (sub_ne_z_of_lt hV hs h))))
  simpa using h1

theorem le_shf {s : T} (hs : isOT s = true) (h : V ≤ s) : V' ≤ shf V V' s := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (lt_shf hV hV' hVV hs h)
  · rw [shf_self]

/-! ## `t ≤ σ t` -/

theorem le_shf_of {t : T} (ht : isOT t = true) (hVt : V ≤ t)
    (ih : sub t V ≤ sh V V' (sub t V)) : t ≤ shf V V' t := by
  have hd := isOT_sub_sfx ht V
  calc t = add V (sub t V) := (add_sub_cancel' hV ht hVt).symm
    _ ≤ add V' (sub t V) := add_le_add_right _ hV' hd hVV
    _ ≤ add V' (sh V V' (sub t V)) := add_le_add_left V' ih

theorem le_sh_aux : ∀ n (t : T), size t ≤ n → isOT t = true → t ≤ sh V V' t
  | 0, t, hn, ht => by
    cases t with
    | z => simp
    | psi => simp [size] at hn
  | n + 1, t, hn, ht => by
    cases t with
    | z => simp
    | psi s y c =>
      have ihy := le_sh_aux n y (by simp [size] at hn; omega) (isOT_arg ht)
      have ihc := le_sh_aux n c (by simp [size] at hn; omega) (isOT_rest ht)
      by_cases hs : V < s
      · rw [sh_psi_gt hs]
        have ihs := le_shf_of hV hV' hVV (isOT_sub ht) (le_of_lt hs)
          (le_sh_aux n (sub s V) (by have := size_sub_le s V; simp [size] at hn; omega)
            (isOT_sub_sfx (isOT_sub ht) V))
        apply psi_le_psi_of
        rcases (le_iff _ _).mp ihs with h1 | h1
        · exact Or.inl h1
        · refine Or.inr ⟨h1, ?_⟩
          rcases (le_iff _ _).mp ihy with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨h2, ihc⟩
      · rw [sh_psi_le hs]
        exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨rfl, ihc⟩⟩)

/-- **`t ≤ σ t`.** -/
theorem le_sh {t : T} (ht : isOT t = true) : t ≤ sh V V' t :=
  le_sh_aux hV hV' hVV (size t) t (Nat.le_refl _) ht

/-- **`s ≤ f(s)`.** -/
theorem le_shf_self {s : T} (hs : isOT s = true) (h : V ≤ s) : s ≤ shf V V' s :=
  le_shf_of hV hV' hVV hs h (le_sh hV hV' hVV (isOT_sub_sfx hs V))

end

/-! ## 標準形の保存 -/

theorem isOT_of_mem_comps (u : T) : ∀ {t g : T}, isOT t = true → g ∈ comps u t → isOT g = true
  | z, _, _, h => by simp [comps] at h
  | psi v x c, g, ht, hg => by
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      · simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact isOT_arg ht
        · exact isOT_of_mem_comps u (isOT_arg ht) hg
        · exact isOT_of_mem_comps u (isOT_sub ht) hg
    · exact isOT_of_mem_comps u (isOT_rest ht) hg

theorem comps_sub_sub (u v V : T) {g : T} (hg : g ∈ comps u (sub v V)) : g ∈ comps u v := by
  obtain ⟨Q, hQ⟩ := sub_suffix v V
  rw [hQ, comps_app]; exact List.mem_append_right _ hg

/-- `add x y` keeps a prefix of `x` and then `y`. -/
theorem add_eq_app_prefix : ∀ x y : T, ∃ P, add x y = app P y ∧ ∀ q ∈ summands P, q ∈ summands x
  | z, y => ⟨z, by simp, by simp [summands]⟩
  | psi a b c, z => ⟨psi a b c, by simp, fun q hq => hq⟩
  | psi a b c, psi d e f => by
    rw [add_psi_psi]
    split
    · exact ⟨z, by simp, by simp [summands]⟩
    · obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix c (psi d e f)
      refine ⟨psi a b P, by simp [hP], ?_⟩
      intro q hq
      simp only [summands, List.mem_cons] at hq ⊢
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr (hPs q h)

/-- The summands of a standard `V′` have subscripts below `V′`. -/
theorem lev_lt_of_summand {W q : T} (hW : isOT W = true) (hq : q ∈ summands W) : lev q < W := by
  obtain ⟨s, y, rfl⟩ := mem_summands hq
  exact lt_of_lt_of_le (sub_lt s y z) (le_trans (summands_le_head hW _ hq) (head_le_self W))

theorem head_sh (V V' : T) : ∀ t : T, head (sh V V' t) = sh V V' (head t)
  | z => by simp [head]
  | psi s y c => by
    rw [sh_psi_app]
    obtain ⟨a, b, hab⟩ := sh_single (V := V) (V' := V') s y
    simp [hab, head]

/-- **`σ` fixes a standard term whose level is at most `V`.** -/
theorem sh_fix {V V' : T} : ∀ {t : T}, isOT t = true → ¬ V < lev t → sh V V' t = t
  | z, _, _ => by simp
  | psi s y c, ht, h => by
    rw [sh_psi_le (show ¬ V < s from h)]
    cases c with
    | z => simp
    | psi s' y' c' =>
      have hh : psi s' y' z ≤ psi s y z := (isOT_psi_iff.mp ht).2.2.2.1
      have hs' : s' ≤ s := lev_le_of_le hh
      have : ¬ V < lev (psi s' y' c') := fun h' => h (lt_of_lt_of_le h' hs')
      rw [sh_fix (isOT_rest ht) this]

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **The components move with `σ`** at a level `u ≥ V` (the new level is `f(u)`). -/
theorem comps_sh_aux {u : T} (hu : isOT u = true) (hVu : V ≤ u) : ∀ n (t : T), size t ≤ n → isOT t = true →
    ∀ g' ∈ comps (shf V V' u) (sh V V' t), ∃ g ∈ comps u t, g' = sh V V' g
  | 0, t, hn, _ => by
    cases t with
    | z => simp [comps]
    | psi => simp [size] at hn
  | n + 1, t, hn, ht => by
    have hVV' := le_of_lt hVV
    cases t with
    | z => simp [comps]
    | psi v x c =>
      have ihc := comps_sh_aux hu hVu n c (by simp [size] at hn; omega) (isOT_rest ht)
      have hcsub : ∀ g ∈ comps u c, g ∈ comps u (psi v x c) := by
        intro g hg; simp only [comps, List.mem_append]; exact Or.inr hg
      have hcpart : ∀ g' ∈ comps (shf V V' u) (sh V V' c), ∃ g ∈ comps u (psi v x c), g' = sh V V' g := by
        intro g' hg'; obtain ⟨g, hg, rfl⟩ := ihc g' hg'; exact ⟨g, hcsub g hg, rfl⟩
      by_cases hv : V < v
      · rw [sh_psi_gt hv]
        intro g' hg'
        simp only [comps, List.mem_append] at hg'
        rcases hg' with hg' | hg'
        · split at hg'
          · simp at hg'
          · rename_i hlt
            have hvu : ¬ v < u := fun h => hlt (shf_lt_shf hV hV' hVV' (isOT_sub ht) hu (le_of_lt hv) h)
            have hmem : ∀ g, g = x ∨ g ∈ comps u x ∨ g ∈ comps u v → g ∈ comps u (psi v x c) := by
              intro g hg
              simp only [comps, List.mem_append]
              left; rw [if_neg (show ¬ lt v u = true from hvu)]; simp only [List.mem_cons, List.mem_append]; exact hg
            simp only [List.mem_cons, List.mem_append] at hg'
            rcases hg' with rfl | hg' | hg'
            · exact ⟨x, hmem x (Or.inl rfl), rfl⟩
            · obtain ⟨g, hg, rfl⟩ := comps_sh_aux hu hVu n x (by simp [size] at hn; omega) (isOT_arg ht) g' hg'
              exact ⟨g, hmem g (Or.inr (Or.inl hg)), rfl⟩
            · -- the components of `f(v) = V′ + σ(v − V)`
              rw [show shf V V' v = add V' (sh V V' (sub v V)) from rfl] at hg'
              obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub v V))
              rw [hP, comps_app] at hg'
              have hP0 : comps (shf V V' u) P = [] := by
                apply comps_eq_nil_of_lev
                intro q hq
                exact lt_of_lt_of_le (lev_lt_of_summand hV' (hPs q hq)) (le_shf hV hV' hVV' hu hVu)
              rw [hP0, List.nil_append] at hg'
              obtain ⟨g, hg, rfl⟩ := comps_sh_aux hu hVu n (sub v V)
                (by have := size_sub_le v V; simp [size] at hn; omega) (isOT_sub_sfx (isOT_sub ht) V) g' hg'
              exact ⟨g, hmem g (Or.inr (Or.inr (comps_sub_sub u v V hg))), rfl⟩
        · exact hcpart g' hg'
      · rw [sh_psi_le hv]
        intro g' hg'
        have hvl : v < shf V V' u :=
          lt_of_le_of_lt (le_of_not_gt hv) (lt_of_lt_of_le hVV (le_shf hV hV' hVV' hu hVu))
        simp only [comps, List.mem_append] at hg'
        rcases hg' with hg' | hg'
        · rw [if_pos (show lt v (shf V V' u) = true from hvl)] at hg'; simp at hg'
        · exact hcpart g' hg'

theorem comps_sh {u t : T} (hu : isOT u = true) (hVu : V ≤ u) (ht : isOT t = true) :
    ∀ g' ∈ comps (shf V V' u) (sh V V' t), ∃ g ∈ comps u t, g' = sh V V' g :=
  comps_sh_aux hV hV' hVV hu hVu (size t) t (Nat.le_refl _) ht

theorem isOT_sh_aux : ∀ n (t : T), size t ≤ n → isOT t = true → isOT (sh V V' t) = true
  | 0, t, hn, ht => by
    cases t with
    | z => simp
    | psi => simp [size] at hn
  | n + 1, t, hn, ht => by
    have hVV' := le_of_lt hVV
    cases t with
    | z => simp
    | psi s y c =>
      by_cases hs : V < s
      · rw [sh_psi_gt hs, isOT_psi_iff]
        have hsub := isOT_sub_sfx (isOT_sub ht) V
        refine ⟨isOT_add hV' (isOT_sh_aux n _ (by have := size_sub_le s V; simp [size] at hn; omega) hsub),
          isOT_sh_aux n y (by simp [size] at hn; omega) (isOT_arg ht),
          isOT_sh_aux n c (by simp [size] at hn; omega) (isOT_rest ht), ?_, ?_⟩
        · rw [head_sh]
          have hhc : head c ≤ psi s y z := (isOT_psi_iff.mp ht).2.2.2.1
          have := sh_le_sh hV hV' hVV' (V := V) (V' := V') (isOT_head' (isOT_rest ht)) (isOT_head ht) hhc
          rwa [sh_psi_gt hs, sh_z] at this
        · intro g' hg'
          obtain ⟨g, hg, rfl⟩ := comps_sh hV hV' hVV (isOT_sub ht) (le_of_lt hs) (isOT_arg ht) g' hg'
          exact sh_lt_sh hV hV' hVV' (isOT_of_mem_comps s (isOT_arg ht) hg) (isOT_arg ht) (comps_lt ht g hg)
      · rw [sh_fix ht hs]; exact ht
where
  isOT_head' {c : T} (hc : isOT c = true) : isOT (head c) = true := by
    cases c with
    | z => rfl
    | psi => exact isOT_head hc

/-- **`σ` preserves standard form.** -/
theorem isOT_sh {t : T} (ht : isOT t = true) : isOT (sh V V' t) = true :=
  isOT_sh_aux hV hV' hVV (size t) t (Nat.le_refl _) ht

theorem isOT_shf {s : T} (hs : isOT s = true) : isOT (shf V V' s) = true :=
  isOT_add hV' (isOT_sh hV hV' hVV (isOT_sub_sfx hs V))

/-- **The root form**: `ψ_s(y)` with `V ≤ s` becomes `ψ_{f(s)}(σ y)` (for `s = V`: `ψ_{V′}(σ y)`). -/
theorem isOT_shTop {s y : T} (h : isOT (psi s y z) = true) (hVs : V ≤ s) :
    isOT (psi (shf V V' s) (sh V V' y) z) = true := by
  rw [isOT_psi_iff]
  refine ⟨isOT_shf hV hV' hVV (isOT_sub h), isOT_sh hV hV' hVV (isOT_arg h), rfl, z_le _, ?_⟩
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := comps_sh hV hV' hVV (isOT_sub h) hVs (isOT_arg h) g' hg'
  exact sh_lt_sh hV hV' (le_of_lt hVV) (isOT_of_mem_comps s (isOT_arg h) hg) (isOT_arg h) (comps_lt h g hg)

end

end Ytosk
