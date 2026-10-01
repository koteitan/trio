/-
**正規化 sp の 1 段と、違いの道の持ち上げ（添字が同じ段）。**

sp a b c は c の加数 ψ_s(y) を 1 つずつ b に足す。b < y かつ ψ_s(y)… > Ω_a のときは、b を
H(s, y) = (y の Ω_{s+1} 以上の部分) + [y に低い部分があれば ψ_s(y)] に置き換える。

`frame_same`: 状態 b が共通で、次の加数が ψ_s(y_u) < ψ_s(y_w)（添字が同じ）なら、その後ろの加数が書き換えを
起こさない限り、sp の結果も真に小さい。
-/
import Ytosk.Omega

namespace Ytosk

open T

/-- The argument that replaces `b` when `ψ_s(y)` triggers in `sp`. -/
def H (s y : T) : T := add (cut (add s one) y) (sub (psi s y z) (psi s (cut (add s one) y) z))

/-- One step of `sp`: the new state after the summand `ψ_s(y)` (with the rest `c`). -/
def step (a b s y c : T) : T :=
  if lt b y = true ∧ lt (psi a z z) (psi s y c) = true then H s y else add b (psi s y z)

/-- The final state of `sp`: `sp a b c = ψ_a(spArg a b c)`. -/
def spArg (a : T) : T → T → T
  | b, z => b
  | b, psi s y c => spArg a (step a b s y c) c

theorem spArg_cons (a b s y c : T) : spArg a b (psi s y c) = spArg a (step a b s y c) c := rfl

theorem sp_eq_spArg (a : T) : ∀ b c : T, sp a b c = psi a (spArg a b c) z
  | b, z => by simp [sp, spArg]
  | b, psi s y c => by
    rw [spArg_cons]
    simp only [sp, step, H]
    by_cases h : lt b y = true ∧ lt (psi a z z) (psi s y c) = true
    · rw [if_pos h, if_pos h]; exact sp_eq_spArg a _ c
    · rw [if_neg h, if_neg h]; exact sp_eq_spArg a _ c

/-! ## 切り取り `cut` と切り分け `split` -/

theorem split_fst_of_head_lt {t : T} : ∀ {c : T}, head c < t → (split c t).1 = z
  | z, _ => rfl
  | psi a b c, h => by
    simp only [split]
    rw [if_pos (show lt (psi a b z) t = true from h)]

/-- On a standard term, `cut w` keeps the leading summands `≥ Ω_w`. -/
theorem cut_eq_split (w : T) : ∀ {y : T}, isOT y = true → cut w y = (split y (psi w z z)).1
  | z, _ => rfl
  | psi s b c, h => by
    have ih := cut_eq_split w (isOT_rest h)
    simp only [cut, split]
    by_cases h1 : lt (psi s b z) (psi w z z) = true
    · have hc : (split c (psi w z z)).1 = z := by
        apply split_fst_of_head_lt
        by_cases hcz : c = z
        · subst hcz; exact T.z_lt_psi _ _ _
        · exact lt_of_le_of_lt (isOT_psi_iff.mp h).2.2.2.1 h1
      rw [ih, hc, if_pos ⟨rfl, h1⟩, if_pos h1]
    · rw [ih, if_neg (fun h2 => h1 h2.2), if_neg h1]

/-- The lower part of the argument of a standard `ψ_s(b) + c` is below `ψ_s(b)`. -/
theorem split_lo_lt {s b c : T} (hx : isOT (psi s b c) = true)
    (hlo : (split b (psi (succ s) z z)).2 ≠ z) : (split b (psi (succ s) z z)).2 < psi s b z := by
  have hcomp := comps_lt hx
  have hss : lt s s = false := Bool.eq_false_iff.mpr (lt_irrefl' s)
  have hbpl := split_app (psi (succ s) z z) b
  have hlo1 := split_snd_head (psi (succ s) z z) b
  generalize (split b (psi (succ s) z z)) = pr at hbpl hlo1 hlo ⊢
  obtain ⟨p, lo⟩ := pr
  simp only at hbpl hlo1 hlo ⊢
  rcases hlo1 with h | h
  · exact absurd h hlo
  cases lo with
  | z => exact absurd rfl hlo
  | psi s' w c'' =>
    have hs' : s' ≤ s := by
      have : s' < succ s := by
        have h' : psi s' w z < psi (succ s) z z := h
        rw [psi_lt_psi_z_iff] at h'
        rcases h' with h' | ⟨_, h'⟩
        · exact h'
        · exact absurd h' (T.not_lt_z _)
      exact lt_succ_iff.mp this
    rw [T.psi_lt_psi]
    rcases (le_iff _ _).mp hs' with h2 | h2
    · exact Or.inl h2
    · refine Or.inr (Or.inl ⟨h2, hcomp w ?_⟩)
      rw [← hbpl, comps_app]; apply List.mem_append_right
      rw [h2]; simp [comps, hss]

/-! ## H -/

/-- `H s y` as a concatenation: the part of `y` at or above `Ω_{s+1}`, then `ψ_s(y)` if `y` has a lower
part. -/
theorem H_eq {s y : T} (hy : isOT (psi s y z) = true) :
    H s y = app (split y (psi (succ s) z z)).1
      (if (split y (psi (succ s) z z)).2 = z then z else psi s y z) := by
  have hs := isOT_sub hy
  have hb := isOT_arg hy
  have hOm : psi s y z < Om (succ s) := by
    rw [Om, psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s)
  unfold H
  rw [add_one_eq_succ hs, cut_eq_split _ hb]
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  generalize (split y (psi (succ s) z z)) = pr at hbpl hpge ⊢
  obtain ⟨p, lo⟩ := pr
  simp only at hbpl hpge ⊢
  have hpot : isOT p = true := by rw [← hbpl] at hb; exact isOT_app_left hb
  by_cases hlo : lo = z
  · subst hlo
    simp only [app_z_right] at hbpl
    subst hbpl
    have h0 : sub (psi s p z) (psi s p z) = z := by
      simp only [sub]; rw [if_neg (show ¬ lt (psi s p z) (psi s p z) = true from lt_irrefl' _)]
    rw [h0, if_pos rfl]; simp
  · have hpb : psi s p z < psi s y z := by
      rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, by rw [← hbpl]; exact lt_app_of hlo⟩
    have hsub : sub (psi s y z) (psi s p z) = psi s y z := by
      simp only [sub]; exact if_pos hpb
    rw [hsub, if_neg hlo]
    have hge : ∀ q ∈ summands p, head (psi s y z) ≤ q := fun q hq =>
      le_of_lt (lt_of_lt_of_le hOm (le_of_not_gt (hpge q hq)))
    exact add_eq_app (isOT_app_of hpot hy hge)

theorem summands_app : ∀ x y : T, summands (app x y) = summands x ++ summands y
  | z, _ => rfl
  | psi a b c, y => by simp [summands, summands_app c y]

/-- Every summand of `H s y` is at least `ψ_s(y)`. -/
theorem H_summands_ge {s y : T} (hy : isOT (psi s y z) = true) :
    ∀ q ∈ summands (H s y), psi s y z ≤ q := by
  have hOm : psi s y z < Om (succ s) := by
    rw [Om, psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s)
  intro q hq
  rw [H_eq hy, summands_app, List.mem_append] at hq
  rcases hq with hq | hq
  · exact le_of_lt (lt_of_lt_of_le hOm (le_of_not_gt (split_fst_ge _ y q hq)))
  · split at hq
    · simp [summands] at hq
    · simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hq
      rw [hq]

/-- `y ≤ H s y`. -/
theorem le_H {s y : T} (hy : isOT (psi s y z) = true) : y ≤ H s y := by
  rw [H_eq hy]
  have hbpl := split_app (psi (succ s) z z) y
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · rw [if_pos hlo]
    conv => lhs; rw [← hbpl, hlo]
  · rw [if_neg hlo]
    conv => lhs; rw [← hbpl]
    exact le_of_lt (app_lt_app_left _ (split_lo_lt hy hlo))

/-- `H s` is strictly monotone on standard arguments. -/
theorem H_lt_H {s y y' : T} (hy : isOT (psi s y z) = true) (hy' : isOT (psi s y' z) = true)
    (h : y < y') : H s y < H s y' := by
  have hOm : psi s y z < Om (succ s) := by
    rw [Om, psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s)
  rw [H_eq hy, H_eq hy']
  rcases split_mono (psi (succ s) z z) h with h1 | ⟨h1, h2⟩
  · apply lt_of_lt_of_le _ (le_app_self _ _)
    apply app_lt_of_lt h1
    intro q hq
    have hr : head (if (split y (psi (succ s) z z)).2 = z then z else psi s y z) ≤ psi s y z := by
      split
      · exact z_le _
      · exact le_refl _
    exact lt_of_le_of_lt hr (lt_of_lt_of_le hOm (le_of_not_gt (split_fst_ge _ y' q hq)))
  · rw [h1]
    apply app_lt_app_left
    have hlo' : (split y' (psi (succ s) z z)).2 ≠ z := fun h3 => by
      rw [h3] at h2; exact T.not_lt_z _ h2
    rw [if_neg hlo']
    have hyy : psi s y z < psi s y' z := by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩
    split
    · exact T.z_lt_psi _ _ _
    · exact hyy

/-! ## 和 `add` の先頭部分 -/

theorem psi_le_psi_rest {a b c c' : T} (h : c ≤ c') : psi a b c ≤ psi a b c' := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
  · exact le_refl _

/-- Adding a principal term keeps a leading part `B` of `b` and drops a rest `X` below it. -/
theorem add_prefix (s y : T) : ∀ b : T,
    ∃ B X, b = app B X ∧ X < psi s y z ∧ add b (psi s y z) = app B (psi s y z)
  | z => ⟨z, z, rfl, T.z_lt_psi _ _ _, by simp⟩
  | psi a1 b1 c1 => by
    rw [add_psi_psi]
    by_cases h1 : psi a1 b1 z < psi s y z
    · rw [if_pos h1]
      exact ⟨z, psi a1 b1 c1, rfl, lt_of_head_lt h1, rfl⟩
    · rw [if_neg h1]
      obtain ⟨B, X, hb, hX, he⟩ := add_prefix s y c1
      exact ⟨psi a1 b1 B, X, by rw [hb]; rfl, hX, by rw [he]; rfl⟩

theorem lt_add_principal (s y b : T) : b < add b (psi s y z) := by
  obtain ⟨B, X, hb, hX, he⟩ := add_prefix s y b
  rw [he]; conv => lhs; rw [hb]
  exact app_lt_app_left B hX

/-- If `c_u < c_w` are principal, then `(b + c_u) ++ R < b + c_w` for every `R`. -/
theorem add_app_lt {s1 y1 s2 y2 : T} (h : psi s1 y1 z < psi s2 y2 z) :
    ∀ b R : T, app (add b (psi s1 y1 z)) R < add b (psi s2 y2 z)
  | z, R => by simp only [add_z_left, app_psi, app_z]; exact lt_of_head_lt h
  | psi a1 b1 c1, R => by
    rw [add_psi_psi, add_psi_psi]
    by_cases h1 : psi a1 b1 z < psi s1 y1 z
    · rw [if_pos h1, if_pos (lt_trans h1 h)]
      simp only [app_psi, app_z]; exact lt_of_head_lt h
    · rw [if_neg h1]
      by_cases h2 : psi a1 b1 z < psi s2 y2 z
      · rw [if_pos h2]; simp only [app_psi]; exact lt_of_head_lt h2
      · rw [if_neg h2]; simp only [app_psi]
        rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, add_app_lt h c1 R⟩)

/-! ## 違いの道の 1 段（添字が同じ） -/

/-- **One frame with equal subscripts.** With a common state `b`, the next summands
`ψ_s(y_u) < ψ_s(y_w)` and the rest `R_u` of the smaller side at most `ψ_s(y_u)`, the state after the
step followed by the rest is strictly smaller on the `u` side. -/
theorem frame_same {a b s yu yw Ru Rw : T}
    (hu : isOT (psi s yu z) = true) (hw : isOT (psi s yw z) = true) (hlt : yu < yw)
    (hRu : head Ru ≤ psi s yu z) :
    app (step a b s yu Ru) Ru < app (step a b s yw Rw) Rw := by
  have hcw : psi s yu z < psi s yw z := by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩
  have hsum : ∀ q ∈ summands (H s yw), head Ru < q := fun q hq =>
    lt_of_le_of_lt hRu (lt_of_lt_of_le hcw (H_summands_ge hw q hq))
  unfold step
  by_cases hU : lt b yu = true ∧ lt (psi a z z) (psi s yu Ru) = true
  · have hW : lt b yw = true ∧ lt (psi a z z) (psi s yw Rw) = true :=
      ⟨lt_trans hU.1 hlt,
       lt_trans hU.2 (show psi s yu Ru < psi s yw Rw by
         rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, hlt⟩))⟩
    rw [if_pos hU, if_pos hW]
    exact lt_of_lt_of_le (app_lt_of_lt (H_lt_H hu hw hlt) hsum) (le_app_self _ _)
  · rw [if_neg hU]
    by_cases hW : lt b yw = true ∧ lt (psi a z z) (psi s yw Rw) = true
    · rw [if_pos hW]
      obtain ⟨B, X, hb, _, he⟩ := add_prefix s yu b
      rw [he, app_assoc]
      apply lt_of_lt_of_le _ (le_app_self _ _)
      have hB : B ≤ b := by rw [hb]; exact le_app_self _ _
      apply app_lt_of_lt (lt_of_le_of_lt hB (lt_of_lt_of_le hW.1 (le_H hw)))
      intro q hq
      exact lt_of_lt_of_le hcw (H_summands_ge hw q hq)
    · rw [if_neg hW]
      exact lt_of_lt_of_le (add_app_lt hcw b Ru) (le_app_self _ _)

/-- **A frame where the smaller side ends.** -/
theorem frame_prefix {a b s yw Rw : T} (hw : isOT (psi s yw z) = true) :
    b < app (step a b s yw Rw) Rw := by
  apply lt_of_lt_of_le _ (le_app_self _ _)
  unfold step
  split
  · rename_i h; exact lt_of_lt_of_le h.1 (le_H hw)
  · exact lt_add_principal s yw b

/-- `frame_same` for the final state of `sp`, when neither rest rewrites. -/
theorem spArg_frame_same {a b s yu yw Ru Rw : T}
    (hu : isOT (psi s yu z) = true) (hw : isOT (psi s yw z) = true) (hlt : yu < yw)
    (hRu : head Ru ≤ psi s yu z)
    (hNu : spArg a (step a b s yu Ru) Ru = app (step a b s yu Ru) Ru)
    (hNw : spArg a (step a b s yw Rw) Rw = app (step a b s yw Rw) Rw) :
    spArg a b (psi s yu Ru) < spArg a b (psi s yw Rw) := by
  rw [spArg_cons, spArg_cons, hNu, hNw]
  exact frame_same hu hw hlt hRu

/-- `frame_prefix` for the final state of `sp`. -/
theorem spArg_frame_prefix {a b s yw Rw : T} (hw : isOT (psi s yw z) = true)
    (hNw : spArg a (step a b s yw Rw) Rw = app (step a b s yw Rw) Rw) :
    spArg a b z < spArg a b (psi s yw Rw) := by
  rw [spArg_cons, hNw]
  exact frame_prefix hw


/-! ## 書き換えが起きない残り -/

/-- The step does not depend on the rest: the comparison with `Ω_a` matters only when `b < y`, and then
`y ≠ 0`. -/
theorem step_rest (a b s y c c' : T) : step a b s y c = step a b s y c' := by
  unfold step
  by_cases h1 : lt b y = true
  · have hy : y ≠ z := by rintro rfl; exact absurd h1 (by simp [lt])
    have key : ∀ d, lt (psi a z z) (psi s y d) = (if a = s then lt z y else lt a s) := by
      intro d; simp only [lt]
      split
      · rename_i h; rw [if_neg (Ne.symm hy)]
      · rfl
    rw [key c, key c']
  · simp [h1]

/-- `sp` over a concatenation: first the prefix, then the rest. -/
theorem spArg_app (a : T) : ∀ b P c : T, spArg a b (app P c) = spArg a (spArg a b P) c
  | b, z, c => rfl
  | b, psi s y P, c => by
    simp only [app_psi, spArg_cons]
    rw [step_rest a b s y (app P c) P]
    exact spArg_app a _ P c

/-- **No rewriting in the rest.** If every summand `ψ_s(y)` of `R` has `y ≤ b` or `s < a`, and `b ++ R` is
standard, then `sp` only appends `R`. -/
theorem spArg_eq_app {a : T} : ∀ {b R : T}, isOT (app b R) = true →
    (∀ s y, psi s y z ∈ summands R → y ≤ b ∨ s < a) → spArg a b R = app b R
  | b, z, _, _ => by simp [spArg]
  | b, psi s y R, hot, hR => by
    rw [spArg_cons]
    have hst : step a b s y R = app b (psi s y z) := by
      unfold step
      have hno : ¬ (lt b y = true ∧ lt (psi a z z) (psi s y R) = true) := by
        rintro ⟨h1, h2⟩
        rcases hR s y (by simp [summands]) with h | h
        · exact absurd (show b < y from h1) (not_lt_of_ge h)
        · have h2' : psi a z z < psi s y R := h2
          rw [T.psi_lt_psi] at h2'
          rcases h2' with h3 | ⟨h3, _⟩ | ⟨h3, _, _⟩
          · exact lt_asymm h3 h
          · subst h3; exact lt_irrefl _ h
          · subst h3; exact lt_irrefl _ h
      rw [if_neg hno]
      have hb' : isOT (app b (psi s y z)) = true := by
        have : app b (psi s y R) = app (app b (psi s y z)) R := by rw [app_assoc]; simp
        rw [this] at hot; exact isOT_app_left hot
      exact add_eq_app hb'
    rw [hst]
    have hassoc : app (app b (psi s y z)) R = app b (psi s y R) := by rw [app_assoc]; simp
    have hot' : isOT (app (app b (psi s y z)) R) = true := by rw [hassoc]; exact hot
    rw [spArg_eq_app hot' (fun s' y' h => (hR s' y' (by simp [summands, h])).imp_left
      (fun h' => le_trans h' (le_app_self _ _))), hassoc]

end Ytosk
