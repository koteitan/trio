/-
**置き換え σ と評価器の演算の交換。**

σ は標準形の上の順序の埋め込みで加数ごとに働くので、加数の比較だけで決まる演算（和・sub・split・last）と交換する。
ω 冪・H・sp は「添字 s の加数が Ω_{s+1} より下か」を比べるが、σ(Ω_{s+1}) = Ω_{f(s)+1}（f(s + 1) = f(s) + 1）なので
これも保たれる。sp の段 a は V ≤ a で f(a) に替わる。a = V（写しの根 r）のときだけ、添字がちょうど V の加数が
書き換えの条件を変えうるので、その加数がないことを仮定する（実測: r の数える子の添字はすべて V より大きい）。

まとめ（`oRhs`・`vRhs` の右辺の形）:
- `sf_psi_sh`: sf(ψ_{f(v)}(σ S)) = ψ_{f(v)}(σ(spArg v 0 S))。v > V ならこれは σ(sf(ψ_v(S)))。
- `shf_add`: f(A + Y) = f(A) + σ(Y)（V ≤ A）。`last_shf`: last(f(B)) = σ(last B)（V < B）。
- `sh_omega`・`sh_sumN`・`sh_add`。
-/
import Ytosk.V3Subst
import Ytosk.V3DropNode
import Ytosk.V3Frame

namespace Ytosk

open T

/-! ## 和の結合則 -/

theorem add_assoc' : ∀ x y w : T, add (add x y) w = add x (add y w)
  | z, y, w => by simp
  | psi a b c, z, w => by simp
  | psi a b c, psi d e f, z => by simp
  | psi a b c, psi d e f, psi g h i => by
    by_cases h1 : psi a b z < psi d e z
    · rw [add_psi_psi a b c d e f, if_pos h1]
      by_cases h2 : psi d e z < psi g h z
      · rw [add_psi_psi d e f g h i, if_pos h2, add_psi_psi, if_pos (lt_trans h1 h2)]
      · rw [add_psi_psi d e f g h i, if_neg h2, add_psi_psi, if_pos h1]
    · rw [add_psi_psi a b c d e f, if_neg h1]
      by_cases h2 : psi d e z < psi g h z
      · rw [add_psi_psi d e f g h i, if_pos h2, add_psi_psi a b (add c (psi d e f)) g h i]
        rw [add_psi_psi a b c g h i]
        split
        · rfl
        · rw [add_assoc' c (psi d e f) (psi g h i), add_psi_psi d e f g h i, if_pos h2]
      · rw [add_psi_psi d e f g h i, if_neg h2, add_psi_psi a b (add c (psi d e f)) g h i]
        have h3 : ¬ psi a b z < psi g h z := fun h3 =>
          h1 (lt_of_lt_of_le h3 (le_of_not_gt h2))
        rw [if_neg h3, add_psi_psi a b c d e (add f (psi g h i)), if_neg h1]
        rw [add_assoc' c (psi d e f) (psi g h i), add_psi_psi d e f g h i, if_neg h2]

/-! ## 加数ごとの演算 -/

section
variable {V V' : T}

theorem sh_app : ∀ p R : T, sh V V' (app p R) = app (sh V V' p) (sh V V' R)
  | z, R => by simp
  | psi s y c, R => by
    rw [app_psi, sh_psi_app, sh_psi_app s y c, sh_app c R]
    obtain ⟨a, b, hab⟩ := sh_single (V := V) (V' := V') s y
    rw [hab]; simp

theorem last_psi_ne {a b c : T} (hc : c ≠ z) : last (psi a b c) = last c := by
  cases c with
  | z => exact absurd rfl hc
  | psi => rfl

theorem sh_last : ∀ t : T, sh V V' (last t) = last (sh V V' t)
  | z => by simp [last]
  | psi s y z => by
    obtain ⟨a, b, hab⟩ := sh_single (V := V) (V' := V') s y
    rw [show last (psi s y z) = psi s y z from rfl, hab]; rfl
  | psi s y (psi s' y' c') => by
    rw [show last (psi s y (psi s' y' c')) = last (psi s' y' c') from rfl, sh_psi_app]
    obtain ⟨a, b, hab⟩ := sh_single (V := V) (V' := V') s y
    rw [hab, app_psi, app_z, last_psi_ne (sh_ne_z (by simp)), sh_last]

end

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **`σ` commutes with the sum.** -/
theorem sh_add : ∀ {a b : T}, isOT a = true → isOT b = true →
    sh V V' (add a b) = add (sh V V' a) (sh V V' b)
  | z, b, _, _ => by simp
  | psi s y c, z, _, _ => by simp
  | psi s y c, psi d e f, ha, hb => by
    have hVV' := le_of_lt hVV
    obtain ⟨a1, b1, h1⟩ := sh_single (V := V) (V' := V') s y
    obtain ⟨d1, e1, h2⟩ := sh_single (V := V) (V' := V') d e
    have hiff : psi a1 b1 z < psi d1 e1 z ↔ psi s y z < psi d e z := by
      rw [← h1, ← h2]; exact sh_lt_iff hV hV' hVV' (isOT_head ha) (isOT_head hb)
    rw [sh_psi_app s y c, sh_psi_app d e f, h1, h2, app_psi, app_psi, app_z, app_z,
      add_psi_psi, add_psi_psi]
    by_cases hlt : psi s y z < psi d e z
    · rw [if_pos hlt, if_pos (hiff.mpr hlt), sh_psi_app, h2]; rfl
    · rw [if_neg hlt, if_neg (fun h => hlt (hiff.mp h)), sh_psi_app, h1, app_psi, app_z,
        sh_add (isOT_rest ha) hb, sh_psi_app d e f, h2]; rfl

theorem isOT_sumN_of {l : List T} (hl : ∀ t ∈ l, isOT t = true) : ∀ acc : T, isOT acc = true →
    isOT (l.foldl (fun a b => sf (add a b)) acc) = true := by
  induction l with
  | nil => intro acc h; exact h
  | cons t l ih =>
    intro acc h
    simp only [List.foldl_cons]
    have ht := hl t (by simp)
    rw [sf_ot (isOT_add h ht)]
    exact ih (fun u hu => hl u (by simp [hu])) _ (isOT_add h ht)

/-- **`σ` commutes with `sumN`.** -/
theorem sh_sumN {l : List T} (hl : ∀ t ∈ l, isOT t = true) :
    sh V V' (sumN l) = sumN (l.map (sh V V')) := by
  unfold sumN
  suffices ∀ acc, isOT acc = true → sh V V' (l.foldl (fun a b => sf (add a b)) acc) =
      (l.map (sh V V')).foldl (fun a b => sf (add a b)) (sh V V' acc) by
    simpa using this z rfl
  induction l with
  | nil => intro acc _; rfl
  | cons t l ih =>
    intro acc hacc
    have ht := hl t (by simp)
    simp only [List.foldl_cons, List.map_cons]
    rw [sf_ot (isOT_add hacc ht), sf_ot (isOT_add (isOT_sh hV hV' hVV hacc) (isOT_sh hV hV' hVV ht)),
      ← sh_add hV hV' hVV hacc ht]
    exact ih (fun u hu => hl u (by simp [hu])) _ (isOT_add hacc ht)

/-- **`f(A + Y) = f(A) + σ(Y)`** for `V ≤ A`. -/
theorem shf_add {A Y : T} (hA : isOT A = true) (hY : isOT Y = true) (hVA : V ≤ A) :
    shf V V' (add A Y) = add (shf V V' A) (sh V V' Y) := by
  unfold shf
  rw [sub_add_dist Y hV hA hVA, sh_add hV hV' hVV (isOT_sub_sfx hA V) hY, add_assoc']

theorem shf_succ {s : T} (hs : isOT s = true) (hVs : V ≤ s) :
    shf V V' (succ s) = succ (shf V V' s) := by
  rw [← add_one_eq_succ hs, shf_add hV hV' hVV hs isOT_one hVs, sh_one,
    add_one_eq_succ (isOT_shf hV hV' hVV hs)]

/-- **`last(f(B)) = σ(last B)`** for `V < B`. -/
theorem last_shf {B : T} (hB : isOT B = true) (hVB : V < B) :
    last (shf V V' B) = sh V V' (last B) := by
  have hne := sub_ne_z_of_lt hV hB hVB
  unfold shf
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub B V))
  rw [hP, last_app P (sh_ne_z hne), ← sh_last]
  obtain ⟨Q, hQ⟩ := sub_suffix B V
  conv_rhs => rw [hQ, last_app Q hne]

/-! ## split・H・ω -/

/-- **`σ` commutes with `split`** when the threshold comparison is preserved. -/
theorem sh_split {t t' : T} (htt : ∀ s y, isOT (psi s y z) = true → (sh V V' (psi s y z) < t' ↔ psi s y z < t)) :
    ∀ {b : T}, isOT b = true → split (sh V V' b) t' = (sh V V' (split b t).1, sh V V' (split b t).2)
  | z, _ => by simp [split]
  | psi s y c, hb => by
    obtain ⟨a1, b1, h1⟩ := sh_single (V := V) (V' := V') s y
    have hiff := htt s y (isOT_head hb)
    rw [h1] at hiff
    rw [sh_psi_app, h1, app_psi, app_z]
    simp only [split]
    by_cases hlt : psi s y z < t
    · rw [if_pos (show lt (psi a1 b1 z) t' = true from hiff.mpr hlt),
        if_pos (show lt (psi s y z) t = true from hlt)]
      rw [sh_z, sh_psi_app s y c, h1]; rfl
    · rw [if_neg (show ¬ lt (psi a1 b1 z) t' = true from fun h => hlt (hiff.mp h)),
        if_neg (show ¬ lt (psi s y z) t = true from hlt)]
      have ih := sh_split htt (isOT_rest hb)
      rw [ih, sh_psi_app s y (split c t).1, h1]; rfl

/-- The threshold `Ω_{s+1}` moves to `Ω_{f(s)+1}`. -/
theorem sh_lt_om_succ {s : T} (hs : isOT s = true) (hVs : V < s) :
    ∀ a b, isOT (psi a b z) = true →
      (sh V V' (psi a b z) < psi (succ (shf V V' s)) z z ↔ psi a b z < psi (succ s) z z) := by
  intro a b hab
  have hVs1 : V < succ s := lt_trans hVs (lt_succ_self s)
  have hs1 : isOT (succ s) = true := isOT_succ hs
  have hom : sh V V' (psi (succ s) z z) = psi (succ (shf V V' s)) z z := by
    rw [sh_psi_gt hVs1, shf_succ hV hV' hVV hs (le_of_lt hVs)]; simp
  rw [← hom]
  exact sh_lt_iff hV hV' (le_of_lt hVV) hab (isOT_om.mpr hs1)

/-- **`σ(H(s, y)) = H(f(s), σ y)`** for `V < s`. -/
theorem sh_H {s y : T} (hy : isOT (psi s y z) = true) (hVs : V < s) :
    sh V V' (H s y) = H (shf V V' s) (sh V V' y) := by
  have hy' : isOT (psi (shf V V' s) (sh V V' y) z) = true := isOT_shTop hV hV' hVV hy (le_of_lt hVs)
  rw [H_eq hy, H_eq hy', sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV (isOT_sub hy) hVs) (isOT_arg hy),
    sh_app]
  congr 1
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · rw [if_pos hlo, if_pos (by rw [hlo]; simp)]; simp
  · rw [if_neg hlo, if_neg (fun h => hlo (sh_eq_z_iff.mp h)), sh_psi_gt hVs]; simp

/-- **`σ` commutes with `ω^·`.** -/
theorem sh_omega {x : T} (hx : isOT x = true) : sh V V' (omega x) = omega (sh V V' x) := by
  have hVV' := le_of_lt hVV
  by_cases hsmall : x < E0
  · have hfix : sh V V' x = x := by
      cases x with
      | z => simp
      | psi s w c =>
        apply sh_fix hx
        rw [lev_psi, (below_E0 hsmall).1]; exact T.not_lt_z V
    rw [hfix, omega_small hsmall, sh_psi_le (T.not_lt_z V)]; simp
  · cases x with
    | z => exact absurd (T.z_lt_psi _ _ _) hsmall
    | psi s b c =>
      have hbig' : ¬ sh V V' (psi s b c) < E0 := fun h =>
        hsmall (lt_of_le_of_lt (le_sh hV hV' hVV' hx) h)
      by_cases hVs : V < s
      · have hx' := isOT_sh hV hV' hVV hx
        have e : sh V V' (psi s b c) = psi (shf V V' s) (sh V V' b) (sh V V' c) := sh_psi_gt hVs
        rw [e] at hbig' hx'
        rw [e, omega_big hx hsmall, omega_big hx' hbig', sh_psi_gt hVs, sh_z, sh_app]
        have hsp := sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV (isOT_sub hx) hVs) (isOT_arg hx)
        rw [hsp]
        congr 2
        by_cases hlo : (split b (psi (succ s) z z)).2 = z
        · rw [if_pos hlo, if_pos (by rw [hlo]; simp)]
        · rw [if_neg hlo, if_neg (fun h => hlo (sh_eq_z_iff.mp h)), sh_psi_gt hVs]
      · rw [sh_fix hx (by simpa using hVs)]
        rw [omega_big hx hsmall, sh_psi_le hVs]; simp

/-! ## sp の段 -/

theorem shf_eq_iff {s t : T} (hs : isOT s = true) (ht : isOT t = true) (hVs : V ≤ s) (hVt : V ≤ t) :
    shf V V' s = shf V V' t ↔ s = t := by
  have hVV' := le_of_lt hVV
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rcases lt_trichotomy s t with h1 | h1 | h1
  · exact absurd h (ne_of_lt (shf_lt_shf hV hV' hVV' hs ht hVs h1))
  · exact h1
  · exact absurd h.symm (ne_of_lt (shf_lt_shf hV hV' hVV' ht hs hVt h1))

/-- **One step of `sp` commutes with `σ`** (summand with subscript `s > V`, level `V ≤ a`). -/
theorem sh_step_gt {a b s y c c' : T} (ha : isOT a = true) (hVa : V ≤ a) (hb : isOT b = true)
    (hy : isOT (psi s y z) = true) (hVs : V < s) :
    step (shf V V' a) (sh V V' b) (shf V V' s) (sh V V' y) c' = sh V V' (step a b s y c) := by
  have hVV' := le_of_lt hVV
  rw [step_rest _ _ _ _ c' z, step_rest a b s y c z]
  have hyo := isOT_arg hy
  have hso := isOT_sub hy
  have e1 : lt (sh V V' b) (sh V V' y) = true ↔ lt b y = true := sh_lt_iff hV hV' hVV' hb hyo
  have e2 : lt (psi (shf V V' a) z z) (psi (shf V V' s) (sh V V' y) z) = true ↔
      lt (psi a z z) (psi s y z) = true := by
    show psi (shf V V' a) z z < psi (shf V V' s) (sh V V' y) z ↔ psi a z z < psi s y z
    rw [T.psi_lt_psi, T.psi_lt_psi, shf_lt_iff hV hV' hVV' ha hso hVa (le_of_lt hVs),
      shf_eq_iff hV hV' hVV ha hso hVa (le_of_lt hVs)]
    have e3 : z < sh V V' y ↔ z < y := by
      constructor
      · intro h; rcases lt_trichotomy z y with h' | h' | h'
        · exact h'
        · subst h'; simp at h
        · exact absurd h' (T.not_lt_z _)
      · intro h; exact lt_of_le_of_ne (z_le _) (Ne.symm (sh_ne_z (ne_of_gt h)))
    rw [e3]; simp
  unfold step
  by_cases hc : lt b y = true ∧ lt (psi a z z) (psi s y z) = true
  · rw [if_pos hc, if_pos ⟨e1.mpr hc.1, e2.mpr hc.2⟩, sh_H hV hV' hVV hy hVs]
  · rw [if_neg hc, if_neg (fun h => hc ⟨e1.mp h.1, e2.mp h.2⟩), sh_add hV hV' hVV hb hy,
      sh_psi_gt hVs, sh_z]

/-- **One step of `sp` with a kept summand** (`s ≤ V`): no trigger on either side. -/
theorem sh_step_le {a b s y c c' : T} (ha : isOT a = true) (hVa : V ≤ a) (hb : isOT b = true)
    (hy : isOT (psi s y z) = true) (hVs : ¬ V < s) (hlev : V < a ∨ s ≠ V) :
    step (shf V V' a) (sh V V' b) s y c' = sh V V' (step a b s y c) := by
  have hVV' := le_of_lt hVV
  rw [step_rest _ _ _ _ c' z, step_rest a b s y c z]
  have hs : s ≤ V := le_of_not_gt hVs
  have hP : ¬ (lt b y = true ∧ lt (psi a z z) (psi s y z) = true) := by
    rintro ⟨_, h2⟩
    have h2' : psi a z z < psi s y z := h2
    rw [T.psi_lt_psi] at h2'
    rcases h2' with h | ⟨rfl, _⟩ | ⟨rfl, _, h⟩
    · exact absurd (lt_of_lt_of_le h hs) (not_lt_of_ge hVa)
    · rcases hlev with hl | hl
      · exact absurd (lt_of_lt_of_le hl hs) (lt_irrefl' _)
      · exact hl (le_antisymm hs hVa)
    · exact T.not_lt_z _ h
  have hN : ¬ (lt (sh V V' b) y = true ∧ lt (psi (shf V V' a) z z) (psi s y z) = true) := by
    rintro ⟨_, h2⟩
    have h2' : psi (shf V V' a) z z < psi s y z := h2
    rw [T.psi_lt_psi] at h2'
    have hlt : s < shf V V' a :=
      lt_of_le_of_lt hs (lt_of_lt_of_le hVV (le_shf hV hV' hVV' ha hVa))
    rcases h2' with h | ⟨h, _⟩ | ⟨h, _, _⟩
    · exact absurd (lt_trans h hlt) (lt_irrefl' _)
    · exact absurd (h ▸ hlt) (lt_irrefl' _)
    · exact absurd (h ▸ hlt) (lt_irrefl' _)
  unfold step
  rw [if_neg hN, if_neg hP, sh_add hV hV' hVV hb hy, sh_fix hy (by simpa using hVs)]

/-- **`sp` commutes with `σ`** at a level `V ≤ a`; for `a = V` no summand of `S` may have subscript `V`. -/
theorem sh_spArg {a : T} (ha : isOT a = true) (hVa : V ≤ a) : ∀ {b S : T}, isOT b = true → isOT S = true →
    (V < a ∨ ∀ q ∈ summands S, lev q ≠ V) →
    spArg (shf V V' a) (sh V V' b) (sh V V' S) = sh V V' (spArg a b S)
  | b, z, _, _, _ => by simp [spArg]
  | b, psi s y c, hb, hS, hlev => by
    have hy := isOT_head hS
    have hlev' : V < a ∨ ∀ q ∈ summands c, lev q ≠ V := by
      rcases hlev with h | h
      · exact Or.inl h
      · exact Or.inr (fun q hq => h q (by simp [summands, hq]))
    have hst : isOT (step a b s y c) = true := by
      rw [step_rest a b s y c z]; exact isOT_step hb hy
    rw [spArg_cons]
    by_cases hVs : V < s
    · rw [sh_psi_gt hVs, spArg_cons, sh_step_gt hV hV' hVV ha hVa hb hy hVs]
      exact sh_spArg ha hVa hst (isOT_rest hS) hlev'
    · rw [sh_psi_le hVs, spArg_cons]
      have hl : V < a ∨ s ≠ V := by
        rcases hlev with h | h
        · exact Or.inl h
        · exact Or.inr (by simpa using h (psi s y z) (by simp [summands]))
      rw [sh_step_le hV hV' hVV ha hVa hb hy hVs hl]
      exact sh_spArg ha hVa hst (isOT_rest hS) hlev'

/-! ## 評価器の右辺の形 -/

/-- **The `o` equation**: `sf(ψ_{f(v)}(σ S)) = ψ_{f(v)}(σ(spArg v 0 S))` for `V ≤ v`
(for `v = V`: no summand of `S` with subscript `V`). -/
theorem sf_psi_sh {v S : T} (hv : isOT v = true) (hS : isOT S = true) (hVv : V ≤ v)
    (hlev : V < v ∨ ∀ q ∈ summands S, lev q ≠ V) :
    sf (psi (shf V V' v) (sh V V' S) z) = psi (shf V V' v) (sh V V' (spArg v z S)) z := by
  rw [sf_psi_spArg (isOT_shf hV hV' hVV hv) (isOT_sh hV hV' hVV hS), ← sh_spArg hV hV' hVV hv hVv rfl hS hlev,
    sh_z]

/-- For `V < v` the new `o` is `σ` of the old one. -/
theorem sf_psi_sh_gt {v S : T} (hv : isOT v = true) (hS : isOT S = true) (hVv : V < v) :
    sf (psi (shf V V' v) (sh V V' S) z) = sh V V' (sf (psi v S z)) := by
  rw [sf_psi_sh hV hV' hVV hv hS (le_of_lt hVv) (Or.inl hVv), sf_psi_spArg hv hS, sh_psi_gt hVv, sh_z]

/-- **The `v` equation, row 2 zero**: `f(A + L) = f(A) + σ(L)`, with `σ(last B) = last(f(B))`. -/
theorem shf_add_last {A B : T} (hA : isOT A = true) (hB : isOT B = true) (hVA : V ≤ A) (hVB : V < B) :
    sf (add (shf V V' A) (last (shf V V' B))) = shf V V' (sf (add A (last B))) := by
  have hl : isOT (last B) = true := isOT_last hB
  rw [last_shf hV hV' hVV hB hVB, sf_ot (isOT_add hA hl), ← shf_add hV hV' hVV hA hl hVA,
    sf_ot (isOT_shf hV hV' hVV (isOT_add hA hl))]
where
  isOT_last : ∀ {t : T}, isOT t = true → isOT (last t) = true
    | z, _ => rfl
    | psi a b z, h => h
    | psi a b (psi a' b' c'), h => by
      show isOT (last (psi a' b' c')) = true; exact isOT_last (isOT_rest h)

theorem shf_add_one {A : T} (hA : isOT A = true) (hVA : V ≤ A) :
    sf (add (shf V V' A) one) = shf V V' (sf (add A one)) := by
  rw [sf_ot (isOT_add hA isOT_one), shf_add hV hV' hVV hA isOT_one hVA, sh_one,
    sf_ot (isOT_add (isOT_shf hV hV' hVV hA) isOT_one)]

/-- **The `v` equation, row 2 nonzero**: `f(A + ω^W) = f(A) + ω^{σ W}`. -/
theorem shf_add_omega {A W : T} (hA : isOT A = true) (hW : isOT W = true) (hVA : V ≤ A) :
    sf (add (shf V V' A) (omega (sh V V' W))) = shf V V' (sf (add A (omega W))) := by
  have hw := isOT_omega hW
  rw [← sh_omega hV hV' hVV hW, sf_ot (isOT_add hA hw), ← shf_add hV hV' hVV hA hw hVA,
    sf_ot (isOT_shf hV hV' hVV (isOT_add hA hw))]

/-! ## 数える子の順序 -/

/-- **Decreasing lists stay decreasing** under `σ`. -/
theorem pairwise_sh {l : List T} (hl : ∀ t ∈ l, isOT t = true) (hp : l.Pairwise (fun a b => b ≤ a)) :
    (l.map (sh V V')).Pairwise (fun a b => b ≤ a) := by
  rw [List.pairwise_map]
  exact hp.imp_of_mem (fun {a b} ha hb h => sh_le_sh hV hV' (le_of_lt hVV) (hl b hb) (hl a ha) h)

end

end Ytosk
