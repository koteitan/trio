/-
**t = 2 の種の列の枠の順序数の部分（closure、2026-10-11）。**

種の列 r（q = r）の最後の枠は繰り返し: Y_1 = B（M.take x での r の引数）、y_m = σ(Y_{m−1})、
Y_m = step(V, B, V′, y_m)。実測（deepA・d3s・deep3、例外 0）で
- σB = B なら m = 2 は書き換えず、m ≥ 3 は pre（y_m = B + R、R ≠ 0 は高い）。
- σB > B なら m = 2 から同じ道の cut がずっと続く。
ここでは cut が続く理由の順序数の補題を示す。
- `cutsNS_same_sh`: B が自分の σ 像の切り口（`B ∈ cutsNS s (σ B)`、つまり σ は B の文脈を動かさない）なら、
  B ∈ cutsNS s h から B ∈ cutsNS s (σ h)（同じ段 s）。添字の鎖は作り直すので条件は要らない。
- `cutsNS_app`: 切り口は後ろに足しても切り口。
-/
import Ytosk.V3PSh

namespace Ytosk

open T

theorem cutsH_ne_z {s : T} : ∀ {h t : T}, t ∈ cutsH s h → t ≠ z
  | z, _, ht => by simp [cutsH] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsH_psi.mp ht with ⟨_, rfl⟩ | ⟨_, u, _, rfl⟩ | ⟨u, _, rfl⟩ <;> simp

theorem cutsNS_ne_z {s : T} : ∀ {h t : T}, t ∈ cutsNS s h → t ≠ z
  | z, _, ht => by simp [cutsNS] at ht
  | psi a x c, t, ht => by
    simp only [cutsNS, List.mem_append, List.mem_map] at ht
    rcases ht with (⟨u, _, rfl⟩ | ⟨u, _, rfl⟩) | ⟨u, _, rfl⟩ <;> simp

theorem cutsNS_app {s : T} : ∀ {h B : T} (X : T), B ∈ cutsNS s h → B ∈ cutsNS s (app h X)
  | z, _, _, hB => by simp [cutsNS] at hB
  | psi a x c, B, X, hB => by
    simp only [cutsNS, List.mem_append, List.mem_map, app] at hB ⊢
    rcases hB with (h | h) | ⟨u, hu, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨u, cutsNS_app X hu, rfl⟩

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
  {s : T} (hs : isOT s = true) (hVs : V < s)
include hV hV' hVV hs hVs

/-- **The subscript chain at the same level**: `f` only raises the subscripts on the chain. -/
theorem scuts_shf_same : ∀ {h t : T}, isOT h = true → t ∈ scuts s h → t ∈ scuts s (shf V V' h)
  | z, _, _, ht => by simp [scuts] at ht
  | psi a x c, t, hot, ht => by
    have ha := isOT_sub hot
    simp only [scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · split at ht
      · rename_i hsa
        simp only [List.mem_singleton] at ht; subst ht
        have hsa' := le_of_le_bool hsa
        have hVa : V < a := lt_of_lt_of_le hVs hsa'
        rw [shf_psi hV hV' hVV ha hVa]
        simp only [scuts, List.mem_append, List.mem_map]
        left
        have : le s (shf V V' a) = true := by
          have h1 : s ≤ shf V V' a := le_trans hsa' (le_shf_self hV hV' (le_of_lt hVV) ha (le_of_lt hVa))
          rcases (le_iff _ _).mp h1 with h | h
          · simp [le, show lt s (shf V V' a) = true from h]
          · simp [le, h]
        rw [if_pos this]; simp
      · simp at ht
    · have hu1 := scuts_ge hu
      have hu2 := scuts_le hu
      have hVa : V < a := lt_of_lt_of_le (lt_trans hVs (lt_Om_self s)) (le_trans hu1 hu2)
      rw [shf_psi hV hV' hVV ha hVa]
      simp only [scuts, List.mem_append, List.mem_map]
      right
      exact ⟨u, scuts_shf_same ha hu, rfl⟩

/-- **The high-path cuts at the same level**, when `σ` fixes the context of the cut. -/
theorem cutsH_same_sh : ∀ {h t : T}, isOT h = true → t ∈ cutsH s (sh V V' t) → t ∈ cutsH s h →
    t ∈ cutsH s (sh V V' h)
  | z, _, _, _, ht => by simp [cutsH] at ht
  | psi a x c, t, hot, hfix, ht => by
    have ha := isOT_sub hot
    rcases mem_cutsH_psi.mp ht with ⟨hsa, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa]
      refine mem_cutsH_psi.mpr (Or.inl ⟨?_, rfl⟩)
      have h1 : s ≤ shf V V' a :=
        le_trans (le_of_le_bool hsa) (le_shf_self hV hV' (le_of_lt hVV) ha (le_of_lt hVa))
      rcases (le_iff _ _).mp h1 with h | h
      · simp [le, show lt s (shf V V' a) = true from h]
      · simp [le, h]
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa, sh_z] at hfix
      -- the fixed context: `f a = a` and `u` is a cut of its image
      rcases mem_cutsH_psi.mp hfix with ⟨_, h⟩ | ⟨_, u', hu', h⟩ | ⟨u', hu', h⟩
      · exact absurd (T.psi.inj h).2.1 (cutsH_ne_z hu)
      · obtain ⟨hfa, rfl, -⟩ := T.psi.inj h
        rw [sh_psi_gt hVa]
        refine mem_cutsH_psi.mpr (Or.inr (Or.inl ⟨by rw [← hfa]; exact hsa, u, ?_, by rw [← hfa]⟩))
        exact cutsH_same_sh (isOT_arg hot) hu' hu
      · simp [cutsH] at hu'
    · by_cases hVa : V < a
      · rw [sh_psi_gt hVa] at hfix ⊢
        rcases mem_cutsH_psi.mp hfix with ⟨_, h⟩ | ⟨_, u', _, h⟩ | ⟨u', hu', h⟩
        · exact absurd (T.psi.inj h).2.2 (cutsH_ne_z hu)
        · exact absurd (T.psi.inj h).2.2 (cutsH_ne_z hu)
        · obtain ⟨hfa, hb, rfl⟩ := T.psi.inj h
          rw [← hfa, ← hb]
          exact mem_cutsH_psi.mpr (Or.inr (Or.inr ⟨_, cutsH_same_sh (isOT_rest hot) hu' hu, rfl⟩))
      · rw [sh_psi_le hVa] at hfix ⊢
        rcases mem_cutsH_psi.mp hfix with ⟨_, h⟩ | ⟨_, u', _, h⟩ | ⟨u', hu', h⟩
        · exact absurd (T.psi.inj h).2.2 (cutsH_ne_z hu)
        · exact absurd (T.psi.inj h).2.2 (cutsH_ne_z hu)
        · obtain ⟨-, -, rfl⟩ := T.psi.inj h
          exact mem_cutsH_psi.mpr (Or.inr (Or.inr ⟨_, cutsH_same_sh (isOT_rest hot) hu' hu, rfl⟩))

/-- **The `PH3c` cuts at the same level**, when `σ` fixes the context (`B` is a cut of its own image). -/
theorem cutsNS_same_sh : ∀ {h B : T}, isOT h = true → AllGeT (psi (succ s) z z) h →
    B ∈ cutsNS s (sh V V' B) → B ∈ cutsNS s h → B ∈ cutsNS s (sh V V' h)
  | z, _, _, _, _, hB => by simp [cutsNS] at hB
  | psi a x c, B, hot, hge, hfix, hB => by
    have ha := isOT_sub hot
    have hsa : succ s ≤ a := by
      have h0 : ¬ psi a x z < psi (succ s) z z := hge _ (by simp [summands])
      rcases lt_or_ge a (succ s) with h | h
      · exact absurd (by rw [psi_lt_psi_z_iff]; exact Or.inl h) h0
      · exact h
    have hVa : V < a := lt_of_lt_of_le (lt_trans hVs (lt_succ_self s)) hsa
    rw [sh_psi_gt hVa]
    simp only [cutsNS, List.mem_append, List.mem_map] at hB ⊢
    rcases hB with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
    · -- the subscript chain is rebuilt
      exact Or.inl (Or.inl ⟨u, scuts_shf_same hV hV' hVV hs hVs ha hu, rfl⟩)
    · rw [sh_psi_gt hVa, sh_z] at hfix
      simp only [cutsNS, List.mem_append, List.mem_map] at hfix
      rcases hfix with (⟨u', _, h⟩ | ⟨u', hu', h⟩) | ⟨u', hu', h⟩
      · exact absurd (T.psi.inj h).2.1.symm (cutsH_ne_z hu)
      · obtain ⟨hfa, huu, -⟩ := T.psi.inj h
        subst huu
        exact Or.inl (Or.inr ⟨u', cutsH_same_sh hV hV' hVV hs hVs (isOT_arg hot) hu' hu, by rw [hfa]⟩)
      · simp at hu'
    · rw [sh_psi_gt hVa] at hfix
      simp only [cutsNS, List.mem_append, List.mem_map] at hfix
      rcases hfix with (⟨u', _, h⟩ | ⟨u', _, h⟩) | ⟨u', hu', h⟩
      · exact absurd (T.psi.inj h).2.2.symm (cutsNS_ne_z hu)
      · exact absurd (T.psi.inj h).2.2.symm (cutsNS_ne_z hu)
      · obtain ⟨hfa, hb, huu⟩ := T.psi.inj h
        subst huu
        exact Or.inr ⟨u', cutsNS_same_sh (isOT_rest hot) (fun q hq => hge q (by simp [summands, hq])) hu' hu,
          by rw [hfa, hb]⟩

end

theorem cutsNS_self {s : T} : ∀ {h B : T}, B ∈ cutsNS s h → B ∈ cutsNS s B
  | z, _, hB => by simp [cutsNS] at hB
  | psi a x c, B, hB => by
    simp only [cutsNS, List.mem_append, List.mem_map] at hB
    rcases hB with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
    · simp only [cutsNS, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨u, scuts_self hu, rfl⟩)
    · simp only [cutsNS, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨u, cutsH_self hu, rfl⟩)
    · simp only [cutsNS, List.mem_append, List.mem_map]
      exact Or.inr ⟨u, cutsNS_self hu, rfl⟩

theorem allGeT_app_of {θ B R : T} (hB : AllGeT θ B) (hR : AllGeT θ R) : AllGeT θ (app B R) := by
  intro q hq
  rw [summands_app, List.mem_append] at hq
  rcases hq with h | h
  · exact hB q h
  · exact hR q h

theorem allGe_mono {θ θ' B : T} (h : θ' ≤ θ) (hB : AllGeT θ B) : AllGeT θ' B :=
  fun q hq hlt => hB q hq (lt_of_lt_of_le hlt h)

/-- The state before the seed's last child extends to `Y` (the seed's final state of an earlier copy). -/
def SeedExt (s B Y : T) : Prop :=
  Y = B ∨ (∃ R, R ≠ z ∧ AllGeT (psi s z z) R ∧ Y = app B R) ∨
    (B ∈ cutsNS s (split Y (psi (succ s) z z)).1 ∧ (split Y (psi (succ s) z z)).1 ≠ B ∧ AllGeT (psi s z z) Y)

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

theorem om_le_succ (s : T) : psi s z z ≤ psi (succ s) z z :=
  le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s)))

/-- `σ` lifts summands at least `Ω_{V′}` to at least `Ω_{V′+1}`. -/
theorem allGe_sh : ∀ {R : T}, isOT R = true → AllGeT (psi V' z z) R → AllGeT (psi (succ V') z z) (sh V V' R)
  | z, _, _ => by simp [AllGeT, summands]
  | psi k g c, hot, hR => by
    have hk : V' ≤ k := by
      have h0 : ¬ psi k g z < psi V' z z := hR _ (by simp [summands])
      rcases lt_or_ge k V' with h | h
      · exact absurd (psi_lt_psi_z_iff.mpr (Or.inl h)) h0
      · exact h
    have hVk : V < k := lt_of_lt_of_le hVV hk
    rw [sh_psi_gt hVk]
    intro q hq
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · intro hlt
      rw [psi_lt_psi_z_iff] at hlt
      have h1 : V' < shf V V' k := lt_of_lt_of_le
        (by have := shf_lt_shf hV hV' (le_of_lt hVV) hV (isOT_sub hot) (le_refl V) (lt_of_lt_of_le hVV hk)
            rwa [shf_self] at this) (le_refl _)
      rcases hlt with h | ⟨_, h'⟩
      · exact absurd (lt_of_lt_of_le h1 (lt_succ_iff.mp h)) (lt_irrefl' _)
      · exact T.not_lt_z _ h'
    · exact allGe_sh (isOT_rest hot) (fun q hq => hR q (by simp [summands, hq])) q hq

end

theorem split_all_hi {θ Y : T} (h : AllGeT θ Y) : (split Y θ).1 = Y ∧ (split Y θ).2 = z := by
  have h2 := split_snd_z_of_ge h
  have e := split_app θ Y
  rw [h2, app_z_right] at e
  exact ⟨e, h2⟩

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

theorem seedExt_allGe {B Y : T} (hBhi : AllGeT (psi (succ V') z z) B) (hE : SeedExt V' B Y) :
    AllGeT (psi V' z z) Y := by
  rcases hE with rfl | ⟨R, _, hR, rfl⟩ | ⟨_, _, h⟩
  · exact allGe_mono (om_le_succ hV hV' hVV V') hBhi
  · exact allGeT_app_of (allGe_mono (om_le_succ hV hV' hVV V') hBhi) hR
  · exact h

/-- **The kind of the seed's last frame** `(B, σ Y)` at level `V′`, from `Fix(B)` and `SeedExt`. -/
theorem seed_kind {B Y : T} (hB : isOT B = true) (hY : isOT Y = true)
    (hBhi : AllGeT (psi (succ V') z z) B)
    (hFix : sh V V' B = B ∨ B ∈ cutsNS V' (sh V V' B)) (hE : SeedExt V' B Y)
    (hlt : B < sh V V' Y) :
    PH3cKind B (split (sh V V' Y) (psi (succ V') z z)).1 (split (sh V V' Y) (psi (succ V') z z)).2 V' := by
  have hshall := allGe_sh hV hV' hVV hY (seedExt_allGe hV hV' hVV hBhi hE)
  obtain ⟨h1, h2⟩ := split_all_hi hshall
  rw [h1, h2]
  have hne : sh V V' Y ≠ B := fun e => by rw [e] at hlt; exact lt_irrefl' _ hlt
  have hV'z : V' ≠ z := fun e => by rw [e] at hVV; exact T.not_lt_z _ hVV
  rcases hE with rfl | ⟨R, hR, _, rfl⟩ | ⟨hc, _, _⟩
  · rcases hFix with h | h
    · rw [h] at hlt; exact absurd hlt (lt_irrefl' _)
    · exact Or.inr ⟨hne, Or.inr ⟨hV'z, h⟩⟩
  · rcases hFix with h | h
    · refine Or.inr ⟨hne, Or.inl ⟨sh V V' R, fun e => hR (sh_eq_z_iff.mp e), ?_⟩⟩
      rw [sh_app, h]
    · refine Or.inr ⟨hne, Or.inr ⟨hV'z, ?_⟩⟩
      rw [sh_app]; exact cutsNS_app _ h
  · have hfix2 : B ∈ cutsNS V' (sh V V' B) := hFix.elim (fun h => by rw [h]; exact cutsNS_self hc) id
    have happ := split_app (psi (succ V') z z) Y
    have hhiot : isOT (split Y (psi (succ V') z z)).1 = true := isOT_app_left (by rw [happ]; exact hY)
    have hc' := cutsNS_same_sh hV hV' hVV hV' hVV hhiot (split_fst_ge _ Y) hfix2 hc
    refine Or.inr ⟨hne, Or.inr ⟨hV'z, ?_⟩⟩
    rw [← happ, sh_app]
    exact cutsNS_app _ hc'

/-- **The seed's final state keeps extending `B`** after the next copy: `step(a, B, V′, σ Y)`. -/
theorem seed_ext {a B Y : T} (hB : isOT B = true) (hY : isOT Y = true)
    (hBhi : AllGeT (psi (succ V') z z) B)
    (hFix : sh V V' B = B ∨ B ∈ cutsNS V' (sh V V' B)) (hE : SeedExt V' B Y)
    (hcv : isOT (psi V' (sh V V' Y) z) = true) :
    SeedExt V' B (step a B V' (sh V V' Y) z) := by
  have hshall := allGe_sh hV hV' hVV hY (seedExt_allGe hV hV' hVV hBhi hE)
  obtain ⟨h1, h2⟩ := split_all_hi hshall
  have hom := om_le_succ hV hV' hVV V'
  unfold step
  split_ifs with hrw
  · rw [H_eq hcv, h1, h2]
    simp only [if_true, app_z_right]
    by_cases hBz : B = z
    · subst hBz
      refine Or.inr (Or.inl ⟨sh V V' Y, ne_z_of_lt hrw.1, allGe_mono hom hshall, rfl⟩)
    have hK := seed_kind hV hV' hVV hB hY hBhi hFix hE hrw.1
    rw [h1, h2] at hK
    rcases hK with ⟨_, h⟩ | ⟨hne, (⟨R, hR, hhi⟩ | ⟨_, hc⟩)⟩
    · exact absurd rfl h
    · refine Or.inr (Or.inl ⟨R, hR, fun q hq => ?_, hhi⟩)
      exact allGe_mono hom hshall q (by rw [hhi]; rw [summands_app, List.mem_append]; exact Or.inr hq)
    · exact Or.inr (Or.inr ⟨by rw [h1]; exact hc, by rw [h1]; exact hne, allGe_mono hom hshall⟩)
  · have happ : add B (psi V' (sh V V' Y) z) = app B (psi V' (sh V V' Y) z) := by
      by_cases hBz : B = z
      · subst hBz; rfl
      apply add_eq_app_of_last hB
      have hl := hBhi (last B) (last_mem_summands hBz)
      simp only [head]
      rcases lt_or_ge (psi V' (sh V V' Y) z) (last B) with h | h
      · exact le_of_lt h
      · exfalso; apply hl
        exact lt_of_le_of_lt h (psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self V')))
    rw [happ]
    refine Or.inr (Or.inl ⟨psi V' (sh V V' Y) z, by simp, ?_, rfl⟩)
    intro q hq
    simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact not_lt_of_ge (psi_le_psi_z (le_refl V'))

end

end Ytosk
