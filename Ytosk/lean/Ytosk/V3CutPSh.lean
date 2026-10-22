/-
**s から始まる位置で切る形は σ で保たれる（2026-10-22、lead）。**

C の種の残りは「X₁ は σ^{k+1} X₁ を s′ から始まる位置で切った形（cutsPNSG）」（すべての k）だった。
`cutsPNS_same_sh`（`cutsNS_same_sh` の写し）で k = 0 の形から全部の k が出る。新しいのは切る位置 Ω_s の場合だけ:
a = s ++ δ で s が σ(s) の頭なら σ(a) = σ(s) ++ σδ も s から始まる（`prefB_shf`）。
-/
import Ytosk.V3PSeedOG
import Ytosk.V3T2CutDom

namespace Ytosk.G

set_option linter.unusedSectionVars false

open T

theorem prefB_self_app : ∀ (s δ : T), prefB s (app s δ) = true
  | z, _ => rfl
  | psi a b c, δ => by
    rw [app_psi]; simp only [prefB, decide_true, Bool.true_and]; exact prefB_self_app c δ

theorem sub_app_of_ne : ∀ {x V : T} (y : T), sub x V ≠ z → sub (app x y) V = app (sub x V) y
  | z, _, _, h => by simp [sub] at h
  | psi a b c, z, y, _ => by rw [app_psi]; simp [sub]
  | psi a b c, psi d e f, y, h => by
    rw [app_psi, sub_psi_psi, sub_psi_psi]
    rw [sub_psi_psi] at h
    split
    · rfl
    · rename_i hlt
      rw [if_neg hlt] at h
      exact sub_app_of_ne y h

theorem add_app_right : ∀ (X : T) {P : T} (Q : T), P ≠ z → add X (app P Q) = app (add X P) Q
  | z, P, Q, _ => rfl
  | psi a b c, z, _, h => absurd rfl h
  | psi a b c, psi d e f, Q, _ => by
    rw [app_psi, add_psi_psi, add_psi_psi]
    split
    · rfl
    · rw [show psi d e (app f Q) = app (psi d e f) Q from rfl, add_app_right c Q (by simp), app_psi]

theorem sub_eq_z_le : ∀ {s V : T}, sub s V = z → s ≤ V
  | z, V, _ => z_le V
  | psi a b c, z, h => by simp [sub] at h
  | psi a b c, psi d e f, h => by
    rw [sub_psi_psi] at h
    split at h
    · simp at h
    · rename_i hlt
      have hc := sub_eq_z_le h
      rcases (le_iff _ _).mp (not_lt.mp hlt) with h1 | h1
      · rw [psi_lt_psi_z_iff] at h1
        refine Or.inl ?_
        show psi a b c < psi d e f
        rw [T.psi_lt_psi]
        rcases h1 with h1 | ⟨rfl, h1⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl ⟨rfl, h1⟩)
      · simp only [psi.injEq, and_true] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rcases (le_iff _ _).mp hc with hc | hc
        · exact Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, hc⟩)))
        · rw [hc]

/-- **`σ(s ++ δ)` starts with `s` when `σ(s)` does.** -/
theorem prefB_shf {V V' s a : T} (hVs : V < s) (hpa : prefB s a = true)
    (hps : prefB s (shf V V' s) = true) : prefB s (shf V V' a) = true := by
  obtain ⟨δ, rfl⟩ := prefB_app hpa
  obtain ⟨ε, hε⟩ := prefB_app hps
  have hne : sub s V ≠ z := fun h => lt_irrefl' _ (lt_of_lt_of_le hVs (sub_eq_z_le h))
  have hsh : sh V V' (sub s V) ≠ z := sh_ne_z hne
  unfold shf at hε ⊢
  rw [sub_app_of_ne δ hne, sh_app, add_app_right _ _ hsh, hε, app_assoc]
  exact prefB_self_app s _

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
  {s : T} (hs : isOT s = true) (hVs : V < s)
include hV hV' hVV hs hVs

theorem sub_fixP {u : T} (hsu : s < u) (hlu : V < lev u) (hfix : psi u z z ∈ cutsPHG s (sh V V' (psi u z z))) :
    u ∈ cutsPHG s (sh V V' u) := by
  have hVu : V < u := lt_trans hVs hsu
  rw [sh_psi_gt hVu, sh_z, shf_eq_sh hV hV' hVV hlu] at hfix
  rcases mem_cutsPHG_psi.mp hfix with ⟨_, _, h⟩ | ⟨u', hu', h⟩ | ⟨_, u', hu', h⟩ | ⟨_, u', hu', h⟩
  · exact absurd ((T.psi.inj h).1 ▸ hsu) (lt_irrefl' _)
  · obtain ⟨rfl, -, -⟩ := T.psi.inj h; exact hu'
  · simp [cutsPHG] at hu'
  · simp [cutsPHG] at hu'

theorem cutsPH_ne_z : ∀ {h t : T}, t ∈ cutsPHG s h → t ≠ z :=
  fun ht => cutsH_ne_z (cutsPHG_sub ht)

/-- **Prefix cuts at the same level**, when `σ` fixes the context of the cut. -/
theorem cutsPH_same_sh : ∀ {h t : T}, isOT h = true → t ∈ cutsPHG s (sh V V' t) → t ∈ cutsPHG s h →
    t ∈ cutsPHG s (sh V V' h)
  | z, _, _, _, ht => by simp [cutsPHG] at ht
  | psi a x c, t, hot, hfix, ht => by
    have ha := isOT_sub hot
    rcases mem_cutsPHG_psi.mp ht with ⟨hsa, hp, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      -- `Ω_s` is a prefix cut of `σ Ω_s = Ω_{f(s)}`, so `s` starts `f(s)`
      have hps : prefB s (shf V V' s) = true := by
        rw [sh_psi_gt hVs, sh_z] at hfix
        rcases mem_cutsPHG_psi.mp hfix with ⟨_, h, _⟩ | ⟨u', hu', h⟩ | ⟨_, u', hu', h⟩ | ⟨_, u', hu', h⟩
        · exact h
        · obtain ⟨rfl, -, -⟩ := T.psi.inj h
          exact absurd (cutsHG_gt (cutsPHG_sub hu')) (lt_irrefl' _)
        · simp [cutsPHG] at hu'
        · simp [cutsPHG] at hu'
      rw [sh_psi_gt hVa]
      exact mem_cutsPHG_psi.mpr (Or.inl ⟨le_shf_of_le_s hV hV' hVV hs hVs ha hsa, prefB_shf hVs hp hps, rfl⟩)
    · have hsu := cutsHG_gt (cutsPHG_sub hu)
      have hla : V < lev a := lt_of_lt_of_le hVs (cutsHG_lev (cutsPHG_sub hu))
      have hVa : V < a := lt_trans hVs (lt_of_lt_of_le hsu (cutsHG_le (cutsPHG_sub hu)))
      have hfu := sub_fixP hV hV' hVV hs hVs hsu (lt_of_lt_of_le hVs (cutsHG_lev_cut (cutsPHG_sub hu))) hfix
      rw [sh_psi_gt hVa, shf_eq_sh hV hV' hVV hla]
      exact mem_cutsPHG_psi.mpr (Or.inr (Or.inl ⟨u, cutsPH_same_sh ha hfu hu, rfl⟩))
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa, sh_z] at hfix
      rcases mem_cutsPHG_psi.mp hfix with ⟨_, _, h⟩ | ⟨u', _, h⟩ | ⟨_, u', hu', h⟩ | ⟨_, u', hu', h⟩
      · exact ((cutsPH_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.1 | exact (T.psi.inj h).2.1.symm)).elim
      · exact ((cutsPH_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.1 | exact (T.psi.inj h).2.1.symm)).elim
      · obtain ⟨hfa, rfl, -⟩ := T.psi.inj h
        rw [sh_psi_gt hVa]
        refine mem_cutsPHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨by rw [← hfa]; exact hsa, u, ?_, by rw [← hfa]⟩)))
        exact cutsPH_same_sh (isOT_arg hot) hu' hu
      · simp [cutsPHG] at hu'
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa] at hfix ⊢
      rcases mem_cutsPHG_psi.mp hfix with ⟨_, _, h⟩ | ⟨u', _, h⟩ | ⟨_, u', _, h⟩ | ⟨_, u', hu', h⟩
      · exact ((cutsPH_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.2 | exact (T.psi.inj h).2.2.symm)).elim
      · exact ((cutsPH_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.2 | exact (T.psi.inj h).2.2.symm)).elim
      · exact ((cutsPH_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.2 | exact (T.psi.inj h).2.2.symm)).elim
      · obtain ⟨hfa, hb, rfl⟩ := T.psi.inj h
        rw [← hfa, ← hb]
        exact mem_cutsPHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hsa, _, cutsPH_same_sh (isOT_rest hot) hu' hu, rfl⟩)))

theorem cutsPNS_ne_z : ∀ {h t : T}, t ∈ cutsPNSG s h → t ≠ z :=
  fun ht => cutsNS_ne_z (cutsPNSG_sub ht)

/-- **`cutsNS_same_sh` for prefix cuts.** -/
theorem cutsPNS_same_sh : ∀ {h B : T}, isOT h = true → AllGeT (psi (succ s) z z) h →
    B ∈ cutsPNSG s (sh V V' B) → B ∈ cutsPNSG s h → B ∈ cutsPNSG s (sh V V' h)
  | z, _, _, _, _, hB => by simp [cutsPNSG] at hB
  | psi a x c, B, hot, hge, hfix, hB => by
    have ha := isOT_sub hot
    have hsa : succ s ≤ a := by
      have h0 : ¬ psi a x z < psi (succ s) z z := hge _ (by simp [summands])
      rcases lt_or_ge a (succ s) with h | h
      · exact absurd (by rw [psi_lt_psi_z_iff]; exact Or.inl h) h0
      · exact h
    have hVa : V < a := lt_of_lt_of_le (lt_trans hVs (lt_succ_self s)) hsa
    rw [sh_psi_gt hVa]
    rcases mem_cutsPNSG_psi.mp hB with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hsu := cutsHG_gt (cutsPHG_sub hu)
      have hVu : V < u := lt_trans hVs hsu
      have hla : V < lev a := lt_of_lt_of_le hVs (cutsHG_lev (cutsPHG_sub hu))
      have hfix' : psi u z z ∈ cutsPHG s (sh V V' (psi u z z)) := by
        rw [sh_psi_gt hVu, sh_z] at hfix ⊢
        rcases mem_cutsPNSG_psi.mp hfix with ⟨u', hu', h⟩ | ⟨u', hu', h⟩ | ⟨u', hu', h⟩
        · exact mem_cutsPHG_psi.mpr (Or.inr (Or.inl ⟨u', hu', h⟩))
        · simp [cutsPHG] at hu'
        · simp [cutsPNSG] at hu'
      have hfu := sub_fixP hV hV' hVV hs hVs hsu (lt_of_lt_of_le hVs (cutsHG_lev_cut (cutsPHG_sub hu))) hfix'
      rw [shf_eq_sh hV hV' hVV hla]
      exact mem_cutsPNSG_psi.mpr (Or.inl ⟨u, cutsPH_same_sh hV hV' hVV hs hVs ha hfu hu, rfl⟩)
    · rw [sh_psi_gt hVa, sh_z] at hfix
      rcases mem_cutsPNSG_psi.mp hfix with ⟨u', _, h⟩ | ⟨u', hu', h⟩ | ⟨u', hu', h⟩
      · exact ((cutsPH_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.1 | exact (T.psi.inj h).2.1.symm)).elim
      · have huu : u = u' := (T.psi.inj h).2.1
        have hfa : a = shf V V' a := (T.psi.inj h).1
        rw [← huu] at hu'
        exact mem_cutsPNSG_psi.mpr (Or.inr (Or.inl ⟨u, cutsPH_same_sh hV hV' hVV hs hVs (isOT_arg hot) hu' hu,
          by rw [← hfa]⟩))
      · simp [cutsPNSG] at hu'
    · rw [sh_psi_gt hVa] at hfix
      rcases mem_cutsPNSG_psi.mp hfix with ⟨u', _, h⟩ | ⟨u', _, h⟩ | ⟨u', hu', h⟩
      · exact ((cutsPNS_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.2 | exact (T.psi.inj h).2.2.symm)).elim
      · exact ((cutsPNS_ne_z hV hV' hVV hs hVs hu) (by first | exact (T.psi.inj h).2.2 | exact (T.psi.inj h).2.2.symm)).elim
      · have hfa : a = shf V V' a := (T.psi.inj h).1
        have hb : x = sh V V' x := (T.psi.inj h).2.1
        have huu : u = u' := (T.psi.inj h).2.2
        rw [← huu] at hu'
        exact mem_cutsPNSG_psi.mpr (Or.inr (Or.inr ⟨u, cutsPNS_same_sh (isOT_rest hot)
          (fun q hq => hge q (by simp [summands, hq])) hu' hu, by rw [← hfa, ← hb]⟩))

end


theorem prefB_refl : ∀ (s : T), prefB s s = true
  | z => rfl
  | psi a b c => by simp only [prefB, decide_true, Bool.true_and]; exact prefB_refl c

/-- A cut of itself is a prefix cut (the chains `Ω_s`, `Ω_{Ω_s}`, …). -/
theorem cutsPHG_of_self {s : T} : ∀ {t : T}, t ∈ cutsHG s t → t ∈ cutsPHG s t
  | z, ht => by simp [cutsHG] at ht
  | psi a x c, ht => by
    rcases mem_cutsHG_psi.mp ht with ⟨hsa, h⟩ | ⟨u, hu, h⟩ | ⟨hsa, u, hu, h⟩ | ⟨hsa, u, hu, h⟩
    · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj h
      exact mem_cutsPHG_psi.mpr (Or.inl ⟨hsa, prefB_refl _, rfl⟩)
    · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj h
      exact mem_cutsPHG_psi.mpr (Or.inr (Or.inl ⟨a, cutsPHG_of_self hu, rfl⟩))
    · obtain ⟨-, rfl, rfl⟩ := T.psi.inj h
      exact mem_cutsPHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hsa, x, cutsPHG_of_self hu, rfl⟩)))
    · obtain ⟨-, -, rfl⟩ := T.psi.inj h
      exact mem_cutsPHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hsa, c, cutsPHG_of_self hu, rfl⟩)))

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
  {s : T} (hs : isOT s = true) (hVs : V < s) (hps : prefB s (shf V V' s) = true)
include hV hV' hVV hs hVs hps

/-- **A cut of its own `σ` image is a prefix cut** when `s` starts `f(s)`: at the cut the term has `Ω_s`, and the
image has `Ω_{f(s)}` there. -/
theorem cutsPH_of_fix : ∀ {t : T}, t ∈ cutsHG s (sh V V' t) → t ∈ cutsPHG s (sh V V' t)
  | z, ht => by simp [cutsHG] at ht
  | psi a x c, ht => by
    by_cases hVa : V < a
    · rw [sh_psi_gt hVa] at ht ⊢
      rcases mem_cutsHG_psi.mp ht with ⟨hsa, h⟩ | ⟨u, hu, h⟩ | ⟨hsa, u, hu, h⟩ | ⟨hsa, u, hu, h⟩
      · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj h
        exact mem_cutsPHG_psi.mpr (Or.inl ⟨hsa, hps, rfl⟩)
      · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj h
        have hsu : s < a := cutsHG_gt hu
        have hlu : V < lev a := lt_of_lt_of_le hVs (cutsHG_lev_cut hu)
        rw [shf_eq_sh hV hV' hVV hlu] at hu ⊢
        exact mem_cutsPHG_psi.mpr (Or.inr (Or.inl ⟨a, cutsPH_of_fix hu, rfl⟩))
      · obtain ⟨hfa, rfl, rfl⟩ := T.psi.inj h
        refine mem_cutsPHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hsa, x, cutsPH_of_fix hu, ?_⟩)))
        rw [← hfa]
      · obtain ⟨hfa, hb, rfl⟩ := T.psi.inj h
        refine mem_cutsPHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hsa, c, cutsPH_of_fix hu, ?_⟩)))
        rw [← hfa, ← hb]
    · rw [sh_psi_le hVa] at ht ⊢
      exfalso
      rcases mem_cutsHG_psi.mp ht with ⟨hsa, _⟩ | ⟨u, hu, h⟩ | ⟨hsa, _⟩ | ⟨hsa, _⟩
      · exact hVa (lt_of_lt_of_le hVs (le_of_le_bool hsa))
      · obtain ⟨rfl, -, -⟩ := T.psi.inj h
        exact hVa (lt_trans hVs (cutsHG_gt hu))
      · exact hVa (lt_of_lt_of_le hVs (le_of_le_bool hsa))
      · exact hVa (lt_of_lt_of_le hVs (le_of_le_bool hsa))

theorem cutsPNS_of_fix : ∀ {B : T}, B ∈ cutsNSG s (sh V V' B) → B ∈ cutsPNSG s (sh V V' B)
  | z, ht => by simp [cutsNSG] at ht
  | psi a x c, ht => by
    by_cases hVa : V < a
    · rw [sh_psi_gt hVa] at ht ⊢
      rcases mem_cutsNSG_psi.mp ht with ⟨u, hu, h⟩ | ⟨u, hu, h⟩ | ⟨u, hu, h⟩
      · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj h
        have hlu : V < lev a := lt_of_lt_of_le hVs (cutsHG_lev_cut hu)
        rw [shf_eq_sh hV hV' hVV hlu] at hu ⊢
        exact mem_cutsPNSG_psi.mpr (Or.inl ⟨a, cutsPH_of_fix hV hV' hVV hs hVs hps hu, rfl⟩)
      · obtain ⟨hfa, rfl, rfl⟩ := T.psi.inj h
        refine mem_cutsPNSG_psi.mpr (Or.inr (Or.inl ⟨x, cutsPH_of_fix hV hV' hVV hs hVs hps hu, ?_⟩))
        rw [← hfa]
      · obtain ⟨hfa, hb, rfl⟩ := T.psi.inj h
        refine mem_cutsPNSG_psi.mpr (Or.inr (Or.inr ⟨c, cutsPNS_of_fix hu, ?_⟩))
        rw [← hfa, ← hb]
    · rw [sh_psi_le hVa] at ht ⊢
      rcases mem_cutsNSG_psi.mp ht with ⟨u, hu, h⟩ | ⟨u, hu, h⟩ | ⟨u, hu, h⟩
      · obtain ⟨rfl, -, -⟩ := T.psi.inj h
        exact absurd (lt_trans hVs (cutsHG_gt hu)) hVa
      · obtain ⟨-, rfl, rfl⟩ := T.psi.inj h
        exact mem_cutsPNSG_psi.mpr (Or.inr (Or.inl ⟨x, cutsPHG_of_self hu, rfl⟩))
      · obtain ⟨-, -, rfl⟩ := T.psi.inj h
        exact mem_cutsPNSG_psi.mpr (Or.inr (Or.inr ⟨c, cutsPNS_of_fix hu, rfl⟩))

end

/-- **The prefix cut of `σ X` carries to every `σ^{k+1} X`** (with the summands of `σ^{k+1} X` at least `Ω_{s+1}`). -/
theorem cutP_all {V s X : T} (hV : isOT V = true) (hs : isOT s = true) (hVs : V < s) (hX : isOT X = true)
    (hhi : AllGeT (psi (succ s) z z) (sh V s X)) (h0 : X ∈ cutsPNSG s (sh V s X)) :
    ∀ k, X ∈ cutsPNSG s (sh V s (shIt V s X k)) ∧ AllGeT (psi (succ s) z z) (sh V s (shIt V s X k))
  | 0 => ⟨h0, hhi⟩
  | k + 1 => by
    obtain ⟨h, ha⟩ := cutP_all hV hs hVs hX hhi h0 k
    have hot : isOT (sh V s (shIt V s X k)) = true := isOT_sh hV hs hVs (isOT_shIt hV hs hVs hX k)
    exact ⟨cutsPNS_same_sh hV hs hVs hs hVs hot ha h0 h,
      allGe_sh hV hs hVs hot (allGe_mono (om_le_succ hV hs hVs s) ha)⟩


/-- `(V + w) − V = w` for a single summand `w`. -/
theorem sub_add_single : ∀ (V : T) {d e : T}, sub (add V (psi d e z)) V = psi d e z
  | z, d, e => by show sub (psi d e z) z = psi d e z; simp [sub]
  | psi a b c, d, e => by
    rw [add_psi_psi]
    split
    · rename_i h; rw [sub_psi_psi, if_pos h]
    · rw [sub_psi_psi, if_neg (lt_irrefl' _)]; exact sub_add_single c

theorem add_single_self (d e : T) : add (psi d e z) (psi d e z) = app (psi d e z) (psi d e z) := by
  rw [add_psi_psi, if_neg (lt_irrefl' _)]; rfl

/-- `(V + w) + w = (V + w) ++ w` for a single summand `w`. -/
theorem add_add_single : ∀ (V : T) {d e : T}, add (add V (psi d e z)) (psi d e z) = app (add V (psi d e z)) (psi d e z)
  | z, d, e => add_single_self d e
  | psi a b c, d, e => by
    rw [add_psi_psi]
    split
    · exact add_single_self d e
    · rename_i h
      rw [add_psi_psi, if_neg h, add_add_single c, app_psi]

/-- **`s′ = V + w` starts `f(s′)`** when the single summand `w` has its subscript at most `V` (`σ` fixes `w`). -/
theorem prefB_shf_of_lev {V d e : T} (hl : ¬ V < d) :
    prefB (add V (psi d e z)) (shf V (add V (psi d e z)) (add V (psi d e z))) = true := by
  unfold shf
  rw [sub_add_single, sh_psi_le hl, sh_z, add_add_single]
  exact prefB_self_app _ _

end Ytosk.G
