/-
**G3 の切り口と t = 2 の置き換え σ（closure、2026-10-12）。**

V3PSh の `cutsH_sh`・`cutsNS_sh`・`ph3cKind_sh` の G3 版。新しい場合（添字の中の位置）は、
位置を含む添字の項の先頭の添字が s 以上（`cutsHG_lev`）なので、そこでは f = σ（`shf_eq_sh`）になり帰納法に戻る。
-/
import Ytosk.V3PKindG

namespace Ytosk

open T

/-- **A cut sits below a head subscript at least `s`.** -/
theorem cutsHG_lev {s : T} (hs : isOT s = true) : ∀ {h t : T}, isOT h = true → t ∈ cutsHG s h → s ≤ lev h
  | z, _, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, hh, ht => by
    simp only [lev_psi]
    rcases mem_cutsHG_psi.mp ht with ⟨hsa, _⟩ | ⟨u, hu, _⟩ | ⟨hsa, _, _, _⟩ | ⟨u, hu, _⟩
    · exact le_of_le_bool hsa
    · exact le_of_lt (lt_of_lt_of_le (cutsHG_gt hs (isOT_sub hh) hu) (cutsHG_le hu))
    · exact le_of_le_bool hsa
    · have h1 := cutsHG_lev hs (isOT_rest hh) hu
      cases c with
      | z => simp [cutsHG] at hu
      | psi c0 c1 c2 =>
        have hhc : head (psi c0 c1 c2) ≤ psi a x z := (isOT_psi_iff.mp hh).2.2.2.1
        simp only [lev_psi] at h1
        refine le_trans h1 ?_
        rcases (le_iff _ _).mp hhc with h | h
        · simp only [head] at h
          rw [psi_lt_psi_z_iff] at h
          rcases h with h | ⟨h, _⟩
          · exact le_of_lt h
          · rw [h]
        · simp only [head, psi.injEq] at h; rw [h.1]

/-- A cut has head subscript above `V`. -/
theorem cutsHG_lev_cut {s : T} (hs : isOT s = true) : ∀ {h t : T}, isOT h = true → t ∈ cutsHG s h → s ≤ lev t
  | z, _, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, hh, ht => by
    rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsa, _, _, rfl⟩ | ⟨u, hu, rfl⟩
    · simp
    · simp only [lev_psi]; exact le_of_lt (cutsHG_gt hs (isOT_sub hh) hu)
    · simp only [lev_psi]; exact le_of_le_bool hsa
    · simp only [lev_psi]; exact cutsHG_lev hs hh ht

/-- `sub a V ≠ 0` when `V < a` (no standard form needed). -/
theorem sub_ne_z_gen : ∀ {a V : T}, V < a → sub a V ≠ z
  | z, _, h => absurd h (T.not_lt_z _)
  | psi a b c, z, _ => by simp [sub]
  | psi a b c, psi d e f, h => by
    simp only [sub]
    split_ifs with hh
    · simp
    · have hhe : psi d e z = psi a b z := by
        rw [T.psi_lt_psi] at h
        rcases h with h1 | ⟨h1, h2⟩ | ⟨h1, h2, _⟩
        · exact absurd (psi_lt_psi_z_iff.mpr (Or.inl h1)) hh
        · exact absurd (psi_lt_psi_z_iff.mpr (Or.inr ⟨h1, h2⟩)) hh
        · rw [h1, h2]
      simp only [psi.injEq, and_true] at hhe
      obtain ⟨rfl, rfl⟩ := hhe
      have hcf : f < c := by
        rw [T.psi_lt_psi] at h
        rcases h with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
        · exact absurd h1 (lt_irrefl' _)
        · exact absurd h1 (lt_irrefl' _)
        · exact h1
      exact sub_ne_z_gen hcf

/-- `lev V′ < V′ + Y` for `V′, Y ≠ 0`. -/
theorem lev_lt_add {V' : T} (hV' : V' ≠ z) : ∀ {Y : T}, Y ≠ z → lev V' < add V' Y
  | z, h => absurd rfl h
  | psi y0 y1 y2, _ => by
    cases V' with
    | z => exact absurd rfl hV'
    | psi a b c =>
      simp only [lev_psi]
      rw [add_psi_psi]
      split_ifs with hh
      · have : psi a b z < psi y0 y1 z := hh
        exact lt_trans (lt_of_lt_of_le (lt_Om_self a) (psi_le_psi_z (le_refl a))) (lt_of_lt_of_le this
          (by rcases (le_iff _ _).mp (z_le y2) with h | h
              · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
              · rw [h]))
      · exact lt_of_lt_of_le (lt_Om_self a) (by
          rcases (le_iff _ _).mp (z_le (add c (psi y0 y1 y2))) with h | h
          · exact le_trans (psi_le_psi_z (le_refl a)) (le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
          · rw [← h]; exact psi_le_psi_z (le_refl a))

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **`f = σ` on a term whose head subscript is above `V`** (the term need not be standard). -/
theorem shf_eq_sh {t : T} (hVt : V < lev t) : shf V V' t = sh V V' t := by
  cases t with
  | z => exact absurd hVt (T.not_lt_z _)
  | psi a b c =>
    simp only [lev_psi] at hVt
    have hsub : sub (psi a b c) V = psi a b c := by
      cases hV0 : V with
      | z => rfl
      | psi d e f =>
        rw [sub_psi_psi, if_pos]
        have hlev : d < psi d e f := lt_of_lt_of_le (lt_Om_self d) (psi_le_psi_anyG (le_refl d))
        rw [hV0] at hVt
        exact psi_lt_psi_z_iff.mpr (Or.inl (lt_trans hlev hVt))
    have hV'z : V' ≠ z := fun h => by rw [h] at hVV; exact T.not_lt_z _ hVV
    unfold shf
    rw [hsub, sh_psi_gt hVt]
    apply add_eq_right_of_head_lt
    have hA := lev_lt_add hV'z (sh_ne_z (sub_ne_z_gen hVt) : sh V V' (sub a V) ≠ z)
    cases hV'0 : V' with
    | z => exact absurd hV'0 hV'z
    | psi d e f =>
      rw [hV'0] at hA
      simp only [head, lev_psi] at hA ⊢
      exact psi_lt_psi_z_iff.mpr (Or.inl hA)

variable {s : T} (hs : isOT s = true) (hVs : V < s)
include hs hVs

/-- **The G3 cuts under `σ`.** -/
theorem cutsHG_sh : ∀ {h t : T}, isOT h = true → t ∈ cutsHG s h → sh V V' t ∈ cutsHG (shf V V' s) (sh V V' h)
  | z, _, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, hot, ht => by
    have ha := isOT_sub hot
    rcases mem_cutsHG_psi.mp ht with ⟨hsa, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa, sh_psi_gt hVs]
      simp only [sh_z]
      exact mem_cutsHG_psi.mpr (Or.inl ⟨le_shf_of_le hV hV' hVV hs ha (le_of_lt hVs) (le_of_le_bool hsa), rfl⟩)
    · -- inside the subscript
      have hsu := cutsHG_gt hs ha hu
      have hVu : V < u := lt_trans hVs hsu
      have hVa : V < a := lt_of_lt_of_le hVu (cutsHG_le hu)
      have hla : V < lev a := lt_of_lt_of_le hVs (cutsHG_lev hs ha hu)
      have hlu : V < lev u := lt_of_lt_of_le hVs (cutsHG_lev_cut hs ha hu)
      rw [sh_psi_gt hVa, sh_psi_gt hVu, sh_z, shf_eq_sh hV hV' hVV hla, shf_eq_sh hV hV' hVV hlu]
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨_, cutsHG_sh ha hu, rfl⟩))
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa, sh_psi_gt hVa]
      simp only [sh_z]
      exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨le_shf_of_le hV hV' hVV hs ha (le_of_lt hVs)
        (le_of_le_bool hsa), _, cutsHG_sh (isOT_arg hot) hu, rfl⟩)))
    · by_cases hVa : V < a
      · rw [sh_psi_gt hVa, sh_psi_gt hVa]
        exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨_, cutsHG_sh (isOT_rest hot) hu, rfl⟩)))
      · rw [sh_psi_le hVa, sh_psi_le hVa]
        exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨_, cutsHG_sh (isOT_rest hot) hu, rfl⟩)))


/-- **The G3 cut positions of `PH3c` under `σ`.** -/
theorem cutsNSG_sh : ∀ {hi B : T}, isOT hi = true → AllGeT (psi (succ s) z z) hi →
    B ∈ cutsNSG s hi → sh V V' B ∈ cutsNSG (shf V V' s) (sh V V' hi)
  | z, _, _, _, hB => by simp [cutsNSG] at hB
  | psi a x c, B, hot, hge, hB => by
    have ha := isOT_sub hot
    have hsa : succ s ≤ a := by
      have h0 : ¬ psi a x z < psi (succ s) z z := hge _ (by simp [summands])
      rcases lt_or_ge a (succ s) with h | h
      · exact absurd (by rw [psi_lt_psi_z_iff]; exact Or.inl h) h0
      · exact h
    have hVa : V < a := lt_of_lt_of_le (lt_trans hVs (lt_succ_self s)) hsa
    rw [sh_psi_gt hVa]
    rcases mem_cutsNSG_psi.mp hB with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hVu : V < u := lt_trans hVs (cutsHG_gt hs ha hu)
      have hla : V < lev a := lt_of_lt_of_le hVs (cutsHG_lev hs ha hu)
      have hlu : V < lev u := lt_of_lt_of_le hVs (cutsHG_lev_cut hs ha hu)
      rw [sh_psi_gt hVu, sh_z, shf_eq_sh hV hV' hVV hla, shf_eq_sh hV hV' hVV hlu]
      exact mem_cutsNSG_psi.mpr (Or.inl ⟨_, cutsHG_sh hV hV' hVV hs hVs ha hu, rfl⟩)
    · rw [sh_psi_gt hVa, sh_z]
      exact mem_cutsNSG_psi.mpr (Or.inr (Or.inl ⟨_, cutsHG_sh hV hV' hVV hs hVs (isOT_arg hot) hu, rfl⟩))
    · rw [sh_psi_gt hVa]
      exact mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨_, cutsNSG_sh (isOT_rest hot)
        (fun q hq => hge q (by simp [summands, hq])) hu, rfl⟩))

/-- **The G3 kind of a frame is kept by `σ`** (`V < s`). -/
theorem ph3cKindG_sh {B y : T} (hB : isOT B = true) (hy : isOT y = true)
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s) :
    PH3cKindG (sh V V' B) (split (sh V V' y) (psi (succ (shf V V' s)) z z)).1
      (split (sh V V' y) (psi (succ (shf V V' s)) z z)).2 (shf V V' s) := by
  rw [sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hs hVs) hy]
  simp only
  set hi := (split y (psi (succ s) z z)).1
  set lo := (split y (psi (succ s) z z)).2
  have happ : app hi lo = y := split_app _ y
  have hhi : isOT hi = true := isOT_app_left (by rw [happ]; exact hy)
  have hne : ∀ {u : T}, isOT u = true → hi ≠ u → sh V V' hi ≠ sh V V' u :=
    fun hu h e => h (sh_inj hV hV' (le_of_lt hVV) hhi hu e)
  rcases hK with ⟨h1, h2⟩ | ⟨h1, (⟨R, hR, h2⟩ | ⟨h2, h3⟩)⟩
  · exact Or.inl ⟨by rw [h1], fun h => h2 (sh_eq_z_iff.mp h)⟩
  · refine Or.inr ⟨hne hB h1, Or.inl ⟨sh V V' R, fun h => hR (sh_eq_z_iff.mp h), ?_⟩⟩
    rw [h2, sh_app]
  · refine Or.inr ⟨hne hB h1, Or.inr ⟨?_, cutsNSG_sh hV hV' hVV hs hVs hhi (split_fst_ge _ y) h3⟩⟩
    intro h
    have := lt_shf hV hV' (le_of_lt hVV) hs hVs
    rw [h] at this; exact T.not_lt_z _ this

end

end Ytosk
