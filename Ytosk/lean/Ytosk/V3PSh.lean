/-
**PH3c の種類は t = 2 の置き換え σ で保たれる（closure、2026-10-11）。**

t = 2 の写しの枠は M[n − 1] の枠の σ の像（B・y は σ、添字 s は f(s) = V′ + σ(s − V)、実測 169/169、V < s）。
ここでは行列によらない順序数の補題を示す: V < s なら PH3cKind B hi lo s から
PH3cKind σ(B) σ(hi) σ(lo) f(s)（σ(hi)・σ(lo) は σ(y) を Ω_{f(s)+1} で分けたもの、`sh_split`）。
- 添字が V より大きい項では f と σ は先頭の添字を f で移す同じ形（`shf_psi`）。
- 切り口の位置への道の節点は添字が s 以上（高い道）で V より大きいので、σ はその中に入る（`cutsH_sh`・`scuts_shf`）。
-/
import Ytosk.V3PKind
import Ytosk.V3SubstC

namespace Ytosk

open T

/-! ## 切り口の大きさ -/

theorem le_of_le_bool {t a : T} (h : le t a = true) : t ≤ a := by
  simp only [le, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · rw [h]
  · exact le_of_lt h

theorem psi_le_psi_any {s a x c : T} (h : s ≤ a) : psi s z z ≤ psi a x c :=
  le_trans (psi_le_psi_z (y := x) h) (by
    rcases (le_iff _ _).mp (z_le c) with h' | h'
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩))
    · rw [h'])

theorem cutsH_le {s : T} : ∀ {h t : T}, t ∈ cutsH s h → t ≤ h
  | z, _, ht => by simp [cutsH] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsH_psi.mp ht with ⟨hs, rfl⟩ | ⟨_, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact psi_le_psi_any (le_of_le_bool hs)
    · rcases (le_iff _ _).mp (cutsH_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩))
      · rcases (le_iff _ _).mp (z_le c) with h | h
        · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
        · rw [h]
    · rcases (le_iff _ _).mp (cutsH_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
      · exact le_refl _

theorem scuts_le {s : T} : ∀ {h t : T}, t ∈ scuts s h → t ≤ h
  | z, _, ht => by simp [scuts] at ht
  | psi a x c, t, ht => by
    simp only [scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · split at ht
      · rename_i hs
        simp only [List.mem_singleton] at ht; subst ht
        exact psi_le_psi_any (le_of_le_bool hs)
      · simp at ht
    · exact psi_le_psi_any (scuts_le hu)

theorem scuts_isOT {s : T} (hs : isOT s = true) : ∀ {h t : T}, t ∈ scuts s h → isOT t = true
  | z, _, ht => by simp [scuts] at ht
  | psi a x c, t, ht => by
    simp only [scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · split at ht
      · simp only [List.mem_singleton] at ht; subst ht; exact isOT_om.mpr hs
      · simp at ht
    · exact isOT_om.mpr (scuts_isOT hs hu)

/-! ## σ と切り口 -/

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **`f` on a term whose head subscript is above `V`** moves the head subscript by `f` like `σ`. -/
theorem shf_psi {a b c : T} (ha : isOT a = true) (hVa : V < a) :
    shf V V' (psi a b c) = psi (shf V V' a) (sh V V' b) (sh V V' c) := by
  have hhead : head V < psi a b z :=
    lt_of_le_of_lt (head_le_self V) (lt_of_lt_of_le (lt_trans hVa (lt_Om_self a)) (psi_le_psi_z (le_refl a)))
  have hsub : sub (psi a b c) V = psi a b c := by
    cases V with
    | z => exact sub_z_right _
    | psi d e f => rw [sub_psi_psi, if_pos (show psi d e z < psi a b z from hhead)]
  unfold shf; rw [hsub, sh_psi_gt hVa]
  have hV'h : head V' < psi (shf V V' a) (sh V V' b) z :=
    lt_of_le_of_lt (head_le_self V') (lt_of_lt_of_le (lt_trans (lt_shf hV hV' (le_of_lt hVV) ha hVa)
      (lt_Om_self _)) (psi_le_psi_z (le_refl _)))
  cases V' with
  | z => rfl
  | psi d e f => rw [add_psi_psi, if_pos (show psi d e z < _ from hV'h)]; rfl

theorem le_shf_of_le {t a : T} (ht : isOT t = true) (ha : isOT a = true) (hVt : V ≤ t) (h : t ≤ a) :
    le (shf V V' t) (shf V V' a) = true := by
  rcases (le_iff _ _).mp h with h | rfl
  · simp [le, show lt (shf V V' t) (shf V V' a) = true from shf_lt_shf hV hV' (le_of_lt hVV) ht ha hVt h]
  · simp [le]

variable {s : T} (hs : isOT s = true) (hVs : V < s)
include hs hVs

/-- **The subscript chain under `f`.** -/
theorem scuts_shf : ∀ {h t : T}, isOT h = true → t ∈ scuts s h → shf V V' t ∈ scuts (shf V V' s) (shf V V' h)
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
        rw [shf_psi hV hV' hVV ha hVa, shf_psi hV hV' hVV hs hVs]
        simp only [sh_z, scuts, List.mem_append, List.mem_map]
        left
        rw [if_pos (le_shf_of_le hV hV' hVV hs ha (le_of_lt hVs) hsa')]
        simp
      · simp at ht
    · have hu1 := scuts_ge hu
      have hu2 := scuts_le hu
      have hVu : V < u := lt_of_lt_of_le (lt_trans hVs (lt_Om_self s)) hu1
      have hVa : V < a := lt_of_lt_of_le hVu hu2
      have huot := scuts_isOT hs hu
      rw [shf_psi hV hV' hVV ha hVa, shf_psi hV hV' hVV huot hVu]
      simp only [sh_z, scuts, List.mem_append, List.mem_map]
      right
      exact ⟨shf V V' u, scuts_shf ha hu, rfl⟩

/-- **The high-path cuts under `σ`.** -/
theorem cutsH_sh : ∀ {h t : T}, isOT h = true → t ∈ cutsH s h → sh V V' t ∈ cutsH (shf V V' s) (sh V V' h)
  | z, _, _, ht => by simp [cutsH] at ht
  | psi a x c, t, hot, ht => by
    have ha := isOT_sub hot
    rcases mem_cutsH_psi.mp ht with ⟨hsa, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa, sh_psi_gt hVs]
      simp only [sh_z]
      exact mem_cutsH_psi.mpr (Or.inl ⟨le_shf_of_le hV hV' hVV hs ha (le_of_lt hVs) (le_of_le_bool hsa), rfl⟩)
    · have hVa : V < a := lt_of_lt_of_le hVs (le_of_le_bool hsa)
      rw [sh_psi_gt hVa, sh_psi_gt hVa]
      simp only [sh_z]
      exact mem_cutsH_psi.mpr (Or.inr (Or.inl ⟨le_shf_of_le hV hV' hVV hs ha (le_of_lt hVs) (le_of_le_bool hsa),
        _, cutsH_sh (isOT_arg hot) hu, rfl⟩))
    · by_cases hVa : V < a
      · rw [sh_psi_gt hVa, sh_psi_gt hVa]
        exact mem_cutsH_psi.mpr (Or.inr (Or.inr ⟨_, cutsH_sh (isOT_rest hot) hu, rfl⟩))
      · rw [sh_psi_le hVa, sh_psi_le hVa]
        exact mem_cutsH_psi.mpr (Or.inr (Or.inr ⟨_, cutsH_sh (isOT_rest hot) hu, rfl⟩))

/-- **The cut positions of `PH3c` under `σ`.** -/
theorem cutsNS_sh : ∀ {hi B : T}, isOT hi = true → AllGeT (psi (succ s) z z) hi →
    B ∈ cutsNS s hi → sh V V' B ∈ cutsNS (shf V V' s) (sh V V' hi)
  | z, _, _, _, hB => by simp [cutsNS] at hB
  | psi a x c, B, hot, hge, hB => by
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
    · have hVu : V < u := lt_of_lt_of_le (lt_trans hVs (lt_Om_self s)) (scuts_ge hu)
      rw [sh_psi_gt hVu]
      simp only [sh_z]
      exact Or.inl (Or.inl ⟨_, scuts_shf hV hV' hVV hs hVs ha hu, rfl⟩)
    · rw [sh_psi_gt hVa]
      simp only [sh_z]
      exact Or.inl (Or.inr ⟨_, cutsH_sh hV hV' hVV hs hVs (isOT_arg hot) hu, rfl⟩)
    · rw [sh_psi_gt hVa]
      exact Or.inr ⟨_, cutsNS_sh (isOT_rest hot) (fun q hq => hge q (by simp [summands, hq])) hu, rfl⟩

/-- **The kind of a frame is kept by `σ`** (`V < s`). -/
theorem ph3cKind_sh {B y : T} (hB : isOT B = true) (hy : isOT y = true)
    (hK : PH3cKind B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s) :
    PH3cKind (sh V V' B) (split (sh V V' y) (psi (succ (shf V V' s)) z z)).1
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
  · refine Or.inr ⟨hne hB h1, Or.inr ⟨?_, cutsNS_sh hV hV' hVV hs hVs hhi (split_fst_ge _ y) h3⟩⟩
    intro h
    have := lt_shf hV hV' (le_of_lt hVV) hs hVs
    rw [h] at this; exact T.not_lt_z _ this

end

/-! ## FC3 の結論と σ -/

theorem last_mem_summands : ∀ {t : T}, t ≠ z → last t ∈ summands t
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last, summands]
  | psi a b (psi c d e), _ => by
    have := last_mem_summands (t := psi c d e) (by simp)
    simp only [last, summands, List.mem_cons] at this ⊢
    exact Or.inr this

theorem isOT_headT : ∀ {x : T}, isOT x = true → isOT (head x) = true
  | z, _ => rfl
  | psi _ _ _, h => isOT_head h

theorem last_le_head : ∀ {x : T}, isOT x = true → last x ≤ head x
  | z, _ => le_refl _
  | psi a b z, _ => le_refl _
  | psi a b (psi c d e), h => by
    have h1 := last_le_head (isOT_rest h)
    have h2 : head (psi c d e) ≤ psi a b z := (isOT_psi_iff.mp h).2.2.2.1
    simp only [last, head] at h1 h2 ⊢
    exact le_trans h1 h2

/-- Adding a term whose head is at most the last summand is concatenation. -/
theorem add_eq_app_of_last : ∀ {x y : T}, isOT x = true → head y ≤ last x → add x y = app x y
  | z, y, _, _ => by simp [add, app]
  | psi a b z, y, _, h => by
    cases y with
    | z => rfl
    | psi d e f =>
      rw [add_psi_psi, if_neg (not_lt_of_ge (by simpa [head, last] using h))]; rfl
  | psi a b (psi c d e), y, hx, h => by
    cases y with
    | z => simp [add, app]
    | psi f g k =>
      have hl : last (psi c d e) ≤ psi a b z :=
        le_trans (last_le_head (isOT_rest hx)) ((isOT_psi_iff.mp hx).2.2.2.1)
      have hn : ¬ psi a b z < psi f g z := not_lt_of_ge (le_trans (by simpa [head, last] using h) hl)
      rw [add_psi_psi, if_neg hn]
      show psi a b (add (psi c d e) (psi f g k)) = psi a b (app (psi c d e) (psi f g k))
      rw [add_eq_app_of_last (isOT_rest hx) (by simpa [last] using h)]

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **The FC3 conclusion is kept by `σ`** (`V ≤ a`, `V < s`). -/
theorem fc3c_sh {a s y : T} (ha : isOT a = true) (hVa : V ≤ a) (hs : isOT s = true) (hVs : V < s)
    (hy : isOT y = true) (h : (split y (psi (succ s) z z)).1 ≠ z → FC3c a s y)
    (hhi : (split (sh V V' y) (psi (succ (shf V V' s)) z z)).1 ≠ z) :
    FC3c (shf V V' a) (shf V V' s) (sh V V' y) := by
  unfold FC3c
  rw [sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hs hVs) hy] at hhi ⊢
  simp only at hhi ⊢
  set hi := (split y (psi (succ s) z z)).1 with hhidef
  have hhiz : hi ≠ z := fun e => hhi (by rw [e, sh_z])
  obtain ⟨hA, hB⟩ := h hhiz
  have happ : app hi (split y (psi (succ s) z z)).2 = y := split_app _ y
  have hhiot : isOT hi = true := isOT_app_left (by rw [happ]; exact hy)
  refine ⟨fun he => ?_, fun hne => ?_⟩
  · have hsa : s = a := (shf_eq_iff hV hV' hVV hs ha (le_of_lt hVs) hVa).mp he
    obtain ⟨h1, h2⟩ := hA hsa
    refine ⟨fun e => by
      have := lt_shf hV hV' (le_of_lt hVV) hs hVs
      rw [e] at this; exact T.not_lt_z _ this, fun e => h2 ?_⟩
    rw [last_shf hV hV' hVV hs hVs, ← sh_one (V := V) (V' := V')] at e
    exact sh_inj hV hV' (le_of_lt hVV) (isOT_last hs) isOT_one e
  · have hsa : s ≠ a := fun e => hne (by rw [e])
    obtain ⟨X, hX, hlev⟩ := hB hsa
    cases hhic : hi with
    | z => exact absurd hhic hhiz
    | psi k b c =>
      rw [← hhidef, hhic] at hlev
      rw [hhic] at hhiot
      simp only [lev] at hlev
      have hkot : isOT k = true := isOT_sub hhiot
      have hsX : isOT (app s X) = true := by rw [← hlev]; exact hkot
      have hXot : isOT X = true := isOT_app_right hsX
      have hVk : V < k := by rw [hlev]; exact lt_of_lt_of_le hVs (le_of_lt (lt_app_of hX))
      rw [sh_psi_gt hVk]
      simp only [lev]
      refine ⟨sh V V' X, fun e => hX (sh_eq_z_iff.mp e), ?_⟩
      rw [hlev, ← add_eq_app hsX, shf_add hV hV' hVV hs hXot (le_of_lt hVs)]
      apply add_eq_app_of_last (isOT_shf hV hV' hVV hs)
      rw [last_shf hV hV' hVV hs hVs, head_sh]
      have hs0 : s ≠ z := fun e => by rw [e] at hVs; exact T.not_lt_z _ hVs
      have hlast : head X ≤ last s := by
        exact summand_ge_of_app hsX (last_mem_summands hs0)
      exact sh_le_sh hV hV' (le_of_lt hVV) (isOT_headT hXot) (isOT_last hs) hlast

end

end Ytosk
