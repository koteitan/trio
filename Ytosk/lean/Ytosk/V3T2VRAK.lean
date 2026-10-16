/-
**t = 2: 写しの枠の σ 移送 QVRAshK の枠の条件 KVRA（2026-10-17、t1）。**

項だけの σ 移送（QVRAsh）は偽なので（V3T2VRA の注）、枠の条件 K を 3 つの値の条件に分ける。段 u ≤ V で
f(s) の成分 g′ は (A) σ で動く位置の成分の像 σ g、(B) 動かない位置の成分 g、(C) V′ の加数の成分のどれか
（`comps_sh_levA`、t0 の comps_sh_lev の (A) を動く位置 `compsAN` に絞ったもの）。
- (C): t0 の共有の条件 `VDomF V V′ a`（V′ の成分は Ω_{f a} 以下か f(a) の成分以下）。Ω_{f a} ≤ Ω_{f s}。
- (B): P の 3 つの選択肢をそのまま運ぶ。第 3 の選択肢 g ≤ d（d ∈ comps u a）は `KA`（d は Ω_{f a} 以下か f(a) のある成分以下）で。
- (A): 動く位置の成分は P で第 1 か第 2 の選択肢（`KG`）。σ は単調なので運べる。
-/
import Ytosk.V3T2VRA
import Ytosk.V3SubstLev
import Ytosk.V3RwClCopy

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The components at the moving positions** (under subscripts `> V` only), with fuel `n`. -/
def compsAN (V u : T) : Nat → T → List T
  | 0, _ => []
  | _ + 1, z => []
  | n + 1, psi s y c =>
    (if ¬ lt s u = true ∧ lt V s = true then y :: (compsAN V u n y ++ compsAN V u n (sub s V)) else []) ++
      compsAN V u n c

theorem compsAN_sub (V u : T) : ∀ (n : Nat) {t g : T}, g ∈ compsAN V u n t → g ∈ comps u t
  | 0, _, _, h => by simp [compsAN] at h
  | n + 1, z, _, h => by simp [compsAN] at h
  | n + 1, psi s y c, g, h => by
    simp only [compsAN, List.mem_append] at h
    rcases h with h | h
    · by_cases hc : ¬ lt s u = true ∧ lt V s = true
      · rw [if_pos hc] at h
        have hsu : ¬ s < u := hc.1
        simp only [List.mem_cons, List.mem_append] at h
        rcases h with rfl | h | h
        · exact comps_psi_mem_of hsu (Or.inl rfl)
        · exact comps_psi_mem_of hsu (Or.inr (Or.inl (compsAN_sub V u n h)))
        · exact comps_psi_mem_of hsu (Or.inr (Or.inr (Or.inl (comps_sub_sub u s V (compsAN_sub V u n h)))))
      · rw [if_neg hc] at h; simp at h
    · exact mem_comps_tail (compsAN_sub V u n h)

/-- **The components of `σ t` at a level `u ≤ V`**: `σ g` for a component at a moving position, a component `g`
of `t`, or a component of a summand of `V′`. -/
theorem comps_sh_levA (V V' : T) {u : T} (huV : u ≤ V) :
    ∀ (n : Nat) (t g' : T), size t ≤ n → g' ∈ comps u (sh V V' t) →
      (∃ g ∈ compsAN V u n t, g' = sh V V' g) ∨ (∃ g ∈ comps u t, g' = g) ∨
        (∃ q ∈ summands V', g' ∈ comps u q)
  | 0, t, g', hn, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi => simp [size] at hn
  | n + 1, t, g', hn, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi s y c =>
      have hny : size y ≤ n := by simp [size] at hn; omega
      have hnc : size c ≤ n := by simp [size] at hn; omega
      have hns : size (sub s V) ≤ n := by have := size_sub_le s V; simp [size] at hn; omega
      have hA : ∀ {g}, g ∈ compsAN V u n c → g ∈ compsAN V u (n + 1) (psi s y c) := fun h => by
        simp only [compsAN, List.mem_append]; exact Or.inr h
      have htail : g' ∈ comps u (sh V V' c) →
          (∃ g ∈ compsAN V u (n + 1) (psi s y c), g' = sh V V' g) ∨ (∃ g ∈ comps u (psi s y c), g' = g) ∨
            (∃ q ∈ summands V', g' ∈ comps u q) := by
        intro h
        rcases comps_sh_levA V V' huV n c g' hnc h with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | h
        · exact Or.inl ⟨g, hA hg, e⟩
        · exact Or.inr (Or.inl ⟨g, mem_comps_tail hg, e⟩)
        · exact Or.inr (Or.inr h)
      by_cases hVs : V < s
      · have hsu : ¬ s < u := fun h => absurd (lt_of_lt_of_le h huV) (not_lt.mpr (le_of_lt hVs))
        have hmov : ∀ {g}, g = y ∨ g ∈ compsAN V u n y ∨ g ∈ compsAN V u n (sub s V) →
            g ∈ compsAN V u (n + 1) (psi s y c) := by
          intro g h
          simp only [compsAN, List.mem_append]
          left
          rw [if_pos ⟨hsu, hVs⟩]
          simp only [List.mem_cons, List.mem_append]
          exact h
        rw [sh_psi_gt hVs] at hg
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · by_cases hf : shf V V' s < u
          · rw [if_pos (show lt (shf V V' s) u = true from hf)] at hg; simp at hg
          rw [if_neg (show ¬ lt (shf V V' s) u = true from hf)] at hg
          simp only [List.mem_cons, List.mem_append] at hg
          rcases hg with rfl | hg | hg
          · exact Or.inl ⟨y, hmov (Or.inl rfl), rfl⟩
          · rcases comps_sh_levA V V' huV n y g' hny hg with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | h
            · exact Or.inl ⟨g, hmov (Or.inr (Or.inl hg)), e⟩
            · exact Or.inr (Or.inl ⟨g, comps_psi_mem_of hsu (Or.inr (Or.inl hg)), e⟩)
            · exact Or.inr (Or.inr h)
          · unfold shf at hg
            obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
            rw [hP, comps_app] at hg
            rcases List.mem_append.mp hg with hg | hg
            · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
              exact Or.inr (Or.inr ⟨q, hPs q hq, hgq⟩)
            · rcases comps_sh_levA V V' huV n (sub s V) g' hns hg with ⟨g, hg, e⟩ | ⟨g, hg, e⟩ | h
              · exact Or.inl ⟨g, hmov (Or.inr (Or.inr hg)), e⟩
              · exact Or.inr (Or.inl ⟨g, comps_psi_mem_of hsu
                  (Or.inr (Or.inr (Or.inl (comps_sub_sub u s V hg)))), e⟩)
              · exact Or.inr (Or.inr h)
        · exact htail hg
      · rw [sh_psi_le hVs] at hg
        simp only [comps, List.mem_append] at hg
        rcases hg with hg | hg
        · by_cases hf : s < u
          · rw [if_pos (show lt s u = true from hf)] at hg; simp at hg
          · rw [if_neg (show ¬ lt s u = true from hf)] at hg
            simp only [List.mem_cons, List.mem_append] at hg
            rcases hg with e | hg | hg
            · exact Or.inr (Or.inl ⟨y, comps_psi_mem_of hf (Or.inl rfl), e⟩)
            · exact Or.inr (Or.inl ⟨g', comps_psi_mem_of hf (Or.inr (Or.inl hg)), rfl⟩)
            · exact Or.inr (Or.inl ⟨g', comps_psi_mem_of hf (Or.inr (Or.inr (Or.inl hg))), rfl⟩)
        · exact htail hg

/-- **The frame condition `K` of the copy frames** at a level `u`: `VDomF` (the components of `V′`), `KA`
(each component of `a` is below `Ω_{f(a)}` or a component of `f(a)`), `KG` (a component at a moving position of `s − V` is
below `Ω_s` or the sum before). -/
def KAG (V V' a : T) (Lv : List T) (cv u : T) : Prop :=
  (∀ d ∈ comps u a, d ≤ psi (shf V V' a) z z ∨ ∃ d' ∈ comps u (shf V V' a), d ≤ d') ∧
    (∀ s y, cv = psi s y z → V < s → ∀ n, ∀ g ∈ compsAN V u n (sub s V),
      g ≤ psi s z z ∨ g ≤ spArg a z (sumN Lv))

def KVRA (V V' a : T) (Lv : List T) (cv u : T) : Prop := VDomF V V' a ∧ KAG V V' a Lv cv u

/-- **`QVRAt` moves with `σ` under `KVRA`.** -/
theorem qVRAshK_KVRA : QVRAshK KVRA := by
  intro V V' a Lv cv u hV hV' hVV ha hVa hs hp hlev huV hK hQ
  obtain ⟨hVD, hKA, hKG⟩ := hK
  have hVV' : V ≤ V' := le_of_lt hVV
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  have hsot : isOT s = true := isOT_sub hcvot
  have hyot : isOT y = true := isOT_arg hcvot
  have hfa : isOT (shf V V' a) = true := isOT_shf hV hV' hVV ha
  have hua : ¬ a < u := not_lt.mpr (le_trans huV hVa)
  have hufa : ¬ shf V V' a < u := not_lt.mpr (le_trans (le_trans huV hVa) (le_shf_self hV hV' hVV' ha hVa))
  intro s' y' hcv' ht' hhi' _ g' hg'
  rw [hB] at ht' ⊢
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have hsy : isOT (psi s y z) = true := hcvot
    -- the premises of `P`
    have ht1 : lt (spArg a z (sumN Lv)) y = true :=
      (sh_lt_iff hV hV' hVV' hBot hyot).mp ht'.1
    have ht2 : lt (psi a z z) (psi s y z) = true := by
      by_cases hVa' : V < a
      · have e1 : sh V V' (psi a z z) = psi (shf V V' a) z z := by rw [sh_psi_gt hVa', sh_z]
        have e2 : sh V V' (psi s y z) = psi (shf V V' s) (sh V V' y) z := by rw [sh_psi_gt hVs, sh_z]
        have h2 : sh V V' (psi a z z) < sh V V' (psi s y z) := by rw [e1, e2]; exact ht'.2
        exact (sh_lt_iff hV hV' hVV' (isOT_psi_zz ha) hsy).mp h2
      · have hVa2 : a = V := by
          rcases (le_iff _ _).mp hVa with h | h
          · exact absurd h hVa'
          · exact h.symm
        show psi a z z < psi s y z
        rw [T.psi_lt_psi]; left; rw [hVa2]; exact hVs
    have hsplit := sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hsot hVs) hyot
    have hhi : (split y (psi (succ s) z z)).1 ≠ z := by
      intro h; apply hhi'; rw [hsplit, h, sh_z]
    have hQ' := hQ s y rfl ⟨ht1, ht2⟩ hhi hua
    -- `a ≤ s`, `Ω_{f a} ≤ Ω_{f s}`, `Ω_s ≤ Ω_{f s}`
    have has : a ≤ s := by
      have h2 : psi a z z < psi s y z := ht2
      rw [T.psi_lt_psi] at h2
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact le_of_lt h
      · rw [h]
      · rw [h]
    have hVs' : V ≤ s := le_of_lt hVs
    have hOmA : psi (shf V V' a) z z ≤ psi (shf V V' s) z z := by
      rcases (le_iff _ _).mp has with h | h
      · exact psi_le_psi_of (Or.inl (shf_lt_shf hV hV' hVV' ha hsot hVa h))
      · rw [h]
    have hOmS : psi s z z ≤ psi (shf V V' s) z z := by
      rcases (le_iff _ _).mp (le_shf_self hV hV' hVV' hsot hVs') with h | h
      · exact psi_le_psi_of (Or.inl h)
      · rw [← h]
    have hshOm : sh V V' (psi s z z) = psi (shf V V' s) z z := by rw [sh_psi_gt hVs, sh_z]
    -- the components of `V′`
    have hVpart : g' ∈ comps u V' → g' ≤ psi (shf V V' s) z z ∨
        g' ≤ sh V V' (spArg a z (sumN Lv)) ∨ ∃ d ∈ comps u (shf V V' a), g' ≤ d := by
      intro h
      rcases hVD u hufa g' h with h1 | h1
      · exact Or.inl (le_trans h1 hOmA)
      · exact Or.inr (Or.inr h1)
    unfold shf at hg'
    obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
    rw [hP, comps_app] at hg'
    rcases List.mem_append.mp hg' with hg | hg
    · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
      exact hVpart (comps_of_mem_summands (hPs q hq) hgq)
    · rcases comps_sh_levA V V' huV (size (sub s V)) (sub s V) g' (Nat.le_refl _) hg with
        ⟨g, hgA, e⟩ | ⟨g, hgB, e⟩ | ⟨q, hq, hgq⟩
      · rw [e]
        have hgs := comps_sub_sub u s V (compsAN_sub V u _ hgA)
        have hgot : isOT g = true := isOT_of_mem_comps u hsot hgs
        rcases hKG s y rfl hVs _ g hgA with h | h
        · left
          have := sh_le_sh hV hV' hVV' hgot (isOT_psi_zz hsot) h
          rwa [hshOm] at this
        · right; left
          exact sh_le_sh hV hV' hVV' hgot hBot h
      · rw [e]
        have hgs := comps_sub_sub u s V hgB
        rcases hQ' g hgs with h | h | ⟨d, hd, h⟩
        · exact Or.inl (le_trans h hOmS)
        · exact Or.inr (Or.inl (le_trans h (le_sh hV hV' hVV' hBot)))
        · rcases hKA d hd with hdd | ⟨d', hd', hdd⟩
          · exact Or.inl (le_trans h (le_trans hdd hOmA))
          · exact Or.inr (Or.inr ⟨d', hd', le_trans h hdd⟩)
      · exact hVpart (comps_of_mem_summands hq hgq)
  · exfalso
    rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have h2 : psi (shf V V' a) z z < psi s y z := ht'.2
    rw [T.psi_lt_psi] at h2
    have hfs : shf V V' a ≤ s := by
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact le_of_lt h
      · rw [h]
      · rw [h]
    have : V' ≤ V := le_trans (le_shf hV hV' hVV' ha hVa) (le_trans hfs (le_of_not_gt hVs))
    exact absurd hVV (not_lt.mpr this)

/-- **The residual `T2VRAK KVRA`** from t0's shared `T2CopyK CopyVDomK` and the `a`/moving-position part. -/
theorem t2VRAK_KVRA_of {M : Mat} (hVD : T2CopyK CopyVDomK M) (hAG : T2VRAK KAG M) : T2VRAK KVRA M :=
  fun r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV =>
    ⟨hVD r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL,
      hAG r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV⟩

end Ytosk
