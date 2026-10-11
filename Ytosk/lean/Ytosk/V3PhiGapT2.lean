/-
**t = 2 の置き換え σ で「正の段の隙間なし」が保たれる。**

- `NoGap V` は「V の部分項 ψ_μ(b) + c（μ ≠ 0）はどれも b < Ω_{μ+1}」（`NoGapS`）と同じ（`noGap_iff_noGapS`）。
- σ（`sh`）と f（`shf`）はこの形を保つ（`noGapS_sh`・`noGap_shf`）。新しい頭 ψ_{f(s)}(σ y) では
  σ y < σ(Ω_{s+1}) = Ω_{f(s)+1}（σ は順序を保ち、f(s + 1) = f(s) + 1）。
- 実測（C′ の t = 2、n = 2..4）: 写しの r の値 V′ = v_N(r + L) は 18720 件すべて隙間なし。
  M[n] の行 1 の子を持つ列で、写しの守られた列の値は f(v_{M[n−1]}) で、元の列も行 1 の子を持つ。
-/
import Ytosk.V3PhiGap
import Ytosk.V3SubstC
import Ytosk.V3ExpT2V

namespace Ytosk

open T

/-- **Single-subterm form of `NoGap`**: every subterm `ψ_μ(b) + c` with `μ ≠ 0` has `b < Ω_{μ+1}`. -/
def NoGapS (V : T) : Prop :=
  ∀ μ b c, SubT (psi μ b c) V → μ ≠ z → b < psi (succ μ) z z

theorem noGapS_of_noGap {V : T} (h : NoGap V) : NoGapS V := by
  intro μ b c hs hμ
  have hu : SubS V (psi μ b z) := ⟨_, hs, Or.inr ⟨μ, b, c, rfl, rfl⟩⟩
  have hlt : psi μ b z < psi (succ μ) z z := by
    rw [T.psi_lt_psi]; exact Or.inl (lt_succ_iff.mpr (le_refl _))
  have := h μ hμ _ hu hlt
  unfold etaOm at this
  rw [T.psi_lt_psi] at this
  rcases this with h1 | ⟨_, h2⟩ | ⟨_, _, h3⟩
  · exact absurd h1 (lt_irrefl' _)
  · exact h2
  · exact absurd h3 (T.not_lt_z _)

theorem noGap_of_noGapS {V : T} (h : NoGapS V) : NoGap V := by
  intro μ hμ u hu hlt
  obtain ⟨w, hw, hu⟩ := hu
  have key : ∀ b c, SubT (psi μ b c) V → ¬ (psi μ b z < etaOm μ) → False := by
    intro b c hs hn
    apply hn
    unfold etaOm; rw [T.psi_lt_psi]
    exact Or.inr (Or.inl ⟨rfl, h μ b c hs hμ⟩)
  by_contra hn
  have hge : etaOm μ ≤ u := le_of_not_gt hn
  cases u with
  | z => exact absurd hge (not_le_of_gt (T.z_lt_psi _ _ _))
  | psi a b c =>
    -- `u = ψ_a(b) + c` with `a ≤ μ`, and `ψ_μ(Ω_{μ+1}) ≤ u` forces `a = μ`, `Ω_{μ+1} ≤ b`
    have hs : ∃ c', SubT (psi a b c') V := by
      rcases hu with rfl | ⟨a', b', c', rfl, he⟩
      · exact ⟨c, hw⟩
      · cases he; exact ⟨c', hw⟩
    obtain ⟨c', hs⟩ := hs
    have ha : a ≤ μ := by
      rw [T.psi_lt_psi] at hlt
      rcases hlt with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
      · exact lt_succ_iff.mp h1
      · exact absurd h1 (T.not_lt_z _)
      · exact absurd h1 (T.not_lt_z _)
    unfold etaOm at hge
    rcases (le_iff _ _).mp hge with h1 | h1
    · rw [T.psi_lt_psi] at h1
      rcases h1 with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, _⟩
      · exact absurd (lt_of_lt_of_le h1 ha) (lt_irrefl' _)
      · exact absurd (h μ b c' hs hμ) (not_lt_of_gt h1)
      · exact absurd (h μ _ c' hs hμ) (lt_irrefl' _)
    · cases h1
      exact absurd (h μ _ c' hs hμ) (lt_irrefl' _)

theorem noGap_iff_noGapS {V : T} : NoGap V ↔ NoGapS V := ⟨noGapS_of_noGap, noGap_of_noGapS⟩

theorem NoGapS.of_subT {V w : T} (h : NoGapS V) (hw : SubT w V) : NoGapS w :=
  fun μ b c hs hμ => h μ b c (SubT.trans hs hw) hμ

/-- Subterms of `P ++ X`: subterms of `X`, or a node headed by a summand of `P`, or inside such a summand. -/
theorem subT_app_cases : ∀ (P X w : T), SubT w (app P X) →
    SubT w X ∨ ∃ a b R, psi a b z ∈ summands P ∧ (w = psi a b R ∨ SubT w a ∨ SubT w b)
  | z, X, w, h => by simpa using Or.inl h
  | psi a b P', X, w, h => by
    simp only [app_psi] at h
    cases h with
    | refl => exact Or.inr ⟨a, b, _, by simp [summands], Or.inl rfl⟩
    | sub h => exact Or.inr ⟨a, b, z, by simp [summands], Or.inr (Or.inl h)⟩
    | arg h => exact Or.inr ⟨a, b, z, by simp [summands], Or.inr (Or.inr h)⟩
    | rest h =>
      rcases subT_app_cases P' X w h with h | ⟨a', b', R, hq, hw⟩
      · exact Or.inl h
      · exact Or.inr ⟨a', b', R, by simp [summands, hq], hw⟩

/-- A summand of `V` heads a subterm of `V`. -/
theorem subT_of_summand {V a b : T} (h : psi a b z ∈ summands V) : ∃ c, SubT (psi a b c) V := by
  obtain ⟨w, hw, hu⟩ := summand_subS h
  rcases hu with rfl | ⟨a', b', c', rfl, he⟩
  · exact ⟨z, hw⟩
  · cases he; exact ⟨c', hw⟩

theorem noGapS_add {A X : T} (hA : NoGapS A) (hX : NoGapS X) : NoGapS (add A X) := by
  obtain ⟨P, hP, hs⟩ := add_eq_app_prefix A X
  rw [hP]
  intro μ b c h hμ
  rcases subT_app_cases P X _ h with h | ⟨a', b', R, hq, hw⟩
  · exact hX μ b c h hμ
  · obtain ⟨c1, hc1⟩ := subT_of_summand (hs _ hq)
    rcases hw with he | hw | hw
    · cases he; exact hA μ b c1 hc1 hμ
    · exact hA μ b c (SubT.trans hw (SubT.sub (.refl a') |>.trans hc1)) hμ
    · exact hA μ b c (SubT.trans hw (SubT.arg (.refl b') |>.trans hc1)) hμ

/-- A suffix is a subterm. -/
theorem subT_app_right : ∀ (Q X : T), SubT X (app Q X)
  | z, X => by simpa using SubT.refl X
  | psi a b Q, X => by simpa using SubT.rest (subT_app_right Q X)

theorem subT_sub (s V : T) : SubT (sub s V) s := by
  obtain ⟨Q, hQ⟩ := sub_suffix s V
  conv => rhs; rw [hQ]
  exact subT_app_right Q _

theorem isOT_Om {s : T} (hs : isOT s = true) : isOT (psi s z z) = true := by
  rw [isOT_psi_iff]
  refine ⟨hs, rfl, rfl, ?_, ?_⟩
  · exact z_le _
  · intro g hg; simp [comps] at hg

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- **σ keeps `NoGapS`**, given `NoGapS V′`. -/
theorem noGapS_sh (hNV' : NoGapS V') : ∀ (t : T), isOT t = true → NoGapS t → NoGapS (sh V V' t)
  | z, _, _ => by
    intro μ b c h; rw [sh_z] at h; cases h
  | psi s y c, ht, hN => by
    have hs := isOT_sub ht
    have hy := isOT_arg ht
    have hc := isOT_rest ht
    have hNy := hN.of_subT (SubT.arg (.refl y))
    have hNc := hN.of_subT (SubT.rest (.refl c))
    have ihy := noGapS_sh hNV' y hy hNy
    have ihc := noGapS_sh hNV' c hc hNc
    by_cases hVs : V < s
    · rw [sh_psi_gt hVs]
      have hsub := isOT_sub_sfx hs V
      have ihs := noGapS_sh hNV' (sub s V) hsub (hN.of_subT ((subT_sub s V).trans (SubT.sub (.refl s))))
      have hF : NoGapS (shf V V' s) := noGapS_add hNV' ihs
      intro μ b c' h hμ
      cases h with
      | refl =>
        have hs0 : s ≠ z := by rintro rfl; exact T.not_lt_z _ hVs
        have h1 : y < psi (succ s) z z := hN s y c (.refl _) hs0
        have h2 := sh_lt_sh hV hV' (le_of_lt hVV) hy (isOT_Om (isOT_succ hs)) h1
        rw [sh_psi_gt (lt_succ_iff.mpr (le_of_lt hVs)), sh_z,
          shf_succ hV hV' hVV hs (le_of_lt hVs)] at h2
        exact h2
      | sub h => exact hF μ b c' h hμ
      | arg h => exact ihy μ b c' h hμ
      | rest h => exact ihc μ b c' h hμ
    · rw [sh_psi_le hVs]
      intro μ b c' h hμ
      cases h with
      | refl => exact hN s y c (.refl _) hμ
      | sub h => exact hN μ b c' (h.trans (SubT.sub (.refl s))) hμ
      | arg h => exact hN μ b c' (h.trans (SubT.arg (.refl y))) hμ
      | rest h => exact ihc μ b c' h hμ
termination_by t => size t
decreasing_by
  all_goals simp only [size]
  all_goals first
    | omega
    | (have := size_sub_le s V; omega)

/-- **f keeps `NoGap`**: `NoGap t ∧ NoGap V′ ⇒ NoGap (f t)`. -/
theorem noGap_shf {t : T} (ht : isOT t = true) (hN : NoGap t) (hNV' : NoGap V') :
    NoGap (shf V V' t) := by
  rw [noGap_iff_noGapS] at hN hNV' ⊢
  exact noGapS_add hNV' (noGapS_sh hV hV' hVV hNV' _ (isOT_sub_sfx ht V) (hN.of_subT (subT_sub t V)))

/-- **σ keeps `NoGap`.** -/
theorem noGap_sh {t : T} (ht : isOT t = true) (hN : NoGap t) (hNV' : NoGap V') :
    NoGap (sh V V' t) := by
  rw [noGap_iff_noGapS] at hN hNV' ⊢
  exact noGapS_sh hV hV' hVV hNV' _ ht hN

end

/-! ## M[n] の NoGapP の組み立て

N の列 i + L（i ≥ r）は P の列 i の写し（`sft`、`hp1` は V3ExpT2V の仮定と同じ形）。行 1 の子を持つ列は
- r + L より前の子を持つ列（`hpre`）、r の写し r + L の行 1 の親（`hx'`）、
- r より前の列（P で行 1 の子を持つ。v は N と P で等しい、`hbase`）、
- 写しの列 i + L（i ≥ r。P で i は行 1 の子を持つ）。値は t = 0・1 では等しく、t = 2 では f(v_P(i)) か等しい
  （`noGap_copy_t2`）。
-/

theorem noGapP_of_copy {N P : Mat} {σ ρ : Valn} {r L : Nat} (hNl : N.length = P.length + L)
    (hp1 : ∀ i, r < i → i < P.length → par N 1 (i + L) = (par P 1 i).map (sft r L))
    (hpre : ∀ c p, c < r + L → par N 1 c = some p → NoGap (σ.v p))
    (hx' : ∀ p, par N 1 (r + L) = some p → NoGap (σ.v p))
    (hbase : ∀ c p, r < c → c < P.length → par P 1 c = some p → p < r → σ.v p = ρ.v p)
    (hcopy : ∀ i c, r ≤ i → i < P.length → r < c → c < P.length → par P 1 c = some i →
      NoGap (ρ.v i) → NoGap (σ.v (i + L)))
    (hNP : NoGapP P ρ) : NoGapP N σ := by
  intro c p hc hp
  rcases Nat.lt_or_ge c (r + L) with hcr | hcr
  · exact hpre c p hcr hp
  rcases Nat.eq_or_lt_of_le hcr with he | hlt
  · rw [← he] at hp; exact hx' p hp
  obtain ⟨c0, rfl⟩ : ∃ c0, c = c0 + L := ⟨c - L, by omega⟩
  have hc0 : c0 < P.length := by omega
  rw [hp1 c0 (by omega) hc0] at hp
  cases ht : par P 1 c0 with
  | none => rw [ht] at hp; cases hp
  | some t =>
    rw [ht] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    unfold sft at hp
    by_cases hrt : r ≤ t
    · rw [if_pos hrt] at hp
      subst hp
      have htl : t < P.length := by have := par_lt P 1 c0 t ht; omega
      exact hcopy t c0 hrt htl (by omega) hc0 ht (hNP c0 t hc0 ht)
    · rw [if_neg hrt] at hp
      subst hp
      rw [hbase c0 t (by omega) hc0 ht (by omega)]
      exact hNP c0 t hc0 ht

/-- **The t = 2 copy keeps `NoGap`**: a guarded copy has `v = f(v_P)`, an unguarded one the same `v`. -/
theorem noGap_copy_t2 {V V' t t' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ht : isOT t = true) (hNV' : NoGap V') (h : t' = shf V V' t ∨ t' = t) (hN : NoGap t) : NoGap t' := by
  rcases h with rfl | rfl
  · exact noGap_shf hV hV' hVV ht hN hNV'
  · exact hN

/-! ## 段 μ の項がない（下半分も含む）

実測（C′、2026-10-11）: のりしろの列 c、鎖の上の p、c の行 0 の子孫の値に Ω_{μ+1} が現れる μ ≠ 0 について、
v(p) は ψ_μ(…) の部分項を持たない（27 万件、例外 0）。したがって [Ω_μ, Ω_{μ+1}) の全体が空
（上半分は NoGap、下半分は t = 1 の種の条件）。
-/

/-- **No subterm with subscript `μ`.** -/
def LevFree (μ V : T) : Prop := ∀ a b c, SubT (psi a b c) V → a ≠ μ

/-- A term in `[Ω_μ, Ω_{μ+1})` has subscript `μ`. -/
theorem sub_eq_of_band {μ a b c : T} (h1 : psi μ z z ≤ psi a b c) (h2 : psi a b c < psi (succ μ) z z) :
    a = μ := by
  have ha : a ≤ μ := by
    rw [T.psi_lt_psi] at h2
    rcases h2 with h | ⟨_, h⟩ | ⟨_, _, h⟩
    · exact lt_succ_iff.mp h
    · exact absurd h (T.not_lt_z _)
    · exact absurd h (T.not_lt_z _)
  rcases (le_iff _ _).mp h1 with h | h
  · rw [T.psi_lt_psi] at h
    rcases h with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
    · exact absurd (lt_of_lt_of_le h ha) (lt_irrefl' _)
    · rfl
    · rfl
  · cases h; rfl

/-- **`LevFree` empties the band `[Ω_μ, Ω_{μ+1})`** among the subterms (and heads) of `V`. -/
theorem band_empty_of_levFree {μ V : T} (h : LevFree μ V) {u : T} (hu : SubS V u)
    (h1 : psi μ z z ≤ u) (h2 : u < psi (succ μ) z z) : False := by
  obtain ⟨w, hw, hu⟩ := hu
  cases u with
  | z => exact absurd h1 (not_le_of_gt (T.z_lt_psi _ _ _))
  | psi a b c =>
    have hs : ∃ c', SubT (psi a b c') V := by
      rcases hu with rfl | ⟨a', b', c', rfl, he⟩
      · exact ⟨c, hw⟩
      · cases he; exact ⟨c', hw⟩
    obtain ⟨c', hs⟩ := hs
    exact h a b c' hs (sub_eq_of_band h1 h2)

/-- **The t = 1 seed condition at a positive level** (t1-exp の AbsDRes・AbsUWRes): with `LevFree μ V`, a
subterm of `V` below `ψ_μ(Ω_{μ+1})` is below `Ω_μ`. -/
theorem lt_Om_of_levFree {μ V u : T} (h : LevFree μ V) (hu : SubS V u) (hlt : u < etaOm μ) :
    u < psi μ z z := by
  by_contra hn
  refine band_empty_of_levFree h hu (le_of_not_gt hn) (lt_trans' hlt ?_)
  unfold etaOm; rw [T.psi_lt_psi]; exact Or.inl (lt_succ_iff.mpr (le_refl _))

/-- `LevFree` also gives the upper half (`NoGap` at `μ`). -/
theorem gapFree_of_levFree {μ V : T} (h : LevFree μ V) :
    ∀ u, SubS V u → u < psi (succ μ) z z → u < etaOm μ := by
  intro u hu hlt
  by_contra hn
  refine band_empty_of_levFree h hu ?_ hlt
  refine le_trans ?_ (le_of_not_gt hn)
  unfold etaOm
  exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, T.z_lt_psi _ _ _⟩))

/-! ## 段 0 の残りの一部: 最後の項が ψ_μ(Ω_{μ+1}) そのもの

W = P + ψ_μ(Ω_{μ+1}) なら fsD(W, ψ_μ(Ω_{μ+1})) = P + ψ_μ(ψ_μ(Ω_{μ+1}))。穴に届く項は P + ψ_μ(b) + …（b < Ω_{μ+1}）
で、ψ_μ(b) が標準形なら b < ψ_μ(Ω_{μ+1})（b が隙間にあれば b の先頭の引数 ≥ Ω_{μ+1} が成分になる）。
したがって集合の項がすべて標準形なら Reach は無条件。一般に穴が fsD の経路の先の節点 ψ_μ(Ω_{μ+1}) にあれば同じ（EtaHole、reach_etaHole: C′ で PhiX0R の 88/122 件、DropPhi0Res の 40/45 件）。
-/

theorem fsD_etaOm (μ η : T) : fsD (etaOm μ) η = psi μ η z := by
  have hne : psi (succ μ) z z ≠ z := by simp
  have hs : isSucc (psi (succ μ) z z) = false := isSucc_psi_ne (Or.inl (succ_ne_z μ))
  have hc : cof (psi (succ μ) z z) = .big μ := by
    simp [cof, succ_ne_z, isSucc_succ, init_succ]
  unfold etaOm fsD
  rw [if_neg hne, hs, hc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [fs_leaf' (succ_ne_z μ) (isSucc_succ μ)]

theorem holeLev_etaOm (μ : T) : holeLev (etaOm μ) = μ := by
  have hne : psi (succ μ) z z ≠ z := by simp
  have hc : cof (psi (succ μ) z z) = .big μ := by
    simp [cof, succ_ne_z, isSucc_succ, init_succ]
  unfold etaOm holeLev
  rw [if_neg hne, hc]

/-- **Reach at `ψ_μ(Ω_{μ+1})` for standard terms.** -/
theorem reach_etaOm {S : T → Prop} (hS : ∀ u, S u → isOT u = true) (μ : T) :
    Reach S (etaOm μ) (etaOm μ) := by
  intro u hu hlt
  rw [fsD_etaOm]
  cases u with
  | z => exact T.z_lt_psi _ _ _
  | psi a b c =>
    unfold etaOm at hlt
    rw [T.psi_lt_psi] at hlt ⊢
    rcases hlt with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      by_contra hn
      have hge : etaOm a ≤ b := le_of_not_gt hn
      cases b with
      | z => exact absurd hge (not_le_of_gt (T.z_lt_psi _ _ _))
      | psi a2 b2 c2 =>
        have hband : psi a z z ≤ psi a2 b2 c2 := by
          refine le_trans (le_of_lt ?_) hge
          unfold etaOm; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, T.z_lt_psi _ _ _⟩)
        have ha2 := sub_eq_of_band hband h2
        subst ha2
        have hb2 : psi (succ a2) z z ≤ b2 := by
          unfold etaOm at hge
          rcases (le_iff _ _).mp hge with h | h
          · rw [T.psi_lt_psi] at h
            rcases h with h | ⟨_, h⟩ | ⟨_, h, _⟩
            · exact absurd h (lt_irrefl' _)
            · exact le_of_lt h
            · rw [h]
          · cases h; exact le_refl _
        have hot := hS _ hu
        rw [isOT_psi_iff] at hot
        have hg : b2 ∈ comps a2 (psi a2 b2 c2) := by
          simp only [comps, List.mem_append]
          exact Or.inl (by rw [if_neg (show ¬ lt a2 a2 = true from lt_irrefl' a2)]; simp)
        have := hot.2.2.2.2 b2 hg
        exact absurd (lt_of_lt_of_le (lt_trans' this h2) hb2) (lt_irrefl' _)
    · exact absurd h3 (T.not_lt_z _)

theorem isOT_of_subT' {w : T} : ∀ {t : T}, SubT w t → isOT t = true → isOT w = true
  | _, .refl _, h => h
  | _, .sub hs, h => isOT_of_subT' hs (isOT_sub h)
  | _, .arg hs, h => isOT_of_subT' hs (isOT_arg h)
  | _, .rest hs, h => isOT_of_subT' hs (isOT_rest h)

theorem isOT_of_subS {V u : T} (hV : isOT V = true) (hu : SubS V u) : isOT u = true := by
  obtain ⟨w, hw, hu⟩ := hu
  have := isOT_of_subT' hw hV
  rcases hu with rfl | ⟨a, b, c, rfl, rfl⟩
  · exact this
  · exact isOT_head this

/-- **Reach when the last summand of `W` is `ψ_μ(Ω_{μ+1})`**, for the subterms of a standard `V`. -/
theorem reach_last_etaOm {V : T} (hV : isOT V = true) (P μ : T) :
    Reach (SubS V) (app P (etaOm μ)) (etaOm (holeLev (app P (etaOm μ)))) := by
  rw [gA_holeLev_app P (by simp [etaOm]), holeLev_etaOm]
  apply reach_app (by simp [etaOm]) P
  apply reach_etaOm
  intro c hc
  exact isOT_of_subT' (subT_app_right P c) (isOT_of_subS hV hc)

/-- **The hole sits at a node `ψ_μ(Ω_{μ+1})`**: following the `fsD` path (rest, subscript, argument),
the hole is reached as the whole argument `Ω_{μ+1}` of a `ψ_μ` with the same `μ`. -/
def EtaHole : T → Prop
  | z => False
  | psi _ _ (psi c d e) => EtaHole (psi c d e)
  | psi a b z =>
    if b = z then (isSucc a = false ∧ EtaHole a)
    else if b = psi (succ a) z z then True else (isSucc b = false ∧ EtaHole b)

theorem holeLev_arg {a b : T} (hb : b ≠ z) : holeLev (psi a b z) = holeLev b := by
  conv_lhs => unfold holeLev
  rw [if_neg hb]
  cases hc : cof b with
  | big μ => exact (holeLev_cof hc).symm
  | zero => rfl
  | succ => rfl
  | omega => rfl

/-- **Reach at an `EtaHole`** for any set of standard terms: the term reaching `ψ_μ(Ω_{μ+1})` has a
standard head `ψ_μ(b)`, so `b` is not in the gap. -/
theorem reach_etaHole : ∀ {X : T} {S : T → Prop}, EtaHole X → (∀ u, S u → isOT u = true) →
    Reach S X (etaOm (holeLev X))
  | z, _, h, _ => absurd h (by simp [EtaHole])
  | psi a b (psi c d e), S, h, hS => by
    have h' : EtaHole (psi c d e) := h
    rw [holeLev_rest]
    exact reach_rest (by simp) (reach_etaHole h' (fun u hu => isOT_rest (hS _ hu)))
  | psi a b z, S, h, hS => by
    by_cases hb : b = z
    · subst hb
      have h' : isSucc a = false ∧ EtaHole a := by simpa [EtaHole] using h
      have ha : a ≠ z := by rintro rfl; exact absurd h'.2 (by simp [EtaHole])
      rw [holeLev_sub' h'.1]
      exact reach_sub ha h'.1 (reach_etaHole h'.2 (fun u ⟨b', c', hu⟩ => isOT_sub (hS _ hu)))
    by_cases he : b = psi (succ a) z z
    · subst he
      show Reach S (etaOm a) (etaOm (holeLev (etaOm a)))
      rw [holeLev_etaOm]
      exact reach_etaOm hS a
    · have h' : isSucc b = false ∧ EtaHole b := by
        unfold EtaHole at h; rw [if_neg hb, if_neg he] at h; exact h
      rw [holeLev_arg hb]
      exact reach_arg hb h'.1 (reach_etaHole h'.2 (fun u ⟨c', hu⟩ => isOT_arg (hS _ hu)))

/-- **The narrowed level-0 residual of the drop**: as `DropPhi0Res`, but the hole of the new bump term is
not an `EtaHole` (C′ で 5 件). -/
def DropPhi0ResN (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ c p, c < x → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c →
    OHole (bumpW (M.take x) ρ' c) → holeLev (bumpW (M.take x) ρ' c) = z → ¬ NoGap0 (ρ.v p) →
    bumpW (M.take x) ρ' c ≠ bumpW M ρ c → ¬ EtaHole (bumpW (M.take x) ρ' c) →
    Reach (SubS (ρ.v p)) (bumpW (M.take x) ρ' c) (etaOm (holeLev (bumpW (M.take x) ρ' c)))

theorem dropPhi0Res_of_N {M : Mat} {x : Nat} {ρ ρ' : Valn} (hx : x + 1 = M.length) (hG : Good3 M ρ)
    (h : DropPhi0ResN M x ρ ρ') : DropPhi0Res M x ρ ρ' := by
  intro c p hc h1 h2 hch hO hμ hg hW
  by_cases hE : EtaHole (bumpW (M.take x) ρ' c)
  · have hpM : p < M.length := by
      obtain ⟨c', hc', hp⟩ := hch.has_child (show c < M.length by omega)
      have := par_lt M 1 c' p hp; omega
    exact reach_etaHole hE (fun u hu => isOT_of_subS (hG.ot_v p hpM) hu)
  · exact h c p hc h1 h2 hch hO hμ hg hW hE

/-- **The narrowed level-0 residual of PhiX** (the hole is not an `EtaHole`, C′ で 34 件). -/
def PhiX0RN (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p, c < M.length → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c → OHole (bumpW M ρ c) →
    holeLev (bumpW M ρ c) = z → ¬ NoGap0 (ρ.v p) → ¬ EtaHole (bumpW M ρ c) →
    Reach (SubS (ρ.v p)) (bumpW M ρ c) (etaOm (holeLev (bumpW M ρ c)))

theorem phiX0R_of_N {M : Mat} {ρ : Valn} (hG : Good3 M ρ) (h : PhiX0RN M ρ) : PhiX0R M ρ := by
  intro c p hc h1 h2 hch hO hμ hg
  by_cases hE : EtaHole (bumpW M ρ c)
  · have hpM : p < M.length := by
      obtain ⟨c', hc', hp⟩ := hch.has_child hc
      have := par_lt M 1 c' p hp; omega
    exact reach_etaHole hE (fun u hu => isOT_of_subS (hG.ot_v p hpM) hu)
  · exact h c p hc h1 h2 hch hO hμ hg hE

end Ytosk
