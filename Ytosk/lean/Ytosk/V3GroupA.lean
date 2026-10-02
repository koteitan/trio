/-
**Inv3 の値の欄のうち A 群（Good3 と構造の不変条件から出るもの）。**

実測（SInvX ∧ RowJ ∧ Good3、長さ ≤ 8 の網羅 573247 個と C′ 404051 個、例外 0）:
VSmallF・AbsD・AbsU・TPLo・AbsUW・TPLoN・AbsDN。

- 上げの先の形（`upg_target_val`）: 上げ i → k の先 k は行 2 が 1 で P_1 k = P_1 i、
  v(k) = v(P_1 i) + W_k（W_k = bumpW k）。したがって last v(k) = W_k。
- AbsU は AbsD から（`absU_of_absD`）。AbsUW は η = 1 の AbsD を上げの先で（`absUW_of`）。
-/
import Ytosk.V3InvDerive
import Ytosk.V3Top
import Ytosk.V3FsdComp

namespace Ytosk

open T


/-! ## 穴の経路に沿った比較の伝播（順序数の部分）

`Reach S X η`: 集合 S の項 u で X より小さいものは fsD(X, η) より小さい。
fsD の再帰（残り・添字・引数）に沿って、比べられる部分項の像の集合を運ぶ。
-/

/-- Every `u ∈ S` below `X` stays below `fsD(X, η)`. -/
def Reach (S : T → Prop) (X η : T) : Prop := ∀ u, S u → u < X → u < fsD X η

/-- The rests after a fixed head. -/
def ImRest (S : T → Prop) (a b : T) : T → Prop := fun c => S (psi a b c)

/-- The subscripts of the heads. -/
def ImSub (S : T → Prop) : T → Prop := fun a => ∃ b c, S (psi a b c)

/-- The arguments of the heads with subscript `a`. -/
def ImArg (S : T → Prop) (a : T) : T → Prop := fun b => ∃ c, S (psi a b c)

theorem Reach.mono {S S' : T → Prop} {X η : T} (h : Reach S' X η) (hS : ∀ u, S u → S' u) :
    Reach S X η := fun u hu hlt => h u (hS u hu) hlt

/-- The rest step. -/
theorem reach_rest {S : T → Prop} {a b c η : T} (hc : c ≠ z) (h : Reach (ImRest S a b) c η) :
    Reach S (psi a b c) η := by
  cases c with
  | z => exact absurd rfl hc
  | psi c1 c2 c3 =>
    intro u hu hlt
    have hf : fsD (psi a b (psi c1 c2 c3)) η = psi a b (fsD (psi c1 c2 c3) η) := rfl
    rw [hf]
    cases u with
    | z => exact T.z_lt_psi _ _ _
    | psi a' b' c' =>
      rw [T.psi_lt_psi] at hlt ⊢
      rcases hlt with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl, h c' hu h3⟩)

/-- The step through a prefix `B ++ X`. -/
theorem reach_app {S : T → Prop} {X η : T} (hX : X ≠ z) :
    ∀ B : T, Reach (fun c => S (app B c)) X η → Reach S (app B X) η
  | z, h => by simpa using h
  | psi a b B', h => by
    rw [app_psi]
    have hne : app B' X ≠ z := fun he => hX (app_eq_z he).2
    exact reach_rest hne (reach_app hX B' (by simpa [ImRest, app_psi] using h))

/-- The subscript step `Ω_a`, `a` a limit. -/
theorem reach_sub {S : T → Prop} {a η : T} (ha : a ≠ z) (hs : isSucc a = false)
    (h : Reach (ImSub S) a η) : Reach S (psi a z z) η := by
  intro u hu hlt
  rw [fsD_sub ha hs]
  cases u with
  | z => exact T.z_lt_psi _ _ _
  | psi a' b' c' =>
    rw [T.psi_lt_psi] at hlt ⊢
    rcases hlt with h1 | ⟨_, h2⟩ | ⟨_, _, h3⟩
    · exact Or.inl (h a' ⟨b', c', hu⟩ h1)
    · exact absurd h2 (T.not_lt_z _)
    · exact absurd h3 (T.not_lt_z _)

/-- The argument step `ψ_a(b)`. -/
theorem reach_arg {S : T → Prop} {a b η : T} (hb : b ≠ z) (hs : isSucc b = false)
    (h : Reach (ImArg S a) b η) : Reach S (psi a b z) η := by
  intro u hu hlt
  rw [fsD_psi hb hs]
  cases u with
  | z => exact T.z_lt_psi _ _ _
  | psi a' b' c' =>
    rw [T.psi_lt_psi] at hlt ⊢
    rcases hlt with h1 | ⟨rfl, h2⟩ | ⟨rfl, _, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨rfl, h b' ⟨c', hu⟩ h2⟩)
    · exact absurd h3 (T.not_lt_z _)

/-- The base `Ω_{μ+1}`: `fsD = η`. -/
theorem reach_base {S : T → Prop} {a η : T} (ha : a ≠ z) (hs : isSucc a = true)
    (h : ∀ u, S u → u < psi a z z → u < η) : Reach S (psi a z z) η := by
  intro u hu hlt
  rw [fsD_leaf hs ha]; exact h u hu hlt

/-! ## 部分項 -/

/-- `u` is a subterm of `t` (reflexive). -/
inductive SubT : T → T → Prop
  | refl (t : T) : SubT t t
  | sub {u a b c : T} : SubT u a → SubT u (psi a b c)
  | arg {u a b c : T} : SubT u b → SubT u (psi a b c)
  | rest {u a b c : T} : SubT u c → SubT u (psi a b c)

theorem SubT.trans {u v : T} (h1 : SubT u v) : ∀ {w : T}, SubT v w → SubT u w
  | _, .refl _ => h1
  | _, .sub h => .sub (SubT.trans h1 h)
  | _, .arg h => .arg (SubT.trans h1 h)
  | _, .rest h => .rest (SubT.trans h1 h)

/-- A set closed under subterms. -/
def SubClosed (S : T → Prop) : Prop := ∀ u, S u → ∀ w, SubT w u → S w

theorem SubClosed.sub {S : T → Prop} (h : SubClosed S) {a b c : T} (hu : S (psi a b c)) : S a :=
  h _ hu _ (.sub (.refl a))

theorem SubClosed.arg {S : T → Prop} (h : SubClosed S) {a b c : T} (hu : S (psi a b c)) : S b :=
  h _ hu _ (.arg (.refl b))

theorem SubClosed.rest {S : T → Prop} (h : SubClosed S) {a b c : T} (hu : S (psi a b c)) : S c :=
  h _ hu _ (.rest (.refl c))

theorem subClosed_subT (V : T) : SubClosed (fun u => SubT u V) :=
  fun _ hu _ hw => SubT.trans hw hu

theorem holeLev_rest {a b c d e : T} : holeLev (psi a b (psi c d e)) = holeLev (psi c d e) := rfl

/-- **The gap lemma**: for a subterm-closed `S` with no member in the gap `[η, Ω_{μ+1})` at the hole level
`μ = holeLev X`, every member below `X` stays below `fsD(X, η)`. -/
theorem reach_gap {S : T → Prop} (hS : SubClosed S) {η : T} :
    ∀ {X : T}, OHole X → (∀ u, S u → u < psi (succ (holeLev X)) z z → u < η) → Reach S X η
  | z, h, _ => absurd h (by simp [OHole])
  | psi a b (psi c d e), hO, hg => by
    have hO' : OHole (psi c d e) := hO
    apply reach_rest (by simp)
    intro u hu hlt
    exact reach_gap hS hO' hg u (hS.rest hu) hlt
  | psi a b z, hO, hg => by
    by_cases hb : b = z
    · subst hb
      have hO2 : a ≠ z ∧ (isSucc a = true ∨ OHole a) := by simpa [OHole] using hO
      obtain ⟨ha, hO2⟩ := hO2
      by_cases hs : isSucc a = true
      · apply reach_base ha hs
        intro u hu hlt
        apply hg u hu
        have hl : holeLev (psi a z z) = init a := by simp [holeLev, hs]
        rw [hl, succ, init_app_one hs]; exact hlt
      · have hOa : OHole a := by simpa [hs] using hO2
        have hs' : isSucc a = false := by simpa using hs
        apply reach_sub ha hs'
        intro u ⟨b', c', hu⟩ hlt
        have hl : holeLev (psi a z z) = holeLev a := by simp [holeLev, hs]
        exact reach_gap hS hOa (by rw [← hl]; exact hg) u (hS.sub hu) hlt
    · have hs : isSucc b = false := by
        by_contra hc
        have : isSucc b = true := by simpa using hc
        simp [OHole, hb, this] at hO
      have hOb : OHole b := by
        cases hcb : cof b with
        | big μ => exact ohole_of_cof_big hcb
        | zero => simpa [OHole, hb, hs, hcb] using hO
        | succ => simpa [OHole, hb, hs, hcb] using hO
        | omega => simpa [OHole, hb, hs, hcb] using hO
      have hl : holeLev (psi a b z) = holeLev b := by
        cases hcb : cof b with
        | big μ => simp [holeLev, hb, hcb, holeLev_cof hcb]
        | zero => simp [holeLev, hb, hcb]
        | succ => simp [holeLev, hb, hcb]
        | omega => simp [holeLev, hb, hcb]
      apply reach_arg hb hs
      intro u ⟨c', hu⟩ hlt
      exact reach_gap hS hOb (by rw [← hl]; exact hg) u (hS.arg hu) hlt



/-! ## 添字の付け替え: fsD(X, ξ₁)・fsD(X, ξ₀) の下にある部分項は fsD(X, ξ₂) の下

S が部分項で閉じていて、S の u について「u < ξ₁ かつ u < ξ₀ なら u < ξ₂」なら、
S の u について「u < fsD(X, ξ₁) かつ u < fsD(X, ξ₀) なら u < fsD(X, ξ₂)」（X に穴があるとき）。
fsD の再帰で両方の比較が同じ経路を降り、穴の位置で添字どうしの比較になるため。
-/

theorem fsD_transfer {S : T → Prop} (hS : SubClosed S) {ξ₀ ξ₁ ξ₂ : T}
    (h : ∀ u, S u → u < ξ₁ → u < ξ₀ → u < ξ₂) :
    ∀ {X : T}, OHole X → ∀ u, S u → u < fsD X ξ₁ → u < fsD X ξ₀ → u < fsD X ξ₂
  | z, hO, _, _, _, _ => absurd hO (by simp [OHole])
  | psi a b (psi c d e), hO, u, hu, h1, h0 => by
    have hO' : OHole (psi c d e) := hO
    have hf : ∀ ξ, fsD (psi a b (psi c d e)) ξ = psi a b (fsD (psi c d e) ξ) := fun _ => rfl
    rw [hf] at h1 h0 ⊢
    cases u with
    | z => exact T.z_lt_psi _ _ _
    | psi a' b' c' =>
      rw [T.psi_lt_psi] at h1 h0 ⊢
      rcases h1 with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · rcases h0 with h0 | ⟨_, h0⟩ | ⟨_, _, h0⟩
        · exact absurd h0 (lt_irrefl' _)
        · exact absurd h0 (lt_irrefl' _)
        · exact Or.inr (Or.inr ⟨rfl, rfl, fsD_transfer hS h hO' c' (hS.rest hu) h3 h0⟩)
  | psi a b z, hO, u, hu, h1, h0 => by
    by_cases hb : b = z
    · subst hb
      have h2 : a ≠ z ∧ (isSucc a = true ∨ OHole a) := by simpa [OHole] using hO
      by_cases hs : isSucc a = true
      · rw [fsD_leaf hs h2.1] at h1 h0 ⊢; exact h u hu h1 h0
      · have hs' : isSucc a = false := by simpa using hs
        have hOa : OHole a := by simpa [hs] using h2.2
        rw [fsD_sub h2.1 hs'] at h1 h0 ⊢
        cases u with
        | z => exact T.z_lt_psi _ _ _
        | psi a' b' c' =>
          rw [T.psi_lt_psi] at h1 h0 ⊢
          rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
          · rcases h0 with h0 | ⟨_, h0⟩ | ⟨_, _, h0⟩
            · exact Or.inl (fsD_transfer hS h hOa a' (hS.sub hu) h1 h0)
            · exact absurd h0 (T.not_lt_z _)
            · exact absurd h0 (T.not_lt_z _)
          · exact absurd h1 (T.not_lt_z _)
          · exact absurd h1 (T.not_lt_z _)
    · have hs : isSucc b = false := by
        by_contra hc
        have : isSucc b = true := by simpa using hc
        simp [OHole, hb, this] at hO
      have hOb : OHole b := by
        cases hcb : cof b with
        | big μ => exact ohole_of_cof_big hcb
        | zero => simpa [OHole, hb, hs, hcb] using hO
        | succ => simpa [OHole, hb, hs, hcb] using hO
        | omega => simpa [OHole, hb, hs, hcb] using hO
      rw [fsD_psi hb hs] at h1 h0 ⊢
      cases u with
      | z => exact T.z_lt_psi _ _ _
      | psi a' b' c' =>
        rw [T.psi_lt_psi] at h1 h0 ⊢
        rcases h1 with h1 | ⟨rfl, h2⟩ | ⟨rfl, _, h3⟩
        · exact Or.inl h1
        · rcases h0 with h0 | ⟨_, h0⟩ | ⟨_, _, h0⟩
          · exact absurd h0 (lt_irrefl' _)
          · exact Or.inr (Or.inl ⟨rfl, fsD_transfer hS h hOb b' (hS.arg hu) h2 h0⟩)
          · exact absurd h0 (T.not_lt_z _)
        · exact absurd h3 (T.not_lt_z _)



theorem subT_z : ∀ t : T, SubT z t
  | z => .refl z
  | psi _ _ c => .rest (subT_z c)

/-- Subterms of `V` and the heads `ψ_a(b)` of subterms `ψ_a(b) + c` (these include the summands). -/
def SubS (V : T) : T → Prop := fun u => ∃ w, SubT w V ∧ (u = w ∨ ∃ a b c, w = psi a b c ∧ u = psi a b z)

theorem subClosed_subS (V : T) : SubClosed (SubS V) := by
  intro u ⟨w, hw, hu⟩ x hx
  rcases hu with rfl | ⟨a, b, c, rfl, rfl⟩
  · exact ⟨x, SubT.trans hx hw, Or.inl rfl⟩
  · cases hx with
    | refl => exact ⟨_, hw, Or.inr ⟨a, b, c, rfl, rfl⟩⟩
    | sub h => exact ⟨x, SubT.trans h (SubT.trans (.sub (.refl a)) hw), Or.inl rfl⟩
    | arg h => exact ⟨x, SubT.trans h (SubT.trans (.arg (.refl b)) hw), Or.inl rfl⟩
    | rest h =>
      have : x = z := by cases h; rfl
      subst this; exact ⟨z, SubT.trans (subT_z _) hw, Or.inl rfl⟩

theorem summand_subS : ∀ {V q : T}, q ∈ summands V → SubS V q
  | z, _, h => by simp [summands] at h
  | psi a b c, q, h => by
    simp only [summands, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨psi a b c, .refl _, Or.inr ⟨a, b, c, rfl, rfl⟩⟩
    · obtain ⟨w, hw, hu⟩ := summand_subS h
      exact ⟨w, .rest hw, hu⟩

theorem subT_subS {V u : T} (h : SubT u V) : SubS V u := ⟨u, h, Or.inl rfl⟩

/-! ## 穴の水準と fsD -/

theorem holeLev_psi_arg {a X : T} (hX : X ≠ z) : holeLev (psi a X z) = holeLev X := by
  cases hc : cof X with
  | big μ => simp [holeLev, hX, hc, holeLev_cof hc]
  | zero => simp [holeLev, hX, hc]
  | succ => simp [holeLev, hX, hc]
  | omega => simp [holeLev, hX, hc]

theorem holeLev_sub' {a : T} (hs : isSucc a = false) : holeLev (psi a z z) = holeLev a := by
  simp [holeLev, hs]

theorem holeLev_fs : ∀ {b μ ζ : T}, cof b = .big μ → ζ ≠ z → isSucc ζ = false →
    holeLev (fs b ζ) = holeLev ζ
  | z, _, _, h, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, ζ, h, hζ, hs => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    rw [fs_rest (by simp)]
    have hX := fs_ne_z_big h' hζ
    cases hf : fs (psi c d e) ζ with
    | z => exact absurd hf hX
    | psi f g k =>
      show holeLev (psi f g k) = holeLev ζ
      rw [← hf]; exact holeLev_fs h' hζ hs
  | psi a b z, μ, ζ, h, hζ, hs => by
    have hc := h
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases has : isSucc a = true
        · rw [fs_leaf' ha has]
        · rw [if_neg has] at h
          have has' : isSucc a = false := by simpa using has
          rw [fs_sub' ha has', holeLev_sub' (isSucc_fs_big h hζ hs), holeLev_fs h hζ hs]
    · rw [if_neg hb] at h
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; cases h
      · rw [if_neg hbs] at h
        have hbs' : isSucc b = false := by simpa using hbs
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h
          by_cases hν : lt ν a = true
          · rw [fs_big' hb hbs' hcb hν, holeLev_psi_arg (fs_ne_z_big hcb hζ), holeLev_fs hcb hζ hs]
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **The hole level after `fsD` at a hole is that of the index.** -/
theorem holeLev_fsD : ∀ {t ζ : T}, OHole t → ζ ≠ z → isSucc ζ = false → holeLev (fsD t ζ) = holeLev ζ
  | z, _, h, _, _ => by simp [OHole] at h
  | psi a b (psi c d e), ζ, h, hζ, hs => by
    have h' : OHole (psi c d e) := h
    rw [fsD_rest (by simp)]
    have hX := fsD_ne_z_oh h' hζ
    cases hf : fsD (psi c d e) ζ with
    | z => exact absurd hf hX
    | psi f g k =>
      show holeLev (psi f g k) = holeLev ζ
      rw [← hf]; exact holeLev_fsD h' hζ hs
  | psi a b z, ζ, h, hζ, hs => by
    unfold OHole at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      obtain ⟨ha, h⟩ := h
      by_cases has : isSucc a = true
      · rw [fsD_leaf has ha]
      · have has' : isSucc a = false := by simpa using has
        have ha' : OHole a := by rcases h with h | h; exact absurd h has; exact h
        rw [fsD_sub ha has', holeLev_sub' (isSucc_fsD_oh ha' hζ hs), holeLev_fsD ha' hζ hs]
    · rw [if_neg hb] at h
      by_cases hbs : isSucc b = true
      · rw [if_pos hbs] at h; exact absurd h id
      · rw [if_neg hbs] at h
        have hbs' : isSucc b = false := by simpa using hbs
        rw [fsD_psi hb hbs']
        cases hcb : cof b with
        | big ν =>
          rw [fsD_eq_fs hcb, holeLev_psi_arg (fs_ne_z_big hcb hζ), holeLev_fs hcb hζ hs]
        | zero =>
          rw [hcb] at h
          rw [holeLev_psi_arg (fsD_ne_z_oh h hζ), holeLev_fsD h hζ hs]
        | succ =>
          rw [hcb] at h
          rw [holeLev_psi_arg (fsD_ne_z_oh h hζ), holeLev_fsD h hζ hs]
        | omega =>
          rw [hcb] at h
          rw [holeLev_psi_arg (fsD_ne_z_oh h hζ), holeLev_fsD h hζ hs]

/-! ## AbsD 型の吸収の保存: のりしろの項が fsD(W, ζ) に替わる

M で「V の加数で W より小さいものは fsD(W, η_W) より小さい」（η_W = ψ_μ(Ω_{μ+1})、μ = holeLev W）。
N で W が W′ = fsD(W, ζ)（V は同じ）になるとき、fsD(W′, θ) = fsD(W, fsD(ζ, θ))（fsD_comp）なので、
添字の付け替え（fsD_transfer）で、種 ζ についての条件
  「V の部分項 u で u < ζ かつ u < η_W なら u < fsD(ζ, θ)」
から N の吸収が出る。
-/

/-- **Absorption survives `W ↦ fsD(W, ζ)`**, given the seed condition on `ζ`. -/
theorem absorb_fsD_W {V W ζ θ : T} (hOW : OHole W) (hζ : ζ ≠ z) (hζs : isSucc ζ = false)
    (hM : ∀ q ∈ summands V, q < W → q < fsD W (etaOm (holeLev W)))
    (hlt : fsD W ζ < W)
    (hseed : ∀ u, SubS V u → u < ζ → u < etaOm (holeLev W) → u < fsD ζ θ) :
    ∀ q ∈ summands V, q < fsD W ζ → q < fsD (fsD W ζ) θ := by
  intro q hq hq1
  rw [fsD_comp hOW hζ hζs θ]
  have hq0 := hM q hq (lt_trans' hq1 hlt)
  have hsub := summand_subS hq
  exact fsD_transfer (subClosed_subS V) (fun u hu h1 h0 => hseed u hu h1 h0) hOW q hsub hq1 hq0


/-- The TPL-type condition `Ω_A ≥ Ω_{s+1}` is `s < A`. -/
theorem tpl_iff {A s : T} : ¬ psi A z z < psi (succ s) z z ↔ s < A := by
  rw [psi_lt_psi_z_iff]
  constructor
  · intro h
    rcases lt_trichotomy' s A with h1 | h1 | h1
    · exact h1
    · exact absurd (Or.inl (lt_succ_iff.mpr (Or.inr h1.symm))) h
    · exact absurd (Or.inl (lt_succ_iff.mpr (Or.inl h1))) h
  · rintro h (h1 | ⟨_, h1⟩)
    · rcases lt_succ_iff.mp h1 with h2 | h2
      · exact lt_irrefl' _ (T.lt_trans' h h2)
      · rw [h2] at h; exact lt_irrefl' _ h
    · exact absurd h1 (T.not_lt_z _)

/-- **TPLo-type comparison survives `a ↦ fsD(a, ζ)`**: from `s < fsD(a, η₀)` (old field) and `s < fsD(a, ζ)`
(the new last subscript is above `s`), with the seed condition on the subterms of `s`. -/
theorem tplo_fsD_gen {s a0 ζ θ η0 : T} (hOa0 : OHole a0) (hζ : ζ ≠ z) (hζs : isSucc ζ = false)
    (hM : s < fsD a0 η0) (hN : s < fsD a0 ζ)
    (hseed : ∀ u, SubS s u → u < ζ → u < η0 → u < fsD ζ θ) :
    s < fsD (fsD a0 ζ) θ := by
  rw [fsD_comp hOa0 hζ hζs θ]
  exact fsD_transfer (subClosed_subS s) (fun u hu h1 h0 => hseed u hu h1 h0) hOa0 s
    (subT_subS (.refl s)) hN hM

/-! ## Key: 吸収が穴の基本列でも保たれるなら v(P_1 d) < fsD(v(d), η) -/

theorem gA_ohole_app_inv : ∀ {P c : T}, c ≠ z → OHole (app P c) → OHole c
  | z, c, _, h => by simpa using h
  | psi a b P, c, hc, h => by
    have hne : app P c ≠ z := fun he => hc (app_eq_z he).2
    simp only [app_psi] at h
    cases hP : app P c with
    | z => exact absurd hP hne
    | psi d e f =>
      rw [hP] at h
      have h' : OHole (psi d e f) := h
      rw [← hP] at h'
      exact gA_ohole_app_inv hc h'

theorem gA_holeLev_app : ∀ (P : T) {c : T}, c ≠ z → holeLev (app P c) = holeLev c
  | z, _, _ => by simp
  | psi a b P, c, hc => by
    have hne : app P c ≠ z := fun he => hc (app_eq_z he).2
    simp only [app_psi]
    cases hP : app P c with
    | z => exact absurd hP hne
    | psi d e f =>
      show holeLev (psi d e f) = holeLev c
      rw [← hP]; exact gA_holeLev_app P hc

/-- `fsD` of a single term with a hole is a single term (for a single index). -/
theorem gA_fsD_single {s y η : T} (hO : OHole (psi s y z)) (hη : ∃ a b, η = psi a b z) :
    ∃ s' y', fsD (psi s y z) η = psi s' y' z := by
  by_cases hy : y = z
  · subst hy
    have h2 : s ≠ z ∧ (isSucc s = true ∨ OHole s) := by simpa [OHole] using hO
    by_cases hs : isSucc s = true
    · rw [fsD_leaf hs h2.1]; exact hη
    · rw [fsD_sub h2.1 (by simpa using hs)]; exact ⟨_, _, rfl⟩
  · have hs : isSucc y = false := by
      by_contra hc
      have : isSucc y = true := by simpa using hc
      simp [OHole, hy, this] at hO
    rw [fsD_psi hy hs]; exact ⟨_, _, rfl⟩

/-- **Key (ordinal form)**: if the summands of `V` absorbed by the single term `X` stay below
`fsD(X, η)`, then `V < fsD(V + X, η)`. -/
theorem lt_fsD_add {V s y η : T} (hO : OHole (psi s y z)) (hη : ∃ a b, η = psi a b z)
    (habs : ∀ q ∈ summands V, q < psi s y z → q < fsD (psi s y z) η) :
    V < fsD (add V (psi s y z)) η := by
  obtain ⟨B, Lo, hb, hLo, he⟩ := add_prefix s y V
  rw [he, fsD_app B (by simp)]
  obtain ⟨s', y', hF⟩ := gA_fsD_single hO hη
  rw [hb]
  apply app_lt_app_left B
  rw [hF]
  cases Lo with
  | z => exact T.z_lt_psi _ _ _
  | psi a b c =>
    have hh : psi a b z < psi s y z := by
      rw [T.psi_lt_psi] at hLo
      rw [psi_lt_psi_z_iff]
      rcases hLo with h1 | ⟨rfl, h2⟩ | ⟨_, _, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, h2⟩
      · exact absurd h3 (T.not_lt_z _)
    have hq : psi a b z ∈ summands V := by
      rw [hb, summands_app]; simp [summands]
    have := habs _ hq hh
    rw [hF, psi_lt_psi_z_iff] at this
    rw [T.psi_lt_psi]
    rcases this with h1 | ⟨rfl, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨rfl, h2⟩)

theorem etaOm_single (μ : T) : ∃ a b, etaOm μ = psi a b z := ⟨_, _, rfl⟩

/-! ## 上げの先の値 -/

section
variable {M : Mat} {ρ : Valn}

/-- **The value of an upgrade target**: `v(k) = v(P_1 i) + W_k`, and the bump column `k` has the
same row-1 parent as `i`. -/
theorem upg_target_val (hC : Cons M ρ) (hG : Good3 M ρ) {i k : Nat} (hiM : i < M.length)
    (hu : upg M i = some k) :
    k < M.length ∧ entry M 1 k ≠ 0 ∧ entry M 2 k ≠ 0 ∧ par M 1 k = par M 1 i ∧
      ρ.v k = add (vOpt ρ (par M 1 i)) (bumpW M ρ k) ∧ Single (bumpW M ρ k) := by
  obtain ⟨m, hm, hmk, hcol, _⟩ := upg_spec hu
  have hkM := upg_lt hiM hu
  have h1k : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact (upg_e12 hu).1
  have h2k : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
  have hpar : par M 1 k = par M 1 i := by rw [hmk, hm]
  have hmM : m < M.length := by have := par_lt M 1 i m hm; omega
  have hVot : isOT (vOpt ρ (par M 1 k)) = true := by rw [hmk]; exact hG.ot_v m hmM
  have hoot : ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  obtain ⟨sW, yW, hv, hWot, _⟩ := v_bump_form hC hkM h1k h2k hVot hoot
  have hW : bumpW M ρ k = psi sW yW z := by
    have hY : isOT (sumN (one :: (children M k).map (bumpTerm M ρ k))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
        unfold bumpTerm
        split
        · rename_i hjb
          apply isOT_omega; apply isOT_sumN
          intro t' ht'
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ht'
          exact hoot j hj hjb k' hk'
        · rfl
    have hv' := (hC k hkM).2
    unfold vRhs at hv'
    rw [if_neg h1k, if_neg h2k, sf_ot (isOT_add hVot (isOT_omega hY))] at hv'
    rw [hv] at hv'
    -- both sides are `add V (single)`; compare the last summands
    have := congrArg last hv'
    rw [last_add_single] at this
    obtain ⟨s', y', hs'⟩ := (single_omega hY).2
    unfold bumpW; rw [hs']; rw [hs', last_add_single] at this; exact this.symm
  refine ⟨hkM, h1k, h2k, hpar, ?_, ?_⟩
  · rw [hv, hW, hpar]
  · rw [hW]; exact ⟨hWot, _, _, rfl⟩

/-- `last v(k)` of an upgrade target is its bump term. -/
theorem upg_target_last (hC : Cons M ρ) (hG : Good3 M ρ) {i k : Nat} (hiM : i < M.length)
    (hu : upg M i = some k) : last (ρ.v k) = bumpW M ρ k := by
  obtain ⟨_, _, _, _, hv, _, s, y, hW⟩ := upg_target_val hC hG hiM hu
  rw [hv, hW, last_add_single]

/-- **AbsU from AbsD**: an upgrade target is a bump column with the same `v(P_1)`. -/
theorem absU_of_absD (hC : Cons M ρ) (hG : Good3 M ρ) (hAD : AbsD M ρ) : AbsU M ρ := by
  intro i k hu hO q hq hlt
  have hiM : i < M.length := by have := upg_succ_lt hu; omega
  obtain ⟨hkM, h1k, h2k, hpar, _, _⟩ := upg_target_val hC hG hiM hu
  rw [upg_target_last hC hG hiM hu] at hO hlt ⊢
  rw [← hpar] at hq
  exact hAD k hkM h1k h2k hO q hq hlt


/-- **Key**: from AbsD and AbsU, `v(P_1 d) < fsD(v(d), ψ_μ(Ω_{μ+1}))` at every column with a hole in `v(d)`. -/
theorem lt_fsD_v (hC : Cons M ρ) (hG : Good3 M ρ) (hAD : AbsD M ρ) (hAU : AbsU M ρ) {d : Nat}
    (hd : d < M.length) (h1 : entry M 1 d ≠ 0) (hO : OHole (ρ.v d)) :
    vOpt ρ (par M 1 d) < fsD (ρ.v d) (etaOm (holeLev (ρ.v d))) := by
  have hVot : isOT (vOpt ρ (par M 1 d)) = true := by
    cases hp : par M 1 d with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 d m hp; omega)
  by_cases h2 : entry M 2 d = 0
  · cases hu : upg M d with
    | none =>
      exfalso
      have hv := (hC d hd).2
      unfold vRhs at hv
      rw [if_neg h1, if_pos h2, hu] at hv
      simp only at hv
      rw [sf_ot (isOT_add hVot rfl)] at hv
      rw [hv] at hO
      have : OHole (last (add (vOpt ρ (par M 1 d)) one)) := by
        obtain ⟨B, X, _, _, he⟩ := add_prefix z z (vOpt ρ (par M 1 d))
        rw [show one = psi z z z from rfl, he] at hO ⊢
        exact absurd (gA_ohole_app_inv (by simp) hO) (by simp [OHole])
      exact absurd this (by
        rw [show one = psi z z z from rfl, last_add_single]; simp [OHole])
    | some k =>
      obtain ⟨hkM, h1k, h2k, hpar, hvk, hWs⟩ := upg_target_val hC hG hd hu
      have hlast := upg_target_last hC hG hd hu
      obtain ⟨hWot, s, y, hW⟩ := hWs
      have hv := (hC d hd).2
      unfold vRhs at hv
      rw [if_neg h1, if_pos h2, hu] at hv
      simp only at hv
      rw [hlast, hW, sf_ot (isOT_add hVot (by rw [← hW]; exact hWot))] at hv
      have hOW : OHole (psi s y z) := by
        obtain ⟨B, X, _, _, he⟩ := add_prefix s y (vOpt ρ (par M 1 d))
        rw [hv, he] at hO; exact gA_ohole_app_inv (by simp) hO
      have hhl : holeLev (ρ.v d) = holeLev (psi s y z) := by
        obtain ⟨B, X, _, _, he⟩ := add_prefix s y (vOpt ρ (par M 1 d))
        rw [hv, he]; exact gA_holeLev_app B (by simp)
      rw [hhl, hv]
      apply lt_fsD_add hOW (etaOm_single _)
      intro q hq hlt
      have := hAU d k hu (by rw [hlast, hW]; exact hOW) q hq (by rw [hlast, hW]; exact hlt)
      rwa [hlast, hW] at this
  · have hoot : ∀ j ∈ children M d, col M j = bump M d → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
      fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
    obtain ⟨sW, yW, hv, _, _⟩ := v_bump_form hC hd h1 h2 hVot hoot
    have hW : bumpW M ρ d = psi sW yW z := by
      have hv' := (hC d hd).2
      unfold vRhs at hv'
      rw [if_neg h1, if_neg h2] at hv'
      have hl := congrArg last (hv'.symm.trans hv)
      rw [last_add_single] at hl
      have hY : isOT (sumN (one :: (children M d).map (bumpTerm M ρ d))) = true := by
        apply isOT_sumN
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
          unfold bumpTerm
          split
          · rename_i hjb
            apply isOT_omega; apply isOT_sumN
            intro t' ht'
            obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ht'
            exact hoot j hj hjb k' hk'
          · rfl
      obtain ⟨s', y', hs'⟩ := (single_omega hY).2
      rw [sf_ot (isOT_add hVot (isOT_omega hY)), hs', last_add_single] at hl
      unfold bumpW; rw [hs']; exact hl
    have hOW : OHole (psi sW yW z) := by
      obtain ⟨B, X, _, _, he⟩ := add_prefix sW yW (vOpt ρ (par M 1 d))
      rw [hv, he] at hO; exact gA_ohole_app_inv (by simp) hO
    have hhl : holeLev (ρ.v d) = holeLev (psi sW yW z) := by
      obtain ⟨B, X, _, _, he⟩ := add_prefix sW yW (vOpt ρ (par M 1 d))
      rw [hv, he]; exact gA_holeLev_app B (by simp)
    rw [hhl, hv]
    apply lt_fsD_add hOW (etaOm_single _)
    intro q hq hlt
    have := hAD d hd h1 h2 (by rw [hW]; exact hOW) q hq (by rw [hW]; exact hlt)
    rwa [hW] at this

/-! ## 候補の不変条件 PhiX: P_1 の鎖の上の v の部分項は、のりしろの項の穴を越えない

C′ の 434787 件で例外 0。長さ 9 の Good3 ∧ 構造の反例では AbsD の 2 個だけで破れる。AbsD・AbsU を含む。
-/

/-- `p` is on the row-1 parent chain of `c` (strictly above). -/
inductive P1Chain (M : Mat) : Nat → Nat → Prop
  | one {p c : Nat} : par M 1 c = some p → P1Chain M p c
  | step {p m c : Nat} : par M 1 c = some m → P1Chain M p m → P1Chain M p c

/-- **PhiX**: the subterms of `v(p)` for `p` on the row-1 chain of a bump column `c` stay below the
fundamental sequence of the bump term `W_c` at its hole. -/
def PhiX (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p, c < M.length → entry M 1 c ≠ 0 → entry M 2 c ≠ 0 → P1Chain M p c → OHole (bumpW M ρ c) →
    Reach (SubS (ρ.v p)) (bumpW M ρ c) (etaOm (holeLev (bumpW M ρ c)))

theorem absD_of_phiX (h : PhiX M ρ) : AbsD M ρ := by
  intro i hi h1 h2 hO q hq hlt
  cases hp : par M 1 i with
  | none => rw [hp] at hq; simp [vOpt, summands] at hq
  | some m =>
    rw [hp] at hq
    exact h i m hi h1 h2 (.one hp) hO q (summand_subS hq) hlt

theorem absU_of_phiX (hC : Cons M ρ) (hG : Good3 M ρ) (h : PhiX M ρ) : AbsU M ρ :=
  absU_of_absD hC hG (absD_of_phiX h)

end

end Ytosk
