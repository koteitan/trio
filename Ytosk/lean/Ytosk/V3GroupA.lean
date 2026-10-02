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

end

end Ytosk
