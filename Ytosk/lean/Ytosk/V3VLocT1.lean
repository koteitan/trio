/-
**3 行・t = 1・q ≠ r: v の枠の局所条件 VLocal を不変条件から。**

- 値の不変条件: TPLo（すべての o で低い部分が空のまま、TPL より強い）、AbsD（のりしろの枠で v(P_1 i) が
  W と fsD(W, ψ_μ(Ω_{μ+1})) に吸収される）、AbsU（上げの枠の吸収）。
- D の v の列の形（`dv_shape`、構造だけから）: 上げなら次の列へ、のりしろなら最後の子 j の最後の子 k だけが D。
-/
import Ytosk.V3FrameT1

namespace Ytosk

open T

/-! ## 値の不変条件 -/

/-- The lower index `ψ_μ(Ω_{μ+1})` for the level `μ`. -/
def etaOm (μ : T) : T := psi μ (psi (succ μ) z z) z

/-- **Value invariant TPLo**: for every `o(c) = ψ_s(y)` whose argument has no part below `Ω_{s+1}` and ends
with `Ω_a` (`a` a limit with a hole), `Ω_{fsD(a, ψ_μ(Ω_{μ+1}))} ≥ Ω_{s+1}`
(SRO より下の L9 網羅で 2080 件、例外 0). -/
def TPLo (M : Mat) (ρ : Valn) : Prop :=
  ∀ c, c < M.length → ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a →
    ¬ psi (fsD a (etaOm (holeLev y))) z z < psi (succ s) z z

theorem TPL_of_TPLo {M : Mat} {ρ : Valn} (h : TPLo M ρ) : TPL M ρ := by
  intro i L c R hch s y hcv _ _ hl a hla hs hOa
  have hc : c ∈ children M i := by rw [hch]; simp
  exact h c (mem_children hc).2 s y hcv hl a hla hs hOa

/-- **Value invariant AbsD**: at a bump frame whose bump term `W` has a hole, `v(P_1 i)` is absorbed by
`W` and by `fsD(W, ψ_μ(Ω_{μ+1}))` (SRO より下の L9 網羅で 4861 枠、例外 0。SRO より上では崩れる例がある). -/
def AbsD (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
    add (vOpt ρ (par M 1 i)) (bumpW M ρ i) = bumpW M ρ i ∧
    add (vOpt ρ (par M 1 i)) (fsD (bumpW M ρ i) (etaOm (holeLev (bumpW M ρ i)))) =
      fsD (bumpW M ρ i) (etaOm (holeLev (bumpW M ρ i)))

/-- **Value invariant AbsU**: at an upgrade `i → k` with a hole in `v(k)`, the summands of `v(P_1 i)` below
`v(k)` stay below `fsD(v(k), ψ_μ(Ω_{μ+1}))` (SRO より下の L9 網羅で 161 件、例外 0). -/
def AbsU (M : Mat) (ρ : Valn) : Prop :=
  ∀ i k, upg M i = some k → OHole (ρ.v k) → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < ρ.v k →
    q < fsD (ρ.v k) (etaOm (holeLev (ρ.v k)))

/-! ## D の v の列の形 -/

theorem mem_take_children {M : Mat} {x i c : Nat} (hc : c ∈ children M i) (hcx : c < x) :
    c ∈ children (M.take x) i := by
  rw [children_take, List.mem_filter]; exact ⟨hc, by simpa using hcx⟩

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq

/-- No `o` in `D` below a child of `p` (a column with row 2 nonzero) that has a later child,
counting `x` as a later child of `q`. -/
theorem nodep_not_last {p d d' : Nat} (h2 : entry M 2 p ≠ 0) (hd : d ∈ children M p)
    (hd' : d' ∈ children M p) (hdd : d < d') {b : Bool} {e : Nat} (hD : DepX M x b e)
    (hde : Anc0 M d e) : False := by
  have hd'l := (mem_children hd').2
  rcases Nat.lt_or_ge d' x with hd'x | hd'x
  · exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hd (mem_take_children hd' hd'x) hdd
      (depX_chgX hD) hde
  · have hd'e : d' = x := by omega
    subst hd'e
    have hpq : p = q := by
      rw [(mem_children_iff.mp hd').2] at hq; exact Option.some.inj hq
    subst hpq
    exact nodep_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq (Anc0.refl d') (fun h => absurd h (lt_irrefl _))
      _ d (Nat.le_refl _) hd hdd b e hD hde

/-- **The shape of a `v` call in `D`.** -/
theorem dv_shape {i : Nat} (hi : i < x) (hv : DepX M x false i) :
    entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
    ((entry M 2 i = 0 ∧ upg M i = some (i + 1) ∧ i + 1 < x ∧ DepX M x false (i + 1)) ∨
     (entry M 2 i ≠ 0 ∧ ∃ L K j k, children M i = L ++ [j] ∧ col M j = bump M i ∧
        children M j = K ++ [k] ∧ DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
        (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e))) := by
  have hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m := by
    intro m hp hdm
    have hmi := par_lt M 1 i m hp
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i hi hp
  cases hv with
  | vpar h1 hp hdm => exact absurd hdm (hpd _ hp)
  | @vupg _ k h1 h2 hu hdk =>
    refine ⟨h1, hpd, Or.inl ⟨h2, ?_⟩⟩
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with rfl | ⟨hA, hki⟩
    · refine ⟨hu, ?_, hdk⟩
      have := upg_succ_lt hu
      rcases Nat.lt_or_ge (i + 1) x with h | h
      · exact h
      · exfalso
        have hix : i + 1 = x := by omega
        rw [hix] at hu; exact upg_ne_e2z hu hx2
    · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
        ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl (by omega)) (by omega)
        hu hA hki).elim
  | @vbump _ j k h1 h2 hj hjb hk hdk =>
    refine ⟨h1, hpd, Or.inr ⟨h2, ?_⟩⟩
    have hj2 : entry M 2 j ≠ 0 := by
      have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
    have hAjk : Anc0 M j k := Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j)
    -- `j` is the last child of `i`
    have hjmax : ∀ j' ∈ children M i, j' ≤ j := by
      intro j' hj'; by_contra hlt
      exact nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq h2 hj hj' (by omega) hdk hAjk
    have hchi := split_last_max _ _ (children_sorted M i) hj hjmax
    -- `k` is the last child of `j`
    have hkmax : ∀ k' ∈ children M j, k' ≤ k := by
      intro k' hk'; by_contra hlt
      exact nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hj2 hk hk' (by omega) hdk (Anc0.refl k)
    have hchj := split_last_max _ _ (children_sorted M j) hk hkmax
    refine ⟨_, _, j, k, hchi, hjb, hchj, hdk, ?_, ?_⟩
    · intro d hd hdD
      have hdM : d ∈ children M j := (List.mem_filter.mp hd).1
      have hdk' : d < k := by simpa using (List.mem_filter.mp hd).2
      exact nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hj2 hdM hk hdk' hdD (Anc0.refl d)
    · intro d hd e he
      have hdM : d ∈ children M i := (List.mem_filter.mp hd).1
      have hdj : d < j := by simpa using (List.mem_filter.mp hd).2
      have hpe : par M 0 e = some d := (mem_children_iff.mp he).2
      have hAde : Anc0 M d e := Anc0.step hpe (Anc0.refl d)
      have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
      have hjx : j < x := by
        rcases Nat.lt_or_ge j x with h | h
        · exact h
        · exfalso
          have : j = x := by have := (mem_children hj).2; omega
          subst this
          have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
      have hej : e < j := by
        by_contra hge
        have hA := anc_between hAde j (by omega) (by omega)
        have := (anc0_par hA (by omega) hpj).le
        have := (mem_children hdM).1
        omega
      exact ⟨by omega, fun hD =>
        nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq h2 hdM hj hdj hD hAde⟩

end

end Ytosk
