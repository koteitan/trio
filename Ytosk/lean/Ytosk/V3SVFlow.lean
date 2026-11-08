/-
**t = 2, sv: the base of the flow for `T2SVStrict` (2026-11-08).**

In the sv case (`q = r`, `x − 1` upgrades to `x`) the column `ℓ = x − 1` is the last column of `T = M.take x`.
`upg_spec` gives `P_1(ℓ) = r` (the row-1 parent of `x` is that of `ℓ`, and it is the row-2 parent of `x`), `Z2`
gives `e₂(ℓ) = 0`, and `ℓ` is not upgraded in `T` (it is the last column), so `v_T(ℓ) = V + 1`.
-/
import Ytosk.V3CDomVRA

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The column `x − 1` in the sv case**: its row-1 parent is `r`, row 1 is nonzero, row 2 is `0`. -/
theorem sv_last_facts {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hux : upg M (r + L - 1) = some (r + L)) :
    par M 1 (r + L - 1) = some r ∧ entry M 1 (r + L - 1) ≠ 0 ∧ entry M 2 (r + L - 1) = 0 := by
  obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hux
  obtain ⟨he1, he2⟩ := upg_e12 hux
  have h2x : entry M 2 (r + L) = entry M 2 m + 1 := by
    have : entry M 2 (r + L) = (col M (r + L)).2.2 := rfl
    rw [this, hcol]
  have hpar2 : par M 2 (r + L) = some m := by
    have hp : par M 2 (r + L) = climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 (r + L)))
        (r + L + 1) (par M 1 (r + L)) := rfl
    rw [hp, hm2]
    simp [climb, h2x]
  have hrm : r = m := by rw [hr] at hpar2; exact Option.some.inj hpar2
  subst hrm
  have := I.z2 (r + L - 1)
  exact ⟨hm1, he1, by omega⟩

/-- **`v_T(x − 1) = V + 1`** in the sv case. -/
theorem sv_last_v {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    τ.v (r + L - 1) = succ (ρ.v r) := by
  obtain ⟨hp1, he1, he2⟩ := sv_last_facts I hlen hr hux
  obtain ⟨hG, hvr, _⟩ := sv_children_ctxV3 hM hS I Ctx hlen hr hq hux hτ
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hl : r + L - 1 < r + L := by omega
  have hlT : r + L - 1 < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  rw [(hτ _ hlT).2]
  unfold vRhs
  rw [entry_take M 1 hl, entry_take M 2 hl, if_neg he1, if_pos he2,
    upg_last_none (show r + L - 1 + 1 = (M.take (r + L)).length by rw [List.length_take]; omega),
    par_take M 1 _ hl, hp1]
  simp only [vOpt]
  rw [hvr, sf_ot (isOT_add hV isOT_one), add_one_eq_succ hV]

/-- **The high region above `r`**: `d` is a proper descendant of `r` and every column on the path from `r` to `d`
(other than `r`) has a larger row-1 entry than `r`. -/
def HighD (M : Mat) (r d : Nat) : Prop :=
  Anc0 M r d ∧ r ≠ d ∧ ∀ q, Anc0 M r q → Anc0 M q d → q ≠ r → entry M 1 r < entry M 1 q

/-- The row-1 parent of a high column is `r` or high. -/
theorem high_par1 {M : Mat} (h00 : entry M 0 0 = 0) (hR01 : R01 M) {r d : Nat} (hd : HighD M r d) :
    ∃ m, par M 1 d = some m ∧ (m = r ∨ HighD M r m) := by
  obtain ⟨hrd, hne, hall⟩ := hd
  have he1 : entry M 1 r < entry M 1 d := hall d hrd (Anc0.refl d) (fun h => hne h.symm)
  obtain ⟨m, hm⟩ := par1_exists h00 hR01 (j := d) (by omega)
  refine ⟨m, hm, ?_⟩
  have hmd : Anc0 M m d := anc0_of_par M 1 m d hm
  rcases anc0_total hmd hrd with hmr | hrm
  · by_cases hmr' : m = r
    · exact Or.inl hmr'
    · exfalso
      have hlt : m < r := lt_of_le_of_ne hmr.le hmr'
      have := par1_between hm r hrd hlt
      omega
  · by_cases hmr' : m = r
    · exact Or.inl hmr'
    · refine Or.inr ⟨hrm, fun h => hmr' h.symm, fun q hrq hqm hqr => hall q hrq (Anc0.trans hqm hmd) hqr⟩

/-- **Levels of the high region** in `T = M.take x`: `V < v(d)` and `V ≤ v(P_1 d)`. -/
theorem high_v {M : Mat} {τ : Valn} {rk : Bool → Nat → Nat} (h00 : entry M 0 0 = 0) (hR01 : R01 M)
    {x r : Nat} (hxM : x ≤ M.length) (hτ : Cons (M.take x) τ) (hG : Good3 (M.take x) τ) (hRk : Rk (M.take x) rk)
    {V : T} (hvr : τ.v r = V) :
    ∀ d, d < x → HighD M r d → V < τ.v d ∧ ∃ m, par M 1 d = some m ∧ V ≤ τ.v m ∧ (m = r ∨ HighD M r m) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdx hd
    obtain ⟨m, hm, hmr⟩ := high_par1 h00 hR01 hd
    have hmd : m < d := par_lt M 1 d m hm
    have he1 : entry M 1 d ≠ 0 := by
      have := hd.2.2 d hd.1 (Anc0.refl d) (fun h => hd.2.1 h.symm); omega
    have hdT : d < (M.take x).length := by rw [List.length_take]; omega
    have hlt : τ.v m < τ.v d :=
      v_par1_lt hτ hG hRk (rk false d) d m le_rfl hdT (by rw [entry_take M 1 hdx]; exact he1)
        (by rw [par_take M 1 d hdx]; exact hm)
    rcases hmr with rfl | hmH
    · exact ⟨hvr ▸ hlt, m, hm, le_of_eq hvr.symm, Or.inl rfl⟩
    · have hVm := (ih m hmd (by omega) hmH).1
      exact ⟨lt_trans hVm hlt, m, hm, le_of_lt hVm, Or.inr hmH⟩

end Ytosk.V3Main.SeedPF
