/-
**t = 2, C1: `decP` split into a shape and the untopped case (2026-11-10).**

`decP` (C1): the last counted child `c₀` of `r` in `T = M.take x` has `qnS < v(c₀)`.
- `c₀` topped in `T`: in all measured frames the shape is `c₀ → b → q − 1` with `b` the bump child of `c₀`
  (`DecPShape`, structural). Then `decP_of_shape` (codex, V3DecPTop): `v(q − 1) = v(q) = qnS` and
  `v(c₀) = V + ω^{… ω^{… + ψ_{qnS}(…)}}`.
- `c₀` untopped (the counted children chain, about 3%): the residual `DecPUntop`.
`P_1 c₀ = r` from `sib_le` (`col q ≤ col c₀`), and `upg(q − 1) = q` from `ChgX.snb`, `TopC` and `no_anc_upg`.
-/
import Ytosk.V3DecPTop

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The shape of `decP` when `c₀` is topped** (structural). -/
def DecPShape (M : Mat) (r L q : Nat) : Prop :=
  ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] → topped (M.take (r + L)) c0 = true →
    ∃ b, b ∈ children M c0 ∧ b < r + L ∧ col M b = bump M c0 ∧ q - 1 ∈ children M b

/-- **`decP` when `c₀` is not topped** (the remaining value claim). -/
def DecPUntop (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
    topped (M.take (r + L)) c0 = false → qnS M ρ r L q < τ.v c0

/-- `decP` from the shape and the untopped case. -/
theorem decP_of_split {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hun : upg M (r + L - 1) = none) (hsh : DecPShape M r L q) (hut : DecPUntop M ρ r L q) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
      ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s := by
  intro τ hτ Lc c0 hCL
  have hx : r + L + 1 = M.length := hlen
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hx1 : M.length - 1 = r + L := by omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx1]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx1] at hG
  obtain ⟨hpq, hnqT, hxb⟩ := c_q_facts hM hS I hlen hr hq hqr hncl
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrq : r < q := par_lt M 0 _ _ hpq
  -- `c₀` is a child of `r` below `x`
  have hc0CL : c0 ∈ CL (M.take (r + L)) r := by rw [hCL]; simp
  have hc0T := cl_mem_children hc0CL
  have hc0T' : c0 < (M.take (r + L)).length := (mem_children hc0T).2
  have hc0x : c0 < r + L := by rw [List.length_take] at hc0T'; omega
  have hc0M : c0 ∈ children M r := by
    rw [children_take] at hc0T; exact (List.mem_filter.mp hc0T).1
  have hpc0 : par M 0 c0 = some r := (mem_children_iff.mp hc0M).2
  have hcc0 : Counted (M.take (r + L)) r c0 := by
    have := (List.mem_filter.mp hc0CL).2; simpa using this
  have hc0q : c0 ≠ q := by rintro rfl; exact hnqT hcc0
  -- `q` is the largest child of `r`
  have hqM : q ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hxr : r + L ∉ children M r := fun h => by
    have := (mem_children_iff.mp h).2; rw [hq] at this; cases this; exact hqr rfl
  have hmax : ∀ d ∈ children M r, d ≤ q := by
    intro d hd
    by_contra hlt
    have hdl := (mem_children hd).2
    have hdx : d ≠ r + L := fun e => hxr (e ▸ hd)
    have hpd := (mem_children_iff.mp hd).2
    have h1 := ((par0_spec M).mp hpd).2.2 q (by omega) (by omega)
    have h2 := ((par0_spec M).mp hq).2.1
    have h3 := ((par0_spec M).mp hq).2.2 d (by omega) (by omega)
    omega
  have hc0lq : c0 < q := lt_of_le_of_ne (hmax c0 hc0M) hc0q
  -- `col q ≤ col c₀`, so `e₁ c₀ ≥ e₁ q > e₁ r`
  obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hc0M
  have hql2 : q ∈ l2 := by
    have hqm : q ∈ l1 ++ c0 :: l2 := by rw [← hsplit]; exact hqM
    rcases List.mem_append.mp hqm with h | h
    · exfalso
      have hs := children_sorted M r
      rw [hsplit] at hs
      have := (List.pairwise_append.mp hs).2.2 q h c0 (by simp)
      omega
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hc0q
      · exact h
  have hcle := sib_le I.sd l2 l1 c0 hsplit q hql2
  have he0 : entry M 0 q = entry M 0 c0 := by
    rw [I.r0p q r hpq, I.r0p c0 r hpc0]
  have he1q : entry M 1 r < entry M 1 q := by
    have h1 := par1_entry_lt (par1_x_r (by omega) I.z2 I.z1 hr)
    have : entry M 1 (r + L) = entry M 1 q := by
      have : entry M 1 (r + L) = (col M (r + L)).2.1 := rfl; rw [this, hxb]; rfl
    omega
  have he1c0 : entry M 1 q ≤ entry M 1 c0 := by
    unfold colLe at hcle
    have e0q : (col M q).1 = entry M 0 q := rfl
    have e0c : (col M c0).1 = entry M 0 c0 := rfl
    have e1q : (col M q).2.1 = entry M 1 q := rfl
    have e1c : (col M c0).2.1 = entry M 1 c0 := rfl
    rw [e0q, e0c, e1q, e1c] at hcle
    omega
  have hp1 : par M 1 c0 = some r := par1_of_child hpc0 (by omega)
  -- `τ.o c₀ = ψ_{v(c₀)}(…)`
  have ho := o_cl_eq hτ hG hc0T'
  refine ⟨τ.v c0, _, ho, ?_⟩
  cases htop : topped (M.take (r + L)) c0 with
  | false => exact hut τ hτ Lc c0 hCL htop
  | true =>
    obtain ⟨b, hb, hbx, hbb, hqb⟩ := hsh Lc c0 hCL htop
    have he2c0 : entry M 2 c0 ≠ 0 := by have := I.be c0 b hb hbb; omega
    -- the upgrader of `q` is `q − 1`
    have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
    have he2q : entry M 2 q ≠ 0 := by have := I.be q (r + L) hxq hxb; omega
    have hchg : ChgX M (r + L) false q := ChgX.snb (by omega) he2q hxq hxb
    have hTop := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchg).1 rfl hqx
    have hqb' : col M q ≠ bump M r := fun h => by
      have := I.be r q hqM h; have := (par2_facts I.z2 (by omega) hr).1; omega
    have hnq : ¬ Counted M r q := by
      intro hc
      apply hnqT
      refine ⟨by rw [col_take M hqx, bump_take M (by omega)]; exact hc.1, fun ⟨hU, _⟩ => ?_⟩
      apply hc.2
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk1, hk⟩ := (isUpg_take M (by omega) q).mp hU
        unfold isUpg; rw [List.any_eq_true]
        exact ⟨k, List.mem_range.mpr (by omega), by simp [hk]⟩
      · have hchq := children_split_x hx hxq
        unfold topped; rw [hchq, List.getLast?_append]; simp [hxb]
    have hUq : isUpg M q = true := by
      by_contra h
      exact hnq ⟨hqb', fun h' => h h'.1⟩
    unfold isUpg at hUq
    rw [List.any_eq_true] at hUq
    obtain ⟨i, _, hiq⟩ := hUq
    have hui : upg M i = some q := by simpa using hiq
    obtain ⟨m, _, _, _, hcase⟩ := upg_spec hui
    have hqi : q = i + 1 := by
      rcases hcase with h | ⟨hA, hlt⟩
      · exact h
      · exact absurd (no_anc_upg hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hTop hqx hui hA hlt) id
    have hupq : upg M (q - 1) = some q := by rw [show q - 1 = i by omega]; exact hui
    exact decP_of_shape hM hS I Ctx hlen hr hq hqr hun hτ hc0x hp1 (by omega) he2c0 hb hbx hbb hqb hupq

#print axioms decP_of_split

end Ytosk.V3Main.SeedPF
