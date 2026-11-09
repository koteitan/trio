/-
**t = 2, C1: `decP` from the sibling chain (2026-11-10).**

The children of `r` from `c₀` to `q`: `c₀`, then upgraded topped siblings, then `q` (last). The shape
(`DecPShape2`, structural, measured): for adjacent siblings `w < w'` in this range, `w` has a bump child `b`
with the child `w' − 1`, and `upg(w' − 1) = w'`. Then from the right: `v(q) = qnS`; `v(w' − 1) = v(w')`
(`v_upg_takeG`), so `qnS ≤ v(w' − 1)` and `qnS < v(w)` (`decP_step`, codex). At `c₀` this is `decP`.
The untopped `c₀` stays as `DecPUntop`.
-/
import Ytosk.V3DecPStep
import Ytosk.V3DecPSplit

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The shape of `decP` when `c₀` is topped**: the sibling chain from `c₀` to `q` (structural). -/
def DecPShape2 (M : Mat) (r L q : Nat) : Prop :=
  ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] → topped (M.take (r + L)) c0 = true →
    ∀ w w', w ∈ children M r → w' ∈ children M r → c0 ≤ w → w < w' → w' ≤ q →
      (∀ c ∈ children M r, ¬ (w < c ∧ c < w')) →
      ∃ b, b ∈ children M w ∧ b < r + L ∧ col M b = bump M w ∧ w' - 1 ∈ children M b ∧
        upg M (w' - 1) = some w'

theorem exists_min_mem : ∀ {l : List Nat}, l ≠ [] → ∃ m ∈ l, ∀ c ∈ l, m ≤ c
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_mem (l := b :: l) (by simp)
    by_cases hab : m ≤ a
    · refine ⟨m, by simp [hm], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hab
      · exact hmin c hc'
    · refine ⟨a, by simp, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact le_rfl
      · have := hmin c hc'; omega

/-- The next sibling. -/
theorem next_child {M : Mat} {r w q : Nat} (hw : w ∈ children M r) (hq : q ∈ children M r) (hwq : w < q) :
    ∃ w' ∈ children M r, w < w' ∧ w' ≤ q ∧ ∀ c ∈ children M r, ¬ (w < c ∧ c < w') := by
  have h1 : q ∈ (children M r).filter (fun c => decide (w < c)) :=
    List.mem_filter.mpr ⟨hq, by simpa using hwq⟩
  obtain ⟨w', hw', hmin⟩ := exists_min_mem (List.ne_nil_of_mem h1)
  obtain ⟨hw'1, hw'2⟩ := List.mem_filter.mp hw'
  have hww' : w < w' := by simpa using hw'2
  refine ⟨w', hw'1, hww', hmin q h1, fun c hc hwc => ?_⟩
  have := hmin c (List.mem_filter.mpr ⟨hc, by simpa using hwc.1⟩)
  omega

/-- `decP` from the sibling chain and the untopped case. -/
theorem decP_of_split2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hun : upg M (r + L - 1) = none) (hsh : DecPShape2 M r L q) (hut : DecPUntop M ρ r L q) :
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
  have hux : ∀ c, upg M (r + L - 1) = some c → c = r + L := by
    intro c hc; rw [hun] at hc; cases hc
  -- `c₀` is a child of `r` below `x`
  have hc0CL : c0 ∈ CL (M.take (r + L)) r := by rw [hCL]; simp
  have hc0T := cl_mem_children hc0CL
  have hc0T' : c0 < (M.take (r + L)).length := (mem_children hc0T).2
  have hc0x : c0 < r + L := by rw [List.length_take] at hc0T'; omega
  have hc0M : c0 ∈ children M r := by
    rw [children_take] at hc0T; exact (List.mem_filter.mp hc0T).1
  have hcc0 : Counted (M.take (r + L)) r c0 := by
    have := (List.mem_filter.mp hc0CL).2; simpa using this
  have hc0q : c0 ≠ q := by rintro rfl; exact hnqT hcc0
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
  have he1q : entry M 1 r < entry M 1 q := by
    have h1 := par1_entry_lt (par1_x_r (by omega) I.z2 I.z1 hr)
    have : entry M 1 (r + L) = entry M 1 q := by
      have : entry M 1 (r + L) = (col M (r + L)).2.1 := rfl; rw [this, hxb]; rfl
    omega
  -- a child `w < q` of `r` has `e₁ w ≥ e₁ q`, so `P₁ w = r`
  have hp1 : ∀ w ∈ children M r, w < q → par M 1 w = some r ∧ entry M 1 w ≠ 0 := by
    intro w hw hwq
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hw
    have hql2 : q ∈ l2 := by
      have hqm : q ∈ l1 ++ w :: l2 := by rw [← hsplit]; exact hqM
      rcases List.mem_append.mp hqm with h | h
      · exfalso
        have hs := children_sorted M r
        rw [hsplit] at hs
        have := (List.pairwise_append.mp hs).2.2 q h w (by simp)
        omega
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
    have hcle := sib_le I.sd l2 l1 w hsplit q hql2
    have hpw : par M 0 w = some r := (mem_children_iff.mp hw).2
    have he1w : entry M 1 q ≤ entry M 1 w := by
      unfold colLe at hcle
      have e0q : (col M q).1 = entry M 0 q := rfl
      have e0c : (col M w).1 = entry M 0 w := rfl
      have e1q : (col M q).2.1 = entry M 1 q := rfl
      have e1c : (col M w).2.1 = entry M 1 w := rfl
      rw [e0q, e0c, e1q, e1c, I.r0p q r hpq, I.r0p w r hpw] at hcle
      omega
    exact ⟨par1_of_child hpw (by omega), by omega⟩
  have ho := o_cl_eq hτ hG hc0T'
  refine ⟨τ.v c0, _, ho, ?_⟩
  cases htop : topped (M.take (r + L)) c0 with
  | false => exact hut τ hτ Lc c0 hCL htop
  | true =>
    -- from the right: `qnS ≤ v(w)` for the children `c₀ ≤ w ≤ q`, strictly below `q`
    have key : ∀ n w, q - w = n → w ∈ children M r → c0 ≤ w → w ≤ q →
        qnS M ρ r L q ≤ τ.v w ∧ (w < q → qnS M ρ r L q < τ.v w) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro w hwn hw hc0w hwq
      rcases Nat.eq_or_lt_of_le hwq with rfl | hwq'
      · exact ⟨le_of_eq (c_vqP_of_un hM hS I hlen hr hq hqr hun τ hτ).symm, fun h => absurd h (lt_irrefl _)⟩
      obtain ⟨w', hw', hww', hw'q, hnb⟩ := next_child hw hqM hwq'
      obtain ⟨b, hb, hbx, hbb, hkb, hupk⟩ := hsh Lc c0 hCL htop w w' hw hw' hc0w hww' hw'q hnb
      have hIH := (ih (q - w') (by omega) w' rfl hw' (by omega) hw'q).1
      have hw'x : w' < r + L := by omega
      have hvk : qnS M ρ r L q ≤ τ.v (w' - 1) := by
        rw [v_upg_takeG I hx hτ hG hux hupk hw'x]; exact hIH
      have hwx : w < r + L := by omega
      obtain ⟨hp1w, he1w⟩ := hp1 w hw hwq'
      have he2w : entry M 2 w ≠ 0 := by have := I.be w b hb hbb; omega
      have hkx : w' - 1 < r + L := by omega
      have hlt := decP_step hM hS I Ctx hlen hr hq hqr hτ hwx hp1w he1w he2w hb hbx hbb hkb hkx hvk
      exact ⟨le_of_lt hlt, fun _ => hlt⟩
    exact (key (q - c0) c0 rfl hc0M le_rfl (le_of_lt hc0lq)).2 hc0lq

#print axioms decP_of_split2

end Ytosk.V3Main.SeedPF
