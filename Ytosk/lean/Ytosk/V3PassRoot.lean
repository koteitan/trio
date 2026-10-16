/-
**PassRootRes を構造の不変条件 EqSibUpg に帰着（2026-10-16、t1）。**

EqSibUpg M: r の子 c に前の兄弟 b があり、c ののりしろの子 j の真の子孫 y が P_1(y) = r なら、c は上げ先。
（R1S の下では c の列は (e0 r + 1, e1 r + 1, 1)。前の兄弟は SibDec で c 以上なので同じ列。）

t = 1（x = 最後の列、r = P_1(x)、x の行 2 は 0）で、r の子 c が c < x・v(c) が D（DepX M x false c）なら:
- c は M.take x で topped（chg_struct の TopC）。
- c ののりしろの子 j の真の子孫 y で P_1(y) = r のものがある（`dep_child_bumpdesc`）:
  c が x の祖先なら y = x。そうでなければ D の出口（dep_exit）で c の部分木の直後の列 c′ が c′ − 1 から上げられ、
  y = c′ − 1。
- よって c に前の兄弟があれば EqSibUpg で c は上げ先。c は topped なので数えない子。
したがって PassRootRes（共終数の条件なし、前の兄弟は数える子に限らない強い形）は EqSibUpg から出る。
値の不変条件は使わない。
-/
import Ytosk.V3StructT1
import Ytosk.V3InvPer3
import Ytosk.V3ExpT1V

namespace Ytosk

open T

/-- **A later child of `r` that reaches `r` by `P_1` under its bump child is an upgrade target.** -/
def EqSibUpg (M : Mat) : Prop :=
  ∀ r b c j y, b ∈ children M r → c ∈ children M r → b < c → j ∈ children M c → col M j = bump M c →
    Anc0 M j y → j ≠ y → par M 1 y = some r → isUpg M c = true

/-- The last child of `c` below `x` is its bump child when `c` is topped in `M.take x`. -/
theorem last_child_bump {M : Mat} {x c p z : Nat} (hcx : c < x) (hT : topped (M.take x) c = true)
    (hpc : par M 0 p = some c) (hpx : p < x) (hpl : p < M.length) (hpz : Anc0 M p z)
    (hle : ∀ e, par M 0 e = some c → e < x → e ≤ z) : col M p = bump M c := by
  have hcp := par_lt M 0 p c hpc
  have hpT : p ∈ children (M.take x) c := by
    rw [children_take, List.mem_filter]; exact ⟨mem_children_iff.mpr ⟨hpl, hpc⟩, by simpa using hpx⟩
  have hmax : ∀ e ∈ children (M.take x) c, e ≤ p := by
    intro e he
    rw [children_take, List.mem_filter] at he
    have hex : e < x := by simpa using he.2
    have hpe : par M 0 e = some c := (mem_children_iff.mp he.1).2
    by_contra hlt
    have hez := hle e hpe hex
    have hA := anc_between hpz e (by omega) hez
    have := (anc0_par hA (by omega) hpe).le
    omega
  have hsplit := split_last_max _ _ (children_sorted (M.take x) c) hpT hmax
  have htop := hT
  unfold topped at htop
  rw [hsplit] at htop
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, decide_eq_true_eq] at htop
  rwa [col_take M hpx, bump_take M hcx] at htop

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {r : Nat} (h1 : par M 1 x = some r)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1

/-- **A child of `r` whose `v` is in `D` reaches `r` by `P_1` strictly under its bump child.** -/
theorem dep_child_bumpdesc {c : Nat} (hc : par M 0 c = some r) (hcx : c < x) (hv : DepX M x false c) :
    ∃ j y, j ∈ children M c ∧ col M j = bump M c ∧ Anc0 M j y ∧ j ≠ y ∧ par M 1 y = some r := by
  have hrx := par_lt M 1 x r h1
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hv)).1 rfl hcx
  have hrc := par_lt M 0 c r hc
  by_cases hAc : Anc0 M c x
  · obtain ⟨p, hpc, hpx⟩ := anc0_child hAc (by omega)
    have hpx' : p ≠ x := by
      intro he
      subst he
      rw [hpc] at hq
      cases hq
      exact nodep_v_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hpc hv
    have hpxlt : p < x := lt_of_le_of_ne hpx.le hpx'
    have hb := last_child_bump hcx hT.1 hpc hpxlt (by omega) hpx (fun e _ hex => hex.le)
    exact ⟨p, x, mem_children_iff.mpr ⟨by omega, hpc⟩, hb, hpx, hpx', h1⟩
  · obtain ⟨c', ⟨hcc', hin, hnot⟩, hc'x, hu, _⟩ :=
      dep_exit hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hv c (Anc0.refl c) hAc
    obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
    have hAr' : Anc0 M r c' := anc_between hA c' (by omega) (by omega)
    have hAmc' : Anc0 M m c' := anc0_of_par M 1 m c' hm2
    have hAmy : Anc0 M m (c' - 1) := anc0_of_par M 1 m (c' - 1) hm1
    have hAcy : Anc0 M c (c' - 1) := hin (c' - 1) (by omega) (by omega)
    have he0c' : entry M 0 c' = entry M 0 m + 1 := e0_of_col hcol
    have hmr : m = r := by
      rcases anc0_total hAmy hAcy with hmc | hcm
      · by_cases hmc' : m = c
        · subst hmc'; exact absurd hAmc' hnot
        have hAmr := anc0_par hmc hmc' hc
        by_contra hne
        have h0 := anc0_e0_lt hAmr hne
        have h0' := anc0_e0_lt hAr' (by omega)
        omega
      · exact absurd (hcm.trans hAmc') hnot
    subst hmr
    have he2r : entry M 2 m = 0 := e2_r_zero h1 hA (by omega) hZ2 hZ1
    have hyc : c' - 1 ≠ c := by
      intro hyc
      have hc'e : c' = c + 1 := by omega
      rw [hyc, hc'e] at hu
      rw [hc'e] at hcol hAr' he0c'
      simp only [Nat.add_sub_cancel] at hcol
      -- `c + 1` is the next child of `m`
      obtain ⟨p', hp'⟩ := par0_of_anc hAr' (by omega)
      have hAp' := anc0_par hAr' (by omega) hp'
      have he0p' := hR0 _ _ hp'
      have hp'm : m = p' := anc0_eq_of_e0 hAp' (Anc0.refl p') (by omega)
      subst hp'm
      have hcl : c + 1 < M.length := by omega
      have hcM : c ∈ children M m := mem_children_iff.mpr ⟨by omega, hc⟩
      have hc1M : c + 1 ∈ children M m := mem_children_iff.mpr ⟨hcl, hp'⟩
      obtain ⟨l1, l2, hsplit⟩ := consec_split (children_sorted M m) hcM hc1M (by omega)
        (fun e _ he => by omega)
      have hle := hSD m l1 l2 c (c + 1) hsplit
      have hne1 := (upg_e12 hu).2
      have hz := hZ2 c
      have hc0 := hR0 c m hc
      unfold colLe at hle
      rw [hcol] at hle
      have h0 : entry M 0 c = (col M c).1 := rfl
      have h1' : entry M 1 c = (col M c).2.1 := rfl
      have h2 : entry M 2 c = (col M c).2.2 := rfl
      simp only at hle
      omega
    obtain ⟨p, hpc, hpy⟩ := anc0_child hAcy (Ne.symm hyc)
    have hcp := par_lt M 0 p c hpc
    have hpx : p < x := by have := hpy.le; omega
    have hle : ∀ e, par M 0 e = some c → e < x → e ≤ c' - 1 := by
      intro e he _
      by_contra hlt
      exact hnot (anc_between (Anc0.step he (Anc0.refl c)) c' (by omega) (by omega))
    have hb := last_child_bump hcx hT.1 hpc hpx (by omega) hpy hle
    have hpy' : p ≠ c' - 1 := by
      intro he
      rw [← he] at hu
      have := (upg_e12 hu).2
      exact this (e2_of_col hb)
    exact ⟨p, c' - 1, mem_children_iff.mpr ⟨by omega, hpc⟩, hb, hpy, hpy', hm1⟩

/-- **A child of `r` whose `v` is in `D` has no earlier sibling at all** (given `EqSibUpg`), if it counts. -/
theorem dep_child_first (hE : EqSibUpg M) {c : Nat} (hc : c ∈ children M r) (hcnt : Counted M r c)
    (hcx : c < x) (hv : DepX M x false c) : ∀ b ∈ children M r, ¬ b < c := by
  intro b hb hbc
  have hpc := (mem_children_iff.mp hc).2
  obtain ⟨j, y, hj, hjb, hjy, hne, hy1⟩ := dep_child_bumpdesc hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hpc hcx hv
  have hup := hE r b c j y hb hc hbc hj hjb hjy hne hy1
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hv)).1 rfl hcx
  have hrx := par_lt M 1 x r h1
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hxc : x ∉ children M c := by
    intro hxc
    have hqc : q = c := by rw [(mem_children_iff.mp hxc).2] at hq; exact (Option.some.inj hq).symm
    subst hqc
    exact nodep_v_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hv
  have htop : topped M c = true := by rw [← topped_take_eq hx hcx hxc]; exact hT.1
  exact hcnt.2 ⟨hup, htop⟩

end

/-- **PassRootRes from EqSibUpg** (structural; the cofinality premise is not used). -/
theorem passRootRes_of_eqSib {M : Mat} {r L : Nat} {ρ : Valn} (S : SInv M) (hE : EqSibUpg M)
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    PassRootRes M r L ρ := by
  intro Lc c R hCL hcd hcx _
  rw [List.eq_nil_iff_forall_not_mem]
  intro d hd
  have hcCL : c ∈ CL M r := by rw [hCL]; simp
  have hdCL : d ∈ CL M r := by rw [hCL]; simp [hd]
  have hcch : c ∈ children M r := (List.mem_filter.mp hcCL).1
  have hccnt : Counted M r c := by simpa using (List.mem_filter.mp hcCL).2
  have hdch : d ∈ children M r := (List.mem_filter.mp hdCL).1
  have hdc : d < c := by
    have hs : (CL M r).Pairwise (· < ·) := (children_sorted M r).filter _
    rw [hCL] at hs
    exact (List.pairwise_append.mp hs).2.2 d hd c (by simp)
  exact dep_child_first hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 h1 hE hcch hccnt hcx hcd d hdch hdc

end Ytosk
