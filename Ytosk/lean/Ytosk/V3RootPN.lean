/-
**3 行・t = 1: 展開 N = M[n] の根の値も左から増えない（rootP）。**

N の根は M の根と同じ（`roots_N_t1`、写しは行 0 が d0 > 0 ずれるので根にならない）。値が変わるのは x の根 Rt
（D に入る、x より前の最後の根）だけで、fsD(o(Rt), Z Rt) ≤ o(Rt) に下がる。前の根の値は変わらない。
根の値が 1 項であること（rootS）は Cons と Good3 から（`rootS_of_good`）。
-/
import Ytosk.V3FrameOTN

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The root values of the glued valuation of `M[n]` do not increase.** -/
theorem rootP_N_t1 {ρ ρN : Valn} {Z : Nat → T} {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hle : fsD (ρ.o Rt) (Z Rt) ≤ ρ.o Rt) :
    ((roots (TRIO.gexp M r L d0 0 n)).map (glueZ M (r + L) ρ ρN Z).o).Pairwise (fun a b => b ≤ a) := by
  have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
  have hRx := hRA.le
  have hsplit := roots_split hlen hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hpre_nd : ∀ c ∈ pre, ¬ DepX M (r + L) true c := by
    intro c hc hd
    have := depX_ge (by omega) hR0e hRx hRlast hd
    have := hpre_lt c hc; omega
  have hglue : (roots M).map (glueZ M (r + L) ρ ρN Z).o = pre.map ρ.o ++ [fsD (ρ.o Rt) (Z Rt)] := by
    rw [hsplit, List.map_append, List.map_singleton, glueZ_o_dep ρ ρN Z (by
      rcases Nat.eq_or_lt_of_le hRx with h | h
      · exfalso
        have h1 : entry M 0 (r + L) ≠ 0 := by
          have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
        rw [h] at hR0e
        exact h1 hR0e
      · exact h) hRd]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact glueZ_o_lt ρ ρN Z (by have := hpre_lt c hc; omega) (hpre_nd c hc)
  have hMl : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  rw [hMl] at hpM
  rw [roots_N_t1 hlen hL hA hd0e hn, hglue]
  rw [List.pairwise_append] at hpM ⊢
  refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb; subst hb
  exact le_trans hle (hpM.2.2 a ha _ (List.mem_singleton_self _))

end

/-! ## n = 1: `M.take x` -/

/-- **A root before the last root of `x` does not change in the drop** (`ICC`: a change would enter its
tree through an upgrade into the next column, but that column is not a root and its parent is in the tree). -/
theorem root_not_chg {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {R a : Nat} (hR0e : entry M 0 R = 0) (hRx : R < x) (ha0 : entry M 0 a = 0) (haR : a < R) :
    ¬ ChgX M x true a := by
  intro h
  have hI := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB h).2
  have hnA : ¬ Anc0 M a (x - 1) := fun hA => by
    have := anc0_interval hA R haR (by omega); omega
  obtain ⟨c', ⟨hac', hsub, hnot⟩, _, hu, _⟩ := hI a (by omega) (Anc0.refl a) hnA
  have he : entry M 0 c' ≠ 0 := by
    have := upg_next_e0 (M := M) (i := c' - 1) (by rw [show c' - 1 + 1 = c' by omega]; exact hu)
    rwa [show c' - 1 + 1 = c' by omega] at this
  obtain ⟨p, hp⟩ := par0_some_of (M := M) (a := a) hac' (by omega)
  obtain ⟨hpc, _, hbet⟩ := (par0_spec M).mp hp
  have hap : a ≤ p := by
    by_contra hlt
    have := hbet a (by omega) hac'; omega
  exact hnot (Anc0.step hp (hsub p hap hpc))

/-- The root order as a carried property. -/
def RootP (N : Mat) (σ : Valn) : Prop := ((roots N).map σ.o).Pairwise (fun a b => b ≤ a)

/-- **The root order is carried** (`t = 1`), with the structural hypotheses from the invariants of `M`. -/
theorem expStep_rootP_t1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {ρ : Valn} (hpM : RootP M ρ) : ExpStepT1 RootP M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 (r + L)
  have hRd := dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hRA
  have hRx : Rt < r + L := by
    rcases Nat.lt_or_ge Rt (r + L) with h | h
    · exact h
    · exfalso
      have : Rt = r + L := by have := hRA.le; omega
      rw [this] at hRt0
      have h2 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hRt0
      have he : entry M 1 (r + L) = 0 := by
        unfold entry; unfold col at h2; simpa using h2
      have := par1_entry_lt h1; omega
  intro n hn ρP Z _ _ _ _ _ _ _ hle _
  exact rootP_N_t1 hlen hL hA hd0e hn hRA hRt0 hRlast hRd hpM (hle Rt hRx hRd).1

/-- **The root order of `M.take x`** with any valuation that lowers the values (the drop), when `x` is
not a root. -/
theorem rootP_take {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hx0 : entry M 0 x ≠ 0)
    {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hle : ∀ i, i < x → ρ'.o i ≤ ρ.o i)
    (hpM : RootP M ρ) : RootP (M.take x) ρ' := by
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 x
  have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hRt0; rw [hRt0]; rfl
  have hRx : Rt < x := by
    rcases Nat.lt_or_ge Rt x with h | h
    · exact h
    · have : Rt = x := by have := hRA.le; omega
      rw [this] at hR0e; exact absurd hR0e hx0
  have hroots : roots (M.take x) = roots M := by
    have hlT : (M.take x).length = x := by rw [List.length_take]; omega
    unfold roots
    rw [hlT, range_filter_cut M.length x _ (by omega) (fun i h1 h2 => by
      simp only [decide_eq_false_iff_not]
      intro h
      have he : entry M 0 i = 0 := by unfold entry; unfold col at h; rw [h]; rfl
      rw [show i = x by omega] at he; exact hx0 he)]
    apply List.filter_congr
    intro i hi
    rw [col_take M (List.mem_range.mp hi)]
  have hsplit := roots_split hx hRA hRt0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hsame : pre.map ρ'.o = pre.map ρ.o := by
    apply List.map_congr_left
    intro c hc
    have hcR := hpre_lt c hc
    have hc0 : entry M 0 c = 0 := by
      have hcm : c ∈ roots M := (List.mem_filter.mp (by rw [← hpre]; exact hc)).1
      have := (mem_roots.mp hcm).2
      unfold entry; unfold col at this; rw [this]; rfl
    exact (chg_off hx hC hG hC' hR' c (by omega)).1
      (root_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hR0e hRx hc0 hcR)
  unfold RootP at hpM ⊢
  rw [hroots, hsplit, List.map_append, List.map_singleton, hsame]
  rw [hsplit, List.map_append, List.map_singleton] at hpM
  rw [List.pairwise_append] at hpM ⊢
  refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb; subst hb
  exact le_trans (hle Rt hRx) (hpM.2.2 a ha _ (List.mem_singleton_self _))

end Ytosk
