/-
**3 行・t = 1: 展開 N = M[n] の貼り合わせの評価も FrameOT（枠の項が標準形）。**

枠の項 ψ_{v(i)}(spArg(v(i), Σ_{d ∈ L} o(d)))（L は数える子の並びの頭）は、x より前の列では M の枠と同じ:
- v が変わる列（D の v）は、数える子を持たない（`OShape` の前半）ので枠がない。
- 数える子の並びは M と同じ（`sameAt_lt`、数えるかどうかは `cnt` の一致から）。D の子は最後の数える子なので、
  枠の頭 L には D の列が入らず、値は M のもの。
x 以後の列は M[n − 1] の枠をずらしたもの（`children_shift`・`cnt_copy`）。
-/
import Ytosk.V3Good3N
import Ytosk.V3DropMain

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- Counting agrees when `cnt` agrees for every valuation. -/
theorem counted_iff_of_cnt {N M : Mat} {i c : Nat} (h : ∀ ρ : Valn, cnt N ρ i c = cnt M ρ i c) :
    Counted N i c ↔ Counted M i c := by
  classical
  have h1 := h ⟨fun _ => one, fun _ => z⟩
  rw [cnt_eq_ite, cnt_eq_ite] at h1
  have hone : one ≠ z := by unfold one; simp
  by_cases hN : Counted N i c <;> by_cases hM : Counted M i c
  · exact ⟨fun _ => hM, fun _ => hN⟩
  · rw [if_pos hN, if_neg hM] at h1; exact absurd h1 hone
  · rw [if_neg hN, if_pos hM] at h1; exact absurd h1.symm hone
  · exact ⟨fun h => absurd h hN, fun h => absurd h hM⟩

/-- Counting agrees when `cnt` agrees for one valuation whose value at `c` is nonzero. -/
theorem counted_iff_of_cnt1 {N M : Mat} {i c i' c' : Nat} {σ ρ : Valn}
    (h : cnt N σ i c = cnt M ρ i' c') (ho : σ.o c = ρ.o c') (hz : ρ.o c' ≠ z) :
    Counted N i c ↔ Counted M i' c' := by
  classical
  rw [cnt_eq_ite, cnt_eq_ite, ho] at h
  by_cases hN : Counted N i c <;> by_cases hM : Counted M i' c'
  · exact ⟨fun _ => hM, fun _ => hN⟩
  · rw [if_pos hN, if_neg hM] at h; exact absurd h hz
  · rw [if_neg hN, if_pos hM] at h; exact absurd h.symm hz
  · exact ⟨fun h => absurd h hN, fun h => absurd h hM⟩

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The frames of the glued valuation of `M[n]` are standard.** -/
theorem frameOT_N_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hFO : FrameOT M ρ) (hFOP : FrameOT (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i) :
    FrameOT (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  intro i hi Lc c R hCL
  rcases Nat.lt_or_ge i (r + L) with h | h
  · -- the frame is that of `M`
    have hS := hSA i h
    have hCLe : CL (TRIO.gexp M r L d0 0 n) i = CL M i := by
      unfold CL; rw [hS.ch]
      apply List.filter_congr
      intro c hc
      exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt c hc))
    rw [hCLe] at hCL
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
    have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
    -- `v(i)` does not change: otherwise `i` has no counted child
    have hvd : ¬ DepX M (r + L) false i := by
      intro hv
      rcases hOS i h (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
      · rcases hnc c hcch with h' | h'
        · exact hccnt.1 h'
        · exact hccnt.2 h'
      · exact hnv hv
    -- the head of the frame avoids `D`
    have hLd : ∀ d ∈ Lc, ¬ DepX M (r + L) true d := by
      intro d hd hdD
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
      have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
      have hdc : d < c := by
        have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
        rw [hCL] at hs
        exact (List.pairwise_append.mp hs).2.2 d hd c List.mem_cons_self
      have hiD : DepX M (r + L) true i := DepX.ochild hdch hdcnt.1 hdcnt.2 hdD
      rcases hOS i h hiD with ⟨hv, _⟩ | ⟨_, L', c', R', hch, _, _, hR', hL'⟩
      · exact hvd hv
      · have hdc' : d = c' := by
          rw [hch] at hdch
          rcases List.mem_append.mp hdch with h' | h'
          · exact absurd hdD (hL' d h' hdcnt)
          · rcases List.mem_cons.mp h' with h' | h'
            · exact h'
            · rcases hR' d h' with h'' | h''
              · exact absurd h'' hdcnt.1
              · exact absurd h'' hdcnt.2
        subst hdc'
        have hsort := children_sorted M i
        rw [hch] at hsort hcch
        rcases List.mem_append.mp hcch with h' | h'
        · have := (List.pairwise_append.mp hsort).2.2 c h' d List.mem_cons_self
          omega
        · rcases List.mem_cons.mp h' with h' | h'
          · omega
          · rcases hR' c h' with h'' | h''
            · exact hccnt.1 h''
            · exact hccnt.2 h''
    have hLo : Lc.map σ.o = Lc.map ρ.o := by
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdM := (mem_children (List.mem_filter.mp hdCL).1).2
      have hdx : d < r + L := by
        rcases Nat.lt_or_ge d (r + L) with h' | h'
        · exact h'
        · exfalso
          have : d = r + L := by omega
          exact hLd d hd (this ▸ DepX.leaf)
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hdx (hLd d hd)]
    rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z h hvd, ← hσ, hLo]
    exact hFO i (by omega) Lc c R hCL
  · -- a copy column
    obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hCLs : CL (TRIO.gexp M r L d0 0 n) (r + L + a) =
        (CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map (· + L) := by
      unfold CL
      rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.filter_map]
      congr 1
      apply List.filter_congr
      intro d hd
      have hdc := mem_children hd
      rw [hlP] at hdc
      show decide (Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L)) =
        decide (Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d)
      apply decide_eq_decide.mpr
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath hz2 (ρ := ρ) (Z := Z) ha hd)
      · have := hσo (d - r); rw [show r + L + (d - r) = d + L by omega,
          show r + (d - r) = d by omega] at this
        exact this
      · obtain ⟨s, y, he⟩ := o_psi_form hCP (i := d) (by rw [hlP]; omega)
        rw [he]; simp
    rw [hCLs] at hCL
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', hT', hc', hR⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR
    rw [hT'] at hsplit
    have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      have hdc := mem_children (List.mem_filter.mp hdCL).1
      have := hσo (d - r)
      rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
      exact this
    rw [hσv, hLo]
    exact hFOP (r + a) (by rw [hlP]; omega) Lc' c' R' hsplit

end

end Ytosk
