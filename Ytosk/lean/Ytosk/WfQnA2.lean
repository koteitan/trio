/-
**WfQnA2 (2026-11-01): the structural hypotheses of the `◁` engine for the t = 1, q ≠ r frame.**
Instance: `N = M[n] = TRIO.gexp M r L d0 0 n`, `x = r + L`, `bnd = x`, seeds `SB B` (the bad leaves, so
`DepS M (SB B) = DepXB M B`), unchanged set `U b i := ¬ DepX M x b i` (off `D`).
Proved here from `OShape` (`hOS_t1`), `dv_shape`, `uncnt_of_depv` and `SameAt` (`sameAt_lt`):
- `hnx_t1`: `v(x)` is not in `D`; `notXB`: `o(x)` is not in the closure;
- `depX_of_xb`: a call of the closure whose `v` is off the closure has its `v` off `D`;
- `hDvNilB`, `hCLnilB`, `hOcB`, `hVcB`, `hupgKB`: the structural hypotheses `hDvNil`, `hCLnil`, `hOc`, `hVc`,
  `hupgK` of `WfQnA1.deps_lhd_otUD` (stated with `DepXB`; `WfQnH8.depS_iff` converts).
-/
import Ytosk.WfQnH8
import Ytosk.WfQnA1
import Ytosk.V3ExpT1V

namespace Ytosk.WfQnA2
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
  {q : Nat} (hq : par M 0 (r + L) = some q)
  {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
include hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq hB

omit hL hd0e hn hq hB in
/-- **`v(x)` is not in `D`** (`t = 1`, `q ≠ r`). -/
theorem hnx_t1 : ¬ DepX M (r + L) false (r + L) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hr : r < r + L := par_lt M 1 (r + L) r h1
  have hrx : r ≠ r + L := by omega
  have hpath := hpath_of_par1 h1 hA hrx
  intro h
  cases h with
  | vpar _ hp hdm =>
    rw [h1] at hp; cases hp
    exact v_r_not_chg hlen hR0 hZ2 hSD hZ1 hUAT hUAB hA hrx hqr hpath (depX_chgX hdm)
  | vupg _ _ hu _ => have := upg_succ_lt hu; omega
  | vbump _ h2 _ _ _ _ => exact h2 hx2

omit hL hd0e hn hq in
/-- **`o(x)` is not in the closure** (`x` has no children and `v(x) ∉ D`). -/
theorem notXB : ¬ DepXB M B true (r + L) := by
  intro h
  cases h with
  | ochild hc _ _ _ => have := mem_children hc; omega
  | ov h => exact hnx_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr (DepXB.sub hB h)

omit hL hd0e hn h1 hqr hB in
/-- A `v` call of `D` counts no child, so an `o` call of the closure off the closure in `v` is off `D` in `v`. -/
theorem depX_of_xb {j : Nat} (hj : j < r + L) (hdt : DepXB M B true j) (hnf : ¬ DepXB M B false j) :
    ¬ DepX M (r + L) false j := by
  intro hv
  cases hdt with
  | ochild hc hcb hcu _ =>
    exact uncnt_of_depv hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hj hv hc ⟨hcb, hcu⟩
  | ov h => exact hnf h

omit hL hd0e hn h1 hqr in
/-- **`hDvNil`**. -/
theorem hDvNilB : ∀ c, c < r + L → DepXB M B false c → CL M c = [] := by
  intro c hc hd
  unfold CL; rw [List.filter_eq_nil_iff]
  intro d hdc
  simp only [decide_eq_true_eq]
  exact uncnt_of_depv hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hc (DepXB.sub hB hd) hdc

omit hqr hq hB in
/-- **`SameAt` before `x`** (`t = 1`). -/
theorem sameAt_t1 : ∀ i, i < r + L → SameAt M (TRIO.gexp M r L d0 0 n) i := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by have := par_lt M 1 (r + L) r h1; omega)
  exact sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)

omit hqr hq hB in
theorem CL_eq_t1 : ∀ j, j < r + L → CL (TRIO.gexp M r L d0 0 n) j = CL M j := by
  intro j hj
  have hS := sameAt_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 j hj
  unfold CL; rw [hS.ch]
  apply List.filter_congr
  intro d hd
  exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt d hd))

omit hqr hq hB in
/-- **`hCLnil`**. -/
theorem hCLnilB : ∀ c, c < r + L → CL M c = [] → CL (TRIO.gexp M r L d0 0 n) c = [] := by
  intro c hc h
  rw [CL_eq_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 c hc]; exact h

/-- **`hOc`**: at an `o` call of the closure whose `v` is off the closure, the last counted child carries it. -/
theorem hOcB : ∀ i, i < r + L → DepXB M B true i → ¬ DepXB M B false i →
    ∃ Lc c, CL M i = Lc ++ [c] ∧ CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] ∧ DepXB M B true c ∧
      c < r + L ∧ (∀ d ∈ Lc, ¬ DepX M (r + L) true d ∧ d < r + L) ∧ ¬ DepX M (r + L) false i ∧
      (¬ DepXB M B false c → ¬ DepX M (r + L) false c) := by
  intro i hi hD hv
  have hvX := depX_of_xb hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hD hv
  cases hD with
  | ov h => exact absurd h hv
  | @ochild _ c hc hcb hcu hdc =>
    rcases hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq i hi (DepX.ochild hc hcb hcu (DepXB.sub hB hdc)) with
      ⟨hvx, _⟩ | ⟨_, L0, c0, R, hch, _, _, hR, hLnd⟩
    · exact absurd hvx hvX
    have hcc : c = c0 := by
      rw [hch] at hc
      rcases List.mem_append.mp hc with h | h
      · exact absurd (DepXB.sub hB hdc) (hLnd c h ⟨hcb, hcu⟩)
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · rcases hR c h with h' | h'
          · exact absurd h' hcb
          · exact absurd h' hcu
    subst hcc
    have hcx : c < r + L := by
      have := (mem_children hc).2
      rcases Nat.lt_or_ge c (r + L) with h | h
      · exact h
      · exfalso
        have : c = r + L := by omega
        subst this
        exact notXB hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hB hdc
    have hRf : R.filter (fun d => decide (Counted M i d)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro d hd
      simp only [decide_eq_true_eq]
      intro hcd
      rcases hR d hd with h' | h'
      · exact hcd.1 h'
      · exact hcd.2 h'
    have hCLM : CL M i = L0.filter (fun d => decide (Counted M i d)) ++ [c] := by
      unfold CL; rw [hch, List.filter_append, List.filter_cons, hRf]
      simp [hcb, hcu, Counted]
    refine ⟨L0.filter (fun d => decide (Counted M i d)), c, hCLM, ?_, hdc, hcx, ?_, hvX, ?_⟩
    · rw [CL_eq_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 i hi]; exact hCLM
    · intro d hd
      rw [List.mem_filter] at hd
      have hnd := hLnd d hd.1 (by simpa using hd.2)
      refine ⟨hnd, ?_⟩
      have hdM : d ∈ children M i := by rw [hch]; simp [hd.1]
      have := (mem_children hdM).2
      rcases Nat.lt_or_ge d (r + L) with h | h
      · exact h
      · exfalso
        have : d = r + L := by omega
        subst this
        exact hnd DepX.leaf
    · intro hnf
      exact depX_of_xb hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hcx hdc hnf

/-- **`hVc`**: the shape of a `v` call of the closure that is not a seed. -/
theorem hVcB {ρ σ : Valn} (hσo : ∀ e, e < r + L → ¬ DepX M (r + L) true e → σ.o e = ρ.o e) :
    ∀ i, i < r + L → ¬ B i → DepXB M B false i →
      entry (TRIO.gexp M r L d0 0 n) 1 i = entry M 1 i ∧ entry (TRIO.gexp M r L d0 0 n) 2 i = entry M 2 i ∧
      par (TRIO.gexp M r L d0 0 n) 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepXB M B false m ∧ ¬ DepX M (r + L) false m) ∧
      upg (TRIO.gexp M r L d0 0 n) i = upg M i ∧
      (∀ k, upg M i = some k → DepXB M B false k → k < r + L) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children (TRIO.gexp M r L d0 0 n) i = Lb ++ [j] ∧
        col M j = bump M i ∧ col (TRIO.gexp M r L d0 0 n) j = bump (TRIO.gexp M r L d0 0 n) i ∧
        children M j = Kb ++ [k] ∧ children (TRIO.gexp M r L d0 0 n) j = Kb ++ [k] ∧ k < r + L ∧
        entry (TRIO.gexp M r L d0 0 n) 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepXB M B true d ∧ d < r + L ∧ ¬ DepX M (r + L) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepXB M B true e) ∧
        (∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L d0 0 n) σ i d = bumpTerm M ρ i d) ∧
        (¬ DepXB M B false k → ¬ DepX M (r + L) false k)) := by
  intro i hi hs hD
  have hSA := sameAt_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2
  have hS := hSA i hi
  have hnx := hnx_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr
  obtain ⟨h1i, hpd, hcase⟩ := dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepXB.sub hB hD)
  refine ⟨hS.e1, hS.e2, hS.par1, fun m hm => ⟨fun h => hpd m hm (DepXB.sub hB h), hpd m hm⟩, hS.upg,
    fun k hk hdk => ?_, fun h2 => ?_⟩
  · have := upg_le hk
    rcases Nat.lt_or_ge k (r + L) with h | h
    · exact h
    · exfalso
      have : k = r + L := by omega
      subst this
      exact hnx (DepXB.sub hB hdk)
  · rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
    · exact absurd h2' h2
    -- `(true, k)` is in the closure
    have hdkB : DepXB M B true k := by
      cases hD with
      | leaf h => exact absurd h hs
      | vpar _ hm hdm => exact absurd (DepXB.sub hB hdm) (hpd _ hm)
      | vupg _ h2' _ _ => exact absurd h2' h2
      | @vbump _ j0 k0 _ _ hj0 hjb0 hk0 hdk0 =>
        rw [hch] at hj0
        rcases List.mem_append.mp hj0 with h | h
        · exact absurd (DepXB.sub hB hdk0) (hLnd j0 h k0 hk0).2
        · have hjj : j0 = j := List.mem_singleton.mp h
          subst hjj
          rw [hchj] at hk0
          rcases List.mem_append.mp hk0 with h' | h'
          · exact absurd (DepXB.sub hB hdk0) (hKnd k0 h')
          · have hkk : k0 = k := List.mem_singleton.mp h'
            subst hkk; exact hdk0
    have hjM : j ∈ children M i := by rw [hch]; simp
    have hkM : k ∈ children M j := by rw [hchj]; simp
    have hjx : j < r + L := by
      have := (mem_children hjM).2
      rcases Nat.lt_or_ge j (r + L) with h | h
      · exact h
      · exfalso
        have : j = r + L := by omega
        subst this
        have := e2_of_col (show col M (r + L) = (entry M 0 i + 1, entry M 1 i, 1) from hjb)
        omega
    have hkx : k < r + L := by
      have := (mem_children hkM).2
      rcases Nat.lt_or_ge k (r + L) with h | h
      · exact h
      · exfalso
        have : k = r + L := by omega
        subst this
        exact notXB hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hB hdkB
    have hbN : bump (TRIO.gexp M r L d0 0 n) i = bump M i := by
      unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
    refine ⟨Lb, Kb, j, k, hch, by rw [hS.ch]; exact hch, hjb, ?_, hchj, by rw [(hSA j hjx).ch]; exact hchj, hkx,
      entry_gexp_pre hlen (by omega) 1 hkx, ?_, ?_, ?_, ?_⟩
    · rw [col_gexp_pre hlen (by omega) hjx, hbN]; exact hjb
    · intro d hd
      have hnd := hKnd d hd
      refine ⟨fun h => hnd (DepXB.sub hB h), ?_, hnd⟩
      have hdM : d ∈ children M j := by rw [hchj]; simp [hd]
      have := (mem_children hdM).2
      rcases Nat.lt_or_ge d (r + L) with h | h
      · exact h
      · exfalso
        have : d = r + L := by omega
        subst this
        exact hnd DepX.leaf
    · intro d hd e he h
      exact (hLnd d hd e he).2 (DepXB.sub hB h)
    · intro d hd
      have hdM : d ∈ children M i := by rw [hch]; simp [hd]
      rw [hS.bt d hdM σ]
      unfold bumpTerm
      split
      · congr 2
        apply List.map_congr_left
        intro e he
        exact hσo e (hLnd d hd e he).1 (hLnd d hd e he).2
      · rfl
    · intro hnf
      exact depX_of_xb hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hkx hdkB hnf

omit hqr hq hB in
/-- **`hupgK`**. -/
theorem hupgKB : ∀ i k, i < r + L → upg M i = some k → ∀ j ∈ children (TRIO.gexp M r L d0 0 n) k,
    col (TRIO.gexp M r L d0 0 n) j = bump (TRIO.gexp M r L d0 0 n) k →
    ∀ k' ∈ children (TRIO.gexp M r L d0 0 n) j, k' < r + L →
      j ∈ children M k ∧ col M j = bump M k ∧ k' ∈ children M j := by
  intro i k hi hu j hj hjb k' hk' _
  have hSA := sameAt_t1 hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hkx : k < r + L := by
    have := upg_le hu
    rcases Nat.lt_or_ge k (r + L) with h | h
    · exact h
    · exfalso
      have : k = r + L := by omega
      subst this
      have hMx := isUpg_M_x hlen hx2
      unfold isUpg at hMx
      rw [Bool.eq_false_iff] at hMx
      apply hMx
      rw [List.any_eq_true]
      exact ⟨i, List.mem_range.mpr (by omega), decide_eq_true hu⟩
  have hjM : j ∈ children M k := by rw [← (hSA k hkx).ch]; exact hj
  have hjx : j < r + L := by
    have := (mem_children hjM).2
    rcases Nat.lt_or_ge j (r + L) with h | h
    · exact h
    · exfalso
      have : j = r + L := by omega
      subst this
      exact hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn k (mem_children_iff.mp hjM).2 hjb
  have hbN : bump (TRIO.gexp M r L d0 0 n) k = bump M k := by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hkx, entry_gexp_pre hlen (by omega) 1 hkx]
  refine ⟨hjM, ?_, by rw [← (hSA j hjx).ch]; exact hk'⟩
  rw [← col_gexp_pre hlen (show 1 ≤ n by omega) hjx, ← hbN]; exact hjb

end

end Ytosk.WfQnA2
