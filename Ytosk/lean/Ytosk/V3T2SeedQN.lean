/-
**3 行・t = 2・q ≠ r: 種 P_0(q) の構造。**

- `qn_par0_q`: P_0(q) = r（P_1(q) = r と RowJ: 間の列 pq は e1 pq = e1 q となり q が pq の bump 子になる）。
- `upg_N_x_q`: N = M[n] で写しの根 x′ は q へ上げる（x′ + 1 は行 0 が大きすぎ、climb の最初の候補 q が合う）。
-/
import Ytosk.V3T2SeedQRL

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section
variable {M : Mat} {r L q d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd1e : entry M 1 (r + L) = entry M 1 r + d1) (he2r : entry M 2 r = 0)
  (h1x : entry M 1 r < entry M 1 (r + L)) (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
  (hr1 : par M 1 (r + L) = some r)
include hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1

/-- **`P_0(q) = r`** (`q ≠ r`). -/
theorem qn_par0_q (hqr : q ≠ r) (hxb : col M (r + L) = bump M q) (hJ : RowJ M) (hR0 : R0P M)
    (hBE : BumpE2 M) : par M 0 q = some r := by
  have hp1q := par1_q hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hqr hxb
  have hrq : Anc0 M r q := anc0_par hA (by have := par_lt M 0 _ _ hq; omega) hq
  obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
  by_cases hpr : pq = r
  · rw [← hpr]; exact hpq
  · exfalso
    have hrpq : Anc0 M r pq := anc0_par hrq (Ne.symm hqr) hpq
    have hpqlt := par_lt M 0 q pq hpq
    obtain ⟨_, _, _, hbet⟩ := par1_facts hp1q
    have h1 := hbet pq hrpq (Anc0.step hpq (Anc0.refl pq)) hpr (by omega)
    have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by have := par_lt M 0 _ _ hq; omega, hq⟩
    have he2q : entry M 2 q = 1 := hBE q (r + L) hxq hxb
    have h2 := hJ q pq (by omega) hpq
    have h0 := hR0 q pq hpq
    apply hqb pq hpq
    rw [col_eq_entries, h0, he2q, show entry M 1 q = entry M 1 pq by omega]
    rfl

/-- **The copy root upgrades to `q`** in `N = M[n]` (`q ≠ r`). -/
theorem upg_N_x_q (hqr : q ≠ r) (hxb : col M (r + L) = bump M q) (hJ : RowJ M) (hR0 : R0P M)
    (hBE : BumpE2 M) : upg (TRIO.gexp M r L d0 d1 n) (r + L) = some q := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hqx := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hrqlt : r < q := lt_of_le_of_ne hrq.le (Ne.symm hqr)
  have hL2 : 2 ≤ L := by omega
  have hpq := qn_par0_q hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hqr hxb hJ hR0 hBE
  have hp1q := par1_q hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hqr hxb
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from hxb)
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := hBE q (r + L) hxq hxb
  have he0q : entry M 0 q = entry M 0 r + 1 := hR0 q r hpq
  -- the copy of `r + 1`
  have hr1A : Anc0 M r (r + 1) := anc_between hA (r + 1) (by omega) (by omega)
  have he0r1 : entry M 0 r < entry M 0 (r + 1) := anc0_e0_lt hr1A (by omega)
  have he0x1 : entry N 0 (r + L + 1) = entry M 0 (r + 1) + d0 := by
    have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
      (k := 1) (q := 1) hlen (by omega) (by omega)
    rw [show r + (1 * L + 1) = r + L + 1 by omega] at h
    have : entry N 0 (r + L + 1) = entry M 0 (r + 1) + 1 * d0 := by unfold entry; rw [hN, h]; rfl
    rw [this]; omega
  have hd0 : 0 < d0 := by have := anc0_e0_lt hA (by omega); omega
  obtain ⟨hx2N, _⟩ := entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn
  have hx1N := entry1_xN hlen hL hA hq hd0e hn hd1e
  have hx1N' : entry N 1 (r + L) = entry M 1 (r + L) := hx1N
  have hp1x := par1_xN hlen hL hA hq hd0e hn hd1e
  rw [hr1] at hp1x
  unfold upg
  rw [if_neg (by
    rintro (h | h | h)
    · rw [← hN] at hx1N; rw [hx1N] at h; omega
    · rw [← hN] at hx2N; rw [hx2N] at h; omega
    · rw [hlN] at h
      have : L ≤ n * L - L := by
        have := Nat.mul_le_mul_right L hn; omega
      omega)]
  rw [hp1x]
  simp only
  rw [if_neg (by
    rintro ⟨_, hc⟩
    have h0 : entry N 0 (r + L + 1) = entry N 0 r + 1 := by
      have : entry N 0 (r + L + 1) = (col N (r + L + 1)).1 := rfl
      rw [this, hc]
    rw [he0x1, entry_gexp_pre hlen hm1 0 (by omega)] at h0
    omega)]
  rw [par0_xN hlen hL hA hq hd0e hn]
  rw [show r + L + 1 = (r + L) + 1 from rfl]
  unfold climb
  rw [if_pos]
  apply decide_eq_true
  refine ⟨by rw [par_gexp_pre hlen hm1 1 hqx]; exact hp1q, ?_, ?_⟩
  · rw [col_gexp_pre hlen hm1 hqx, col_eq_entries, entry_gexp_pre hlen hm1 0 (by omega),
      entry_gexp_pre hlen hm1 2 (by omega), he0q, he2q, he2r, ← he1q, hx1N']
  · rw [entry_gexp_pre hlen hm1 0 hqx, he0x1, he0q]; omega

end

/-- **The closure of the `q ≠ r` seeds stays in the subtree of `q` or above `o(r)` in rank** (`P_0(q) = r`, `q`
counted at `r` and topped, `e2 r = 0`): every call of `DepS M {v(q), o(r)}` is a descendant of `q` or has rank at
least that of `o(r)`. -/
theorem depS_SQ_inv {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk) {q r : Nat} (hpq : par M 0 q = some r)
    (hqb : col M q ≠ bump M r) (hnU : ¬ (isUpg M q = true ∧ topped M q = true)) (htq : topped M q = true)
    (he2r : entry M 2 r = 0) :
    ∀ {b i}, DepS M (SQ q r) b i → i < M.length → Anc0 M q i ∨ rk true r ≤ rk b i := by
  intro b i h
  induction h with
  | @seed b i hs =>
    intro _
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Anc0.refl _)
    · exact Or.inr (le_refl _)
  | @ochild i c hc hcb hcu _ ih =>
    intro hi
    have hrk := (hR _ hi).2.1 _ hc hcb hcu
    rcases ih (mem_children hc).2 with hA | hle
    · by_cases hcq : c = q
      · subst hcq
        have : i = r := by rw [(mem_children_iff.mp hc).2] at hpq; exact Option.some.inj hpq
        subst this; exact Or.inr (le_refl _)
      · exact Or.inl (anc0_par hA (Ne.symm hcq) (mem_children_iff.mp hc).2)
    · exact Or.inr (by omega)
  | ov _ ih =>
    intro hi
    have := (hR _ hi).1
    rcases ih hi with hA | hle
    · exact Or.inl hA
    · exact Or.inr (by omega)
  | @vpar i m h1 hm _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).1 _ hm
    rcases ih (by have := par_lt _ 1 _ _ hm; omega) with hA | hle
    · exact Or.inl (Anc0.trans hA (anc0_of_par M 1 m i hm))
    · exact Or.inr (by omega)
  | @vupg i k h1 h2 hk _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).2.1 h2 _ hk
    rcases ih (upg_lt hi hk) with hA | hle
    · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
      rcases hcase with hk1 | ⟨hAk, _⟩
      · by_cases hkq : k = q
        · exfalso
          apply hnU
          refine ⟨?_, htq⟩
          unfold isUpg; apply List.any_eq_true.mpr
          exact ⟨i, List.mem_range.mpr hi, by rw [← hkq]; simpa using hk⟩
        · have hqk := hA.le
          exact Or.inl (anc_between hA i (by omega) (by omega))
      · exact Or.inl (Anc0.trans hA hAk)
    · exact Or.inr (by omega)
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).2.2 h2 _ hj hjb _ hk
    have hjl := (mem_children hj).2
    have hkl := (mem_children hk).2
    rcases ih hkl with hA | hle
    · by_cases hkq : k = q
      · subst hkq
        have hjr : j = r := by rw [(mem_children_iff.mp hk).2] at hpq; exact Option.some.inj hpq
        subst hjr
        exfalso
        have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
      · have hAj : Anc0 M q j := anc0_par hA (Ne.symm hkq) (mem_children_iff.mp hk).2
        by_cases hjq : j = q
        · subst hjq
          have hir : i = r := by rw [(mem_children_iff.mp hj).2] at hpq; exact Option.some.inj hpq
          subst hir
          exact absurd hjb hqb
        · exact Or.inl (anc0_par hAj (Ne.symm hjq) (mem_children_iff.mp hj).2)
    · exact Or.inr (by omega)

end Ytosk
