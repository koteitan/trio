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

/-- **The seed column `P_0(q) = r` of `M[n]`** (`t = 2`, `q ≠ r` counted at `r`): with `CL M r = Lc ++ [q]`,
`o_N(r) = ψ_a(step_a(B, v_N(q), step_{v_N(q)}(0, v_N(x′), σ(arg of o_P(r)))))` and `v_N(x′) = a + last(v_N(q))`.
The standard form of `o_N(q)` and the order of the counted values of `N` at `r` are given (`hqOT`, `hdecN`). -/
theorem o_r_level_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    (hqOT : isOT (σ.o q) = true)
    (hdecN : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a)) :
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
    σ.o r = psi (ρ.v r) (step (ρ.v r) (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) (σ.v q)
      (step (σ.v q) z (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z) z) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hqc := cl_mem_children hqcl
  have hpq : par M 0 q = some r := (mem_children_iff.mp hqc).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqcnt : Counted M r (r + qp) := by simpa using (List.mem_filter.mp hqcl).2
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hqcntN : Counted N r (r + qp) := by
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact hqcnt.1, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hCLN : CL N r = Lc ++ [r + qp] := by
    rw [← hCLM]; unfold CL
    rw [hchN r (by omega)]
    apply List.filter_congr
    intro c hc
    by_cases hcq : c = r + qp
    · rw [hcq]; simp [hqcntN, hqcnt]
    · have hcx : c < r + L := by
        have hcl := (mem_children hc).2
        by_contra h'
        have hcx' : c = r + L := by omega
        rw [hcx'] at hc
        have := (mem_children_iff.mp hc).2; rw [hq] at this
        have := Option.some.inj this; omega
      simp only [decide_eq_decide]
      exact hcntN r c (by omega) hcx hcq
  -- `N` agrees with `M` outside `D = DepS M {v(q), o(r)}`
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hq Txb I.be h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := fun i hi =>
    upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children N i → r + L ≤ j → col N j ≠ bump N i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL0 hA hq hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col N (r + L) = (entry N 0 i + 1, entry N 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) r) (bnd := r + L) I.cons hCN hRN (by omega) (by rw [hlN]; omega)
    (fun i hi _ => hchN i hi) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i hqi hb => by have h' := (mem_children_iff.mp hqi).2; rw [hpq] at h'; cases h'; exact Tqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntN i c hi hcx (by
      intro hcq; apply hd; apply DepS.seed; right; refine ⟨rfl, ?_⟩
      have h' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h'; exact (Option.some.inj h').symm))
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hq Txb I.be hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb Tqb)
  have htq : topped M (r + qp) = true := by
    unfold topped; rw [hsplitq]; simp [Txb]
  have hinv : ∀ {b i}, DepS M (SQ (r + qp) r) b i → i < M.length → Anc0 M (r + qp) i ∨ rk true r ≤ rk b i :=
    fun h hi => depS_SQ_inv I.rank hpq Tqb hqcnt.2 htq he2r h hi
  have hvr : σ.v r = ρ.v r := (hoff r (by omega)).2 (fun hD => by
    rcases hinv hD hrM with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).1; omega)
  have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdq : d < r + qp := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + qp) (by simp)
    refine (hoff d (by omega)).1 (fun hD => ?_)
    rcases hinv hD (by omega) with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2; omega
  -- the copy root `x′`
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = a + last(v_N(q))`
  have hvq := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb I.be I.uat hUN I.cons I.good hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hvx : σ.v (r + L) = add (ρ.v r) (last (σ.v (r + qp))) := by
    rw [(hCN (r + L) hxN).2]; unfold vRhs
    have he1 : entry N 1 (r + L) ≠ 0 := by
      have := entry1_xN hlen hL0 hA hq hd0e hn hd1e
      rw [← hN] at this; rw [this]; omega
    rw [if_neg he1, if_pos hx2N]
    have hp1 := par1_xN hlen hL0 hA hq hd0e hn hd1e
    rw [hr1, ← hN] at hp1
    have hu := upg_N_x_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb hJ hX.r0p I.be
    rw [← hN] at hu
    rw [hp1, hu]
    show sf (add (σ.v r) (last (σ.v (r + qp)))) = _
    rw [hvr, sf_ot (isOT_add hVot (isOT_last hvq.1))]
  refine ⟨hvx, ?_⟩
  -- the frame of `q`: only `x′`
  have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
    rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
  have hxOT : isOT (psi (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have := isOT_shTop (V' := σ.v (r + L)) (hGP.ot_v r hrP) hV' hVV hPo (le_refl _)
    rwa [shf_self] at this
  have hoq := o_last_form (Lc := []) hCN hqN hvq.1 (by rw [hCLNq]; rfl)
    (fun c hc => by rw [hCLNq] at hc; simp at hc; rw [hc, hox]; exact ⟨hxOT, _, _, rfl⟩)
    (by rw [hCLNq]; simp) hox
  -- the frame of `r`
  have hoqf : ∃ s y, σ.o (r + qp) = psi s y z := ⟨_, _, hoq⟩
  have hsN : ∀ c ∈ CL N r, Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [hLc c hc]
      exact single_o I.cons I.good (mem_children (cl_mem_children (show c ∈ CL M r by rw [hCLM]; simp [hc]))).2
    · simp at hc; rw [hc]; exact ⟨hqOT, hoqf⟩
  have hor := o_last_form hCN hrN (by rw [hvr]; exact hVot) hCLN hsN hdecN hoq
  rw [hor, hvr, List.map_congr_left hLc]
  rfl

end Ytosk
