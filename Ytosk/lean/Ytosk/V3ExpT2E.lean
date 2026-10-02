/-
**3 行・t = 2: M[n] の依存の順位（組み立て）。**

`rk_N_t2_abs`（V3ExpT2R）の構造の仮定を、x より前（V3ExpT2D の前半）と写し（V3ExpT2C・V3ExpT2D の後半）の
補題で埋める。M[n − 1] の順位は n についての帰納法で、底は M[1] = M.take x（`rk_take`）。

残る仮定（C′ の t = 2 の 8000 行列 × n = 2, 3, 4 で例外 0、`probe_t2struct.py`）:
- `hF2`: q ≠ r のとき o(q) は o(P_0 q) に依存しない（M で）。
- `htgt`: 写しの列の v が読む x より前の列 g（P_1 と上げの行き先）は、o(q)・o(p2) に依存しない（M で）。
-/
import Ytosk.V3ExpT2D

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L q p2 d0 d1 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
  (h1x : entry M 1 r < entry M 1 (r + L))
  (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
  (hp2 : q ≠ r → par M 0 q = some p2)
  (hF2 : p2 ≠ q → ¬ DepS M (SR p2) true q)
  (hUM : UAT M)
include hlen hL hA hq hd0e hd0 hd1 hgx he2r h1x hqb hp2 hF2 hUM

/-- The targets below `x` of the `v`-edges of the copies lie outside both seeded sets. -/
def T2Tgt (M : Mat) (r L q p2 : Nat) (N : Mat) : Prop :=
  ∀ g, g < r + L → (∃ a, r + L + a < N.length ∧ entry N 1 (r + L + a) ≠ 0 ∧
      (par N 1 (r + L + a) = some g ∨ (entry N 2 (r + L + a) = 0 ∧ upg N (r + L + a) = some g))) →
    ¬ DepS M (SR q) false g ∧ ¬ DepS M (SR p2) false g

/-- **The ranking of `M[n]`** (`t = 2`) from those of `M` and `M[n − 1]`. -/
theorem rk_gexp_t2 {n : Nat} (hn : 2 ≤ n) (hUN : UAT (TRIO.gexp M r L d0 d1 n))
    (hBEP : BumpE2 (TRIO.gexp M r L d0 d1 (n - 1)))
    (htgt : T2Tgt M r L q p2 (TRIO.gexp M r L d0 d1 n))
    {rkM rkP : Bool → Nat → Nat} (hRM : Rk M rkM) (hRP : Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP) :
    ∃ rk, Rk (TRIO.gexp M r L d0 d1 n) rk := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  have hm1 : 1 ≤ n := by omega
  refine ⟨_, rk_N_t2_abs (N := TRIO.gexp M r L d0 d1 n) (P := TRIO.gexp M r L d0 d1 (n - 1))
    (by omega) hlen hq ?_ ?_ ?_ hF2 ?_ ?_ ?_ htgt hRM hRP⟩
  · intro i hi
    exact ⟨entry_gexp_pre hlen hm1 1 hi, entry_gexp_pre hlen hm1 2 hi, par_gexp_pre hlen hm1 1 hi,
      children_N2g hlen hL hA hq hd0e hn hi, fun k hk => upg_N2g hlen hL hA hq hd0e hn he2r hi hk⟩
  · intro i hi c hc hct
    rcases counted_N2g hlen hL hA hq hd0e hn he2r h1x hUM hUN hi hc hct with h | h | ⟨hqr, hcq, hpi⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have := hp2 hqr; rw [this] at hpi; cases hpi
      exact Or.inr (Or.inr ⟨rfl, hcq⟩)
  · intro i hi j hj hjb
    exact bmp_N2g hlen hL hA hq hd0e hn he2r hqb hi hj hjb
  · intro a ha
    have ha' : a < (n - 1) * L := by omega
    refine ⟨children_shift2 hlen hL hA hd0e hn ha', fun d hd => ⟨?_, ?_⟩, e2_copy2 hlen hL hA hd0e hn ha'⟩
    · exact counted_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP ha' hd
    · exact bump_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP ha' hd
  · intro a ha0 ha
    have ha' : a < (n - 1) * L := by omega
    refine ⟨?_, par1_copy2 hlen hL hA hd0e hn hd0 hd1 hgx ha0 ha',
      upg_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r ha0 ha'⟩
    intro h1
    rw [show r + L + a = (r + a) + L by omega,
      e1_shift2 hlen hL hA hd0e hn hd0 hd1 hgx (by omega) (by omega)] at h1
    by_cases hg : TRIO.le1 (TRIO.gexp M r L d0 d1 (n - 1)) r (r + a)
    · have := guard_e1P hlen hL hA hd0e hn hd0 hd1 hgx ha0 ha' hg; omega
    · rw [if_neg hg] at h1; simpa using h1
  · refine ⟨(entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn).1.trans he2r,
      fun m hm => par_lt _ 1 _ _ hm, fun k hk => upg_rootN hlen hL hA hd0e hn hd0 hd1 hgx he2r hk⟩

/-- **Every `M[n]` (`n ≥ 1`) has a ranking** (`t = 2`), by induction on `n` from `M[1] = M.take x`. -/
theorem rk_gexp_t2_all (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hUN : ∀ n, 2 ≤ n → UAT (TRIO.gexp M r L d0 d1 n))
    (hBE : ∀ n, 1 ≤ n → BumpE2 (TRIO.gexp M r L d0 d1 n))
    (htgt : ∀ n, 2 ≤ n → T2Tgt M r L q p2 (TRIO.gexp M r L d0 d1 n))
    {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) :
    ∀ n, 1 ≤ n → ∃ rk, Rk (TRIO.gexp M r L d0 d1 n) rk := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      refine ⟨rkM, ?_⟩
      rw [gexp_one_gen hlen]
      have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUM
      rw [show M.length - 1 = r + L by omega] at hcnt
      exact rk_take (by omega) hRM hcnt
    · obtain ⟨rkP, hRP⟩ := ih hm0
      have := rk_gexp_t2 hlen hL hA hq hd0e hd0 hd1 hgx he2r h1x hqb hp2 hF2 hUM (n := m + 1) (by omega)
        (hUN _ (by omega)) (by simpa using hBE m hm0) (htgt _ (by omega)) hRM (by simpa using hRP)
      exact this

end

end Ytosk
