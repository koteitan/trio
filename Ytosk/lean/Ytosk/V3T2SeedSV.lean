/-
**3 行・t = 2・sv（q = r で x − 1 が x へ上げる）: M[n] と M.take x の値の一致。**

M.take x = M[n].take x で、x より前の列の右辺が M[n] と M.take x で違うのは r の o だけ（r の子 x′ が増える）。
そこで P = M.take x の順位で o(r) より下の呼び出しは、M[n] と M.take x で同じ値（`sv_agree`、agree_off_at）。
仮定: M.take x で r の最後の子はのりしろでない（topped (M.take x) r = false、5 集合で例外 0）。
-/
import Ytosk.V3T2SeedQNV
import Ytosk.V3T2V
import Ytosk.V3ExpT2SB

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- `oRhs` of a prefix: the children are below the cut and keep their counted status. -/
theorem oRhs_takeX {N : Mat} {x i : Nat} {σ : Valn} (hall : ∀ c ∈ children N i, c < x)
    (hcnt : ∀ c ∈ children N i, (Counted (N.take x) i c ↔ Counted N i c)) :
    oRhs (N.take x) σ i = oRhs N σ i := by
  unfold oRhs
  have hch : children (N.take x) i = children N i := by
    rw [children_take, List.filter_eq_self]; intro c hc; simpa using hall c hc
  rw [hch, List.map_congr_left (fun c hc => cnt_take_eq (hcnt c hc))]

/-- `vRhs` of a prefix: same upgrade, and (row 2 nonzero) the children and bump grandchildren below the cut. -/
theorem vRhs_takeX {N : Mat} {x i : Nat} {σ : Valn} (hi : i < x) (hupg : upg (N.take x) i = upg N i)
    (hb : entry N 2 i ≠ 0 → (∀ c ∈ children N i, c < x) ∧
      ∀ j ∈ children N i, col N j = bump N i → ∀ c ∈ children N j, c < x) :
    vRhs (N.take x) σ i = vRhs N σ i := by
  unfold vRhs
  rw [entry_take N 1 hi, entry_take N 2 hi, par_take N 1 i hi, hupg]
  by_cases h2 : entry N 2 i = 0
  · simp only [h2, if_true]
  · obtain ⟨hall, hj⟩ := hb h2
    have hch : children (N.take x) i = children N i := by
      rw [children_take, List.filter_eq_self]; intro c hc; simpa using hall c hc
    rw [hch]
    have hbt : ∀ j ∈ children N i, bumpTerm (N.take x) σ i j = bumpTerm N σ i j := by
      intro j hj'
      have hjx := hall j hj'
      unfold bumpTerm
      rw [col_take N hjx, bump_take N hi]
      by_cases hjb : col N j = bump N i
      · rw [if_pos hjb, if_pos hjb]
        have hchj : children (N.take x) j = children N j := by
          rw [children_take, List.filter_eq_self]; intro c hc; simpa using hj j hj' hjb c hc
        rw [hchj]
      · rw [if_neg hjb, if_neg hjb]
    rw [List.map_congr_left hbt]

/-- **sv: the counted children before `x`** are the same in `M[n]`, `M` and `M.take x`. -/
theorem sv_cnt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false) {n : Nat} (hn : 2 ≤ n) :
    (∀ i c, i < r + L → c < r + L → (Counted (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) i c ↔ Counted M i c)) ∧
    (∀ i c, i < r + L → c < r + L → (Counted (M.take (r + L)) i c ↔ Counted M i c)) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  obtain ⟨he2r, _⟩ := par2_facts hX.z2 (by omega) hr
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hxr := col_x_ne_bump_r hq hux
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : expand M n = N := by
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT N := by rw [← hexp]; exact (sInvX_expand hX n).toSInv.uat
  have hcolN : ∀ d, d < r + L → col N d = col M d := fun d hd => col_gexp_pre hlen (by omega) hd
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have htMr : topped M r = false := by
    unfold topped; rw [children_split_x hlen hxrc]; simp [hxr]
  have hIUt : ∀ c, c < r + L → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    have hcr : c ≠ r := by rintro rfl; rw [htMr] at htM; cases htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (children_N2 hlen hL0 hq hd0e (by omega) hn hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      exact hcr (hxc c d hd (by omega)).2)) (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → (Counted N i c ↔ Counted M i c) := by
    intro i c hi hc
    unfold Counted
    rw [hcolN c hc, hbN i hi, topped_NV hlen hL0 hq hd0e hn hxr he2r hc]
    by_cases ht : topped M c = true
    · rw [hIUt c hc ht]
    · simp [ht]
  have hcntP : ∀ i c, i < r + L → c < r + L → (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hc
    unfold Counted
    have hu' : upg M (r + L - 1) ≠ some c := by
      rw [hux]; intro h; cases h; omega
    rw [col_take M hc, bump_take M hi, isUpg_take_eq hlen hu' hc]
    by_cases hcr : c = r
    · subst hcr; rw [htP, htMr]
    · rw [topped_take_eq hlen hc (fun h => hcr (hxc c (r + L) h (le_refl _)).2)]
  exact ⟨hcntN, hcntP⟩

/-- **sv: `M[n]` and `M.take x` agree below `o(r)`** (in the ranking of `M.take x`). -/
theorem sv_agree {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ τ : Valn} {rk0 : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hC0 : Cons (M.take (r + L)) τ) (hR0 : Rk (M.take (r + L)) rk0) :
    ∀ i, i < r + L → (rk0 true i < rk0 true r → τ.o i = σ.o i) ∧ (rk0 false i < rk0 true r → τ.v i = σ.v i) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  obtain ⟨he2r, _⟩ := par2_facts hX.z2 (by omega) hr
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hxr := col_x_ne_bump_r hq hux
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : expand M n = N := by
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT N := by rw [← hexp]; exact (sInvX_expand hX n).toSInv.uat
  have hcolN : ∀ d, d < r + L → col N d = col M d := fun d hd => col_gexp_pre hlen (by omega) hd
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have htMr : topped M r = false := by
    unfold topped; rw [children_split_x hlen hxrc]; simp [hxr]
  have hIUt : ∀ c, c < r + L → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    have hcr : c ≠ r := by rintro rfl; rw [htMr] at htM; cases htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (children_N2 hlen hL0 hq hd0e (by omega) hn hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      exact hcr (hxc c d hd (by omega)).2)) (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → (Counted N i c ↔ Counted M i c) := by
    intro i c hi hc
    unfold Counted
    rw [hcolN c hc, hbN i hi, topped_NV hlen hL0 hq hd0e hn hxr he2r hc]
    by_cases ht : topped M c = true
    · rw [hIUt c hc ht]
    · simp [ht]
  have hcntP : ∀ i c, i < r + L → c < r + L → (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hc
    unfold Counted
    have hu' : upg M (r + L - 1) ≠ some c := by
      rw [hux]; intro h; cases h; omega
    rw [col_take M hc, bump_take M hi, isUpg_take_eq hlen hu' hc]
    by_cases hcr : c = r
    · subst hcr; rw [htP, htMr]
    · rw [topped_take_eq hlen hc (fun h => hcr (hxc c (r + L) h (le_refl _)).2)]
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hag := agree_off_at (M := N) (M' := M.take (r + L)) (fun b i => rk0 true r ≤ rk0 b i) hCN hC0 hR0
    (by rw [hlT, hlN]; omega)
    (by
      intro i hi hE
      rw [hlT] at hi
      have hir : i ≠ r := by intro e; rw [e] at hE; exact hE (le_refl _)
      rw [← hT]
      apply oRhs_takeX
      · intro c hc
        rw [children_N2 hlen hL0 hq hd0e (by omega) hn hi] at hc
        by_contra h'
        exact hir (hxc i c hc (by omega)).2
      · intro c hc
        rw [children_N2 hlen hL0 hq hd0e (by omega) hn hi] at hc
        have hcx : c < r + L := by
          by_contra h'
          exact hir (hxc i c hc (by omega)).2
        rw [hT]
        exact (hcntP i c hi hcx).trans (hcntN i c hi hcx).symm)
    (by
      intro i hi _
      rw [hlT] at hi
      rw [← hT]
      apply vRhs_takeX hi
      · by_cases hi1 : i + 1 < r + L
        · exact upg_take N hi1
        · have hix : i = r + L - 1 := by omega
          rw [hix, upg_take_last N (by omega) (by omega)]
          exact (upgN_xm1_none hlen hL0 hq hd0e hn hux he2r).symm
      · intro h2
        have hir : i ≠ r := by
          intro e; rw [e] at h2; rw [entry_gexp_pre hlen (by omega) 2 hrx] at h2; exact h2 he2r
        rw [children_N2 hlen hL0 hq hd0e (by omega) hn hi]
        refine ⟨fun c hc => ?_, fun j hj hjb c hc => ?_⟩
        · by_contra h'
          exact hir (hxc i c hc (by omega)).2
        · have hjx : j < r + L := by
            by_contra h'
            exact hir (hxc i j hj (by omega)).2
          have hjr : j ≠ r := by
            intro e
            rw [e] at hjb hj
            rw [hcolN r hrx, hbN i hi] at hjb
            exact hrb i (mem_children_iff.mp hj).2 hjb
          rw [children_N2 hlen hL0 hq hd0e (by omega) hn hjx] at hc
          by_contra h'
          exact hjr (hxc j c hc (by omega)).2)
    (by
      intro i hi hE
      refine ⟨fun h => hE (le_trans h (le_of_lt (hR0 i hi).1)), fun c hc hcnt h => ?_⟩
      exact hE (le_trans h (le_of_lt ((hR0 i hi).2.1 c hc hcnt.1 hcnt.2))))
    (by
      intro i hi hE h1
      obtain ⟨hp1, hup, hbk⟩ := (hR0 i hi).2.2 h1
      exact ⟨fun m hm h => hE (le_trans h (le_of_lt (hp1 m hm))),
        fun h2 k hk h => hE (le_trans h (le_of_lt (hup h2 k hk))),
        fun h2 j hj hjb k hk h => hE (le_trans h (le_of_lt (hbk h2 j hj hjb k hk)))⟩)
  intro i hi
  have hi' : i < (M.take (r + L)).length := by rw [hlT]; exact hi
  exact ⟨fun h => (hag i hi').1 (by omega), fun h => (hag i hi').2 (by omega)⟩

/-- **The value of the seed `r` in `M[n]`** (sv, `n ≥ 2`): the counted children of `r` are those of `M.take x`
with the values of `M.take x`, then the copy root `x′` with `v = V + 1`. -/
theorem o_r_level_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0)
    (hdecN : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a)) :
    σ.o r = psi (τ0.v r) (step (τ0.v r) (spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)))
      (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L
        (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) r).map ρP.o)))) z) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨hcntN, hcntP⟩ := sv_cnt hM hS I hz h2 hlen hr hq hux htP hn
  have hag := sv_agree hM hS I hz h2 hlen hr hq hux htP hn hCN hC0 hR0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hrM : r < M.length := by omega
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  -- the counted children of `r` in `N`
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + L] := by
    unfold CL
    rw [children_N2 hlen hL0 hq hd0e (by omega) hn hrx, children_take]
    conv_lhs => rw [children_split_x hlen hxrc, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + L] = [r + L] by simp [hxcN]]
    congr 1
    apply List.filter_congr
    intro c hc
    have hcx : c < r + L := by simpa using (List.mem_filter.mp hc).2
    simp only [decide_eq_decide]
    exact (hcntN r c hrx hcx).trans (hcntP r c hrx hcx).symm
  -- the values of the earlier children are those of `M.take x`
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    exact ((hag d (by have := (mem_children hdc).2; omega)).1
      ((hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2)).symm
  have hvr : σ.v r = τ0.v r := ((hag r hrx).2 (hR0 r hrT).1).symm
  -- the copy root `x′`
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  have hshOT : isOT (psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
      rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
    have := isOT_shTop (V' := succ (ρ.v r)) (hGP.ot_v r hrP) (by rw [← hvx]; exact hV') (by rw [← hvx]; exact hVV)
      hPo (le_refl _)
    rwa [shf_self] at this
  have hsN : ∀ c ∈ CL N r, Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [hval c hc]
      exact single_o hC0 hG0 (mem_children (cl_mem_children hc)).2
    · simp at hc; rw [hc, hox]; exact ⟨hshOT, _, _, rfl⟩
  have hform := o_last_form hCN hrN (by rw [hvr]; exact hG0.ot_v r hrT) hCLN hsN hdecN hox
  rw [hform, hvr, List.map_congr_left hval]

/-- The iterate `σ^k(X)` of `σ = σ_{V, V′}`. -/
def shIt (V V' X : T) : Nat → T
  | 0 => X
  | k + 1 => sh V V' (shIt V V' X k)

/-- `r`'s argument in `M.take x`. -/
def t2X1 (M : Mat) (r L : Nat) (τ : Valn) : T :=
  spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o))

/-- **The residual of the seed `r` in the sv case** (`q = r`, `x − 1` upgrades to `x`): properties of `M` and
`M.take x`. With `X₁` the argument of `r` in `M.take x` and `V′ = V + 1`: every level rewrites to `σ(X)`
(`step V X₁ V′ (σ X) = σ X`), and `ψ_V(σ^k X₁) ◁ o_M(r)` for `k ≥ 1`. -/
structure T2SeedSVRes (M : Mat) (ρ : Valn) (r L : Nat) : Prop where
  topP : topped (M.take (r + L)) r = false
  vP : ∀ τ, Cons (M.take (r + L)) τ → τ.v r = ρ.v r
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (succ (ρ.v r))
      (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)) z =
    sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)
  lhd : ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
    Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)

/-- **The value of the seed `r` in every `M[n]`** (sv, `n ≥ 2`): `ψ_V(σ^{n−1} X₁)`. -/
theorem seed_r_value_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        σ.o r = psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) (n - 1)) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hrx : r < r + L := par_lt M 0 _ _ hq
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
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hv0 := hRes.vP τ0 hC0
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ihs =>
  intro hGlow σ hCN hdecN
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have h := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  have key : ∀ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP → Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP → ρP.v r = (ρ.v r) →
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) =
        shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) (n - 2) →
      σ.o r = psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) (n - 1)) z := by
    intro ρP rkP hCP hGP hRP hvP hXP
    have h := o_r_level_sv hM hS I R hz h2 hlen hr hq hux hRes.topP hn hCN hRN hCP hGP hRP hC0 hG0 hR0 hdecN
    have hX1 : t2X1 M r L τ0 = spArg (ρ.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) := by
      unfold t2X1; rw [hv0]
    rw [h, hXP, hvP, hv0, show n - 1 = (n - 2) + 1 by omega, ← hX1, hRes.rw τ0 hC0 (n - 2)]
    rfl
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hG0
    have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hR0
    exact key τ0 rk0 hCP hGP hRP hv0 (by rw [show 2 - 1 = 1 from rfl, hP1]; rfl)
  · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hP := ihs (n - 1) (by omega) (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
    have hform := o_cl_eq hCP hGP hrP
    rw [hP] at hform
    simp only [psi.injEq] at hform
    refine key _ rkP hCP hGP hRP hform.1.symm ?_
    rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]

/-- **SeedL in the sv case**: `o_N(r) ◁ o_M(r)` for every `M[n]` (`n ≥ 2`). -/
theorem seedL_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        Lhd z (σ.o r) (ρ.o r) := by
  intro n hn hGlow σ hCN hdecN
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  rw [seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hRk1 n hn hGlow σ hCN hdecN]
  exact hRes.lhd _ hC0 (n - 1) (by omega)

end Ytosk
