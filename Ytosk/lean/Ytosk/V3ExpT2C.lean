/-
**3 行・t = 2: 写しの列の構造（N = M[n] と P = M[n − 1] の対応、行 1 はガードつき）。**

N = gexp M r L d0 d1 n、P = gexp M r L d0 d1 (n − 1)、x = r + L。
- 行 0 は d1 によらない（`e0_gexp_d1`）。だから行 0 の親・子・祖先の列は t = 1（d1 = 0）の補題がそのまま使える
  （`ancL_copy2`: N の x + j の祖先の列は P の r + j の祖先の列の r より後ろを L ずらし、x の祖先を続けたもの）。
- 行 1 は le1 P r のガードつきで d1 ずれる（`e1_shift2`）。ガードの窓（`le1_window`）で比較が戻る。
-/
import Ytosk.V3ExpT2R
import Ytosk.V3InvPer4

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-! ## 行 0 は d1 によらない -/

theorem e0_gexp_d1 {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (i : Nat) :
    entry (TRIO.gexp M r L d0 d1 n) 0 i = entry (TRIO.gexp M r L d0 0 n) 0 i := by
  rcases Nat.lt_or_ge i r with h | h
  · unfold entry; rw [TRIO.gexp_getD_low hlen h, TRIO.gexp_getD_low hlen h]
  · rcases Nat.lt_or_ge i (r + n * L) with h' | h'
    · rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL; simp at h'; omega
      obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL h h'
      rw [entry0_gexp_mir hlen hk hq, entry0_gexp_mir hlen hk hq]
    · rw [entry_out (by rw [TRIO.gexp_length hlen]; omega), entry_out (by rw [TRIO.gexp_length hlen]; omega)]

theorem par0_gexp_d1 {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (b : Nat) :
    par (TRIO.gexp M r L d0 d1 n) 0 b = par (TRIO.gexp M r L d0 0 n) 0 b :=
  par0_congr_e0 (fun q _ => e0_gexp_d1 hlen q)

theorem ancL_gexp_d1 {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (b : Nat) :
    ancL (TRIO.gexp M r L d0 d1 n) b = ancL (TRIO.gexp M r L d0 0 n) b :=
  ancL_congr_e0 (fun q _ => e0_gexp_d1 hlen q)

theorem children_gexp_d1 {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (b : Nat) :
    children (TRIO.gexp M r L d0 d1 n) b = children (TRIO.gexp M r L d0 0 n) b := by
  unfold children
  rw [TRIO.gexp_length hlen, TRIO.gexp_length hlen]
  apply List.filter_congr
  intro i _
  rw [par0_gexp_d1 hlen]

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The ancestor list of a copy column** (`t = 2`): as in `t = 1` (row 0 does not see `d1`). -/
theorem ancL_copy2 : ∀ j, 0 < j → j < (n - 1) * L →
    ∃ S : List Nat, ancL (TRIO.gexp M r L d0 d1 (n - 1)) (r + j) = S ++ r :: ancL M r ∧
      ancL (TRIO.gexp M r L d0 d1 n) (r + L + j) = S.map (· + L) ++ (r + L) :: ancL M (r + L) ∧
      ∀ s ∈ S, r < s ∧ s < r + j := by
  intro j hj0 hj
  obtain ⟨S, h1, h2, h3⟩ := ancL_copy hlen hL hA hd0e hn j hj0 hj
  exact ⟨S, by rw [ancL_gexp_d1 hlen]; exact h1, by rw [ancL_gexp_d1 hlen]; exact h2, h3⟩

/-- **Children shift by one copy** (`t = 2`). -/
theorem children_shift2 {p : Nat} (hp : p < (n - 1) * L) :
    children (TRIO.gexp M r L d0 d1 n) (r + L + p) =
      (children (TRIO.gexp M r L d0 d1 (n - 1)) (r + p)).map (· + L) := by
  rw [children_gexp_d1 (n := n) (d1 := d1) hlen, children_gexp_d1 (n := n - 1) (d1 := d1) hlen]
  exact children_shift hlen hL hA hd0e hn hp

end

/-! ## 祖先の列は位置の降順。find? は条件を満たす最も近い祖先 -/

theorem ancL_pairwise (M : Mat) : ∀ b, (ancL M b).Pairwise (fun a c => c < a) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    cases hp : par M 0 b with
    | none => rw [ancL_none hp]; exact List.Pairwise.nil
    | some q =>
      rw [ancL_eq hp]
      exact List.Pairwise.cons (fun c hc => mem_ancL_lt hc) (ih q (par_lt M 0 b q hp))

theorem find?_dec {l : List Nat} (hl : l.Pairwise (fun a c => c < a)) {p : Nat → Bool} {a : Nat} :
    l.find? p = some a ↔ a ∈ l ∧ p a = true ∧ ∀ y ∈ l, a < y → p y = false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.find?_cons]
    by_cases hb : p b = true
    · rw [hb]
      constructor
      · intro h; cases h
        refine ⟨List.mem_cons_self, hb, fun y hy hby => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have := hl.1 y hy; omega
      · rintro ⟨ha, hpa, hmax⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · have := hl.1 a ha
          have := hmax b List.mem_cons_self (by omega)
          rw [hb] at this; cases this
    · simp only [Bool.not_eq_true] at hb
      rw [hb, ih hl.2]
      constructor
      · rintro ⟨ha, hpa, hmax⟩
        refine ⟨List.mem_cons_of_mem _ ha, hpa, fun y hy hay => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hb
        · exact hmax y hy hay
      · rintro ⟨ha, hpa, hmax⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · rw [hb] at hpa; cases hpa
        · exact ⟨ha, hpa, fun y hy hay => hmax y (List.mem_cons_of_mem _ hy) hay⟩

theorem find?_none_dec {l : List Nat} {p : Nat → Bool} :
    l.find? p = none ↔ ∀ y ∈ l, p y = false := by
  rw [List.find?_eq_none]; simp

/-- **`P_1` is the nearest ancestor with a smaller row 1.** -/
theorem par1_some_iff (M : Mat) (b a : Nat) :
    par M 1 b = some a ↔ a ∈ ancL M b ∧ entry M 1 a < entry M 1 b ∧
      ∀ y ∈ ancL M b, a < y → entry M 1 b ≤ entry M 1 y := by
  rw [par1_find, find?_dec (ancL_pairwise M b)]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt]

theorem par1_none_iff (M : Mat) (b : Nat) :
    par M 1 b = none ↔ ∀ y ∈ ancL M b, entry M 1 b ≤ entry M 1 y := by
  rw [par1_find, find?_none_dec]
  simp only [decide_eq_false_iff_not, Nat.not_lt]

/-! ## 行 1 のガードつきのずれ（t = 2） -/

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L))
include hlen hL hA hd0e hn hd0 hd1 hgx

theorem hup_of : ∀ l, r < l → l ≤ r + L → TRIO.entry M 0 r < TRIO.entry M 0 l := fun l h1 h2 =>
  anc0_e0_lt (anc_between hA l (by omega) h2) (by omega)

/-- **The guard of a copy column** is that of the bad part. -/
theorem guard_gexp {m k q : Nat} (hk : k < m) (hq : q < L) :
    TRIO.le1 (TRIO.gexp M r L d0 d1 m) r (r + (k * L + q)) ↔ TRIO.le1 M r (r + q) :=
  TRIO.gexp_guard_transport hlen hk hq (hup_of hlen hL hA hd0e hn hd0 hd1 hgx) hd0 hd0e hd1 hgx

/-- **Row 1 of `N` one copy later**: `+ d1` exactly on the guarded columns. -/
theorem e1_shift2 {s : Nat} (hrs : r ≤ s) (hs : s < r + (n - 1) * L) :
    entry (TRIO.gexp M r L d0 d1 n) 1 (s + L) =
      entry (TRIO.gexp M r L d0 d1 (n - 1)) 1 s +
        (if TRIO.le1 (TRIO.gexp M r L d0 d1 (n - 1)) r s then d1 else 0) := by
  obtain ⟨k, q, hk, hq, hkq⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n - 1) (p := s) hL hrs hs
  have hs' : s + L = r + ((k + 1) * L + q) := by rw [hkq, Nat.succ_mul]; omega
  rw [hs', hkq, e1N_blk hlen (show k + 1 < n by omega) hq, e1N_blk hlen hk hq,
    guard_gexp hlen hL hA hd0e hn hd0 hd1 hgx hk hq]
  split_ifs
  · rw [Nat.succ_mul]; omega
  · omega


/-- **`P_1` of a copy column** (`t = 2`): that of `P`, shifted when at or after `r`. -/
theorem par1_copy2 {j : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) :
    par (TRIO.gexp M r L d0 d1 n) 1 (r + L + j) =
      (par (TRIO.gexp M r L d0 d1 (n - 1)) 1 (r + j)).map (fun t => if r ≤ t then t + L else t) := by
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  obtain ⟨S, hSP, hSN, hS⟩ := ancL_copy2 (d1 := d1) hlen hL hA hd0e hn j hj0 hj
  obtain ⟨S0, hS0, hS0p⟩ := ancL_through hA (by omega)
  -- entries
  have hm1 : 1 ≤ n - 1 := by omega
  have ePlow : ∀ y, y < r + L → entry P 1 y = entry M 1 y := fun y hy =>
    entry_gexp_pre hlen hm1 1 hy
  have eNlow : ∀ y, y < r + L → entry N 1 y = entry M 1 y := fun y hy =>
    entry_gexp_pre hlen (by omega) 1 hy
  have eS : ∀ s, r ≤ s → s < r + (n - 1) * L →
      entry N 1 (s + L) = entry P 1 s + (if TRIO.le1 P r s then d1 else 0) :=
    fun s h1 h2 => e1_shift2 hlen hL hA hd0e hn hd0 hd1 hgx h1 h2
  set r1 := entry M 1 r with hr1
  have hPr : entry P 1 r = r1 := ePlow r (by omega)
  have hrP : r < P.length := by have : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL; omega
  have hgr : TRIO.le1 P r r := le1_self hrP
  have hNx : entry N 1 (r + L) = r1 + d1 := by
    have := eS r (le_refl _) (by omega); rw [if_pos hgr, hPr] at this; exact this
  set c := r + j with hc
  set eP := entry P 1 c with heP
  have hcP : c < P.length := by omega
  -- ancestors of `c` in `P`
  have hmemP : ∀ y, y ∈ ancL P c ↔ y ∈ S ∨ y = r ∨ y ∈ ancL M r := by
    intro y; rw [hSP]; simp [List.mem_append, List.mem_cons]
  have hrA : Anc0 P r c := anc0_of_mem_ancL ((hmemP r).mpr (Or.inr (Or.inl rfl)))
  have hrs : ∀ s ∈ S, Anc0 P r s ∧ Anc0 P s c := by
    intro s hs
    have hsc : Anc0 P s c := anc0_of_mem_ancL ((hmemP s).mpr (Or.inl hs))
    refine ⟨?_, hsc⟩
    rcases anc0_total hrA hsc with h | h
    · exact h
    · have := h.le; have := (hS s hs).1; omega
  have hwin : ∀ s, Anc0 P r s → s < P.length →
      (TRIO.le1 P r s ↔ ∀ y, Anc0 P r y → Anc0 P y s → y ≠ r → r1 < entry P 1 y) := by
    intro s hrs' hs'
    rw [le1_window hs' hrs', hPr]
  set gj := TRIO.le1 P r c with hgj
  have eNc : entry N 1 (r + L + j) = eP + (if gj then d1 else 0) := by
    rw [show r + L + j = c + L by omega]; exact eS c (by omega) (by omega)
  -- the path of `x` in `M` is above row 1 of `r`
  have hS0e : ∀ y ∈ S0, r1 < entry N 1 y := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := hS0p y hy
    rw [eNlow y (by omega)]
    exact (le1_window (by omega) hA).mp hgx y h3 h4 (by omega)
  -- a guarded column of `S` is above row 1 of `r`
  have hgup : ∀ s ∈ S, TRIO.le1 P r s → r1 < entry P 1 s := by
    intro s hs hg
    have := (hS s hs).1
    exact (hwin s (hrs s hs).1 (by have := (hS s hs).2; omega)).mp hg s (hrs s hs).1 (Anc0.refl _) (by omega)
  -- `c` guarded: everything on the path is guarded, and `c` is above row 1 of `r`
  have hgpath : gj → ∀ s ∈ S, TRIO.le1 P r s := by
    intro hg s hs
    rw [hwin s (hrs s hs).1 (by have := (hS s hs).2; omega)]
    intro y h1 h2 h3
    exact (hwin c hrA hcP).mp hg y h1 (Anc0.trans h2 (hrs s hs).2) h3
  have hgc : gj → r1 < eP := fun hg =>
    (hwin c hrA hcP).mp hg c hrA (Anc0.refl _) (by omega)
  -- `c` unguarded: a low column on the path
  have hlow : ¬ gj → ∃ z, Anc0 P r z ∧ Anc0 P z c ∧ z ≠ r ∧ entry P 1 z ≤ r1 := by
    intro hg
    rw [hgj, hwin c hrA hcP] at hg
    push_neg at hg
    exact hg
  -- the membership in `N`
  have hmemN : ∀ y, y ∈ ancL N (r + L + j) ↔
      (∃ s ∈ S, y = s + L) ∨ y = r + L ∨ y ∈ S0 ∨ y = r ∨ y ∈ ancL M r := by
    intro y; rw [hSN, hS0]; simp [List.mem_append, List.mem_cons, List.mem_map, eq_comm]
  cases hpa : par P 1 c with
  | none =>
    rw [par1_none_iff] at hpa
    have hngj : ¬ gj := fun hg => by
      have := hpa r ((hmemP r).mpr (Or.inr (Or.inl rfl))); rw [hPr] at this
      have := hgc hg; omega
    have heNc : entry N 1 (r + L + j) = eP := by rw [eNc, if_neg hngj]; omega
    have hePr : eP ≤ r1 := by have := hpa r ((hmemP r).mpr (Or.inr (Or.inl rfl))); rw [hPr] at this; exact this
    simp only [Option.map_none]
    rw [par1_none_iff, heNc]
    intro y hy
    rcases (hmemN y).mp hy with ⟨s, hs, rfl⟩ | rfl | hy | hyr | hy
    · have h1 := hpa s ((hmemP s).mpr (Or.inl hs))
      rw [eS s (by have := (hS s hs).1; omega) (by have := (hS s hs).2; omega)]; split_ifs <;> omega
    · rw [hNx]; omega
    · have := hS0e y hy; omega
    · subst y; rw [eNlow r (by omega)]; exact hePr
    · have hyr := mem_ancL_lt hy
      have := hpa y ((hmemP y).mpr (Or.inr (Or.inr hy)))
      rw [eNlow y (by omega)]; rw [ePlow y (by omega)] at this; exact this
  | some a =>
    obtain ⟨haP, hlt, hmax⟩ := (par1_some_iff P c a).mp hpa
    simp only [Option.map_some]
    rcases (hmemP a).mp haP with haS | har0 | haM
    · -- `a` in the copies
      have har := (hS a haS).1
      rw [if_pos (by omega)]
      have hga : TRIO.le1 P r a ↔ gj := by
        constructor
        · intro hg
          by_contra hng
          obtain ⟨z, hz1, hz2, hz3, hz4⟩ := hlow hng
          rcases anc0_total hz2 (hrs a haS).2 with hza | haz
          · have := (hwin a (hrs a haS).1 (by have := (hS a haS).2; omega)).mp hg z hz1 hza hz3; omega
          · have hzc : eP ≤ entry P 1 z := by
              by_cases hzc : z = c
              · rw [hzc]
              · have hzm : z ∈ ancL P c := mem_ancL_of_anc hz2 hzc
                by_cases hza : z = a
                · subst hza; have := hgup z haS hg; omega
                · exact hmax z hzm (by have := haz.le; omega)
            have := hgup a haS hg; omega
        · intro hg; exact hgpath hg a haS
      rw [par1_some_iff, eNc]
      refine ⟨(hmemN (a + L)).mpr (Or.inl ⟨a, haS, rfl⟩), ?_, ?_⟩
      · rw [eS a (by omega) (by have := (hS a haS).2; omega)]
        by_cases hg : gj
        · rw [if_pos (hga.mpr hg), if_pos hg]; omega
        · rw [if_neg (fun h => hg (hga.mp h)), if_neg hg]; omega
      · intro y hy hay
        rcases (hmemN y).mp hy with ⟨s, hs, rfl⟩ | rfl | hy | hyr | hy
        · have h1 := hmax s ((hmemP s).mpr (Or.inl hs)) (by omega)
          rw [eS s (by have := (hS s hs).1; omega) (by have := (hS s hs).2; omega)]
          by_cases hg : gj
          · rw [if_pos hg, if_pos (hgpath hg s hs)]; omega
          · rw [if_neg hg]; split_ifs <;> omega
        · omega
        · have := (hS0p y hy).2.1; omega
        · subst y; omega
        · have := mem_ancL_lt hy; omega
    · -- `a = r`
      subst a
      rw [if_pos (le_refl _)]
      have hg : gj := by
        by_contra hng
        obtain ⟨z, hz1, hz2, hz3, hz4⟩ := hlow hng
        have hzc : eP ≤ entry P 1 z := by
          by_cases hzc : z = c
          · rw [hzc]
          · exact hmax z (mem_ancL_of_anc hz2 hzc) (by have := hz1.le; omega)
        rw [hPr] at hlt; omega
      rw [par1_some_iff, eNc, if_pos hg]
      refine ⟨(hmemN (r + L)).mpr (Or.inr (Or.inl rfl)), by rw [hNx]; rw [hPr] at hlt; omega, ?_⟩
      intro y hy hay
      rcases (hmemN y).mp hy with ⟨s, hs, rfl⟩ | rfl | hy | hyr | hy
      · have h1 := hmax s ((hmemP s).mpr (Or.inl hs)) (by omega)
        rw [eS s (by have := (hS s hs).1; omega) (by have := (hS s hs).2; omega), if_pos (hgpath hg s hs)]
        omega
      · omega
      · have := (hS0p y hy).2.1; omega
      · subst y; omega
      · have := mem_ancL_lt hy; omega
    · -- `a` before `r`
      have har := mem_ancL_lt haM
      rw [if_neg (by omega)]
      have hePr : eP ≤ r1 := by
        have := hmax r ((hmemP r).mpr (Or.inr (Or.inl rfl))) har; rw [hPr] at this; exact this
      have hng : ¬ gj := fun hg => by have := hgc hg; omega
      have heNc : entry N 1 (r + L + j) = eP := by rw [eNc, if_neg hng]; omega
      rw [par1_some_iff, heNc]
      refine ⟨(hmemN a).mpr (Or.inr (Or.inr (Or.inr (Or.inr haM)))), ?_, ?_⟩
      · rw [eNlow a (by omega)]; rw [ePlow a (by omega)] at hlt; exact hlt
      · intro y hy hay
        rcases (hmemN y).mp hy with ⟨s, hs, rfl⟩ | rfl | hy | hyr | hy
        · have h1 := hmax s ((hmemP s).mpr (Or.inl hs)) (by have := (hS s hs).1; omega)
          rw [eS s (by have := (hS s hs).1; omega) (by have := (hS s hs).2; omega)]; split_ifs <;> omega
        · rw [hNx]; omega
        · have := hS0e y hy; omega
        · subst y; rw [eNlow r (by omega)]; exact hePr
        · have hyr := mem_ancL_lt hy
          have := hmax y ((hmemP y).mpr (Or.inr (Or.inr hy))) hay
          rw [eNlow y (by omega)]; rw [ePlow y (by omega)] at this; exact this

end

end Ytosk
