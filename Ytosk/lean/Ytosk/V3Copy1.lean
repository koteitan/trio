/-
**3 行・t = 1: 写しの列の祖先の列と P_1。**

N = gexp M r L d0 0 n（= M[n]）、P = gexp M r L d0 0 (n−1)（= M[n−1]）、x = r + L。
写しの列 x + j（0 < j）の行 0 の祖先の列は、P の r + j の祖先の列のうち r より後ろの部分を L ずらし、
x のあとに M の x の祖先の列（q, …, r, r の祖先）を続けたもの（`ancL_copy`）。
x と r の間の経路の列の行 1 が r の行 1 より大きければ、P_1 は P の P_1 を「r 以後なら L ずらす」ことで得られる
（`par1_copy`）。
-/
import Ytosk.V3Chain
import Ytosk.TwoRowC
import Ytosk.TwoRowZ

namespace Ytosk

/-! ## 行 0 の値だけで決まるもの -/

theorem climb_congr' {step : Nat → Option Nat} {ok ok' : Nat → Bool}
    (hs : ∀ q q', step q = some q' → q' < q) :
    ∀ f q, (∀ q', q' ≤ q → ok q' = ok' q') → climb step ok f (some q) = climb step ok' f (some q)
  | 0, _, _ => rfl
  | f + 1, q, h => by
    simp only [climb]
    rw [h q (Nat.le_refl _)]
    split
    · rfl
    · cases hq : step q with
      | none => cases f <;> rfl
      | some q' =>
        have := hs q q' hq
        exact climb_congr' hs f q' (fun q'' hq'' => h q'' (by omega))

theorem prev_lt : ∀ q q', prev q = some q' → q' < q
  | 0, _, h => by simp [prev] at h
  | q + 1, q', h => by simp [prev] at h; omega

/-- `P_0(b)` only reads row 0 of the columns up to `b`. -/
theorem par0_congr_e0 {M M' : Mat} {b : Nat} (h : ∀ q, q ≤ b → entry M 0 q = entry M' 0 q) :
    par M 0 b = par M' 0 b := by
  cases b with
  | zero => rfl
  | succ b =>
    show climb prev _ (b + 1 + 1) (prev (b + 1)) = climb prev _ (b + 1 + 1) (prev (b + 1))
    simp only [prev]
    apply climb_congr' prev_lt
    intro q' hq'
    rw [h q' (by omega), h (b + 1) (Nat.le_refl _)]

/-- The ancestor list only reads row 0 of the columns up to `b`. -/
theorem ancL_congr_e0 {M M' : Mat} : ∀ {b : Nat}, (∀ q, q ≤ b → entry M 0 q = entry M' 0 q) →
    ancL M b = ancL M' b := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro h
    have hp := par0_congr_e0 h
    cases hq : par M 0 b with
    | none => rw [ancL_none hq, ancL_none (by rw [← hp, hq])]
    | some q =>
      have hq' : par M' 0 b = some q := by rw [← hp, hq]
      have hqb := par_lt M 0 b q hq
      rw [ancL_eq hq, ancL_eq hq', ih q hqb (fun q' hq'' => h q' (by omega))]

theorem find?_congr' {l : List Nat} {p p' : Nat → Bool} (h : ∀ a ∈ l, p a = p' a) :
    l.find? p = l.find? p' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-! ## t = 1 の写し -/

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

omit hA hn in
/-- Row 0 of `gexp` up to `x = r + L` (`m ≥ 2`) or before it (`m ≥ 1`) is that of `M`. -/
theorem e0_gexp_pre {m q : Nat} (hm : 1 ≤ m) (hq : q < r + L) :
    entry (TRIO.gexp M r L d0 0 m) 0 q = entry M 0 q := by
  rcases Nat.lt_or_ge q r with h | h
  · unfold entry; rw [TRIO.gexp_getD_low hlen h]
  · have := entry0_gexp_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := m)
      (k := 0) (q := q - r) hlen (by omega) (by omega)
    rw [show r + (0 * L + (q - r)) = q by omega] at this
    rw [this, show r + (q - r) = q by omega]; simp

omit hA in
theorem e0_gexp_x :
    entry (TRIO.gexp M r L d0 0 n) 0 (r + L) = entry M 0 (r + L) := by
  have := entry0_gexp_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n)
    (k := 1) (q := 0) hlen (by omega) hL
  rw [show r + (1 * L + 0) = r + L by omega] at this
  rw [this, hd0e]; simp

theorem ancL_N_pre {q : Nat} (hq : q ≤ r + L) :
    ancL (TRIO.gexp M r L d0 0 n) q = ancL M q := by
  apply ancL_congr_e0
  intro q' hq'
  rcases Nat.lt_or_ge q' (r + L) with h | h
  · exact e0_gexp_pre hlen hL hd0e (by omega) h
  · rw [show q' = r + L by omega]; exact e0_gexp_x hlen hL hd0e hn

omit hA in
theorem ancL_P_pre {q : Nat} (hq : q < r + L) :
    ancL (TRIO.gexp M r L d0 0 (n - 1)) q = ancL M q := by
  apply ancL_congr_e0
  intro q' hq'
  exact e0_gexp_pre hlen hL hd0e (by omega) (by omega)

/-- In `P`, a copy column `r + j` (`0 < j`) has its row-0 parent at or after `r`. -/
theorem parP_ge {j : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) :
    ∃ p, par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) = some p ∧ r ≤ p := by
  have hlenN : (TRIO.gexp M r L d0 0 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  obtain ⟨p, hp, hpx⟩ := par0_gexp_ge (d1 := 0) (n := n) hlen hL hA hd0e
    (c := r + L + j) (by omega) (by omega)
  rw [par0_gexp_shift hlen hL hA hd0e hn hj0 hj] at hp
  cases hq : par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) with
  | none => rw [hq] at hp; cases hp
  | some p' => rw [hq] at hp; simp at hp; exact ⟨p', rfl, by omega⟩

/-- **The ancestor list of a copy column.** -/
theorem ancL_copy : ∀ j, 0 < j → j < (n - 1) * L →
    ∃ S : List Nat, ancL (TRIO.gexp M r L d0 0 (n - 1)) (r + j) = S ++ r :: ancL M r ∧
      ancL (TRIO.gexp M r L d0 0 n) (r + L + j) = S.map (· + L) ++ (r + L) :: ancL M (r + L) ∧
      ∀ s ∈ S, r < s ∧ s < r + j := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj0 hj
    obtain ⟨p, hp, hrp⟩ := parP_ge hlen hL hA hd0e hn hj0 hj
    have hpN : par (TRIO.gexp M r L d0 0 n) 0 (r + L + j) = some (p + L) := by
      rw [par0_gexp_shift hlen hL hA hd0e hn hj0 hj, hp]; rfl
    have hpj := par_lt _ 0 _ _ hp
    rcases Nat.eq_or_lt_of_le hrp with heq | hlt
    · subst heq
      refine ⟨[], ?_, ?_, by simp⟩
      · rw [ancL_eq hp, ancL_P_pre hlen hL hd0e hn (by omega)]; rfl
      · rw [ancL_eq hpN, ancL_N_pre hlen hL hA hd0e hn (by omega)]; rfl
    · obtain ⟨S, h1, h2, h3⟩ := ih (p - r) (by omega) (by omega) (by omega)
      rw [show r + (p - r) = p by omega] at h1
      rw [show r + L + (p - r) = p + L by omega] at h2
      refine ⟨p :: S, ?_, ?_, ?_⟩
      · rw [ancL_eq hp, h1]; rfl
      · rw [ancL_eq hpN, h2]; rfl
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨hlt, hpj⟩
        · have := h3 s hs; omega

omit hA hd0e in
theorem e1_gexp_shift {a : Nat} (ha : a < (n - 1) * L) :
    entry (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) := by
  obtain ⟨k, qb, hk, hqb, hak⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := a) hL
    (Nat.zero_le _) (by simpa using ha)
  simp only [Nat.zero_add] at hak
  subst hak
  rw [show r + L + (k * L + qb) = r + ((k + 1) * L + qb) by rw [Nat.succ_mul]; omega,
    entry1_gexp_d1z hlen (by omega) hqb, entry1_gexp_d1z hlen hk hqb]

omit hL hA hd0e hn in
theorem e1_gexp_pre {m q : Nat} (hm : 1 ≤ m) (hq : q < r + L) :
    entry (TRIO.gexp M r L d0 0 m) 1 q = entry M 1 q := by
  rcases Nat.lt_or_ge q r with h | h
  · unfold entry; rw [TRIO.gexp_getD_low hlen h]
  · have := entry1_gexp_d1z (M := M) (r := r) (L := L) (d0 := d0) (m := m) (k := 0) (q := q - r)
      hlen (by omega) (by omega)
    rw [show r + (0 * L + (q - r)) = q by omega, show r + (q - r) = q by omega] at this
    exact this

/-- **P_1 of a copy column**, when the path between `r` and `x` stays above row 1 of `r`. -/
theorem par1_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s)
    {j : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) :
    par (TRIO.gexp M r L d0 0 n) 1 (r + L + j) =
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j)).map (fun p => if r ≤ p then p + L else p) := by
  have hlenN : (TRIO.gexp M r L d0 0 n).length = r + n * L := TRIO.gexp_length hlen
  obtain ⟨S, hSP, hSN, hS⟩ := ancL_copy hlen hL hA hd0e hn j hj0 hj
  obtain ⟨S0, hS0, hS0p⟩ := ancL_through hA (by omega)
  rw [par1_find, par1_find, hSP, hSN, hS0, e1_gexp_shift hlen hL hn (by omega)]
  set e := entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j) with he
  -- row 1 along the lists
  have hSe : ∀ s ∈ S, entry (TRIO.gexp M r L d0 0 n) 1 (s + L) =
      entry (TRIO.gexp M r L d0 0 (n - 1)) 1 s := by
    intro s hs
    have := hS s hs
    rw [show s + L = r + L + (s - r) by omega, e1_gexp_shift hlen hL hn (by omega),
      show r + (s - r) = s by omega]
  have hrN : entry (TRIO.gexp M r L d0 0 n) 1 (r + L) = entry M 1 r := by
    have h0 : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
    have := e1_gexp_shift (M := M) (r := r) (L := L) (d0 := d0) (n := n) (a := 0) hlen hL hn h0
    rw [show r + L + 0 = r + L by omega, show r + 0 = r by omega] at this
    have hr' : entry (TRIO.gexp M r L d0 0 (n - 1)) 1 r = entry M 1 r :=
      e1_gexp_pre (m := n - 1) hlen (by omega) (by omega)
    rw [this, hr']
  have hrP : entry (TRIO.gexp M r L d0 0 (n - 1)) 1 r = entry M 1 r :=
    e1_gexp_pre (m := n - 1) hlen (by omega) (by omega)
  have hlow : ∀ q ∈ ancL M r, entry (TRIO.gexp M r L d0 0 n) 1 q = entry M 1 q ∧
      entry (TRIO.gexp M r L d0 0 (n - 1)) 1 q = entry M 1 q := by
    intro q hq
    have := mem_ancL_lt hq
    exact ⟨e1_gexp_pre (m := n) hlen (by omega) (by omega),
      e1_gexp_pre (m := n - 1) hlen (by omega) (by omega)⟩
  have hS0e : ∀ s ∈ S0, entry (TRIO.gexp M r L d0 0 n) 1 s = entry M 1 s := by
    intro s hs
    have := hS0p s hs
    exact e1_gexp_pre (m := n) hlen (by omega) (by omega)
  simp only [List.find?_append, List.find?_cons, List.find?_map]
  -- the part in the copies
  have hfS : S.find? ((fun q => decide (entry (TRIO.gexp M r L d0 0 n) 1 q < e)) ∘ (· + L)) =
      S.find? (fun q => decide (entry (TRIO.gexp M r L d0 0 (n - 1)) 1 q < e)) := by
    apply find?_congr'
    intro s hs
    simp only [Function.comp, hSe s hs]
  rw [hfS]
  cases hf : S.find? (fun q => decide (entry (TRIO.gexp M r L d0 0 (n - 1)) 1 q < e)) with
  | some s =>
    have hsS := List.mem_of_find?_eq_some hf
    have := hS s hsS
    simp only [Option.or_some, Option.map_some, Option.map_map]
    simp [show r ≤ s by omega]
  | none =>
    simp only [Option.or_none, Option.map_none, hrN, hrP]
    by_cases her : entry M 1 r < e
    · simp [her]
    · simp only [her, decide_false, Bool.false_eq_true, ↓reduceIte]
      -- the path part fails
      have hfS0 : S0.find? (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 1 q < e)) = none := by
        rw [List.find?_eq_none]
        intro s hs
        obtain ⟨h1, h2, h3, h4⟩ := hS0p s hs
        have := hpath s h3 h4 (by omega) (by omega)
        rw [hS0e s hs]; simp; omega
      rw [hfS0]
      have hNr : entry (TRIO.gexp M r L d0 0 n) 1 r = entry M 1 r :=
        e1_gexp_pre (m := n) hlen (by omega) (by omega)
      have hfl : (ancL M r).find? (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 1 q < e)) =
          (ancL M r).find? (fun q => decide (entry (TRIO.gexp M r L d0 0 (n - 1)) 1 q < e)) := by
        apply find?_congr'
        intro q hq
        rw [(hlow q hq).1, (hlow q hq).2]
      simp only [Option.or, hNr, her, decide_false, hfl]
      cases hf2 : (ancL M r).find? (fun q => decide (entry (TRIO.gexp M r L d0 0 (n - 1)) 1 q < e)) with
      | none => rfl
      | some q =>
        have := mem_ancL_lt (List.mem_of_find?_eq_some hf2)
        simp [show ¬ r ≤ q by omega]

end

end Ytosk
