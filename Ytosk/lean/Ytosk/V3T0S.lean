/-
**3 行・t = 0: 展開 N = M[n] = gexp M r L 0 0 n の形（構造）。**

t = 0（x の行 1 が 0）では行 0 のずれも 0 なので、N = M.take r ++ B ^ n（B = M[r, x)）。
- 列: N の r + kL + q は M の r + q（`col_copy0`）。x より前は M と同じ。
- 行 0 の親: コピーの中は同じコピーの中（`par0_copy0`）、コピーの根は M の r の親 g（`par0_root0`）。
- 祖先の列: N の r + kL + q の祖先の列は、M の r + q の祖先の列を「r 以後なら kL ずらす」もの（`ancL_copy0`）。
  したがって P_1 も同じずらし（`par1_copy0`）。
-/
import Ytosk.V3T0

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The shift of a column of `M` into the `k`-th copy. -/
def shk (r s : Nat) (p : Nat) : Nat := if r ≤ p then p + s else p

/-- The column of `M` that a column of `N` copies. -/
def phi0 (r L i : Nat) : Nat := if i < r then i else r + (i - r) % L

theorem phi0_lt {r L i : Nat} (h : i < r) : phi0 r L i = i := by unfold phi0; rw [if_pos h]

theorem phi0_copy {r L k q : Nat} (hq : q < L) : phi0 r L (r + (k * L + q)) = r + q := by
  unfold phi0; rw [if_neg (by omega), show r + (k * L + q) - r = q + k * L by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

theorem phi0_lt_x {r L t : Nat} (ht : t < r + L) : phi0 r L t = t := by
  by_cases h : t < r
  · exact phi0_lt h
  · have := phi0_copy (r := r) (L := L) (k := 0) (q := t - r) (by omega)
    rw [show r + (0 * L + (t - r)) = t by omega, show r + (t - r) = t by omega] at this; exact this

theorem shk_inj (r s : Nat) : ∀ a b, shk r s a = shk r s b → a = b := by
  intro a b h
  unfold shk at h
  split at h <;> split at h <;> omega

theorem decomp_unique {L k q k' q' : Nat} (hq : q < L) (hq' : q' < L) (h : k * L + q = k' * L + q') :
    k = k' ∧ q = q' := by
  have hL : 0 < L := by omega
  have h1 : (k * L + q) / L = k := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hq]; simp
  have h2 : (k' * L + q') / L = k' := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hq']; simp
  have hk : k = k' := by rw [← h1, ← h2, h]
  subst hk
  exact ⟨rfl, by omega⟩

theorem map_range_pred_last (f : Nat → Nat) {m : Nat} (hm : 1 ≤ m) :
    (List.range m).map f = (List.range (m - 1)).map f ++ [f (m - 1)] := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [List.range_succ]

/-- An ancestor-type upgrade lands on a column with row 0 below that of the next column. -/
theorem upg_climb_e0 {M : Mat} {i k : Nat} (h : upg M i = some k) (hne : k ≠ i + 1) :
    entry M 0 k < entry M 0 (i + 1) := by
  unfold upg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i m _
      simp only at h
      split at h
      · cases h; exact absurd rfl hne
      · rw [upgClimb_find] at h
        have := List.find?_some h
        simp only [decide_eq_true_eq] at this
        exact this.2.2

/-! ## 上げの移送 -/

theorem option_map_inj {f : Nat → Nat} (hf : ∀ a b, f a = f b → a = b) {o : Option Nat} {m : Nat} :
    o.map f = some (f m) ↔ o = some m := by
  cases o with
  | none => simp
  | some a => simp only [Option.map_some, Option.some.injEq]; exact ⟨fun h => by rw [hf a m h], fun h => by rw [h]⟩

/-- **The upgrade is transported** along an injective map of columns that matches everything `upg`
reads. -/
theorem upg_transfer {A B : Mat} {ia ib : Nat} (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b)
    (h1 : entry A 1 ia = entry B 1 ib) (h2 : entry A 2 ia = entry B 2 ib)
    (hlen : ia + 1 = A.length ↔ ib + 1 = B.length)
    (hp1 : par A 1 ia = (par B 1 ib).map f)
    (hm : ∀ m, par B 1 ib = some m → entry A 0 (f m) = entry B 0 m ∧ entry A 2 (f m) = entry B 2 m)
    (hn1 : par A 1 (ia + 1) = (par B 1 (ib + 1)).map f)
    (hnc : col A (ia + 1) = col B (ib + 1)) (hfn : f (ib + 1) = ia + 1)
    (hanc : ancL A ia = (ancL B ib).map f)
    (hpred : ∀ a ∈ ancL B ib, par A 1 (f a) = (par B 1 a).map f ∧ col A (f a) = col B a ∧
      (entry A 0 (f a) < entry A 0 (ia + 1) ↔ entry B 0 a < entry B 0 (ib + 1))) :
    upg A ia = (upg B ib).map f := by
  unfold upg
  rw [h1, h2]
  by_cases hc : entry B 1 ib = 0 ∨ entry B 2 ib = 1 ∨ ib + 1 = B.length
  · have hc' : entry B 1 ib = 0 ∨ entry B 2 ib = 1 ∨ ia + 1 = A.length := by
      rcases hc with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (hlen.mpr h))
    rw [if_pos hc', if_pos hc]; rfl
  · have hc' : ¬ (entry B 1 ib = 0 ∨ entry B 2 ib = 1 ∨ ia + 1 = A.length) := by
      intro h; apply hc
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (hlen.mp h))
    rw [if_neg hc', if_neg hc, hp1]
    cases hpm : par B 1 ib with
    | none => rfl
    | some m =>
      simp only [Option.map_some]
      obtain ⟨hm0, hm2⟩ := hm m hpm
      rw [hm0, hm2]
      have hfw : (par A 1 (ia + 1) = some (f m) ∧
          col A (ia + 1) = (entry B 0 m + 1, entry B 1 ib, entry B 2 m + 1)) ↔
          (par B 1 (ib + 1) = some m ∧ col B (ib + 1) = (entry B 0 m + 1, entry B 1 ib, entry B 2 m + 1)) := by
        rw [hn1, option_map_inj hf, hnc]
      by_cases hF : par B 1 (ib + 1) = some m ∧
          col B (ib + 1) = (entry B 0 m + 1, entry B 1 ib, entry B 2 m + 1)
      · rw [if_pos (hfw.mpr hF), if_pos hF]; simp [hfn]
      · rw [if_neg (fun h => hF (hfw.mp h)), if_neg hF, upgClimb_find, upgClimb_find, hanc, List.find?_map]
        congr 1
        apply find?_congr'
        intro a ha
        obtain ⟨hpa, hca, hea⟩ := hpred a ha
        simp only [Function.comp, hpa, hca, option_map_inj hf]
        simp only [decide_eq_decide]
        rw [hea]

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

omit hL hp in
theorem lenN0 : (TRIO.gexp M r L 0 0 n).length = r + n * L := TRIO.gexp_length hlen

omit hL hp hn in
/-- **The copies are exact** (`d0 = 0`). -/
theorem getD_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    (TRIO.gexp M r L 0 0 n).getD (r + (k * L + q)) (0, 0, 0) = M.getD (r + q) (0, 0, 0) := by
  rw [TRIO.gexp_getD_mir hlen hk hq, TRIO.getD_eq_entries]
  simp

omit hL hp hn in
theorem entry_copy0 {k q : Nat} (hk : k < n) (hq : q < L) (y : Nat) :
    entry (TRIO.gexp M r L 0 0 n) y (r + (k * L + q)) = entry M y (r + q) := by
  unfold entry; rw [getD_copy0 hlen hk hq]

omit hL hp hn in
theorem col_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    col (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = col M (r + q) := by
  unfold col; rw [getD_copy0 hlen hk hq]

omit hL hp in
theorem entry_pre0 (y : Nat) {i : Nat} (hi : i < r + L) :
    entry (TRIO.gexp M r L 0 0 n) y i = entry M y i := entry_gexp_pre hlen hn y hi

omit hn in
/-- The columns of `B` are in the subtree of `r`. -/
theorem anc_B {q : Nat} (hq : q ≤ L) : Anc0 M r (r + q) :=
  anc_between (anc0_of_par M 0 r (r + L) hp) (r + q) (by omega) (by omega)

omit hn in
theorem e0_B_gt {q : Nat} (hq0 : 0 < q) (hq : q ≤ L) : entry M 0 r < entry M 0 (r + q) :=
  anc0_e0_lt (anc_B hlen hL hp hq) (by omega)

omit hn in
theorem e0_B_ge {q : Nat} (hq : q < L) : entry M 0 r ≤ entry M 0 (r + q) := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · exact le_of_lt (e0_B_gt hlen hL hp h (by omega))

/-- Every column of the copies has row 0 at least that of `r`. -/
theorem e0_copies_ge {j : Nat} (hj0 : r ≤ j) (hj : j < r + n * L) :
    entry M 0 r ≤ entry (TRIO.gexp M r L 0 0 n) 0 j := by
  obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL hj0 hj
  rw [entry_copy0 hlen hk hq]
  exact e0_B_ge hlen hL hp hq

/-- **The parent of a column inside a copy** is in the same copy. -/
theorem par0_copy0 {k q p : Nat} (hk : k < n) (hq : q < L) (hq0 : 0 < q)
    (hpq : par M 0 (r + q) = some p) :
    par (TRIO.gexp M r L 0 0 n) 0 (r + (k * L + q)) = some (r + (k * L + (p - r))) := by
  have hpr : r ≤ p := by
    have hA := anc_B hlen hL hp (show q ≤ L by omega)
    exact (anc0_par hA (by omega) hpq).le
  obtain ⟨h1, h2, h3⟩ := (par0_spec M).mp hpq
  rw [par0_spec]
  refine ⟨by omega, ?_, fun j hj1 hj2 => ?_⟩
  · rw [entry_copy0 hlen hk (by omega), entry_copy0 hlen hk hq,
      show r + (p - r) = p by omega]; exact h2
  · have hj : j = r + (k * L + (j - r - k * L)) := by omega
    rw [hj, entry_copy0 hlen hk hq 0, entry_copy0 hlen hk (q := j - r - k * L) (by omega) 0]
    exact h3 (r + (j - r - k * L)) (by omega) (by omega)

/-- **The parent of a copy root** is the parent of `r`. -/
theorem par0_root0 {k : Nat} (hk : k < n) :
    par (TRIO.gexp M r L 0 0 n) 0 (r + k * L) = par M 0 r := by
  have hrk : entry (TRIO.gexp M r L 0 0 n) 0 (r + k * L) = entry M 0 r := by
    have := entry_copy0 hlen hk hL 0 (M := M) (q := 0)
    rwa [Nat.add_zero, Nat.add_zero] at this
  have hlo : ∀ j, j < r → entry (TRIO.gexp M r L 0 0 n) 0 j = entry M 0 j :=
    fun j hj => entry_pre0 hlen hn 0 (by omega)
  cases hg : par M 0 r with
  | some g =>
    obtain ⟨h1, h2, h3⟩ := (par0_spec M).mp hg
    rw [par0_spec]
    refine ⟨by omega, by rw [hlo g h1, hrk]; exact h2, fun j hj1 hj2 => ?_⟩
    rw [hrk]
    rcases Nat.lt_or_ge j r with h | h
    · rw [hlo j h]; exact h3 j hj1 h
    · exact e0_copies_ge hlen hL hp hn h (by
        have : k * L < n * L := Nat.mul_lt_mul_of_pos_right hk hL
        omega)
  | none =>
    cases hN : par (TRIO.gexp M r L 0 0 n) 0 (r + k * L) with
    | none => rfl
    | some a =>
      exfalso
      obtain ⟨h1, h2, h3⟩ := (par0_spec _).mp hN
      rw [hrk] at h2 h3
      rcases Nat.lt_or_ge a r with h | h
      · rw [hlo a h] at h2
        have : par M 0 r = some a := (par0_spec M).mpr ⟨h, h2, fun j hj1 hj2 => by
          have := h3 j hj1 (by omega); rwa [hlo j hj2] at this⟩
        rw [hg] at this; cases this
      · have := e0_copies_ge hlen hL hp hn h (by
          have : k * L < n * L := Nat.mul_lt_mul_of_pos_right hk hL
          omega)
        omega

/-- **The ancestors of a copy column** are those of the column of `B`, shifted into the copy. -/
theorem ancL_copy0 {k : Nat} (hk : k < n) :
    ∀ q, q < L → ancL (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = (ancL M (r + q)).map (shk r (k * L)) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
  intro hq
  rcases Nat.eq_zero_or_pos q with h0 | hq0
  · subst h0
    simp only [Nat.add_zero]
    have hpr := par0_root0 hlen hL hp hn hk
    cases hg : par M 0 r with
    | none =>
      rw [hg] at hpr
      rw [ancL_none hpr, ancL_none hg]; rfl
    | some g =>
      rw [hg] at hpr
      have hgr := par_lt M 0 r g hg
      rw [ancL_eq hpr, ancL_eq hg, List.map_cons]
      have hcong : ancL (TRIO.gexp M r L 0 0 n) g = ancL M g :=
        ancL_congr_e0 (fun j hj => entry_pre0 hlen hn 0 (by omega))
      rw [hcong]
      have hshg : shk r (k * L) g = g := by unfold shk; rw [if_neg (by omega)]
      rw [hshg]
      congr 1
      symm
      conv_rhs => rw [← List.map_id (ancL M g)]
      apply List.map_congr_left
      intro a ha
      have := mem_ancL_lt ha
      unfold shk; rw [if_neg (by omega)]; rfl
  · have hA := anc_B hlen hL hp (show q ≤ L by omega)
    obtain ⟨p, hpq⟩ := par0_of_anc hA (by omega)
    have hpr : r ≤ p := (anc0_par hA (by omega) hpq).le
    have hpq' := par_lt M 0 (r + q) p hpq
    have hN := par0_copy0 hlen hL hp hn hk hq hq0 hpq
    rw [ancL_eq hN, ancL_eq hpq, List.map_cons]
    have ih' := ih (p - r) (by omega) (by omega)
    rw [show r + (p - r) = p by omega] at ih'
    rw [ih']
    congr 1
    unfold shk; rw [if_pos hpr]; omega

/-- **`P_1` of a copy column** is that of the column of `B`, shifted. -/
theorem par1_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    par (TRIO.gexp M r L 0 0 n) 1 (r + (k * L + q)) = (par M 1 (r + q)).map (shk r (k * L)) := by
  rw [par1_find, par1_find, ancL_copy0 hlen hL hp hn hk q hq, entry_copy0 hlen hk hq 1, List.find?_map]
  congr 1
  apply find?_congr'
  intro a ha
  have hal := mem_ancL_lt ha
  simp only [Function.comp]
  unfold shk
  split
  · rename_i hra
    rw [show a + k * L = r + (k * L + (a - r)) by omega, entry_copy0 hlen hk (by omega) 1,
      show r + (a - r) = a by omega]
  · rw [entry_pre0 hlen hn 1 (by omega)]

theorem entry_shk {k a : Nat} (hk : k < n) (ha : a < r + L) (y : Nat) :
    entry (TRIO.gexp M r L 0 0 n) y (shk r (k * L) a) = entry M y a := by
  unfold shk
  split
  · rename_i h
    rw [show a + k * L = r + (k * L + (a - r)) by omega, entry_copy0 hlen hk (by omega) y,
      show r + (a - r) = a by omega]
  · exact entry_pre0 hlen hn y ha

theorem col_shk {k a : Nat} (hk : k < n) (ha : a < r + L) :
    col (TRIO.gexp M r L 0 0 n) (shk r (k * L) a) = col M a := by
  rw [col_eq_entries, col_eq_entries, entry_shk hlen hL hp hn hk ha, entry_shk hlen hL hp hn hk ha,
    entry_shk hlen hL hp hn hk ha]

theorem par1_shk {k a : Nat} (hk : k < n) (ha : a < r + L) :
    par (TRIO.gexp M r L 0 0 n) 1 (shk r (k * L) a) = (par M 1 a).map (shk r (k * L)) := by
  by_cases har : r ≤ a
  · have h := par1_copy0 hlen hL hp hn hk (q := a - r) (by omega)
    rw [show r + (k * L + (a - r)) = shk r (k * L) a by unfold shk; rw [if_pos har]; omega,
      show r + (a - r) = a by omega] at h
    exact h
  · have hs : shk r (k * L) a = a := by unfold shk; rw [if_neg har]
    rw [hs, par_gexp_pre hlen hn 1 ha]
    cases hm : par M 1 a with
    | none => rfl
    | some m =>
      have := par_lt M 1 a m hm
      simp only [Option.map_some, Option.some.injEq]
      unfold shk; rw [if_neg (by omega)]

/-- **The upgrade of a column inside a copy** (not its last column) is that of `B`, shifted. -/
theorem upg_copy0 {k q : Nat} (hk : k < n) (hq : q + 1 < L) :
    upg (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = (upg M (r + q)).map (shk r (k * L)) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hkL : k * L + L ≤ n * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  apply upg_transfer (shk r (k * L)) (shk_inj r _)
  · exact entry_copy0 hlen hk (by omega) 1
  · exact entry_copy0 hlen hk (by omega) 2
  · rw [hlN]; omega
  · exact par1_copy0 hlen hL hp hn hk (by omega)
  · intro m hm
    have := par_lt M 1 _ m hm
    exact ⟨entry_shk hlen hL hp hn hk (by omega) 0, entry_shk hlen hL hp hn hk (by omega) 2⟩
  · have h := par1_shk hlen hL hp hn hk (a := r + q + 1) (by omega)
    rw [show shk r (k * L) (r + q + 1) = r + (k * L + q) + 1 by unfold shk; rw [if_pos (by omega)]; omega] at h
    exact h
  · have h := col_copy0 hlen hk (q := q + 1) (by omega) (M := M) (n := n)
    rw [show r + (k * L + (q + 1)) = r + (k * L + q) + 1 by omega, show r + (q + 1) = r + q + 1 by omega] at h
    exact h
  · unfold shk; rw [if_pos (by omega)]; omega
  · exact ancL_copy0 hlen hL hp hn hk q (by omega)
  · intro a ha
    have hal := mem_ancL_lt ha
    refine ⟨par1_shk hlen hL hp hn hk (by omega), col_shk hlen hL hp hn hk (by omega), ?_⟩
    have he := entry_copy0 hlen hk (q := q + 1) (by omega) 0 (M := M) (n := n)
    rw [show r + (k * L + (q + 1)) = r + (k * L + q) + 1 by omega, show r + (q + 1) = r + q + 1 by omega] at he
    rw [he, entry_shk hlen hL hp hn hk (by omega) 0]

/-- In a column before `x`, the upgrade of `N` is that of `M`. -/
theorem upg_pre0 {i : Nat} (hi : i + 1 < r + L) :
    upg (TRIO.gexp M r L 0 0 n) i = upg M i := by
  rw [← upg_take _ hi, gexp_take_x hlen hn, upg_take M hi]

/-- The ancestors of `x − 1` have row 0 at most that of `r` only at `r` and above `r`. -/
theorem anc_xm1_e0 {a : Nat} (ha : a ∈ ancL M (r + (L - 1))) (hle : entry M 0 a ≤ entry M 0 r) :
    a ≤ r := by
  by_contra h
  have hal := mem_ancL_lt ha
  have := e0_B_gt hlen hL hp (q := a - r) (by omega) (by omega)
  rw [show r + (a - r) = a by omega] at this
  omega

/-- **The upgrade of the last column of a copy** (not the last copy): as `x − 1` in `M`, except that an
upgrade to `r` goes to the next copy root. -/
theorem upg_copy_last0 (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {k : Nat} (hk : k + 1 < n) :
    upg (TRIO.gexp M r L 0 0 n) (r + (k * L + (L - 1))) =
      (upg M (r + (L - 1))).map (fun t => if t = r then r + (k + 1) * L else t) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hkL : (k + 1) * L + L ≤ n * L := by
    have := Nat.mul_le_mul_right L (show k + 1 + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  have hnext : r + (k * L + (L - 1)) + 1 = r + ((k + 1) * L + 0) := by rw [Nat.succ_mul]; omega
  have hxm : r + (L - 1) + 1 = r + L := by omega
  unfold upg
  rw [entry_copy0 hlen (by omega) (by omega) 1, entry_copy0 hlen (by omega) (by omega) 2, hlN, hxm,
    ← hlen]
  by_cases hc : entry M 1 (r + (L - 1)) = 0 ∨ entry M 2 (r + (L - 1)) = 1 ∨ r + L = r + L + 1
  · rcases hc with h | h | h
    · rw [if_pos (Or.inl h), if_pos (Or.inl h)]; rfl
    · rw [if_pos (Or.inr (Or.inl h)), if_pos (Or.inr (Or.inl h))]; rfl
    · omega
  have hc' : ¬ (entry M 1 (r + (L - 1)) = 0 ∨ entry M 2 (r + (L - 1)) = 1 ∨
      r + (k * L + (L - 1)) + 1 = r + n * L) := by
    rintro (h | h | h)
    · exact hc (Or.inl h)
    · exact hc (Or.inr (Or.inl h))
    · omega
  rw [if_neg hc', if_neg (fun h => hc (by rcases h with h | h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h); omega])),
    par1_copy0 hlen hL hp hn (by omega) (show L - 1 < L by omega)]
  cases hpm : par M 1 (r + (L - 1)) with
  | none => rfl
  | some m =>
    simp only [Option.map_some]
    have hmx := par_lt M 1 _ m hpm
    rw [entry_shk hlen hL hp hn (by omega) (by omega) 0, entry_shk hlen hL hp hn (by omega) (by omega) 2]
    -- `M` never upgrades forward onto `x`
    have hfM : ¬ (par M 1 (r + L) = some m ∧
        col M (r + L) = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1)) := by
      rintro ⟨_, hcol⟩
      have : entry M 2 (r + L) = entry M 2 m + 1 := by rw [col_eq_entries] at hcol; simp at hcol; omega
      omega
    have hp1n : par (TRIO.gexp M r L 0 0 n) 1 (r + (k * L + (L - 1)) + 1) = par M 1 r := by
      rw [hnext, par1_copy0 hlen hL hp hn (by omega) hL, Nat.add_zero]
      cases h : par M 1 r with
      | none => rfl
      | some m' =>
        have := par_lt M 1 r m' h
        simp only [Option.map_some, Option.some.injEq]; unfold shk; rw [if_neg (by omega)]
    have hcn : col (TRIO.gexp M r L 0 0 n) (r + (k * L + (L - 1)) + 1) = col M r := by
      have := col_copy0 hlen (by omega) hL (M := M) (n := n) (k := k + 1) (q := 0)
      rw [hnext]; simpa using this
    have hen : entry (TRIO.gexp M r L 0 0 n) 0 (r + (k * L + (L - 1)) + 1) = entry M 0 r := by
      have := entry_copy0 hlen (by omega) hL 0 (M := M) (n := n) (k := k + 1) (q := 0)
      rw [hnext]; simpa using this
    have he0x : entry M 0 (r + L) = entry M 0 r + 1 := hR0 _ _ hp
    have hclM : ∀ ok, climb (par M 0) ok (r + L) (par M 0 (r + (L - 1))) =
        (ancL M (r + (L - 1))).find? ok := fun ok => by rw [← hxm]; exact upgClimb_find M _ ok
    rw [if_neg hfM, upgClimb_find, hclM, hp1n, hcn,
      ancL_copy0 hlen hL hp hn (by omega) (L - 1) (by omega), List.find?_map]
    -- the three kinds of ancestors of `x − 1`
    have hkind : ∀ a ∈ ancL M (r + (L - 1)), a = r ∨ (r < a ∧ entry M 0 r < entry M 0 a) ∨
        (a < r ∧ entry M 0 a < entry M 0 r) := by
      intro a ha
      have hAa := anc0_of_mem_ancL ha
      have hAr : Anc0 M r (r + (L - 1)) := anc_B hlen hL hp (by omega)
      rcases anc0_total hAa hAr with h | h
      · by_cases har : a = r
        · exact Or.inl har
        · right; right
          exact ⟨lt_of_le_of_ne h.le har, anc0_e0_lt h har⟩
      · by_cases har : a = r
        · exact Or.inl har
        · right; left
          exact ⟨lt_of_le_of_ne h.le (Ne.symm har), anc0_e0_lt h (Ne.symm har)⟩
    have hmlt : ∀ a, par M 1 a = some m → a < r → m < r := fun a h ha => by
      have := par_lt M 1 a m h; omega
    by_cases hfr : par M 1 r = some m ∧
        col M r = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1)
    · have hmr : m < r := par_lt M 1 r m hfr.1
      have hsm : shk r (k * L) m = m := by unfold shk; rw [if_neg (by omega)]
      rw [hsm, if_pos hfr]
      have hL1 : L ≠ 1 := by
        intro h1
        have h0 : L - 1 = 0 := by omega
        have hz := hZ2 (r + (L - 1))
        have hne2 : entry M 2 (r + (L - 1)) ≠ 1 := fun h => hc (Or.inr (Or.inl h))
        have h2 := hfr.2
        rw [col_eq_entries] at h2; simp only [Prod.mk.injEq] at h2
        rw [h0, Nat.add_zero] at hz hne2
        omega
      -- `M` climbs to `r`
      obtain ⟨S, hS, hSp⟩ := ancL_through (anc_B hlen hL hp (show L - 1 ≤ L by omega)) (by omega)
      rw [hS, List.find?_append, List.find?_cons]
      have hSn : S.find? (fun q => decide (par M 1 q = some m ∧
          col M q = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1) ∧
          entry M 0 q < entry M 0 (r + L))) = none := by
        rw [List.find?_eq_none]
        intro s hs
        obtain ⟨h1, h2, h3, _⟩ := hSp s hs
        have := anc0_e0_lt h3 (by omega)
        simp only [decide_eq_true_eq, not_and]; intro _ _; omega
      rw [hSn]
      simp only [Option.none_or]
      have hdec : decide (par M 1 r = some m ∧
          col M r = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1) ∧
          entry M 0 r < entry M 0 (r + L)) = true := by
        simp only [decide_eq_true_eq]; exact ⟨hfr.1, hfr.2, by omega⟩
      rw [hdec]
      simp only [Option.map_some, Option.some.injEq, if_true]
      rw [Nat.succ_mul]; omega
    · have hfN : ¬ (par M 1 r = some (shk r (k * L) m) ∧
          col M r = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1)) := by
        rintro ⟨h1, h2⟩
        apply hfr
        by_cases hmr : r ≤ m
        · have := par_lt M 1 r _ h1; unfold shk at this; rw [if_pos hmr] at this; omega
        · unfold shk at h1; rw [if_neg hmr] at h1; exact ⟨h1, h2⟩
      rw [if_neg hfN]
      have hfind : (ancL M (r + (L - 1))).find? ((fun q => decide (par (TRIO.gexp M r L 0 0 n) 1 q =
            some (shk r (k * L) m) ∧ col (TRIO.gexp M r L 0 0 n) q =
              (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1) ∧
            entry (TRIO.gexp M r L 0 0 n) 0 q < entry (TRIO.gexp M r L 0 0 n) 0
              (r + (k * L + (L - 1)) + 1))) ∘ shk r (k * L)) =
          (ancL M (r + (L - 1))).find? (fun q => decide (par M 1 q = some m ∧
            col M q = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1) ∧
            entry M 0 q < entry M 0 (r + L))) := by
        apply find?_congr'
        intro a ha
        have hal := mem_ancL_lt ha
        have hk' : k < n := by omega
        have ha' : a < r + L := by omega
        simp only [Function.comp]
        rw [par1_shk hlen hL hp hn hk' ha', col_shk hlen hL hp hn hk' ha', entry_shk hlen hL hp hn hk' ha',
          hen, he0x]
        simp only [option_map_inj (shk_inj r _)]
        rcases hkind a ha with har | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst har
          simp only [decide_eq_decide]
          constructor
          · rintro ⟨_, _, h⟩; omega
          · rintro ⟨h1', h2', _⟩; exact absurd ⟨h1', h2'⟩ hfr
        · simp only [decide_eq_decide]
          constructor
          · rintro ⟨_, _, h⟩; omega
          · rintro ⟨_, _, h⟩; omega
        · simp only [decide_eq_decide]
          constructor
          · rintro ⟨h3, h4, _⟩; exact ⟨h3, h4, by omega⟩
          · rintro ⟨h3, h4, _⟩; exact ⟨h3, h4, h2⟩
      rw [hfind]
      cases hF : (ancL M (r + (L - 1))).find? (fun q => decide (par M 1 q = some m ∧
          col M q = (entry M 0 m + 1, entry M 1 (r + (L - 1)), entry M 2 m + 1) ∧
          entry M 0 q < entry M 0 (r + L))) with
      | none => rfl
      | some F =>
        have hFm := List.mem_of_find?_eq_some hF
        have hFp := List.find?_some hF
        simp only [decide_eq_true_eq] at hFp
        simp only [Option.map_some, Option.some.injEq]
        rcases hkind F hFm with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd ⟨hFp.1, hFp.2.1⟩ hfr
        · omega
        · unfold shk; rw [if_neg (by omega), if_neg (by omega)]

/-- **The parent of a column after `x`**: a copy root has the parent of `r`, any other column has its
parent in the same copy (after `x`). -/
theorem par0_tail {c : Nat} (hc0 : r + L ≤ c) (hc : c < r + n * L) :
    (∃ k, 1 ≤ k ∧ k < n ∧ c = r + k * L ∧ par (TRIO.gexp M r L 0 0 n) 0 c = par M 0 r) ∨
    (∃ p, par (TRIO.gexp M r L 0 0 n) 0 c = some p ∧ r + L ≤ p ∧ p < c) := by
  obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hc
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this; omega
  rcases Nat.eq_zero_or_pos q with h0 | hq0
  · subst h0
    left
    exact ⟨k, hk1, hk, by omega, by rw [show r + (k * L + 0) = r + k * L by omega]; exact par0_root0 hlen hL hp hn hk⟩
  · right
    have hA := anc_B hlen hL hp (show q ≤ L by omega)
    obtain ⟨p', hp'⟩ := par0_of_anc hA (by omega)
    have hpr : r ≤ p' := (anc0_par hA (by omega) hp').le
    have hp'q := par_lt M 0 _ p' hp'
    refine ⟨_, par0_copy0 hlen hL hp hn hk hq hq0 hp', ?_, by omega⟩
    have : L ≤ k * L := Nat.le_mul_of_pos_left L hk1
    omega

/-- **The children of a column before `r`** other than the parent of `r` are those in `M`. -/
theorem children_pre0 {i : Nat} (hi : i < r) (hig : par M 0 r ≠ some i) :
    children (TRIO.gexp M r L 0 0 n) i = children M i := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  apply eq_of_sorted_mem _ _ (children_sorted _ i) (children_sorted M i)
  intro c
  rw [mem_children_iff, mem_children_iff, hlN, ← hlen]
  constructor
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hn 0 h] at hpc; exact ⟨by omega, hpc⟩
    · rcases par0_tail hlen hL hp hn h hc with ⟨k, _, _, _, hpk⟩ | ⟨p', hp', hp'1, _⟩
      · rw [hpc] at hpk; exact absurd hpk.symm hig
      · rw [hpc] at hp'; cases hp'; omega
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hn 0 h]; exact ⟨by omega, hpc⟩
    · have : c = r + L := by omega
      subst this; rw [hp] at hpc; cases hpc; omega

/-- **The children of the parent of `r`**: those in `M` (ending with `r`), then the other copy roots. -/
theorem children_g0 {g : Nat} (hg : par M 0 r = some g) :
    children (TRIO.gexp M r L 0 0 n) g =
      children M g ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr := par_lt M 0 r g hg
  -- the children of `g` in `M` are at most `r`
  have hle : ∀ c ∈ children M g, c ≤ r := by
    intro c hc
    have hpc := (mem_children_iff.mp hc).2
    by_contra h
    have hcl := (mem_children hc).2
    rcases Nat.lt_or_ge c (r + L) with h' | h'
    · have hA := anc_B hlen hL hp (q := c - r) (by omega)
      rw [show r + (c - r) = c by omega] at hA
      have := (anc0_par hA (by omega) hpc).le; omega
    · have : c = r + L := by omega
      subst this; rw [hp] at hpc; cases hpc; omega
  apply eq_of_sorted_mem _ _ (children_sorted _ g)
  · apply List.pairwise_append.mpr
    refine ⟨children_sorted M g, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact List.pairwise_lt_range.imp (fun {a b} h => by
        have := Nat.mul_lt_mul_of_pos_right (show a + 1 < b + 1 by omega) hL; omega)
    · intro a ha b hb
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
      have := hle a ha
      have : L ≤ (k + 1) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
  intro c
  rw [List.mem_append, mem_children_iff, mem_children_iff, hlN, ← hlen, List.mem_map]
  constructor
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hn 0 h] at hpc; exact Or.inl ⟨by omega, hpc⟩
    · rcases par0_tail hlen hL hp hn h hc with ⟨k, hk1, hk, hck, _⟩ | ⟨p', hp', hp'1, _⟩
      · right; exact ⟨k - 1, List.mem_range.mpr (by omega), by rw [hck, show k - 1 + 1 = k by omega]⟩
      · rw [hpc] at hp'; cases hp'; omega
  · rintro (⟨hc, hpc⟩ | ⟨k, hk, rfl⟩)
    · rcases Nat.lt_or_ge c (r + L) with h | h
      · rw [par_gexp_pre hlen hn 0 h]; exact ⟨by omega, hpc⟩
      · have : c = r + L := by omega
        subst this; rw [hp] at hpc; cases hpc; omega
    · have hk' := List.mem_range.mp hk
      have hkn : k + 1 < n := by omega
      refine ⟨?_, ?_⟩
      · have := Nat.mul_lt_mul_of_pos_right (show k + 1 < n by omega) hL; omega
      · have := par0_root0 hlen hL hp hn hkn
        rw [hg] at this; exact this

/-- **The children of a copy column**: those of the column of `B` (without `x`), shifted. -/
theorem children_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    children (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) =
      ((children M (r + q)).filter (fun c => decide (c < r + L))).map (shk r (k * L)) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hkL : k * L + L ≤ n * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  apply eq_of_sorted_mem _ _ (children_sorted _ _)
  · rw [List.pairwise_map]
    exact ((children_sorted M (r + q)).filter _).imp_of_mem (fun {a b} ha hb h => by
      have ha' := (mem_children (List.mem_filter.mp ha).1).1
      have hb' := (mem_children (List.mem_filter.mp hb).1).1
      unfold shk; rw [if_pos (by omega), if_pos (by omega)]; omega)
  intro c
  rw [mem_children_iff, hlN, List.mem_map]
  constructor
  · rintro ⟨hc, hpc⟩
    have hci := par_lt _ 0 c _ hpc
    rcases Nat.lt_or_ge c (r + L) with h | h
    · -- `k = 0`
      rw [par_gexp_pre hlen hn 0 h] at hpc
      have hk0 : k = 0 := by
        by_contra hk0
        have : L ≤ k * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      subst hk0
      refine ⟨c, List.mem_filter.mpr ⟨mem_children_iff.mpr ⟨by omega, by simpa using hpc⟩,
        by simpa using h⟩, ?_⟩
      unfold shk; split <;> simp
    · rcases par0_tail hlen hL hp hn h hc with ⟨k', _, _, hck, hpk⟩ | ⟨p', hp', hp'1, hp'2⟩
      · rw [hpc] at hpk
        have := par_lt M 0 r _ hpk.symm; omega
      · obtain ⟨k', q', hk', hq', rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hc
        have hq'0 : 0 < q' := by
          by_contra h0
          have : q' = 0 := by omega
          subst this
          rcases par0_tail hlen hL hp hn h hc with ⟨k2, _, _, _, hpk⟩ | _
          · rw [hpc] at hpk; have := par_lt M 0 r _ hpk.symm; omega
          · have := par0_root0 hlen hL hp hn hk'
            rw [show r + (k' * L + 0) = r + k' * L by omega, this] at hpc
            have := par_lt M 0 r _ hpc; omega
        have hA := anc_B hlen hL hp (show q' ≤ L by omega)
        obtain ⟨p2, hp2⟩ := par0_of_anc hA (by omega)
        have hp2r : r ≤ p2 := (anc0_par hA (by omega) hp2).le
        have hp2q := par_lt M 0 _ p2 hp2
        rw [par0_copy0 hlen hL hp hn hk' hq' hq'0 hp2] at hpc
        simp only [Option.some.injEq] at hpc
        obtain ⟨hkk, hqq⟩ := decomp_unique (L := L) (by omega) hq (show k' * L + (p2 - r) = k * L + q by omega)
        subst hkk
        refine ⟨r + q', List.mem_filter.mpr ⟨mem_children_iff.mpr ⟨by omega, ?_⟩, by simpa using hq'⟩, ?_⟩
        · rw [hp2]; congr 1; omega
        · unfold shk; rw [if_pos (by omega)]; omega
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨hdM, hdx⟩ := List.mem_filter.mp hd
    have hdx' : d < r + L := by simpa using hdx
    have hpd := (mem_children_iff.mp hdM).2
    have hdq := par_lt M 0 d _ hpd
    have hrd : r ≤ d := by have := (mem_children hdM).1; omega
    have hq'0 : 0 < d - r := by omega
    have := par0_copy0 hlen hL hp hn hk (q := d - r) (by omega) hq'0
      (by rw [show r + (d - r) = d by omega]; exact hpd)
    refine ⟨?_, ?_⟩
    · unfold shk; rw [if_pos hrd]; omega
    · unfold shk; rw [if_pos hrd, show d + k * L = r + (k * L + (d - r)) by omega, this]
      congr 1; omega

theorem upg_none_last0 : upg (TRIO.gexp M r L 0 0 n) (r + ((n - 1) * L + (L - 1))) = none := by
  unfold upg
  rw [if_pos (Or.inr (Or.inr (by
    rw [lenN0 hlen hn]
    have : (n - 1) * L + L = n * L := by
      rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    omega)))]

/-- **Upgrades into a column before `r`** are those of `M` (`n ≥ 2`, so the first copy is not the last). -/
theorem isUpg_pre0 (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n) {c : Nat}
    (hc : c < r) : isUpg (TRIO.gexp M r L 0 0 n) c = isUpg M c := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hxm : r + (0 * L + (L - 1)) = r + L - 1 := by omega
  apply Bool.eq_iff_iff.mpr
  unfold isUpg
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hu⟩
    have hj' := List.mem_range.mp hj
    rw [hlN] at hj'
    have hu' : upg (TRIO.gexp M r L 0 0 n) j = some c := by simpa using hu
    have key : ∃ j', j' < M.length ∧ upg M j' = some c := by
      rcases Nat.lt_or_ge (j + 1) (r + L) with h | h
      · rw [upg_pre0 hlen hL hp hn h] at hu'; exact ⟨j, by omega, hu'⟩
      · obtain ⟨k, q, hk, hq, hjkq⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hj'
        by_cases hq1 : q + 1 < L
        · rw [hjkq, upg_copy0 hlen hL hp hn hk hq1] at hu'
          cases hU : upg M (r + q) with
          | none => rw [hU] at hu'; cases hu'
          | some t =>
            rw [hU] at hu'
            simp only [Option.map_some, Option.some.injEq] at hu'
            have htc : t = c := by unfold shk at hu'; split at hu' <;> omega
            exact ⟨r + q, by omega, by rw [hU, htc]⟩
        · have hqL : q = L - 1 := by omega
          rw [hqL] at hjkq
          by_cases hkn : k + 1 < n
          · rw [hjkq, upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 hkn] at hu'
            cases hU : upg M (r + (L - 1)) with
            | none => rw [hU] at hu'; cases hu'
            | some t =>
              rw [hU] at hu'
              simp only [Option.map_some, Option.some.injEq] at hu'
              have htc : t = c := by split at hu' <;> omega
              exact ⟨r + (L - 1), by omega, by rw [hU, htc]⟩
          · have hk1 : k = n - 1 := by omega
            rw [hjkq, hk1, upg_none_last0 hlen hL hp hn] at hu'; cases hu'
    obtain ⟨j', hj'M, hj'u⟩ := key
    exact ⟨j', List.mem_range.mpr hj'M, by simpa using hj'u⟩
  · rintro ⟨j, hj, hu⟩
    have hj' := List.mem_range.mp hj
    have hu' : upg M j = some c := by simpa using hu
    have hjx : j < r + L := by
      by_contra h
      have : j + 1 = M.length := by omega
      unfold upg at hu'; rw [if_pos (Or.inr (Or.inr this))] at hu'; cases hu'
    rcases Nat.lt_or_ge (j + 1) (r + L) with h | h
    · refine ⟨j, List.mem_range.mpr (by rw [hlN]; omega), ?_⟩
      rw [upg_pre0 hlen hL hp hn h, hu']; simp
    · have hjL : j = r + (0 * L + (L - 1)) := by omega
      refine ⟨j, List.mem_range.mpr (by rw [hlN]; omega), ?_⟩
      have := upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 (k := 0) (by omega)
      rw [← hjL, show r + (L - 1) = j by omega, hu'] at this
      rw [this]
      simp only [Option.map_some, decide_eq_true_eq, Option.some.injEq]
      rw [if_neg (by omega)]

omit hn in
/-- The children of the parent of `r` in `M` are at most `r`. -/
theorem children_g_le {g c : Nat} (hg : par M 0 r = some g) (hc : c ∈ children M g) : c ≤ r := by
  have hpc := (mem_children_iff.mp hc).2
  have hgr := par_lt M 0 r g hg
  by_contra h
  have hcl := (mem_children hc).2
  rcases Nat.lt_or_ge c (r + L) with h' | h'
  · have hA := anc_B hlen hL hp (q := c - r) (by omega)
    rw [show r + (c - r) = c by omega] at hA
    have := (anc0_par hA (by omega) hpc).le; omega
  · have : c = r + L := by omega
    subst this; rw [hp] at hpc; cases hpc; omega

omit hn in
theorem children_g_last {g : Nat} (hg : par M 0 r = some g) :
    children M g = (children M g).filter (fun d => decide (d < r)) ++ [r] :=
  split_last_max _ _ (children_sorted M g)
    (mem_children_iff.mpr ⟨by omega, hg⟩) (fun d hd => children_g_le hlen hL hp hg hd)

omit hn in
/-- The children of a column before `r` other than its parent are before `r`. -/
theorem children_lt_r {i c : Nat} (hi : i < r) (hig : par M 0 r ≠ some i) (hc : c ∈ children M i) :
    c < r := by
  have hpc := (mem_children_iff.mp hc).2
  have hic := (mem_children hc).1
  by_contra h
  have hcl := (mem_children hc).2
  rcases Nat.lt_or_ge c (r + L) with h' | h'
  · have hA := anc_B hlen hL hp (q := c - r) (by omega)
    rw [show r + (c - r) = c by omega] at hA
    by_cases hcr : c = r
    · subst hcr; exact hig hpc
    · have := (anc0_par hA (by omega) hpc).le; omega
  · have : c = r + L := by omega
    subst this; rw [hp] at hpc; cases hpc; omega

theorem bump_pre0 {i : Nat} (hi : i < r + L) :
    bump (TRIO.gexp M r L 0 0 n) i = bump M i := by
  unfold bump; rw [entry_pre0 hlen hn 0 hi, entry_pre0 hlen hn 1 hi]

theorem col_pre0 {i : Nat} (hi : i < r + L) : col (TRIO.gexp M r L 0 0 n) i = col M i := by
  rw [col_eq_entries, col_eq_entries, entry_pre0 hlen hn 0 hi, entry_pre0 hlen hn 1 hi,
    entry_pre0 hlen hn 2 hi]

/-- **`topped` before `r`** is that of `M` (`n ≥ 2`). -/
theorem topped_lt0 (hn2 : 2 ≤ n) {c : Nat} (hc : c < r) :
    topped (TRIO.gexp M r L 0 0 n) c = topped M c := by
  by_cases hcg : par M 0 r = some c
  · -- `c` is the parent of `r`: the last child is a copy root
    unfold topped
    rw [children_g0 hlen hL hp hn hcg, children_g_last hlen hL hp hcg]
    have hne := map_range_pred_last (fun k => r + (k + 1) * L) (m := n - 1) (by omega)
    simp only [show n - 1 - 1 + 1 = n - 1 by omega] at hne
    rw [hne, ← List.append_assoc]
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    have h1 := col_copy0 hlen (show n - 1 < n by omega) hL (M := M) (n := n) (k := n - 1) (q := 0)
    rw [Nat.add_zero, Nat.add_zero] at h1
    rw [h1, bump_pre0 hlen hL hp hn (by omega)]
  · unfold topped
    rw [children_pre0 hlen hL hp hn hc hcg]
    cases hl : (children M c).getLast? with
    | none => rfl
    | some d =>
      have hd := List.mem_of_getLast? hl
      have := children_lt_r hlen hL hp hc hcg hd
      simp only
      rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]

/-- **Counting before `r`** is that of `M`. -/
theorem counted_lt0 (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
    {i c : Nat} (hi : i < r) (hc : c < r) :
    Counted (TRIO.gexp M r L 0 0 n) i c ↔ Counted M i c := by
  unfold Counted
  rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega), isUpg_pre0 hlen hL hp hn hR0 hZ2 he2 hn2 hc,
    topped_lt0 hlen hL hp hn hn2 hc]

/-- **An upgrade of `N` into a non-root column of a copy** comes from the same copy, as in `M`. -/
theorem isUpg_copy0 (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {k q : Nat} (hk : k < n)
    (hq : q < L) (hq0 : 0 < q) :
    isUpg (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = isUpg M (r + q) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hkL : k * L + L ≤ n * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  apply Bool.eq_iff_iff.mpr
  unfold isUpg
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hu⟩
    have hj' := List.mem_range.mp hj
    rw [hlN] at hj'
    have hu' : upg (TRIO.gexp M r L 0 0 n) j = some (r + (k * L + q)) := by simpa using hu
    have hjt := upg_lt (by rw [hlN]; exact hj') hu'
    -- the source is in the same copy
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
    have hsrc : ∃ q', q' < L ∧ j = r + (k * L + q') := by
      rcases hcase with h | ⟨hA, hlt⟩
      · exact ⟨q - 1, by omega, by omega⟩
      · -- an ancestor-type upgrade: the source is a descendant of a non-root copy column
        rcases Nat.lt_or_ge j (r + n * L) with hjn | hjn
        · obtain ⟨k', q', hk', hq', rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL
            (by omega) hjn
          -- `j` and the target are in the same copy: the target is an ancestor of `j`
          have hA' := ancL_copy0 hlen hL hp hn hk' q' hq'
          have hmem : r + (k * L + q) ∈ ancL (TRIO.gexp M r L 0 0 n) (r + (k' * L + q')) :=
            mem_ancL_of_anc hA (by omega)
          rw [hA'] at hmem
          obtain ⟨a, ha, hae⟩ := List.mem_map.mp hmem
          have hal := mem_ancL_lt ha
          unfold shk at hae
          split at hae
          · rename_i hra
            obtain ⟨hkk, _⟩ := decomp_unique (L := L) (show a - r < L by omega) hq
              (show k' * L + (a - r) = k * L + q by omega)
            subst hkk; exact ⟨q', hq', rfl⟩
          · omega
        · omega
    obtain ⟨q', hq', rfl⟩ := hsrc
    by_cases hq1 : q' + 1 < L
    · rw [upg_copy0 hlen hL hp hn hk hq1] at hu'
      cases hU : upg M (r + q') with
      | none => rw [hU] at hu'; cases hu'
      | some t =>
        rw [hU] at hu'
        simp only [Option.map_some, Option.some.injEq] at hu'
        have htq : t = r + q := by unfold shk at hu'; split at hu' <;> omega
        exact ⟨r + q', List.mem_range.mpr (by omega), by rw [hU, htq]; simp⟩
    · -- the last column of a copy upgrades only to `r`, the next root, or before `r`
      have hq'L : q' = L - 1 := by omega
      subst hq'L
      by_cases hkn : k + 1 < n
      · rw [upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 hkn] at hu'
        cases hU : upg M (r + (L - 1)) with
        | none => rw [hU] at hu'; cases hu'
        | some t =>
          rw [hU] at hu'
          simp only [Option.map_some, Option.some.injEq] at hu'
          exfalso
          split at hu'
          · rw [Nat.succ_mul] at hu'; omega
          · -- `t` is an ancestor of `x − 1` with row 0 at most that of `r`
            have ht2 := upg_target_e2 hU
            obtain ⟨_, _, _, _, hc2⟩ := upg_spec hU
            have hR := hR0 _ _ hp
            rcases hc2 with h | ⟨hA, hlt⟩
            · rw [show r + (L - 1) + 1 = r + L by omega] at h
              rw [h] at ht2; omega
            · have he0 := upg_climb_e0 hU (by omega)
              rw [show r + (L - 1) + 1 = r + L by omega] at he0
              have hk0 : k = 0 := by
                by_contra hk0
                have : L ≤ k * L := Nat.le_mul_of_pos_left L (by omega)
                omega
              subst hk0
              have := e0_B_gt hlen hL hp hq0 (by omega)
              rw [hu'] at he0
              simp at he0
              omega
      · have hk1 : k = n - 1 := by omega
        rw [hk1, upg_none_last0 hlen hL hp hn] at hu'; cases hu'
  · rintro ⟨j, hj, hu⟩
    have hj' := List.mem_range.mp hj
    have hu' : upg M j = some (r + q) := by simpa using hu
    have hjx : j < r + L := by
      by_contra h
      have : j + 1 = M.length := by omega
      unfold upg at hu'; rw [if_pos (Or.inr (Or.inr this))] at hu'; cases hu'
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
    -- the source is in `B`, not the last column
    have hjr : r ≤ j := by
      rcases hcase with h | ⟨hA, hlt⟩
      · omega
      · have := hA.le; omega
    by_cases hj1 : j + 1 < r + L
    · refine ⟨r + (k * L + (j - r)), List.mem_range.mpr (by rw [hlN]; omega), ?_⟩
      rw [upg_copy0 hlen hL hp hn hk (q := j - r) (by omega), show r + (j - r) = j by omega, hu']
      simp only [Option.map_some, decide_eq_true_eq, Option.some.injEq]
      unfold shk; rw [if_pos (by omega)]; omega
    · exfalso
      have hjL : j = r + (L - 1) := by omega
      rcases hcase with h | ⟨hA, hlt⟩
      · omega
      · -- an ancestor-type upgrade from `x − 1` lands at `r` or before
        have he0 : entry M 0 (r + q) < entry M 0 (r + L) := by
          have := upg_climb_e0 hu' (by omega)
          rw [show j + 1 = r + L by omega] at this; exact this
        have := e0_B_gt hlen hL hp hq0 (by omega)
        have hR := hR0 _ _ hp
        omega

/-- **`topped` of a copy column** is that of the column of `B` in `M.take x`. -/
theorem topped_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    topped (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = topped (M.take (r + L)) (r + q) := by
  unfold topped
  rw [children_copy0 hlen hL hp hn hk hq, children_take, List.getLast?_map]
  cases hl : ((children M (r + q)).filter (fun c => decide (c < r + L))).getLast? with
  | none => rfl
  | some d =>
    have hd := List.mem_of_getLast? hl
    have hdx : d < r + L := by simpa using (List.mem_filter.mp hd).2
    simp only [Option.map_some]
    rw [col_shk hlen hL hp hn hk hdx, col_take M hdx, bump_take M (show r + q < r + L by omega)]
    unfold bump
    rw [entry_copy0 hlen hk hq 0, entry_copy0 hlen hk hq 1]

omit hn in
/-- In `M.take x`, a column of `B` other than `r` has the same `topped` as in `M`. -/
theorem topped_take_B {q : Nat} (hq : q < L) (hq0 : 0 < q) :
    topped (M.take (r + L)) (r + q) = topped M (r + q) := by
  unfold topped
  rw [children_take, List.filter_eq_self.mpr]
  · cases hl : (children M (r + q)).getLast? with
    | none => rfl
    | some d =>
      have hd := List.mem_of_getLast? hl
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h
        have : d = r + L := by omega
        subst this
        have := (mem_children_iff.mp hd).2; rw [hp] at this
        have := Option.some.inj this; omega
      simp only
      rw [col_take M hdx, bump_take M (show r + q < r + L by omega)]
  · intro d hd
    have := (mem_children hd).2
    simp only [decide_eq_true_eq]
    by_contra h
    have : d = r + L := by omega
    subst this
    have := (mem_children_iff.mp hd).2; rw [hp] at this
    have := Option.some.inj this; omega

/-- **Counting inside a copy** is that of `M`. -/
theorem counted_copy0 (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {k q q' : Nat}
    (hk : k < n) (hq : q < L) (hq' : q' < L) (hq'0 : 0 < q') :
    Counted (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) (r + (k * L + q')) ↔
      Counted M (r + q) (r + q') := by
  unfold Counted
  have hb : bump (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = bump M (r + q) := by
    unfold bump; rw [entry_copy0 hlen hk hq 0, entry_copy0 hlen hk hq 1]
  rw [col_copy0 hlen hk hq', hb, isUpg_copy0 hlen hL hp hn hR0 hZ2 he2 hk hq' hq'0,
    topped_copy0 hlen hL hp hn hk hq', topped_take_B hlen hL hp hq' hq'0]

omit hn in
/-- `r` is not `topped` in `M` (its last child `x` is not a bump column). -/
theorem not_topped_r (he2 : entry M 2 (r + L) = 0) : topped M r = false := by
  unfold topped
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  rw [split_last_max _ _ (children_sorted M r) hxr (fun d hd => by have := (mem_children hd).2; omega)]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, decide_eq_false_iff_not]
  intro h
  have : entry M 2 (r + L) = 1 := by
    have := congrArg (fun t => t.2.2) h
    simpa [col_eq_entries, bump] using this
  omega

/-- **A counted copy root makes `r` counted in `M`.** -/
theorem counted_root_imp (he2 : entry M 2 (r + L) = 0) {g k : Nat} (hk : k < n) :
    Counted (TRIO.gexp M r L 0 0 n) g (r + k * L) → g < r → Counted M g r := by
  intro h hg
  have hc := col_copy0 hlen hk hL (M := M) (n := n) (q := 0)
  rw [Nat.add_zero, Nat.add_zero] at hc
  refine ⟨?_, fun h' => by rw [not_topped_r hlen hL hp he2] at h'; exact absurd h'.2 (by simp)⟩
  have := h.1
  rw [hc, bump_pre0 hlen hL hp hn (by omega)] at this
  exact this

theorem phi0_shk {k t : Nat} (ht : t < r + L) : phi0 r L (shk r (k * L) t) = t := by
  unfold shk
  split
  · rename_i h
    rw [show t + k * L = r + (k * L + (t - r)) by omega, phi0_copy (by omega)]; omega
  · exact phi0_lt (by omega)

/-- **The ranking of `M` ranks `N`** through the copy map `phi0` (`n ≥ 2`). -/
theorem rk_N0 (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
    {rk : Bool → Nat → Nat} (hRM : Rk M rk) :
    Rk (TRIO.gexp M r L 0 0 n) (fun b i => rk b (phi0 r L i)) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  intro i hi
  rw [hlN] at hi
  simp only
  by_cases hir : i < r
  · -- a column before `r`
    rw [phi0_lt hir]
    obtain ⟨h1, h2, h3⟩ := hRM i (by omega)
    refine ⟨h1, ?_, ?_⟩
    · intro c hc hcb hcu
      have hcN : Counted (TRIO.gexp M r L 0 0 n) i c := ⟨hcb, hcu⟩
      by_cases hig : par M 0 r = some i
      · rw [children_g0 hlen hL hp hn hig] at hc
        rcases List.mem_append.mp hc with hc | hc
        · have hcr := children_g_le hlen hL hp hig hc
          rcases Nat.lt_or_ge c r with hcr' | hcr'
          · have := (counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hir hcr').mp hcN
            rw [phi0_lt hcr']; exact h2 c hc this.1 this.2
          · have hc' : c = r := by omega
            rw [hc'] at hcN hc ⊢
            have := counted_root_imp hlen hL hp hn he2 (k := 0) (by omega)
              (by rw [show r + 0 * L = r by omega]; exact hcN) hir
            rw [phi0_lt_x (by omega)]; exact h2 r hc this.1 this.2
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
          have hk' := List.mem_range.mp hk
          have := counted_root_imp hlen hL hp hn he2 (k := k + 1) (by omega) hcN hir
          have hrM : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
          rw [show r + (k + 1) * L = r + ((k + 1) * L + 0) by omega, phi0_copy hL, Nat.add_zero]
          exact h2 r hrM this.1 this.2
      · rw [children_pre0 hlen hL hp hn hir hig] at hc
        have hcr := children_lt_r hlen hL hp hir hig hc
        have := (counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hir hcr).mp hcN
        rw [phi0_lt hcr]; exact h2 c hc this.1 this.2
    · intro he1N
      rw [entry_pre0 hlen hn 1 (by omega)] at he1N
      obtain ⟨p1, p2, p3⟩ := h3 he1N
      refine ⟨fun m hm => ?_, fun he2N k hk => ?_, fun he2N j hj hjb k' hk' => ?_⟩
      · rw [par_gexp_pre hlen hn 1 (by omega)] at hm
        have := par_lt M 1 i m hm
        rw [phi0_lt (by omega)]; exact p1 m hm
      · rw [entry_pre0 hlen hn 2 (by omega)] at he2N
        rw [upg_pre0 hlen hL hp hn (by omega)] at hk
        have := upg_le hk
        rw [phi0_lt_x (by omega)]; exact p2 he2N k hk
      · rw [entry_pre0 hlen hn 2 (by omega)] at he2N
        -- the bump child `j` and its child `k'`
        have hjb' : ∀ j0, j0 < r + L → j = j0 → col M j0 = bump M i := by
          intro j0 hj0 hjj
          subst hjj
          rw [← col_pre0 hlen hL hp hn hj0, ← bump_pre0 hlen hL hp hn (by omega)]; exact hjb
        by_cases hig : par M 0 r = some i
        · rw [children_g0 hlen hL hp hn hig] at hj
          rcases List.mem_append.mp hj with hj | hj
          · have hjr := children_g_le hlen hL hp hig hj
            rcases Nat.lt_or_ge j r with hjr' | hjr'
            · have hjg : par M 0 r ≠ some j := by
                intro h; rw [hig] at h; have := (mem_children hj).1; cases h; omega
              rw [children_pre0 hlen hL hp hn hjr' hjg] at hk'
              have := children_lt_r hlen hL hp hjr' hjg hk'
              rw [phi0_lt this]; exact p3 he2N j hj (hjb' j (by omega) rfl) k' hk'
            · have hjr'' : j = r := by omega
              rw [hjr''] at hj hk' hjb'
              have hj0 := children_copy0 hlen hL hp hn (k := 0) (q := 0) (by omega) hL
              simp only [Nat.zero_mul, Nat.add_zero] at hj0
              rw [hj0] at hk'
              obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
              have hex : e < r + L := by simpa using (List.mem_filter.mp he).2
              have := phi0_shk hlen hL hp hn (k := 0) hex
              simp only [Nat.zero_mul] at this
              rw [this]
              exact p3 he2N r hj (hjb' r (by omega) rfl) e (List.mem_filter.mp he).1
          · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
            have hk1 := List.mem_range.mp hk
            have hrM : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
            have hcolr : col M r = bump M i := by
              have := col_copy0 hlen (show k + 1 < n by omega) hL (M := M) (n := n) (q := 0)
              simp only [Nat.add_zero] at this
              rw [← this, ← bump_pre0 hlen hL hp hn (by omega)]
              rw [show r + (k + 1) * L = r + (k + 1) * L from rfl] at hjb; exact hjb
            have hj0 := children_copy0 hlen hL hp hn (k := k + 1) (q := 0) (by omega) hL
            rw [Nat.add_zero, Nat.add_zero] at hj0
            rw [hj0] at hk'
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
            have hex : e < r + L := by simpa using (List.mem_filter.mp he).2
            rw [phi0_shk hlen hL hp hn hex]
            exact p3 he2N r hrM hcolr e (List.mem_filter.mp he).1
        · rw [children_pre0 hlen hL hp hn hir hig] at hj
          have hjr := children_lt_r hlen hL hp hir hig hj
          by_cases hjg : par M 0 r = some j
          · rw [children_g0 hlen hL hp hn hjg] at hk'
            rcases List.mem_append.mp hk' with hk' | hk'
            · rw [phi0_lt_x (by have := children_g_le hlen hL hp hjg hk'; omega)]
              exact p3 he2N j hj (hjb' j (by omega) rfl) k' hk'
            · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
              rw [show r + (k + 1) * L = r + ((k + 1) * L + 0) by omega, phi0_copy hL, Nat.add_zero]
              exact p3 he2N j hj (hjb' j (by omega) rfl) r (mem_children_iff.mpr ⟨by omega, hjg⟩)
          · rw [children_pre0 hlen hL hp hn hjr hjg] at hk'
            have := children_lt_r hlen hL hp hjr hjg hk'
            rw [phi0_lt this]; exact p3 he2N j hj (hjb' j (by omega) rfl) k' hk'
  · -- a copy column
    obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hi
    rw [phi0_copy hq]
    obtain ⟨h1, h2, h3⟩ := hRM (r + q) (by omega)
    refine ⟨h1, ?_, ?_⟩
    · intro c hc hcb hcu
      rw [children_copy0 hlen hL hp hn hk hq] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hdM, hdx⟩ := List.mem_filter.mp hd
      have hdx' : d < r + L := by simpa using hdx
      have hdq := (mem_children hdM).1
      have hcd : shk r (k * L) d = r + (k * L + (d - r)) := by unfold shk; rw [if_pos (by omega)]; omega
      rw [hcd] at hcb hcu
      have := (counted_copy0 hlen hL hp hn hR0 hZ2 he2 hk hq (q' := d - r) (by omega) (by omega)).mp
        ⟨hcb, hcu⟩
      rw [show r + (d - r) = d by omega] at this
      rw [hcd, phi0_copy (by omega), show r + (d - r) = d by omega]
      exact h2 d hdM this.1 this.2
    · intro he1N
      rw [entry_copy0 hlen hk hq 1] at he1N
      obtain ⟨p1, p2, p3⟩ := h3 he1N
      refine ⟨fun m hm => ?_, fun he2N t ht => ?_, fun he2N j hj hjb k' hk' => ?_⟩
      · rw [par1_copy0 hlen hL hp hn hk hq] at hm
        cases hm1 : par M 1 (r + q) with
        | none => rw [hm1] at hm; cases hm
        | some m0 =>
          rw [hm1] at hm
          simp only [Option.map_some, Option.some.injEq] at hm
          subst hm
          have := par_lt M 1 _ m0 hm1
          rw [phi0_shk hlen hL hp hn (by omega)]; exact p1 m0 hm1
      · rw [entry_copy0 hlen hk hq 2] at he2N
        by_cases hq1 : q + 1 < L
        · rw [upg_copy0 hlen hL hp hn hk hq1] at ht
          cases hU : upg M (r + q) with
          | none => rw [hU] at ht; cases ht
          | some t0 =>
            rw [hU] at ht
            simp only [Option.map_some, Option.some.injEq] at ht
            subst ht
            have := upg_le hU
            rw [phi0_shk hlen hL hp hn (by omega)]; exact p2 he2N t0 hU
        · have hqL : q = L - 1 := by omega
          subst hqL
          by_cases hkn : k + 1 < n
          · rw [upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 hkn] at ht
            cases hU : upg M (r + (L - 1)) with
            | none => rw [hU] at ht; cases ht
            | some t0 =>
              rw [hU] at ht
              simp only [Option.map_some, Option.some.injEq] at ht
              have ht0x : t0 < r + L := by
                have := upg_le hU
                by_contra h
                have : t0 = r + L := by omega
                subst this
                have := upg_target_e2 hU; omega
              split at ht
              · rename_i htr
                subst ht; subst htr
                rw [show t0 + (k + 1) * L = t0 + ((k + 1) * L + 0) by omega, phi0_copy hL, Nat.add_zero]
                exact p2 he2N t0 hU
              · subst ht
                rw [phi0_lt_x ht0x]; exact p2 he2N t0 hU
          · have hk1 : k = n - 1 := by omega
            subst hk1
            rw [upg_none_last0 hlen hL hp hn] at ht; cases ht
      · rw [entry_copy0 hlen hk hq 2] at he2N
        rw [children_copy0 hlen hL hp hn hk hq] at hj
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hj
        obtain ⟨hdM, hdx⟩ := List.mem_filter.mp hd
        have hdx' : d < r + L := by simpa using hdx
        have hdq := (mem_children hdM).1
        have hcd : shk r (k * L) d = r + (k * L + (d - r)) := by unfold shk; rw [if_pos (by omega)]; omega
        have hjb' : col M d = bump M (r + q) := by
          rw [← col_shk hlen hL hp hn hk hdx']
          have hb : bump (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = bump M (r + q) := by
            unfold bump; rw [entry_copy0 hlen hk hq 0, entry_copy0 hlen hk hq 1]
          rw [← hb]; exact hjb
        rw [hcd, children_copy0 hlen hL hp hn hk (q := d - r) (by omega), show r + (d - r) = d by omega] at hk'
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
        have hex : e < r + L := by simpa using (List.mem_filter.mp he).2
        rw [phi0_shk hlen hL hp hn hex]
        exact p3 he2N d hdM hjb' e (List.mem_filter.mp he).1

end

end Ytosk
