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

theorem shk_inj (r s : Nat) : ∀ a b, shk r s a = shk r s b → a = b := by
  intro a b h
  unfold shk at h
  split at h <;> split at h <;> omega

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

end

end Ytosk
