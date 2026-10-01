/-
**Ytosk の展開を trio 本体の `gexp`（先頭 ++ コピー）の形で書く。**
これで trio 本体のコピーの親の補題（`gexp_nextrel0_mir` など）が使える。
-/
import Ytosk.Path
import Gtrans

namespace Ytosk

theorem parent_eq_of_par {M : Mat} {t r x : Nat} (ht : t ≤ 2) (hx : x < M.length)
    (hp : par M t x = some r) : TRIO.parent M t x = r := by
  have hn : TRIO.nextR M t r x := (nextR_iff M ht hx).mp hp
  have h1 : TRIO.nextR M t (TRIO.parent M t x) x := by
    unfold TRIO.parent; exact Classical.epsilon_spec (p := fun j0 => TRIO.nextR M t j0 x) ⟨r, hn⟩
  have := (nextR_iff M ht hx).mpr h1; rw [hp] at this; exact (Option.some.inj this).symm

theorem hasParent_of_par {M : Mat} {t r x : Nat} (ht : t ≤ 2) (hx : x < M.length)
    (hp : par M t x = some r) : TRIO.hasParent M t x :=
  ⟨r, (nextR_iff M ht hx).mp hp, fun j hj => by
    have := (nextR_iff M ht hx).mpr hj; rw [hp] at this; exact (Option.some.inj this).symm⟩

/-- **The expansion as `gexp`.** -/
theorem expand_eq_gexp (M : Mat) (n : Nat) (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hp : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r) :
    expand M n = TRIO.gexp M r (M.length - 1 - r)
      (if 0 < TRIO.srow M (M.length - 1) then TRIO.entry M 0 (M.length - 1) - TRIO.entry M 0 r else 0)
      (if 1 < TRIO.srow M (M.length - 1) then TRIO.entry M 1 (M.length - 1) - TRIO.entry M 1 r else 0)
      n := by
  have ht : TRIO.srow M (M.length - 1) ≤ 2 := by unfold TRIO.srow; split_ifs <;> omega
  have hx : M.length - 1 < M.length := by omega
  rw [expand_eq_oper M n hM, TRIO.oper_gcopies n (by omega) hz (hasParent_of_par ht hx hp),
    parent_eq_of_par ht hx hp]
  rfl

/-- Row-0 parent inside a copy. -/
theorem par0_gexp_mir {M : Mat} {j0 Lb d0 d1 n k qa qb : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hqb : qb < Lb) (h : par M 0 (j0 + qb) = some (j0 + qa)) :
    par (TRIO.gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + qb)) = some (j0 + (k * Lb + qa)) := by
  have hbnd : j0 + (k * Lb + qb) < (TRIO.gexp M j0 Lb d0 d1 n).length := by
    rw [TRIO.gexp_length hlen]
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  exact (par0_iff _ hbnd).mpr
    (TRIO.gexp_nextrel0_mir hlen hk hqb ((par0_iff M (by omega)).mp h))

/-- Row-0 parent of the root of copy `k ≥ 1`: the copy `k - 1` of the parent of the last column. -/
theorem par0_gexp_root {M : Mat} {j0 Lb d0 d1 n k qp : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hk1 : 1 ≤ k) (hqp : qp < Lb)
    (hd0e : TRIO.entry M 0 (j0 + Lb) = TRIO.entry M 0 j0 + d0)
    (h : par M 0 (j0 + Lb) = some (j0 + qp)) :
    par (TRIO.gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + 0)) = some (j0 + ((k - 1) * Lb + qp)) := by
  have hLb : 0 < Lb := by omega
  have hbnd : j0 + (k * Lb + 0) < (TRIO.gexp M j0 Lb d0 d1 n).length := by
    rw [TRIO.gexp_length hlen]
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  exact (par0_iff _ hbnd).mpr
    (TRIO.gexp_nextrel0_root hlen hk hk1 hqp hd0e ((par0_iff M (by omega)).mp h))

/-- The row-0 parent depends only on the columns up to the column itself. -/
theorem par0_take (M : Mat) {l i : Nat} (hi : i < l) : par (M.take l) 0 i = par M 0 i :=
  par_take M 0 i hi

/-- Before the last column, the row-0 parents after expansion are those of `M`. -/
theorem par0_expand_prefix (M : Mat) {n i : Nat} (hM : 2 ≤ M.length) (hn : 1 ≤ n)
    (hi : i < M.length - 1) : par (expand M n) 0 i = par M 0 i := by
  have h1 : (expand M n).take (M.length - 1) = M.take (M.length - 1) := by
    rw [expand_eq_oper M n hM]; exact TRIO.oper_take_prefix (by omega) hn (le_refl _)
  rw [← par0_take (expand M n) hi, h1, par0_take M hi]

/-! ## 展開の列の行 0 の親（コピーの領域） -/

theorem Anc0.trans {M : Mat} {a b c : Nat} (h1 : Anc0 M a b) (h2 : Anc0 M b c) : Anc0 M a c := by
  induction h2 with
  | refl => exact h1
  | step hp _ ih => exact Anc0.step hp ih

theorem anc0_climb {M : Mat} {t : Nat} (hs : ∀ a b, par M t b = some a → Anc0 M a b)
    {ok : Nat → Bool} : ∀ f q r, climb (par M t) ok f (some q) = some r → Anc0 M r q
  | 0, _, _, h => by simp [climb] at h
  | f + 1, q, r, h => by
    simp only [climb] at h
    split at h
    · cases h; exact Anc0.refl _
    · cases hq : par M t q with
      | none => rw [hq] at h; cases f <;> simp [climb] at h
      | some q' =>
        rw [hq] at h
        exact (anc0_climb hs f q' r h).trans (hs q' q hq)

/-- **The parent in any row is a row-0 ancestor.** -/
theorem anc0_of_par (M : Mat) : ∀ t a b, par M t b = some a → Anc0 M a b
  | 0, a, b, h => Anc0.step h (Anc0.refl a)
  | t + 1, a, b, h => by
    simp only [par] at h
    cases hq : par M t b with
    | none => rw [hq] at h; simp [climb] at h
    | some q =>
      rw [hq] at h
      exact (anc0_climb (anc0_of_par M t) (b + 1) q a h).trans (anc0_of_par M t q b hq)

theorem par0_some_of {M : Mat} {a b : Nat} (hab : a < b) (he : entry M 0 a < entry M 0 b) :
    ∃ p, par M 0 b = some p := by
  cases hp : par M 0 b with
  | some p => exact ⟨p, rfl⟩
  | none =>
    exfalso
    cases b with
    | zero => omega
    | succ c =>
      simp only [par, prev] at hp
      have := (climb_prev_none _ c (c + 1 + 1) (by omega)).mp hp a (by omega)
      simp at this; omega

/-- **Inside the copies (after the first copy root), row-0 parents stay in the copies.** -/
theorem par0_gexp_ge {M : Mat} {j0 Lb d0 d1 n c : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hA : Anc0 M j0 (j0 + Lb)) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hc1 : j0 + Lb < c) (hc2 : c < j0 + n * Lb) :
    ∃ p, par (TRIO.gexp M j0 Lb d0 d1 n) 0 c = some p ∧ j0 + Lb ≤ p := by
  obtain ⟨k, qb, hk, hqb, rfl⟩ := TRIO.gexp_pos_decomp (n := n) hLb (by omega) hc2
  have hk1 : 1 ≤ k := by
    rcases Nat.lt_or_ge k 1 with h | h
    · have : k = 0 := by omega
      subst this; simp at hc1; omega
    · exact h
  rcases Nat.eq_zero_or_pos qb with hq0 | hq0
  · -- a copy root `k ≥ 2`
    subst hq0
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · have : k = 1 := by omega
        subst this; simp at hc1
      · exact h
    obtain ⟨q, hq⟩ := par0_some_of (show j0 < j0 + Lb by omega)
      (anc0_interval hA (j0 + Lb) (by omega) (Nat.le_refl _))
    have hjq : j0 ≤ q := by
      obtain ⟨_, _, hbet⟩ := (par0_spec M).mp hq
      rcases Nat.lt_or_ge q j0 with h2 | h2
      · have h3 := hbet j0 h2 (by omega)
        have h4 := anc0_interval hA (j0 + Lb) (by omega) (Nat.le_refl _); omega
      · exact h2
    have hqlt : q < j0 + Lb := par_lt M 0 _ _ hq
    have hq' : par M 0 (j0 + Lb) = some (j0 + (q - j0)) := by rw [hq]; congr 1; omega
    refine ⟨_, par0_gexp_root hlen hk (by omega) (by omega) hd0e hq', ?_⟩
    have : Lb ≤ (k - 1) * Lb := by
      have := Nat.mul_le_mul_right Lb (show 1 ≤ k - 1 by omega); simpa using this
    omega
  · -- a non-root offset
    obtain ⟨pa, hpa⟩ := par0_some_of (show j0 < j0 + qb by omega)
      (anc0_interval hA (j0 + qb) (by omega) (by omega))
    have hge := par0_ge_of_anc hA (show j0 < j0 + qb by omega) (by omega) hpa
    have hlt := par_lt M 0 _ _ hpa
    have hpa' : par M 0 (j0 + qb) = some (j0 + (pa - j0)) := by rw [hpa]; congr 1; omega
    refine ⟨_, par0_gexp_mir hlen hk hqb hpa', ?_⟩
    have : Lb ≤ k * Lb := by
      have := Nat.mul_le_mul_right Lb hk1; simpa using this
    omega

/-- The data of an expansion with `t ≥ 1`: `M[n]` is the `gexp` with root `r`, block length `x - r`. -/
theorem expand_gexp_data (M : Mat) (n : Nat) (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht : 0 < TRIO.srow M (M.length - 1)) :
    ∃ d1, expand M n = TRIO.gexp M r (M.length - 1 - r)
      (entry M 0 (M.length - 1) - entry M 0 r) d1 n ∧
      r + (M.length - 1 - r) + 1 = M.length ∧ 0 < M.length - 1 - r ∧
      Anc0 M r (r + (M.length - 1 - r)) ∧
      entry M 0 (r + (M.length - 1 - r)) = entry M 0 r + (entry M 0 (M.length - 1) - entry M 0 r) := by
  have hrx := par_lt M _ _ _ hr
  have hA := anc0_of_par M _ _ _ hr
  have hxr : r + (M.length - 1 - r) = M.length - 1 := by omega
  have he := anc0_interval hA (M.length - 1) hrx (Nat.le_refl _)
  refine ⟨if 1 < TRIO.srow M (M.length - 1) then TRIO.entry M 1 (M.length - 1) - TRIO.entry M 1 r else 0,
    ?_, by omega, by omega, by rw [hxr]; exact hA, by rw [hxr]; omega⟩
  rw [expand_eq_gexp M n hM hz hr, if_pos ht]
  rfl

/-- **Before the last column, children are unchanged** (`n ≥ 2`, `t ≥ 1`). -/
theorem children_expand_lt (M : Mat) (n : Nat) (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht : 0 < TRIO.srow M (M.length - 1)) (hn : 2 ≤ n) {h : Nat} (hh : h < M.length - 1) :
    children (expand M n) h = children M h := by
  obtain ⟨d1, heq, hlen, hLb, hA, hd0e⟩ := expand_gexp_data M n hM hz hr ht
  generalize hL : M.length - 1 - r = L at heq hlen hLb hA hd0e
  have hlen' : (expand M n).length = r + n * L := by rw [heq]; exact TRIO.gexp_length hlen
  have hnL : L ≤ (n - 1) * L := by
    have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simpa using this
  have hnL2 : n * L = (n - 1) * L + L := by
    rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  unfold children
  rw [hlen', show r + n * L = M.length + (r + n * L - M.length) by omega, List.range_add,
    List.filter_append]
  have h2 : List.filter (fun i => decide (par (expand M n) 0 i = some h))
      (List.map (fun x => M.length + x) (List.range (r + n * L - M.length))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    have hc'' := List.mem_range.mp hc'
    rw [heq]
    obtain ⟨p, hp, hpx⟩ := par0_gexp_ge (d1 := d1) (n := n) hlen hLb hA hd0e
      (c := M.length + c') (by omega) (by omega)
    rw [hp]; simp; omega
  rw [h2, List.append_nil]
  apply List.filter_congr
  intro c hc
  have hc' := List.mem_range.mp hc
  rcases Nat.lt_or_ge c (M.length - 1) with h3 | h3
  · rw [par0_expand_prefix M hM (by omega) h3]
  · obtain ⟨q, hq⟩ := par0_some_of (show r < r + L by omega)
      (anc0_interval hA (r + L) (by omega) (Nat.le_refl _))
    have hrq : r ≤ q := by
      obtain ⟨_, _, hbet⟩ := (par0_spec M).mp hq
      rcases Nat.lt_or_ge q r with h4 | h4
      · have h5 := hbet r h4 (by omega)
        have h6 := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      · exact h4
    have hqx := par_lt M 0 _ _ hq
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [hq]; congr 1; omega
    have hroot := par0_gexp_root (d1 := d1) (n := n) hlen (k := 1) (by omega) (Nat.le_refl _)
      (by omega) hd0e hq'
    have hroot' : par (TRIO.gexp M r L (entry M 0 (M.length - 1) - entry M 0 r) d1 n) 0 (r + L) =
        some q := by
      have := hroot
      rw [show r + (1 * L + 0) = r + L by omega, show r + ((1 - 1) * L + (q - r)) = q by omega] at this
      exact this
    rw [show c = r + L by omega, heq, hroot', hq]

end Ytosk
