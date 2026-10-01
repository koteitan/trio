/-
**n = 0: M[0] = M.take r の根の値は M の根の値より真に小さい。**

- 根の列 k（列 (0,0,0)）の前で切ると、値は M と一致する（`take_root_agree`）。
  k より前の列の子・上げ・のりしろはすべて k より前にある（k の行 0 は 0 なので、k は誰の子孫でもない）。
- したがって k が x の根（x の祖先で、k より後ろに根がない）なら、根の値は o(k) ≠ 0 の項が消えて真に下がる
  （`root_take_root`）。t = 1・q ≠ r で r が根のとき（R = r）は無条件（`t1_n0_root`）。
-/
import Ytosk.V3N1T1

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 根の列の前で切る -/

section
variable {M : Mat} {k : Nat} (hk : col M k = (0, 0, 0)) (hkl : k < M.length)
include hk hkl

omit hkl in
theorem e0_rootcol : entry M 0 k = 0 := by
  rw [col_eq_entries] at hk; simp only [Prod.mk.injEq] at hk; exact hk.1

/-- A column before a root column is not an ancestor of anything at or after it. -/
theorem not_anc_past_root {i c : Nat} (hi : i < k) (hkc : k ≤ c) : ¬ Anc0 M i c := by
  intro hA
  have h1 := anc_between hA k (by omega) hkc
  have := anc0_e0_lt h1 (by omega)
  rw [e0_rootcol hk] at this; omega

omit hkl in
theorem children_lt_root {i c : Nat} (hi : i < k) (hc : c ∈ children M i) : c < k := by
  have hcl := (mem_children hc).2
  by_contra h
  exact not_anc_past_root hk (by omega) hi (by omega)
    (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl i))

theorem upg_prev_root (hk0 : 0 < k) : upg M (k - 1) = none := by
  unfold upg
  split
  · rfl
  · cases hp : par M 1 (k - 1) with
    | none => rfl
    | some m =>
      simp only
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1]
      have hcolne : col M k ≠ (entry M 0 m + 1, entry M 1 (k - 1), entry M 2 m + 1) := by
        rw [hk]; intro h; simp only [Prod.mk.injEq] at h; omega
      rw [if_neg (fun h => hcolne h.2)]
      cases hq : par M 0 (k - 1) with
      | none => exact climb_none _ _ _
      | some q =>
        have hqk := par_lt M 0 (k - 1) q hq
        rw [Option.eq_none_iff_forall_ne_some]
        intro a ha
        have := ((climb_chain_iff (par M 0) _ (par_lt M 0) a k q (by omega)).mp ha).2.1
        simp only [decide_eq_true_eq] at this
        rw [e0_rootcol hk] at this; omega

theorem upg_take_root {i : Nat} (hi : i < k) : upg (M.take k) i = upg M i := by
  rcases Nat.lt_or_ge (i + 1) k with h | h
  · exact upg_take M h
  · have hik : i = k - 1 := by omega
    subst hik
    rw [upg_take_last M (by omega) (by omega), upg_prev_root hk hkl (by omega)]

theorem upg_lt_root {j c : Nat} (hu : upg M j = some c) (hc : c < k) : j + 1 < k := by
  by_contra h
  obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
  rcases hcase with h' | ⟨hA, hcj⟩
  · omega
  · rcases Nat.eq_or_lt_of_le (show k ≤ j + 1 by omega) with h1 | h1
    · -- `j = k - 1`
      have hj : j = k - 1 := by omega
      rw [hj, upg_prev_root hk hkl (by omega)] at hu; cases hu
    · exact not_anc_past_root hk hkl hc (by omega) hA

theorem isUpg_take_root {c : Nat} (hc : c < k) : isUpg (M.take k) c = isUpg M c := by
  apply Bool.eq_iff_iff.mpr
  rw [isUpg_take M (by omega) c]
  unfold isUpg
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hu⟩
    exact ⟨j, List.mem_range.mpr (by omega), by simp [hu]⟩
  · rintro ⟨j, _, hu⟩
    have hu' : upg M j = some c := by simpa using hu
    exact ⟨j, upg_lt_root hk hkl hu' hc, hu'⟩

omit hkl in
theorem children_take_root {i : Nat} (hi : i < k) : children (M.take k) i = children M i := by
  rw [children_take, List.filter_eq_self]
  intro c hc; simp only [decide_eq_true_eq]; exact children_lt_root hk hi hc

omit hkl in
theorem topped_take_root {c : Nat} (hc : c < k) : topped (M.take k) c = topped M c := by
  unfold topped
  rw [children_take_root hk hc]
  cases hl : (children M c).getLast? with
  | none => rfl
  | some d =>
    have hd : d ∈ children M c := List.mem_of_getLast? hl
    simp only
    rw [col_take M (children_lt_root hk hc hd), bump_take M hc]

theorem cnt_take_root {ρ : Valn} {i c : Nat} (hi : i < k) (hc : c ∈ children M i) :
    cnt (M.take k) ρ i c = cnt M ρ i c := by
  have hck := children_lt_root hk hi hc
  unfold cnt
  rw [col_take M hck, bump_take M hi, isUpg_take_root hk hkl hck, topped_take_root hk hck]

theorem counted_take_root {i c : Nat} (hi : i < k) (hc : c ∈ children M i) :
    Counted (M.take k) i c ↔ Counted M i c := by
  have hck := children_lt_root hk hi hc
  unfold Counted
  rw [col_take M hck, bump_take M hi, isUpg_take_root hk hkl hck, topped_take_root hk hck]

theorem oRhs_take_root {ρ : Valn} {i : Nat} (hi : i < k) : oRhs (M.take k) ρ i = oRhs M ρ i := by
  unfold oRhs
  rw [children_take_root hk hi, List.map_congr_left (fun c hc => cnt_take_root hk hkl hi hc)]

theorem vRhs_take_root {ρ : Valn} {i : Nat} (hi : i < k) : vRhs (M.take k) ρ i = vRhs M ρ i := by
  unfold vRhs
  rw [entry_take M 1 hi, entry_take M 2 hi, par_take M 1 i hi, upg_take_root hk hkl hi,
    children_take_root hk hi]
  have hbt : ∀ j ∈ children M i, bumpTerm (M.take k) ρ i j = bumpTerm M ρ i j := by
    intro j hj
    have hjk := children_lt_root hk hi hj
    unfold bumpTerm
    rw [col_take M hjk, bump_take M hi, children_take_root hk hjk]
  rw [List.map_congr_left hbt]

/-- **Before a root column, `M.take k` has the values of `M`.** -/
theorem take_root_agree {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ)
    (hC' : Cons (M.take k) ρ') (hR' : Rk (M.take k) rk') :
    ∀ i, i < k → ρ'.o i = ρ.o i ∧ ρ'.v i = ρ.v i := by
  have hlen : (M.take k).length = k := by rw [List.length_take]; omega
  intro i hi
  have h := agree_off_at (fun _ _ => False) hC hC' hR' (by rw [hlen]; omega)
    (fun i hi _ => oRhs_take_root hk hkl (by omega))
    (fun i hi _ => vRhs_take_root hk hkl (by omega))
    (fun _ _ _ => ⟨id, fun _ _ _ h => h⟩)
    (fun _ _ _ _ => ⟨fun _ _ h => h, fun _ _ _ h => h, fun _ _ _ _ _ _ h => h⟩) i (by omega)
  exact ⟨h.1 id, h.2 id⟩

/-- The ranking of `M` ranks the prefix before a root column. -/
theorem rk_take_root {rk : Bool → Nat → Nat} (hR : Rk M rk) : Rk (M.take k) rk :=
  rk_take (by omega) hR (fun i c hi hc hcnt => by
    rw [children_take_root hk hi] at hc
    exact (counted_take_root hk hkl hi hc).mp hcnt)

end

/-! ## 和の末尾の 0 -/

theorem sumN_range_tail (f : Nat → T) {n : Nat} :
    ∀ m, n ≤ m → (∀ i, i < m → isOT (f i) = true) → (∀ i, n ≤ i → i < m → f i = z) →
      sumN ((List.range m).map f) = sumN ((List.range n).map f)
  | 0, h, _, _ => by rw [show n = 0 by omega]
  | m + 1, h, hot, hz => by
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · rw [List.range_succ, List.map_append, List.map_singleton, hz m (by omega) (by omega),
        sumN_snoc_z (fun t ht => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact hot i (by have := List.mem_range.mp hi; omega))]
      exact sumN_range_tail f m (by omega) (fun i hi => hot i (by omega)) (fun i h1 h2 => hz i h1 (by omega))

/-- **Cutting before the last root lowers the root value.** -/
theorem root_take_root {M : Mat} {k : Nat} (hk : col M k = (0, 0, 0)) (hkl : k < M.length)
    (hlast : ∀ j, k < j → j < M.length → col M j ≠ (0, 0, 0))
    {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take k) ρ') (hR' : Rk (M.take k) rk') :
    isOT (root (M.take k) ρ') = true ∧ root (M.take k) ρ' < root M ρ := by
  classical
  have hlen : (M.take k).length = k := by rw [List.length_take]; omega
  have hag := take_root_agree hk hkl hC hC' hR'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hot : ∀ i, i < M.length → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i hi
    · rfl
  have hroot' : root (M.take k) ρ' = sumN ((List.range k).map f) := by
    unfold root
    rw [hlen]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hik := List.mem_range.mp hi
    rw [col_take M hik, (hag i hik).1]
  have hroot : root M ρ = sumN ((List.range (k + 1)).map f) :=
    sumN_range_tail f _ (by omega) hot (fun i h1 h2 => by
      simp only [hf]; rw [if_neg (hlast i (by omega) h2)])
  have hl : ∀ t ∈ (List.range k).map f, isOT t = true := by
    intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hot i (by have := List.mem_range.mp hi; omega)
  refine ⟨by rw [hroot']; exact isOT_sumN _ hl, ?_⟩
  rw [hroot', hroot, List.range_succ, List.map_append, List.map_singleton]
  have hfk : f k = ρ.o k := by simp only [hf]; rw [if_pos hk]
  rw [hfk]
  apply sumN_lt_snoc hl (hG.ot_o k hkl) (le_refl _)
  obtain ⟨s0, y0, h0⟩ := o_psi_form hC hkl
  rw [h0]; exact T.z_lt_psi _ _ _

/-! ## t = 1・q ≠ r で r が根の場合（無条件） -/

theorem gexp_zero_eq (M : Mat) (r L d0 : Nat) : TRIO.gexp M r L d0 0 0 = M.take r := by
  unfold TRIO.gexp TRIO.gcopies; simp

/-- **`t = 1`, `n = 0`, `r` a root**: `M[0] = M.take r` has a standard root value below that of `M`.
Only the shape (`r` an ancestor of the last column) is used. -/
theorem t1_n0_root {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (h1 : par M 1 (r + L) = some r) (hroot : col M r = (0, 0, 0))
    {ρ : Valn} {rkM : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 0) ρN ∧ Rk (TRIO.gexp M r L d0 0 0) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 0) ρN) = true ∧ root (TRIO.gexp M r L d0 0 0) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrl : r < M.length := by omega
  have hRk := rk_take_root hroot hrl hRM
  rw [gexp_zero_eq]
  refine ⟨_, rkM, cons_of_rk hRk, hRk, root_take_root hroot hrl ?_ hC hG (cons_of_rk hRk) hRk⟩
  intro j hrj hj hcj
  have hAj := anc_between hA j (by omega) (by omega)
  have := anc0_e0_lt hAj (by omega)
  rw [e0_rootcol hcj] at this; omega

/-! ## 一般の場合: 1 列ずつ落とす鎖 -/

/-- The value hypotheses of the drop lemma `drop_all` for dropping the last column `x` of `N`
(with the valuation `σ` of `N` and `σ′` of `N.take x`), and the structural invariants `UAT`・`UAB`
of `N` (the others pass to prefixes). -/
structure DropHyp (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  uat : UAT N
  uab : UAB N
  g : Good3 N σ
  vs : VSmall N σ
  fc : FrameClosed N σ
  fo : FrameOT N σ
  argT : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (N.take x) i = Lc ++ [cs] →
    ∀ s y, σ'.o cs = psi s y z → ¬ lt s (σ.v i) = true →
    ∀ g ∈ comps (σ.v i) y, g ≤ step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y z
  kd : BumpKidsDec N σ
  td : BumpTermDec N σ
  ab : BumpAbs N σ
  ws : BumpWeakShape N σ
  vst : BumpVSmallTake N x σ σ'
  ua : UpgAbs N σ

/-- **Dropping the last column does not raise the root value** (weak form of `root_take_lt`). -/
theorem root_take_le {N : Mat} {x : Nat} (hx : x + 1 = N.length) {σ σ' : Valn} (hG : Good3 N σ)
    (hot' : ∀ i, i < x → isOT (σ'.o i) = true) (hle : ∀ i, i < x → σ'.o i ≤ σ.o i) :
    isOT (root (N.take x) σ') = true ∧ root (N.take x) σ' ≤ root N σ := by
  classical
  have hlenT : (N.take x).length = x := by rw [List.length_take]; omega
  set f' : Nat → T := fun i => if col N i = (0, 0, 0) then σ'.o i else z with hf'
  set f : Nat → T := fun i => if col N i = (0, 0, 0) then σ.o i else z with hf
  have hroot' : root (N.take x) σ' = sumN ((List.range x).map f') := by
    unfold root
    rw [hlenT]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [col_take N (List.mem_range.mp hi)]
  have hroot : root N σ = sumN ((List.range x).map f ++ [f x]) := by
    unfold root
    rw [← hx, List.range_succ, List.map_append, List.map_singleton]
  have hl' : ∀ t ∈ (List.range x).map f', isOT t = true := by
    intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    simp only [hf']; split
    · exact hot' i (List.mem_range.mp hi)
    · rfl
  have hotf : ∀ i, i < x + 1 → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i (by omega)
    · rfl
  have hl : ∀ t ∈ (List.range x).map f, isOT t = true := by
    intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hotf i (by have := List.mem_range.mp hi; omega)
  refine ⟨by rw [hroot']; exact isOT_sumN _ hl', ?_⟩
  rw [hroot', hroot]
  have h1 : sumN ((List.range x).map f') ≤ sumN ((List.range x).map f) :=
    sumN_le2 (forall2_map_le (fun i hi => by
      simp only [hf', hf]; split
      · exact hle i (List.mem_range.mp hi)
      · exact le_refl _)) hl' hl
  apply le_trans h1
  rw [sumN_snoc, sf_ot (isOT_add (isOT_sumN _ hl) (hotf x (by omega)))]
  have := add_le_add_left (sumN ((List.range x).map f)) (z_le (f x))
  rwa [add_z_right] at this

/-- **One step of the chain**: the drop lemma on `N` gives `root(N.take x) ≤ root(N)`. -/
theorem drop_root_le {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hD : DropHyp N x σ σ')
    (hC : Cons N σ) (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) :
    isOT (root (N.take x) σ') = true ∧ root (N.take x) σ' ≤ root N σ := by
  have hdrop := drop_all hx hR0 hZ2 hSD hZ1 hD.uat hD.uab hC hD.g hC' hRk' hD.vs hD.fc hD.fo hD.argT
    (bump_drop hx hR0 hZ2 hSD hZ1 hD.uat hD.uab hC hD.g hC' hRk' hD.vs hD.kd hD.td hD.ab hD.ws hD.vst)
    (fun i k W _ hu hv hW => hD.ua i k W hu hv hW)
  exact root_take_le hx hD.g (fun i hi => (hdrop i hi).1.2.1) (fun i hi => (hdrop i hi).1.le)

theorem root_congr {N : Mat} {σ₁ σ₂ : Valn} (h : ∀ i, i < N.length → σ₁.o i = σ₂.o i) :
    root N σ₁ = root N σ₂ := by
  unfold root
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

end Ytosk
