/-
**n = 1: M[1] = M.take x の根の値は M の根の値より真に小さい。**

- 一般形（`root_take_lt`、型によらない）: 最後の列 x を落とした M′ = M.take x で、
  各列の o′ ≤ o（落とす補題 `drop_all` の結論から）、x の根の祖先 R で o′(R) < o(R) なら、
  根の値の和 root(M′) < root(M)。R より後ろの列は根でない（`root_t1`）ので、和の最後の 0 でない項が
  真に下がる。x 自身が根なら、o(x) ≠ 0 の項が消える。
- t = 1・q ≠ r（`t1_n1`）: R での狭義性は `o_r_strict` と同じ D の帰納法 `dep_strict` から。
  仮定は `t1_main_strict` の仮定の部分集合（枠の条件 hW・hLo、r の値 hμr・hro、根の値 hsM・hpM は要らない）。
-/
import Ytosk.V3StrictR

namespace Ytosk

open T

/-! ## 和の最後の 0 でない項が下がる -/

/-- **A sum over `range n` drops** when every term is weakly smaller, the term at `R` is strictly
smaller, and all later terms are `0`. -/
theorem sumN_range_lt (f' f : Nat → T) {R : Nat} : ∀ n, R < n →
    (∀ i, i < n → isOT (f' i) = true) → (∀ i, i < n → isOT (f i) = true) →
    (∀ i, i < n → f' i ≤ f i) → f' R < f R → (∀ i, R < i → i < n → f' i = z ∧ f i = z) →
    sumN ((List.range n).map f') < sumN ((List.range n).map f)
  | 0, h, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, hRn, hot', hot, hle, hlt, hz => by
    have hl' : ∀ t ∈ (List.range n).map f', isOT t = true := by
      intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact hot' i (by have := List.mem_range.mp hi; omega)
    have hl : ∀ t ∈ (List.range n).map f, isOT t = true := by
      intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact hot i (by have := List.mem_range.mp hi; omega)
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
    by_cases hR : R = n
    · subst hR
      apply sumN_snoc_lt hl' hl (hot' R (by omega)) (hot R (by omega)) _ hlt
      exact sumN_le2 (forall2_map_le (fun i hi => hle i (by have := List.mem_range.mp hi; omega))) hl' hl
    · obtain ⟨h1, h2⟩ := hz n (by omega) (by omega)
      rw [h1, h2, sumN_snoc_z hl', sumN_snoc_z hl]
      exact sumN_range_lt f' f n (by omega) (fun i hi => hot' i (by omega)) (fun i hi => hot i (by omega))
        (fun i hi => hle i (by omega)) hlt (fun i h1 h2 => hz i h1 (by omega))

/-! ## 一般形: 根の値の和 -/

/-- **The root value of `M.take x` is standard and below that of `M`** (any type of the last column),
from the drop lemma's `o′ ≤ o` and the strict drop at the root above `x`. -/
theorem root_take_lt {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    {ρ ρ' : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hot' : ∀ i, i < x → isOT (ρ'.o i) = true) (hle : ∀ i, i < x → ρ'.o i ≤ ρ.o i)
    (hstrict : ∀ R, R < x → Anc0 M R x → col M R = (0, 0, 0) → ρ'.o R < ρ.o R) :
    isOT (root (M.take x) ρ') = true ∧ root (M.take x) ρ' < root M ρ := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  classical
  set f' : Nat → T := fun i => if col M i = (0, 0, 0) then ρ'.o i else z with hf'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hroot' : root (M.take x) ρ' = sumN ((List.range x).map f') := by
    unfold root
    rw [hlenT]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [col_take M (List.mem_range.mp hi)]
  have hroot : root M ρ = sumN ((List.range x).map f ++ [f x]) := by
    unfold root
    rw [← hx, List.range_succ, List.map_append, List.map_singleton]
  have hot'f : ∀ i, i < x → isOT (f' i) = true := by
    intro i hi; simp only [hf']; split
    · exact hot' i hi
    · rfl
  have hotf : ∀ i, i < x + 1 → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i (by omega)
    · rfl
  have hlef : ∀ i, i < x → f' i ≤ f i := by
    intro i hi; simp only [hf', hf]; split
    · exact hle i hi
    · exact le_refl _
  have hl' : ∀ t ∈ (List.range x).map f', isOT t = true := by
    intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact hot'f i (List.mem_range.mp hi)
  have hl : ∀ t ∈ (List.range x).map f, isOT t = true := by
    intro t ht; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hotf i (by have := List.mem_range.mp hi; omega)
  refine ⟨by rw [hroot']; exact isOT_sumN _ hl', ?_⟩
  rw [hroot', hroot]
  obtain ⟨R, hRA, hR0, hRl⟩ := root_t1 hR01 hR12 h00 x
  by_cases hRx : R = x
  · -- `x` is a root: its term disappears
    subst hRx
    have hfx : f R = ρ.o R := by simp only [hf]; rw [if_pos hR0]
    rw [hfx]
    apply sumN_lt_snoc hl (hG.ot_o R (by omega))
      (sumN_le2 (forall2_map_le (fun i hi => hlef i (List.mem_range.mp hi))) hl' hl)
    obtain ⟨s0, y0, h0⟩ := o_psi_form hC (show R < M.length by omega)
    rw [h0]; exact T.z_lt_psi _ _ _
  · have hRx' : R < x := lt_of_le_of_ne hRA.le hRx
    have hnr : ∀ j, R < j → j ≤ x → col M j ≠ (0, 0, 0) := by
      intro j h1 h2 hc
      apply hRl j h1 h2
      rw [col_eq_entries] at hc
      simp only [Prod.mk.injEq] at hc
      exact hc.1
    have hfx : f x = z := by simp only [hf]; rw [if_neg (hnr x hRx' (le_refl _))]
    rw [hfx, sumN_snoc_z hl]
    apply sumN_range_lt f' f x hRx' hot'f (fun i hi => hotf i (by omega)) hlef
    · simp only [hf', hf]; rw [if_pos hR0, if_pos hR0]; exact hstrict R hRx' hRA hR0
    · intro i h1 h2
      have hn := hnr i h1 (by omega)
      simp only [hf', hf]; exact ⟨if_neg hn, if_neg hn⟩

/-! ## t = 1・q ≠ r の n = 1 -/

/-- **`t = 1`, `q ≠ r`, `n = 1`**: `M[1] = M.take x` has a value, standard at the root and below the
root value of `M`. -/
theorem t1_n1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbs M ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {ζ μ : T} (hVL : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ ζ μ i) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 1) ρN ∧ Rk (TRIO.gexp M r L d0 0 1) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 1) ρN) = true ∧ root (TRIO.gexp M r L d0 0 1) ρN < root M ρ := by
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS)
    hUA
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hr : r < r + L := par_lt M 1 (r + L) r h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hnx : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact v_r_not_chg (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hA (by omega) hqr
        (hpath_of_par1 h1 hA (by omega)) (depX_chgX hdm)
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  have hD := dep_strict (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hq hnx hVL
  refine ⟨drop1 M (r + L) rkM, rkM, ?_⟩
  rw [gexp_one_eq hlen]
  refine ⟨hC1, hRk1, root_take_lt (by omega) hR01 hR12 h00 hC hG
    (fun i hi => (hdrop i hi).1.2.1) (fun i hi => (hdrop i hi).1.le) ?_⟩
  intro R hR hRA _
  exact hD true R (dep_anc_x hUAT hZ2 hR12 hBE (by omega) hx2 hRA) hR

end Ytosk
