/-
**3 行・t = 0（x の行 1 が 0、r = P_0(x) = q）: n = 1 と n = 0。**

- n = 1（M[1] = M.take x）: 落とす補題は型によらないので、t = 1 と同じく `root_take_lt` と D の狭義性 `dep_strict` で。
  dep_strict の t = 1 専用だった仮定は t = 0 でも構造から出る: x の行 2 は 0（R12）、x は根でない（親 r）、
  v(x) は D に入らない（行 1 が 0 なので D の v の辺はどれも x から出ない）（`t0_n1`）。
- n = 0（M[0] = M.take r）: 接頭辞を 1 列ずつ落とす鎖（各段の仮定 `DropRes`）と、最後の段 M → M.take x の狭義性
  （`t0_n0r`）。
-/
import Ytosk.V3DropPres

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`t = 0`, `n = 1`**: `M[1] = M.take x` has a value, standard at the root and below the root value of
`M`. -/
theorem t0_n1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {ζ μ : T} (hVL : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ ζ μ i) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 1) ρN ∧ Rk (TRIO.gexp M r L d0 0 1) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 1) ρN) = true ∧ root (TRIO.gexp M r L d0 0 1) ρN < root M ρ := by
  have hx2 : entry M 2 (r + L) = 0 := hR12 _ he1
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS)
    hUA
  have hnx : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar h1 _ _ => exact h1 he1
    | vupg h1 _ _ _ => exact h1 he1
    | vbump h1 _ _ _ _ _ => exact h1 he1
  have hD := dep_strict (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx hVL
  refine ⟨drop1 M (r + L) rkM, rkM, ?_⟩
  rw [gexp_one_eq hlen]
  refine ⟨hC1, hRk1, root_take_lt (by omega) hR01 hR12 h00 hC hG
    (fun i hi => (hdrop i hi).1.2.1) (fun i hi => (hdrop i hi).1.le) ?_⟩
  intro R hR hRA _
  exact hD true R (dep_anc_x hUAT hZ2 hR12 hBE (by omega) hx2 hRA) hR

/-- **`t = 0`, `n = 0`**: `M[0] = M.take r`, through the chain of one-column drops (with the remaining
hypotheses `DropRes` of the drops `M.take (j + 1) → M.take j`, `r ≤ j < x`). -/
theorem t0_n0r {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {ζ μ : T} (hVL : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ ζ μ i)
    (hres : ∀ j, r ≤ j → j < r + L →
      DropRes (M.take (j + 1)) j (drop1 M (j + 1) rkM) (drop1 M j rkM)) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 0) ρN ∧ Rk (TRIO.gexp M r L d0 0 0) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 0) ρN) = true ∧ root (TRIO.gexp M r L d0 0 0) ρN < root M ρ := by
  have hr : r < r + L := par_lt M 0 (r + L) r hp
  have hlj : ∀ j, j ≤ r + L → (M.take (j + 1)).length = j + 1 := by
    intro j hj; rw [List.length_take]; omega
  have hUATt := fun k => UAT_take hR0 hZ2 hSD hZ1 hUAB k
  -- the ranking of every prefix
  have hRkj : ∀ m j, r + L - j ≤ m → j ≤ r + L → Rk (M.take j) rkM := by
    intro m
    induction m with
    | zero =>
      intro j hm hj
      have hjx : j = r + L := by omega
      subst hjx
      exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
    | succ m ih =>
      intro j hm hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
      · have hN := ih (j + 1) (by omega) hjx
        have hcnt := counted_take_last (M := M.take (j + 1)) (by rw [hlj j (by omega)]; omega)
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
        rw [hlj j (by omega), show j + 1 - 1 = j by omega] at hcnt
        have := rk_take (by rw [hlj j (by omega)]; omega) hN hcnt
        rwa [take_take_succ] at this
  have hRk : ∀ j, j ≤ r + L → Rk (M.take j) rkM := fun j h => hRkj _ j (le_refl _) h
  have hCj : ∀ j, j ≤ r + L → Cons (M.take j) (drop1 M j rkM) := fun j h => cons_of_rk (hRk j h)
  -- the invariants of `M.take x` and down the chain
  have hIx : ValInv (M.take (r + L)) (drop1 M (r + L) rkM) :=
    drop_pres (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC ⟨hG, hVS, hF, hFO, hKD, hTD⟩
      ⟨hArgT, hVSt, hWS, hUA, hAbs⟩ (hCj _ (le_refl _)) (hRk _ (le_refl _))
  have hIj : ∀ m j, r + L - j ≤ m → r ≤ j → j ≤ r + L → ValInv (M.take j) (drop1 M j rkM) := by
    intro m
    induction m with
    | zero =>
      intro j hm _ hj
      have hjx : j = r + L := by omega
      subst hjx; exact hIx
    | succ m ih =>
      intro j hm hrj hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact hIx
      · have hN := ih (j + 1) (by omega) (by omega) hjx
        have := drop_pres (N := M.take (j + 1)) (x := j) (hlj j (by omega)).symm
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
          (UAB_take hUAB _) (hCj _ hjx) hN (hres j hrj hjx)
          (by rw [take_take_succ]; exact hCj j (by omega))
          (by rw [take_take_succ]; exact hRk j (by omega))
        rwa [take_take_succ] at this
  -- one step of the chain
  have hone : ∀ j, r ≤ j → j < r + L →
      isOT (root (M.take j) (drop1 M j rkM)) = true ∧
        root (M.take j) (drop1 M j rkM) ≤ root (M.take (j + 1)) (drop1 M (j + 1) rkM) := by
    intro j hrj hjx
    have h := drop_root_le (N := M.take (j + 1)) (x := j) (hlj j (by omega)).symm
      (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _)
      ((DropHypV.of (hIj _ (j + 1) (le_refl _) (by omega) hjx) (hres j hrj hjx)).toDropHyp
        (hUATt _) (UAB_take hUAB _))
      (hCj (j + 1) (by omega))
      (by rw [take_take_succ]; exact hCj j (by omega))
      (by rw [take_take_succ]; exact hRk j (by omega))
    rwa [take_take_succ] at h
  have hchain : ∀ m, r + m ≤ r + L →
      root (M.take r) (drop1 M r rkM) ≤ root (M.take (r + m)) (drop1 M (r + m) rkM) := by
    intro m
    induction m with
    | zero => intro _; exact le_refl _
    | succ m ih =>
      intro hm
      exact le_trans (ih (by omega)) (hone (r + m) (by omega) (by omega)).2
  -- the last step is strict
  obtain ⟨ρ1, rk1, hC1, hR1, _, hlt1⟩ := t0_n1 (d0 := d0) hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01
    h00 hp he1 hC hG hRM hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA hVL
  rw [gexp_one_eq hlen] at hC1 hR1 hlt1
  have heq : root (M.take (r + L)) ρ1 = root (M.take (r + L)) (drop1 M (r + L) rkM) :=
    root_congr (fun i hi => (cons_unique hC1 (hCj (r + L) (le_refl _)) hR1 i hi).1)
  rw [heq] at hlt1
  rw [gexp_zero_eq]
  exact ⟨drop1 M r rkM, rkM, hCj r (by omega), hRk r (by omega),
    (hone r (le_refl _) hr).1, lt_of_le_of_lt (hchain L (le_refl _)) hlt1⟩

end Ytosk
