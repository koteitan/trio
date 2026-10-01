/-
**3 行・t = 1・q = r: n = 1 と n = 0。**

t1（q ≠ r）の `t1_n1`・`t1_n0`・`t1_n0r` と同じ組み立てで、R での狭義性を `dep_strict0`（VLocal なし）と
`qr_dep`（v(r) は D でない）から出す。
- n = 1（`qr_n1`）: M[1] = M.take x の根の値は M の根の値より小さい（`root_take_lt`）。
- n = 0（`qr_n0`）: M.take r から M.take x まで 1 列ずつ落とす鎖（`drop_root_le`）と n = 1。
- `qr_n0r`: 鎖の各段の仮定を残りの形 `DropRes` だけにしたもの（値の不変条件は `drop_pres` で運ぶ）。
-/
import Ytosk.V3QRFinal3
import Ytosk.V3DropPres

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`t = 1`, `q = r`, `n = 1`.** -/
theorem qr_n1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ) :
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
  have hdep := qr_dep (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hnx : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact hdep.2.1 hdm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hq hnx
  refine ⟨drop1 M (r + L) rkM, rkM, ?_⟩
  rw [gexp_one_eq hlen]
  refine ⟨hC1, hRk1, root_take_lt (by omega) hR01 hR12 h00 hC hG
    (fun i hi => (hdrop i hi).1.2.1) (fun i hi => (hdrop i hi).1.le) ?_⟩
  intro R hR hRA _
  exact hD true R (dep_anc_x hUAT hZ2 hR12 hBE (by omega) hx2 hRA) hR

/-- **`t = 1`, `q = r`, `n = 0`**, given the drop lemma's hypotheses on the prefixes
`M.take (j + 1)` (`r ≤ j < x`): `root(M.take r) ≤ … ≤ root(M.take x) < root(M)`. -/
theorem qr_n0 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    (hstep : ∀ j, r ≤ j → j < r + L →
      DropHyp (M.take (j + 1)) j (drop1 M (j + 1) rkM) (drop1 M j rkM)) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 0) ρN ∧ Rk (TRIO.gexp M r L d0 0 0) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 0) ρN) = true ∧ root (TRIO.gexp M r L d0 0 0) ρN < root M ρ := by
  have hr : r < r + L := par_lt M 1 (r + L) r h1
  have hlj : ∀ j, j ≤ r + L → (M.take (j + 1)).length = j + 1 := by
    intro j hj; rw [List.length_take]; omega
  -- the ranking of every prefix
  have hRkj : ∀ m j, r + L - j ≤ m → r ≤ j → j ≤ r + L → Rk (M.take j) rkM := by
    intro m
    induction m with
    | zero =>
      intro j hm _ hj
      have hjx : j = r + L := by omega
      subst hjx
      exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
    | succ m ih =>
      intro j hm hrj hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
      · have hN := ih (j + 1) (by omega) (by omega) hjx
        have hcnt := counted_take_last (M := M.take (j + 1)) (by rw [hlj j (by omega)]; omega)
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hstep j hrj hjx).uat
        rw [hlj j (by omega), show j + 1 - 1 = j by omega] at hcnt
        have := rk_take (by rw [hlj j (by omega)]; omega) hN hcnt
        rwa [take_take_succ] at this
  have hRk : ∀ j, r ≤ j → j ≤ r + L → Rk (M.take j) rkM := fun j h1 h2 => hRkj _ j (le_refl _) h1 h2
  have hCj : ∀ j, r ≤ j → j ≤ r + L → Cons (M.take j) (drop1 M j rkM) :=
    fun j h1 h2 => cons_of_rk (hRk j h1 h2)
  -- one step
  have hone : ∀ j, r ≤ j → j < r + L →
      isOT (root (M.take j) (drop1 M j rkM)) = true ∧
        root (M.take j) (drop1 M j rkM) ≤ root (M.take (j + 1)) (drop1 M (j + 1) rkM) := by
    intro j hrj hjx
    have h := drop_root_le (N := M.take (j + 1)) (x := j) (hlj j (by omega)).symm
      (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hstep j hrj hjx)
      (hCj (j + 1) (by omega) (by omega))
      (by rw [take_take_succ]; exact hCj j hrj (by omega))
      (by rw [take_take_succ]; exact hRk j hrj (by omega))
    rwa [take_take_succ] at h
  -- the chain
  have hchain : ∀ m, r + m ≤ r + L →
      root (M.take r) (drop1 M r rkM) ≤ root (M.take (r + m)) (drop1 M (r + m) rkM) := by
    intro m
    induction m with
    | zero => intro _; exact le_refl _
    | succ m ih =>
      intro hm
      exact le_trans (ih (by omega)) (hone (r + m) (by omega) (by omega)).2
  -- the last step is strict
  obtain ⟨ρ1, rk1, hC1, hR1, _, hlt1⟩ := qr_n1 (d0 := d0) hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00
    h1 hx2 hq hC hG hRM hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA
  rw [gexp_one_eq hlen] at hC1 hR1 hlt1
  have heq : root (M.take (r + L)) ρ1 = root (M.take (r + L)) (drop1 M (r + L) rkM) :=
    root_congr (fun i hi => (cons_unique hC1 (hCj (r + L) (by omega) (le_refl _)) hR1 i hi).1)
  rw [heq] at hlt1
  rw [gexp_zero_eq]
  refine ⟨drop1 M r rkM, rkM, hCj r (le_refl _) (by omega), hRk r (le_refl _) (by omega),
    (hone r (le_refl _) hr).1, lt_of_le_of_lt (hchain L (le_refl _)) hlt1⟩

/-- **`t = 1`, `q = r`, `n = 0`**, with only the remaining hypotheses `DropRes` of the drops
`M.take (j + 1) → M.take j` (`r ≤ j < x`) and the new weak sources of the first drop `M → M.take x`;
the value invariants of the prefixes come from those of `M`. -/
theorem qr_n0r {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    (hres : ∀ j, r ≤ j → j < r + L →
      DropRes (M.take (j + 1)) j (drop1 M (j + 1) rkM) (drop1 M j rkM)) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 0) ρN ∧ Rk (TRIO.gexp M r L d0 0 0) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 0) ρN) = true ∧ root (TRIO.gexp M r L d0 0 0) ρN < root M ρ := by
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
  -- the invariants of `M.take x`
  have hIx : ValInv (M.take (r + L)) (drop1 M (r + L) rkM) :=
    drop_pres (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC ⟨hG, hVS, hF, hFO, hKD, hTD⟩
      ⟨hArgT, hVSt, hWS, hUA, hAbs⟩ (hCj _ (le_refl _)) (hRk _ (le_refl _))
  -- down the chain
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
  exact qr_n0 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hVS hF hFO hArgT
    hKD hTD hAbs hWS hVSt hUA (fun j hrj hjx =>
      (DropHypV.of (hIj _ (j + 1) (le_refl _) (by omega) hjx) (hres j hrj hjx)).toDropHyp
        (UAT_take hR0 hZ2 hSD hZ1 hUAB _) (UAB_take hUAB _))

end Ytosk
