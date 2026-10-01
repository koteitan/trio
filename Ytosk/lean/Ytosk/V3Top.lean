/-
**3 行: トップレベルの組み立て（停止性への還元）。**

- n = 0・n = 1 の型によらない形（`drop_n1`・`drop_n0`・`drop_n0r`）: x の行 2 が 0 で、v(x) が D に入らなければ、
  落とす補題と D の狭義性 `dep_strict0` から（t = 0、t = 1 の q ≠ r・q = r に共通）。
- 最後の列が 0 の列（`zero_last_desc`）: M[n] = M.take x、根の列の前で切る（`root_take_root`）。
- 最後の列の親は構造から（`parLast_of`）。
- 不変条件の束 `Inv3`（構造・評価・値の不変条件）と残りの仮定の束 `Res3`（落とす補題の残り DropRes、
  q = r の始点の条件 hcs、t = 0 の `t0_main` の残りの仮定）。1 つの行列での段 1（`desc_step`）: 型（0 の列、t = 0、
  t = 1 の q ≠ r・q = r、t = 2）と n（0、1、≥ 2）で場合分け。t = 2 は仮定。
- 段 3（`terminates_of_desc3`）: **BMS.lean の `WellFounded Step` は偽**（`not_wf_Step`）。
  expand SRO 0 = (0,0,0)、expand (0,0,0) 0 = [] なので [] は Std に入り、expand [] n = [] なので Step [] [] が
  成り立ち、[] で無限に回る。正しい主張は「SRO からのどの展開の列も [] にたどり着く」で、これは空の行列を
  終わりにした `Step'`（M ≠ [] を条件に足す）の整礎性。BMS.lean・Val.lean は変えない。
- トップの定理 `trio_terminates`: 仮定は残りの仕事そのもの（Inv3・Res3 が Std の行列で成り立つこと、t = 2）。
-/
import Ytosk.V3QRFinal4
import Ytosk.V3T0
import Ytosk.V3T0M
import Ytosk.V3T0Last
import Ytosk.V3RootPN
import Ytosk.V3BumpN

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`n = 1`, any type with row 2 of `x` zero.** -/
theorem drop_n1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hL : 0 < L) (hx2 : entry M 2 (r + L) = 0) {q : Nat} (hq : par M 0 (r + L) = some q)
    (hnx : ¬ DepX M (r + L) false (r + L))
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
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hq hnx
  refine ⟨drop1 M (r + L) rkM, rkM, ?_⟩
  rw [gexp_one_eq hlen]
  refine ⟨hC1, hRk1, root_take_lt (by omega) hR01 hR12 h00 hC hG
    (fun i hi => (hdrop i hi).1.2.1) (fun i hi => (hdrop i hi).1.le) ?_⟩
  intro R hR hRA _
  exact hD true R (dep_anc_x hUAT hZ2 hR12 hBE (by omega) hx2 hRA) hR

/-- **`n = 0`, any type with row 2 of `x` zero**, given the drop lemma's hypotheses on the prefixes
`M.take (j + 1)` (`r ≤ j < x`): `root(M.take r) ≤ … ≤ root(M.take x) < root(M)`. -/
theorem drop_n0 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hL : 0 < L) (hx2 : entry M 2 (r + L) = 0) {q : Nat} (hq : par M 0 (r + L) = some q)
    (hnx : ¬ DepX M (r + L) false (r + L))
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
  have hr : r < r + L := by omega
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
  obtain ⟨ρ1, rk1, hC1, hR1, _, hlt1⟩ := drop_n1 (d0 := d0) hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00
    hL hx2 hq hnx hC hG hRM hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA
  rw [gexp_one_eq hlen] at hC1 hR1 hlt1
  have heq : root (M.take (r + L)) ρ1 = root (M.take (r + L)) (drop1 M (r + L) rkM) :=
    root_congr (fun i hi => (cons_unique hC1 (hCj (r + L) (by omega) (le_refl _)) hR1 i hi).1)
  rw [heq] at hlt1
  rw [gexp_zero_eq]
  refine ⟨drop1 M r rkM, rkM, hCj r (le_refl _) (by omega), hRk r (le_refl _) (by omega),
    (hone r (le_refl _) hr).1, lt_of_le_of_lt (hchain L (le_refl _)) hlt1⟩

/-- **`n = 0`, any type with row 2 of `x` zero**, with only the remaining hypotheses `DropRes` of the drops
`M.take (j + 1) → M.take j` (`r ≤ j < x`) and the new weak sources of the first drop `M → M.take x`;
the value invariants of the prefixes come from those of `M`. -/
theorem drop_n0r {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hL : 0 < L) (hx2 : entry M 2 (r + L) = 0) {q : Nat} (hq : par M 0 (r + L) = some q)
    (hnx : ¬ DepX M (r + L) false (r + L))
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
  exact drop_n0 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 hL hx2 hq hnx hC hG hRM hVS hF hFO hArgT
    hKD hTD hAbs hWS hVSt hUA (fun j hrj hjx =>
      (DropHypV.of (hIj _ (j + 1) (le_refl _) (by omega) hjx) (hres j hrj hjx)).toDropHyp
        (UAT_take hR0 hZ2 hSD hZ1 hUAB _) (UAB_take hUAB _))

/-! ## 最後の列が 0 の列 -/

theorem expand_zero_last {M : Mat} (hne : M ≠ []) (hz : col M (M.length - 1) = (0, 0, 0)) (n : Nat) :
    expand M n = M.take (M.length - 1) := by
  obtain ⟨c, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [expand]
  rw [if_pos hz]

/-- **The last column is a root column**: `M[n] = M.take x` drops the root value. -/
theorem zero_last_desc {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hne : M ≠ [])
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) (hz : col M (M.length - 1) = (0, 0, 0)) (n : Nat) :
    ∃ t', Val (expand M n) t' ∧ isOT t' = true ∧ t' < root M ρ := by
  have hpos : 0 < M.length := List.length_pos_of_ne_nil hne
  have hkl : M.length - 1 < M.length := by omega
  rw [expand_zero_last hne hz n]
  have hR' : Rk (M.take (M.length - 1)) rk := rk_take_root hz hkl hR
  have hC' := cons_of_rk hR'
  obtain ⟨hot, hlt⟩ := root_take_root hz hkl (fun j h1 h2 => absurd h2 (by omega)) hC hG hC' hR'
  exact ⟨_, ⟨_, rk, hC', hR', rfl⟩, hot, hlt⟩

/-! ## 最後の列の親（構造から） -/

section
variable {M : Mat} (h00 : entry M 0 0 = 0) (hR01 : R01 M) (hR12 : R12 M) (hZ2 : Z2 M)

include h00 hR01 in
/-- Going up row 0 from `c`, some ancestor has row 1 below `e`, when `e > 0`. -/
theorem anc_e1_below {e : Nat} (he : 0 < e) :
    ∀ c, ∃ a, Relation.ReflTransGen (StepRel (par M 0)) a c ∧ entry M 1 a < e := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases Nat.eq_zero_or_pos (entry M 0 c) with h0 | h0
    · exact ⟨c, Relation.ReflTransGen.refl, by rw [hR01 c h0]; exact he⟩
    · have hc : 0 < c := by
        rcases Nat.eq_zero_or_pos c with hc | hc
        · subst hc; omega
        · exact hc
      obtain ⟨k, hk⟩ := par0_some_of hc (by rw [h00]; exact h0)
      obtain ⟨a, ha, hae⟩ := ih k (par_lt M 0 c k hk)
      exact ⟨a, Relation.ReflTransGen.tail ha hk, hae⟩

include h00 hR01 in
/-- **A column with row 1 positive has a row-1 parent.** -/
theorem par1_exists {j : Nat} (h1 : 0 < entry M 1 j) : ∃ m, par M 1 j = some m := by
  have h0 : 0 < entry M 0 j := by
    rcases Nat.eq_zero_or_pos (entry M 0 j) with h | h
    · rw [hR01 j h] at h1; omega
    · exact h
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; omega
    · exact hj
  obtain ⟨k, hk⟩ := par0_some_of hj (by rw [h00]; exact h0)
  have hkj := par_lt M 0 j k hk
  obtain ⟨a, ha, hae⟩ := anc_e1_below h00 hR01 h1 k
  have hpar : par M 1 j = climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 j)) (j + 1)
      (par M 0 j) := rfl
  have hne : par M 1 j ≠ none := by
    rw [hpar, hk]
    exact climb_ne_none (par_lt M 0) (j + 1) k (by omega) ⟨a, ha, by simpa using hae⟩
  exact Option.ne_none_iff_exists'.mp hne

include h00 hR01 hR12 in
/-- Going up row 1 from `c`, some ancestor has row 2 equal to `0`. -/
theorem anc1_e2_zero : ∀ c, ∃ a, Relation.ReflTransGen (StepRel (par M 1)) a c ∧ entry M 2 a = 0 := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases Nat.eq_zero_or_pos (entry M 2 c) with h2 | h2
    · exact ⟨c, Relation.ReflTransGen.refl, h2⟩
    · have h1 : 0 < entry M 1 c := by
        rcases Nat.eq_zero_or_pos (entry M 1 c) with h | h
        · rw [hR12 c h] at h2; omega
        · exact h
      obtain ⟨k, hk⟩ := par1_exists h00 hR01 h1
      obtain ⟨a, ha, hae⟩ := ih k (par_lt M 1 c k hk)
      exact ⟨a, Relation.ReflTransGen.tail ha hk, hae⟩

include h00 hR01 hR12 in
/-- **A column with row 2 positive has a row-2 parent.** -/
theorem par2_exists {j : Nat} (h2 : 0 < entry M 2 j) : ∃ m, par M 2 j = some m := by
  have h1 : 0 < entry M 1 j := by
    rcases Nat.eq_zero_or_pos (entry M 1 j) with h | h
    · rw [hR12 j h] at h2; omega
    · exact h
  obtain ⟨k, hk⟩ := par1_exists h00 hR01 h1
  have hkj := par_lt M 1 j k hk
  obtain ⟨a, ha, hae⟩ := anc1_e2_zero h00 hR01 hR12 k
  have hpar : par M 2 j = climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 j)) (j + 1)
      (par M 1 j) := rfl
  have hne : par M 2 j ≠ none := by
    rw [hpar, hk]
    exact climb_ne_none (par_lt M 1) (j + 1) k (by omega) ⟨a, ha, by simp [hae]; omega⟩
  exact Option.ne_none_iff_exists'.mp hne

include h00 hR01 hR12 in
/-- **The last column (not a root column) has its parent in the row `srow`.** -/
theorem parLast_of {j : Nat} (hz : col M j ≠ (0, 0, 0)) : ∃ r, par M (TRIO.srow M j) j = some r := by
  unfold TRIO.srow
  by_cases h2 : 0 < TRIO.entry M 2 j
  · rw [if_pos h2]; exact par2_exists h00 hR01 hR12 h2
  rw [if_neg h2]
  by_cases h1 : 0 < TRIO.entry M 1 j
  · rw [if_pos h1]; exact par1_exists h00 hR01 h1
  rw [if_neg h1]
  have h0 : 0 < entry M 0 j := by
    rcases Nat.eq_zero_or_pos (entry M 0 j) with h | h
    · exact absurd ((col_zero_iff M j).mpr ⟨h, by omega, by omega⟩) hz
    · exact h
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; omega
    · exact hj
  exact par0_some_of hj (by rw [h00]; exact h0)

end

/-! ## 不変条件の束と、残りの仮定の束 -/

/-- **The invariants of a 3-row matrix** with its valuation `ρ` and ranking `rk`: structural invariants,
the evaluation, and the value invariants used by the per-type theorems. -/
structure Inv3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  r0p : R0P M
  z2 : Z2 M
  sd : SibDec M
  z1 : Z1C M
  uat : UAT M
  uab : UAB M
  r12 : R12 M
  be : BumpE2 M
  r01 : R01 M
  e00 : entry M 0 0 = 0
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  ad : AbsD M ρ
  au : AbsU M ρ
  tp1 : TP1 M ρ
  tplo : TPLo M ρ
  tp1w : TP1W M ρ
  tplow : TPLoW M ρ
  auw : AbsUW M ρ
  adw : AbsDW M ρ
  trig : TrigOm M ρ
  tplon : TPLoN M ρ
  adn : AbsDN M ρ
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- **The remaining per-matrix hypotheses**: the drop lemma's
remaining hypotheses (`DropRes`) for `M → M.take x` and for every prefix drop, and the seed condition
`hcs` of `t = 1`, `q = r`. -/
structure Res3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  chain : ∀ j, j + 1 < M.length → DropRes (M.take (j + 1)) j (drop1 M (j + 1) rk) (drop1 M j rk)
  seed : ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    lt (sf ((drop1 M (M.length - 1) rk).v r)) (ρ.v r) = true →
    ∀ u g, g ∈ comps u ((drop1 M (M.length - 1) rk).o r) → g < (drop1 M (M.length - 1) rk).o r
  t0 : ∀ r L, r + L + 1 = M.length → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r → ∀ g Lc,
      par M 0 r = some g → CL M g = Lc ++ [r] → ∀ s y, ρ.o r = psi s y z →
      lt (spArg (ρ.v g) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true →
      VSmallV s') ∧
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      Good3 (TRIO.gexp M r L 0 0 n) σ ∧ VSmallNewN M r ρ σ ∧
      (∀ i ∈ roots (TRIO.gexp M r L 0 0 n), Single (σ.o i)) ∧
      ((roots (TRIO.gexp M r L 0 0 n)).map σ.o).Pairwise (fun a b => b ≤ a))

/-- **`M[1] = M.take x` with the drop valuation keeps the value invariants** (`t = 1`), from `drop_pres`. -/
theorem valInv_drop1 {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hRM : Rk M rk) (hI : ValInv M ρ)
    (hD : DropRes M x ρ (drop1 M x rk)) : ValInv (M.take x) (drop1 M x rk) := by
  have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = x by omega] at hcnt
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) hRM hcnt
  exact drop_pres hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI hD (cons_of_rk hRk1) hRk1

/-- **The root order of `M[1] = M.take x`** with the drop valuation (`x` not a root). -/
theorem rootP_drop1 {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hx0 : entry M 0 x ≠ 0)
    {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hRM : Rk M rk) (hI : ValInv M ρ)
    (hD : DropRes M x ρ (drop1 M x rk)) (hpM : RootP M ρ) : RootP (M.take x) (drop1 M x rk) := by
  have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = x by omega] at hcnt
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) hRM hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC1 hRk1 hI.vs hD.vst hI.fc hI.fo hD.argT
    (bump_drop hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC1 hRk1 hI.kd hI.td hD.ab hD.ws) hD.ua
  exact rootP_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hx0 hC hI.g hC1 hRk1
    (fun i hi => (hdrop i hi).1.le) hpM

/-- **`M[1] = M.take x` with the drop valuation is good** (`t = 1`), from `drop_pres`. -/
theorem good3_drop1 {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hRM : Rk M rk) (hI : ValInv M ρ)
    (hD : DropRes M x ρ (drop1 M x rk)) : Good3 (M.take x) (drop1 M x rk) := by
  have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = x by omega] at hcnt
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) hRM hcnt
  exact (drop_pres hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI hD (cons_of_rk hRk1) hRk1).g

/-- The value drops under `M[n]` (the per-matrix form of step 1). -/
def DropsAt (M : Mat) (ρ : Valn) (n : Nat) : Prop :=
  ∃ t', Val (expand M n) t' ∧ isOT t' = true ∧ t' < root M ρ

theorem dropsAt_of {M N : Mat} {ρ : Valn} {n : Nat} (he : expand M n = N)
    (h : ∃ ρN rkN, Cons N ρN ∧ Rk N rkN ∧ isOT (root N ρN) = true ∧ root N ρN < root M ρ) :
    DropsAt M ρ n := by
  obtain ⟨ρN, rkN, hC, hR, hot, hlt⟩ := h
  unfold DropsAt
  rw [he]
  exact ⟨_, ⟨ρN, rkN, hC, hR, rfl⟩, hot, hlt⟩

/-- **Step 1 for one matrix**, by the type of the last column and `n`. The cases `t = 0`, `n ≥ 2` and
`t = 2` are hypotheses. -/
theorem desc_step {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hne : M ≠ [])
    (I : Inv3 M ρ rk) (R : Res3 M ρ rk)
    (hT2 : col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n)
    (n : Nat) : DropsAt M ρ n := by
  have hpos : 0 < M.length := List.length_pos_of_ne_nil hne
  by_cases hz : col M (M.length - 1) = (0, 0, 0)
  · exact zero_last_desc hne I.cons I.good I.rank hz n
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hsrow : TRIO.srow M (M.length - 1) = 0 ∨ TRIO.srow M (M.length - 1) = 1 ∨
      TRIO.srow M (M.length - 1) = 2 := by
    unfold TRIO.srow; split_ifs <;> simp
  rcases hsrow with h0 | h1t | h2
  · -- `t = 0`
    have he1 : entry M 1 (M.length - 1) = 0 := by
      unfold TRIO.srow at h0
      by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
      · rw [if_pos ha] at h0; cases h0
      · rw [if_neg ha] at h0
        by_cases hb : 0 < TRIO.entry M 1 (M.length - 1)
        · rw [if_pos hb] at h0; cases h0
        · show TRIO.entry M 1 (M.length - 1) = 0; omega
    have hx2 : entry M 2 (M.length - 1) = 0 := I.r12 _ he1
    rw [h0] at hr
    have hexp := expand_eq_gexp M n hlen2 hzT (by rw [h0]; exact hr)
    rw [h0] at hexp
    simp only [show ¬ (0 < 0) from by omega, show ¬ (1 < 0) from by omega, if_false] at hexp
    have hdr := R.drop
    have hch := R.chain
    have ht0 := R.t0
    have hrx : r < M.length - 1 := par_lt M 0 _ r hr
    obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
    rw [hL] at hexp hr he1 hx2 hdr
    simp only [Nat.add_sub_cancel_left] at hexp
    have hlen : r + L + 1 = M.length := by omega
    have hL0 : 0 < L := by omega
    have hnx : ¬ DepX M (r + L) false (r + L) := by
      intro h
      cases h with
      | vpar h1 _ _ => exact h1 he1
      | vupg h1 _ _ _ => exact h1 he1
      | vbump h1 _ _ _ _ _ => exact h1 he1
    rcases n with _ | _ | n
    · apply dropsAt_of hexp
      exact drop_n0r (d0 := 0) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hL0 hx2 hr hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        (fun j _ hj => hch j (by omega))
    · apply dropsAt_of hexp
      exact drop_n1 (d0 := 0) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hL0 hx2 hr hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
    · apply dropsAt_of hexp
      obtain ⟨hVr, hN⟩ := ht0 r L hlen hr he1
      have hLast := fun n (hn : 2 ≤ n) g (hg : par M 0 r = some g) (hc : Counted M g r) =>
        counted_last0 hlen hL0 hr he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc
      exact t0_main' hlen hL0 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr he1 I.cons I.good
        I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.rootS I.rootP hLast
        hVr hN (n + 2) (by omega)
  · -- `t = 1`
    have hx2 : entry M 2 (M.length - 1) = 0 := by
      unfold TRIO.srow at h1t
      by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
      · rw [if_pos ha] at h1t; cases h1t
      · show TRIO.entry M 2 (M.length - 1) = 0; omega
    rw [h1t] at hr
    have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
    have hdr := R.drop
    have hch := R.chain
    have hsd := R.seed
    have hrx : r < M.length - 1 := par_lt M 1 _ r hr
    obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
    rw [hL] at hexp hr hx2 hdr hsd
    simp only [Nat.add_sub_cancel_left] at hexp
    have hlen : r + L + 1 = M.length := by omega
    have hL0 : 0 < L := by omega
    have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
    have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
      have := anc0_e0_lt hA (by omega); omega
    obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
    have hnx : ¬ DepX M (r + L) false (r + L) := by
      intro h
      cases h with
      | vpar _ hp hdm =>
        rw [hr] at hp; cases hp
        by_cases hqr : q = r
        · subst hqr
          exact (qr_dep hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq).2.1 hdm
        · exact v_r_not_chg hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hA (by omega)
            (fun h' => hqr (Option.some.inj (hq.symm.trans h')))
            (hpath_of_par1 hr hA (by omega)) (depX_chgX hdm)
      | vupg _ _ hu _ => have := upg_succ_lt hu; omega
      | vbump _ h2 _ _ _ _ => exact h2 hx2
    rcases n with _ | _ | n
    · apply dropsAt_of hexp
      exact drop_n0r (d0 := entry M 0 (r + L) - entry M 0 r) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
        I.be I.r01 I.e00 hL0 hx2 hq hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        (fun j _ hj => hch j (by omega))
    · apply dropsAt_of hexp
      exact drop_n1 (d0 := entry M 0 (r + L) - entry M 0 r) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
        I.be I.r01 I.e00 hL0 hx2 hq hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
    · apply dropsAt_of hexp
      by_cases hqr : q = r
      · subst hqr
        obtain ⟨ρN, rkN, hCN, hRN, _, _, hot, hlt⟩ :=
          qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
          I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
          I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) (fun N σ => FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ)
          ⟨(valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
            ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr).fo, rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00
            (by have := anc0_interval hA (q + L) (by omega) (Nat.le_refl _); omega) I.cons I.rank
            ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr I.rootP,
            (valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
              ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr).kd,
            (valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
              ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr).td⟩
          (expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
            (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
              (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good ⟨I.kd, I.td⟩)))
          (n + 2) (by omega)
        exact ⟨ρN, rkN, hCN, hRN, hot, hlt⟩
      · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
        have h := t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
          (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
          I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
          (good3_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
            ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr) (fun N σ => FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ)
          ⟨(valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
            ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr).fo, rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00
            (by have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega) I.cons I.rank
            ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr I.rootP,
            (valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
              ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr).kd,
            (valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
              ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr).td⟩
          (expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
            (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
              (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good ⟨I.kd, I.td⟩)))
          (n + 2) (by omega)
        obtain ⟨ρN, rkN, hCN, hRN, _, _, hot, hlt⟩ := h
        exact ⟨ρN, rkN, hCN, hRN, hot, hlt⟩
  · exact hT2 hz h2 n

/-! ## 段 3: 停止性（空の行列は終わり） -/

/-- The root value of a standard valuation is standard. -/
theorem root_ot {M : Mat} {ρ : Valn} (hG : Good3 M ρ) : isOT (root M ρ) = true := by
  unfold root
  apply isOT_sumN
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  split
  · exact hG.ot_o i (List.mem_range.mp hi)
  · rfl

/-- **One expansion step from a nonempty matrix inside `Std`.** The empty matrix is terminal
(`expand [] n = []`, and `[]` is reached from SRO: `SRO → (0,0,0) → []`, so `Step` itself loops at `[]`). -/
def Step' (M' M : Mat) : Prop := Std M ∧ M ≠ [] ∧ ∃ n, M' = expand M n

/-- Step 1 away from SRO and the empty matrix. -/
def Desc3 : Prop :=
  ∀ M n, Std M → M ≠ SRO → M ≠ [] →
    ∃ t t', Val M t ∧ Val (expand M n) t' ∧ isOT t = true ∧ t' < t

/-- **Step 3**: step 1 gives termination (with the empty matrix terminal). -/
theorem terminates_of_desc3 (hD : Desc3) : WellFounded Step' := by
  have accE : Acc Step' [] := ⟨_, fun _ h => absurd rfl h.2.1⟩
  have main : ∀ t, Acc (fun s t : T => isOT s = true ∧ isOT t = true ∧ s < t) t →
      ∀ M, Std M → M ≠ SRO → M ≠ [] → Val M t → Acc Step' M := by
    intro t hacc
    induction hacc with
    | intro t _ ih =>
      intro M hM hne hne' hev
      constructor
      rintro M' ⟨_, _, n, rfl⟩
      obtain ⟨t1, t', h1, h2, hot, hlt⟩ := hD M n hM hne hne'
      cases val_unique hev h1
      have hM' : Std (expand M n) := Std.exp n hM
      have hneS : expand M n ≠ SRO := by
        intro h; rw [h] at h2; exact not_val_SRO _ h2
      by_cases hE : expand M n = []
      · rw [hE]; exact accE
      obtain ⟨t2, _, h3, _, hot', _⟩ := hD (expand M n) 0 hM' hneS hE
      cases val_unique h2 h3
      exact ih t' ⟨hot', hot, hlt⟩ (expand M n) hM' hneS hE h2
  have accM : ∀ M, Std M → M ≠ SRO → Acc Step' M := by
    intro M hM hne
    by_cases hE : M = []
    · rw [hE]; exact accE
    obtain ⟨t, _, h1, _, _, _⟩ := hD M 0 hM hne hE
    exact main t (wf_OT.apply t) M hM hne hE h1
  constructor
  intro M
  by_cases hM : Std M
  · by_cases hne : M = SRO
    · subst hne
      constructor
      rintro M' ⟨_, _, n, rfl⟩
      apply accM _ (Std.exp n Std.sro)
      intro h
      have hlen := congrArg List.length h
      rw [expand_SRO_length] at hlen
      simp [SRO] at hlen
      omega
    · exact accM M hM hne
  · constructor
    rintro M' ⟨hM', _⟩
    exact absurd hM' hM

/-! ## トップの定理 -/

/-- **Termination of the 3-row BMS from SRO**, with exactly the remaining work as hypotheses:
- `hInv`: every nonempty `Std` matrix other than SRO has a valuation with the invariants `Inv3` and the
  remaining per-matrix hypotheses `Res3` (drop-lemma residuals, the seed
  condition `hcs` of `t = 1`, `q = r`);
- `hT2`: the case `t = 2`. -/
theorem trio_terminates
    (hInv : ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3 M ρ rk ∧ Res3 M ρ rk)
    (hT2 : ∀ M ρ rk, Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' := by
  apply terminates_of_desc3
  intro M n hM hne hne'
  obtain ⟨ρ, rk, I, R⟩ := hInv M hM hne hne'
  obtain ⟨t', hv, _, hlt⟩ := desc_step hne' I R (hT2 M ρ rk I R) n
  exact ⟨root M ρ, t', ⟨ρ, rk, I.cons, I.rank, rfl⟩, hv, root_ot I.good, hlt⟩

/-! ## 元の Step は整礎でない -/

theorem std_nil : Std [] := by
  have h1 : expand SRO 0 = [(0, 0, 0)] := by decide
  have h2 : expand [(0, 0, 0)] 0 = [] := by decide
  have := Std.exp 0 (Std.exp 0 Std.sro)
  rw [h1, h2] at this
  exact this

/-- **`Step` loops at the empty matrix**, so `WellFounded Step` (BMS.lean) is false. -/
theorem not_wf_Step : ¬ WellFounded Step := by
  intro hwf
  have hstep : Step [] [] := ⟨std_nil, 0, rfl⟩
  have hacc := hwf.apply []
  have key : ∀ M, Acc Step M → M ≠ [] := by
    intro M hM
    induction hM with
    | intro M _ ih =>
      intro hM
      subst hM
      exact ih [] hstep rfl
  exact key [] hacc rfl

end Ytosk
