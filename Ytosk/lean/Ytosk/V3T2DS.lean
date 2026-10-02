/-
**3 行・t = 2: 種の集合 S からの D = DepS M S の形（種が x の祖先で、変化の集合 ChgX に入るとき）。**

V3T2D の DepX 版（`dep_exitX`・`nodep_sibX`・`p1_depX`・`uncnt_of_depvX`・`hOS_t1X`・`nodep_not_lastX`・
`dv_shapeX`）の写し。違いは:
- 葉 o(x) の代わりに種 S。種は x の（x より前の）祖先で、ChgX に入る（`hSC`・`hSA`）。
- DepS ⊆ ChgX（`depS_chgX`）から、ChgX の構造（`chg_struct` の TopC・ICC、`chg_last`、`chg_only_last`）を使う。
- x が q ののりしろの子でもよい（q ≠ r）。x の親 q の v が D に入るときの扱いだけ仮定に残す。
-/
import Ytosk.V3T2T

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hXu : ∀ i, upg M i ≠ some x) {S : Bool → Nat → Prop}
  (hSC : ∀ b i, S b i → ChgX M x b i) (hSA : ∀ b i, S b i → Anc0 M i x ∧ i < x)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA

omit hR0 hZ2 hSD hZ1 hUAT hUAB hSA in
/-- **`D ⊆ ChgX`** below `x`. -/
theorem depS_chgX {b : Bool} {i : Nat} (h : DepS M S b i) : i < x → ChgX M x b i := by
  induction h with
  | seed hs => intro _; exact hSC _ _ hs
  | @ochild i c hc hcb hcu _ ih =>
    intro _
    have hcl := (mem_children hc).2
    rcases Nat.lt_or_ge c x with h | h
    · exact ChgX.ochild hc hcb hcu (ih h)
    · have : c = x := by omega
      subst this; exact ChgX.ochild hc hcb hcu ChgX.leaf
  | ov _ ih => intro hi; exact ChgX.ov (ih hi)
  | @vpar i m h1 hpm _ ih =>
    intro hi; exact ChgX.vpar h1 hpm (ih (by have := par_lt M 1 i m hpm; omega))
  | @vupg i k h1 h2 hu _ ih =>
    intro hi
    have hkl := upg_lt (by omega) hu
    have hkx : k < x := by
      rcases Nat.lt_or_ge k x with h | h
      · exact h
      · exfalso; have : k = x := by omega
        exact hXu i (this ▸ hu)
    exact ChgX.vupg h1 h2 hu (ih hkx)
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro _
    have hkl := (mem_children hk).2
    rcases Nat.lt_or_ge k x with h | h
    · exact ChgX.vbump h1 h2 hj hjb hk (ih h)
    · have : k = x := by omega
      subst this; exact ChgX.vbump h1 h2 hj hjb hk ChgX.leaf

/-- TopC of a `v` call in `D`. -/
theorem topC_of_depS {m : Nat} (hm : m < x) (h : DepS M S false m) : TopC M x m :=
  (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depS_chgX hx hXu hSC h hm)).1 rfl hm

/-- **The exit of `D` from a subtree** not containing `x`. -/
theorem dep_exitS {b : Bool} {d : Nat} (h : DepS M S b d) :
    ∀ c, Anc0 M c d → ¬ Anc0 M c x →
      ∃ c', NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧ DepS M S false c' := by
  induction h with
  | seed hs => intro c hc hn; exact absurd (Anc0.trans hc (hSA _ _ hs).1) hn
  | @ochild i c0 hc0 _ _ _ ih =>
    intro c hci hn
    exact ih c (Anc0.step (mem_children_iff.mp hc0).2 hci) hn
  | ov _ ih => exact ih
  | @vpar i m _ hp hdm _ =>
    intro c hci hn
    exfalso
    have hmi := par_lt M 1 i m hp
    have hil : i < M.length := anc0_lt_len (anc0_of_par M 1 m i hp) (by omega)
    have hix : i < x := by
      rcases Nat.lt_or_ge i x with h | h
      · exact h
      · have : i = x := by omega
        exact absurd (this ▸ hci) hn
    exact (topC_of_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA (by omega) hdm).2.2 i hix hp
  | @vupg i k _ _ hu hdk ih =>
    intro c hci hn
    by_cases hck : Anc0 M c k
    · exact ih c hck hn
    · have hix : i < x := by have := upg_succ_lt hu; omega
      obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
      rcases hcase with rfl | ⟨hA, hki⟩
      · have hi1 : i + 1 < x := by
          rcases Nat.lt_or_ge (i + 1) x with h | h
          · exact h
          · exfalso
            have : i + 1 = x := by omega
            rw [this] at hu
            exact absurd hu (hXu _)
        exact ⟨i + 1, ⟨by have := hci.le; omega, fun e h1 h2 => anc_between hci e h1 (by omega), hck⟩,
          hi1, by simpa using hu, hdk⟩
      · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
          (topC_of_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA (by omega) hdk) (by omega) hu hA hki).elim
  | @vbump i j k _ _ hj _ hk _ ih =>
    intro c hci hn
    exact ih c (Anc0.step (mem_children_iff.mp hk).2 (Anc0.step (mem_children_iff.mp hj).2 hci)) hn

/-- **No `D` below an earlier sibling of a column on the path to `x`**, if that column's `v` is not in
`D`. -/
theorem nodep_sibS {p a : Nat} (hpa : par M 0 p = some a) (hpx : Anc0 M p x)
    (hnp : p < x → ¬ DepS M S false p) :
    ∀ n c, p - c ≤ n → c ∈ children M a → c < p → ∀ b d, DepS M S b d → ¬ Anc0 M c d := by
  intro n
  induction n with
  | zero => intro c hn _ hcp; omega
  | succ n ih =>
    intro c hn hc hcp b d hd hcd
    have hca : par M 0 c = some a := (mem_children_iff.mp hc).2
    have hac := par_lt M 0 c a hca
    have hap := par_lt M 0 p a hpa
    have hpl : p < M.length := by have := hpx.le; omega
    have hcx : ¬ Anc0 M c x := by
      intro hA
      rcases anc0_total hA hpx with h | h
      · have := (anc0_par h (by omega) hpa).le; omega
      · have := h.le; omega
    obtain ⟨c', hN, hc'x, _, hdc'⟩ := dep_exitS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hd c hcd hcx
    have hAap : Anc0 M a p := Anc0.step hpa (Anc0.refl a)
    have hc'p : c' ≤ p := by
      by_contra hlt
      have hA := hN.2.1 p (by omega) (by omega)
      have := (anc0_par hA (by omega) hpa).le; omega
    have hAac' : Anc0 M a c' := anc_between hAap c' (by have := hN.1; omega) hc'p
    obtain ⟨h', hph⟩ := par0_of_anc hAac' (by have := hN.1; omega)
    obtain ⟨_, hha⟩ := next_parent hca hpa hcp hN hph
    rw [hha] at hph
    rcases Nat.eq_or_lt_of_le hc'p with heq | hlt
    · subst heq; exact hnp hc'x hdc'
    · have hc'M : c' ∈ children M a := mem_children_iff.mpr ⟨by omega, hph⟩
      exact ih c' (by have := hN.1; omega) hc'M hlt false c' hdc' (Anc0.refl c')

/-- No `D` below a child of the parent `q` of `x` (other than `x`). -/
theorem nodep_below_q {q c : Nat} (hq : par M 0 x = some q) (hc : c ∈ children M q) (hcx : c < x)
    {b : Bool} {d : Nat} (hd : DepS M S b d) : ¬ Anc0 M c d :=
  nodep_sibS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hq (Anc0.refl x) (fun h => absurd h (lt_irrefl _))
    _ c (Nat.le_refl _) hc hcx b d hd

/-- **(P1 in `M`)** After a child in `D`, no sibling counts (the sibling not the parent of `x`). -/
theorem p1_depS {i c c₂ : Nat} (hi : i < x) (hc : c ∈ children M i) (hc₂ : c₂ ∈ children M i)
    (hcc : c < c₂) (hD : DepS M S true c) (hcnt : Counted M i c₂) (hxc₂ : x ∉ children M c₂) : False := by
  have hc₂l := (mem_children hc₂).2
  have hpc₂ : par M 0 c₂ = some i := (mem_children_iff.mp hc₂).2
  rcases Nat.lt_or_ge c₂ x with hc₂x | hc₂x
  · have hcT : c ∈ children (M.take x) i := by
      rw [children_take, List.mem_filter]; exact ⟨hc, by simpa using (show c < x by omega)⟩
    have hc₂T : c₂ ∈ children (M.take x) i := by
      rw [children_take, List.mem_filter]; exact ⟨hc₂, by simpa using hc₂x⟩
    exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hcT (depS_chgX hx hXu hSC hD (by omega)) c₂ hc₂T hcc
      (cnt_take_of_M hx hi hc₂x hxc₂ hcnt)
  · have hc₂e : c₂ = x := by omega
    subst hc₂e
    exact nodep_below_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hpc₂ hc (by omega) hD (Anc0.refl c)

/-- **A column whose `v` is in `D` counts no child** (in `M`), when `x` is not counted at its parent. -/
theorem uncnt_of_depvS {i d : Nat} (hi : i < x) (hv : DepS M S false i) (hd : d ∈ children M i)
    (hxq : x ∈ children M i → ¬ Counted M i x) : ¬ Counted M i d := by
  have hdl := (mem_children hd).2
  have hpd : par M 0 d = some i := (mem_children_iff.mp hd).2
  have hid := (mem_children hd).1
  rcases Nat.lt_or_ge d x with hdx | hdx
  · have hT := topC_of_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hi hv
    have hdT : d ∈ children (M.take x) i := by
      rw [children_take, List.mem_filter]; exact ⟨hd, by simpa using hdx⟩
    by_cases hxd : x ∈ children M d
    · have hAdx : Anc0 M d x := Anc0.step (mem_children_iff.mp hxd).2 (Anc0.refl d)
      have hmax : ∀ e ∈ children (M.take x) i, e ≤ d := by
        intro e he
        rw [children_take, List.mem_filter] at he
        have hex : e < x := by simpa using he.2
        have hpe : par M 0 e = some i := (mem_children_iff.mp he.1).2
        by_contra hlt
        have hA := anc_between hAdx e (by omega) (by omega)
        have := (anc0_par hA (by omega) hpe).le; omega
      have hsplit := split_last_max _ _ (children_sorted (M.take x) i) hdT hmax
      have htop := hT.1
      unfold topped at htop
      rw [hsplit] at htop
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, decide_eq_true_eq] at htop
      rw [col_take M hdx, bump_take M hi] at htop
      exact fun h => h.1 htop
    · exact fun h => hT.2.1 d hdT (cnt_take_of_M hx hi hdx hxd h)
  · have hdx' : d = x := by omega
    subst hdx'
    exact hxq hd

/-- **No `D` below a child of `p` (row 2 nonzero) that has a later child.** -/
theorem nodep_not_lastS {p d d' : Nat} (h2 : entry M 2 p ≠ 0) (hd : d ∈ children M p)
    (hd' : d' ∈ children M p) (hdd : d < d') {b : Bool} {e : Nat} (hD : DepS M S b e)
    (hde : Anc0 M d e) : False := by
  have hd'l := (mem_children hd').2
  have hel : e < M.length := by
    rcases Nat.eq_or_lt_of_le hde.le with h | h
    · rw [← h]; have := (mem_children hd).2; omega
    · exact anc0_lt_len hde (by omega)
  rcases Nat.lt_or_ge d' x with hd'x | hd'x
  · have hex : e < x := by
      by_contra h'
      have : e = x := by omega
      subst this
      have := (mem_children hd).1
      have := anc_between hde d' (by omega) (by omega)
      have := (anc0_par this (by omega) (mem_children_iff.mp hd').2).le
      omega
    exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hd (mem_take_children hd' hd'x) hdd
      (depS_chgX hx hXu hSC hD hex) hde
  · have hd'e : d' = x := by omega
    subst hd'e
    exact nodep_below_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA (mem_children_iff.mp hd').2 hd hdd hD hde

/-- **The `v` shape of `D`** (`VSh`) at a non-seed `v` call. -/
theorem vsh_S {i : Nat} (hi : i < x) (hns : ¬ S false i) (hv : DepS M S false i) :
    (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧
    (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
      children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M S true d) ∧
      (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e)) := by
  have hpd : ∀ m, par M 1 i = some m → ¬ DepS M S false m := by
    intro m hp hdm
    have hmi := par_lt M 1 i m hp
    exact (topC_of_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA (by omega) hdm).2.2 i hi hp
  refine ⟨hpd, fun h2 => ?_⟩
  cases hv with
  | seed h => exact absurd h hns
  | vpar h1 hp hdm => exact absurd hdm (hpd _ hp)
  | vupg _ h2' _ _ => exact absurd h2' h2
  | @vbump _ j k h1 _ hj hjb hk hdk =>
    have hj2 : entry M 2 j ≠ 0 := by
      have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
    have hAjk : Anc0 M j k := Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j)
    have hjmax : ∀ j' ∈ children M i, j' ≤ j := by
      intro j' hj'; by_contra hlt
      exact nodep_not_lastS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA h2 hj hj' (by omega) hdk hAjk
    have hchi := split_last_max _ _ (children_sorted M i) hj hjmax
    have hkmax : ∀ k' ∈ children M j, k' ≤ k := by
      intro k' hk'; by_contra hlt
      exact nodep_not_lastS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hj2 hk hk' (by omega) hdk (Anc0.refl k)
    have hchj := split_last_max _ _ (children_sorted M j) hk hkmax
    refine ⟨_, _, j, k, hchi, hjb, hchj, ?_, ?_⟩
    · intro d hd hdD
      have hdM : d ∈ children M j := (List.mem_filter.mp hd).1
      have hdk' : d < k := by simpa using (List.mem_filter.mp hd).2
      exact nodep_not_lastS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hj2 hdM hk hdk' hdD (Anc0.refl d)
    · intro d hd e he hD
      have hdM : d ∈ children M i := (List.mem_filter.mp hd).1
      have hdj : d < j := by simpa using (List.mem_filter.mp hd).2
      exact nodep_not_lastS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA h2 hdM hj hdj hD
        (Anc0.step (mem_children_iff.mp he).2 (Anc0.refl d))

/-- **The `o` shape of `D`** at a non-seed `o` call whose `v` is not in `D`, when no child of `i` is the
parent of `x`. -/
theorem os_S {i : Nat} (hi : i < x) (hns : ¬ S true i) (hD : DepS M S true i) (hv : ¬ DepS M S false i)
    (hnx : ∀ d ∈ children M i, x ∉ children M d) :
    ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M S true c ∧
      (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M S true d) := by
  cases hD with
  | seed h => exact absurd h hns
  | ov h => exact absurd h hv
  | @ochild _ c hc hcb hcu hdc =>
    obtain ⟨L, R, hLR⟩ := List.append_of_mem hc
    obtain ⟨hL, hR⟩ := sib_order (children_sorted M i) hLR
    refine ⟨L, c, R, hLR, ⟨hcb, hcu⟩, hdc, fun d hd hcnt => ?_, fun d hd hcnt hdD => ?_⟩
    · have hdM : d ∈ children M i := by rw [hLR]; simp [hd]
      exact p1_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hi hc hdM (hR d hd) hdc hcnt (hnx d hdM)
    · have hdM : d ∈ children M i := by rw [hLR]; simp [hd]
      exact p1_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hi hdM hc (hL d hd) hdD ⟨hcb, hcu⟩ (hnx c hc)

end

end Ytosk
