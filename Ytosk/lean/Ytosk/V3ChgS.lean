/-
**落とす補題: 変化の集合 C（`ChgX`）の構造。**

構造の不変条件（R0P・Z2・SibDec・Z1C・UAT・UAB）のもとで:
- 行 2 が 1 の列を par1 で指す列はない（`no_par1_of_e2`）。
- 行 2 が 1 の列の最後の子がのりしろ列なら、子はすべてのりしろ列（`all_bump_of_last`）。
- 上げの先の形（`upg_spec`）。
-/
import Ytosk.V3Chg
import Ytosk.V3InvTake

namespace Ytosk

open T

/-- An ancestor-type upgrade never comes from below a bump child of its target. -/
def UAB (M : Mat) : Prop :=
  ∀ i k, upg M i = some k → k ≠ i + 1 → ∀ j, j ∈ children M k → col M j = bump M k → ¬ Anc0 M j i

/-! ## 行 2 が 1 の列 -/

/-- **No column has a row-1 parent with row 2 equal to `1`.** -/
theorem no_par1_of_e2 {M : Mat} (hZ1 : Z1C M) {i d : Nat} (hd : d < M.length) (he : entry M 2 i = 1)
    (hp : par M 1 d = some i) : False := by
  have hA := anc0_of_par M 1 i d hp
  have hid : i ≠ d := by have := par_lt M 1 d i hp; omega
  obtain ⟨p, hpi, hpd⟩ := anc0_child hA hid
  have hpl : p < M.length := by have := hpd.le; omega
  have hpc : p ∈ children M i := mem_children_iff.mpr ⟨hpl, hpi⟩
  have h1 := hZ1 i p he hpc
  have h2 := par1_between hp p hpd (par_lt M 0 p i hpi)
  have h3 := par1_entry_lt hp
  omega

theorem colLe_trans {a b c : Nat × Nat × Nat} (h1 : colLe a b) (h2 : colLe b c) : colLe a c := by
  unfold colLe at *
  omega

/-- Siblings do not increase (any two, not only consecutive ones). -/
theorem sib_le {M : Mat} (hSD : SibDec M) {p : Nat} :
    ∀ (l₂ l₁ : List Nat) (a : Nat), children M p = l₁ ++ a :: l₂ → ∀ b ∈ l₂, colLe (col M b) (col M a)
  | [], _, _, _, b, hb => absurd hb (by simp)
  | c :: l₂, l₁, a, h, b, hb => by
    have hac := hSD p l₁ l₂ a c h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hac
    · have h' : children M p = (l₁ ++ [a]) ++ c :: l₂ := by rw [h]; simp
      exact colLe_trans (sib_le hSD l₂ (l₁ ++ [a]) c h' b hb) hac

/-- **All children are bump columns** when row 2 is `1` and the last child is the bump column. -/
theorem all_bump_of_last {M : Mat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    {i j : Nat} {L : List Nat} (he : entry M 2 i = 1) (hch : children M i = L ++ [j])
    (hjb : col M j = bump M i) : ∀ c ∈ children M i, col M c = bump M i := by
  intro c hc
  rw [hch] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hc
    have hch' : children M i = l₁ ++ c :: (l₂ ++ [j]) := by rw [hch, hl]; simp
    have hle := sib_le hSD (l₂ ++ [j]) l₁ c hch' j (by simp)
    have hcm : c ∈ children M i := by rw [hch']; simp
    have hpc : par M 0 c = some i := (mem_children_iff.mp hcm).2
    have h0 := hR0 c i hpc
    have h1 := hZ1 i c he hcm
    have h2 := hZ2 c
    rw [hjb] at hle
    unfold colLe bump at hle
    unfold bump
    have e0 : (col M c).1 = entry M 0 c := rfl
    have e1 : (col M c).2.1 = entry M 1 c := rfl
    have e2 : (col M c).2.2 = entry M 2 c := rfl
    simp only at hle
    rw [e0, e1, e2] at hle
    have hc1 : entry M 1 c = entry M 1 i := by omega
    have hc2 : entry M 2 c = 1 := by omega
    rcases hcol : col M c with ⟨a0, a1, a2⟩
    rw [hcol] at e0 e1 e2
    simp only at e0 e1 e2
    rw [e0, e1, e2, h0, hc1, hc2]
  · rw [List.mem_singleton] at hc; rw [hc]; exact hjb

/-! ## 部分木 -/

/-- **Subtrees are intervals.** -/
theorem anc_between {M : Mat} {a b : Nat} (h : Anc0 M a b) : ∀ j, a ≤ j → j ≤ b → Anc0 M a j := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro haj hjb
    rcases Nat.eq_or_lt_of_le haj with rfl | hlt
    · exact Anc0.refl _
    · have he := anc0_interval h j hlt hjb
      obtain ⟨p, hp⟩ := par0_some_of hlt he
      have hpj := par_lt M 0 j p hp
      have hap := par0_ge_of_anc h hlt hjb hp
      exact Anc0.step hp (ih p hpj hap (by omega))

/-- An ancestor of a column has a smaller row 0. -/
theorem anc0_e0_lt {M : Mat} {a b : Nat} (h : Anc0 M a b) (hne : a ≠ b) : entry M 0 a < entry M 0 b :=
  anc0_interval h b (lt_of_le_of_ne h.le hne) (Nat.le_refl _)

/-- **Ancestors are determined by their row 0.** -/
theorem anc0_eq_of_e0 {M : Mat} {a b d : Nat} (ha : Anc0 M a d) (hb : Anc0 M b d)
    (he : entry M 0 a = entry M 0 b) : a = b := by
  rcases anc0_total ha hb with h | h
  · by_contra hne; have := anc0_e0_lt h hne; omega
  · by_contra hne; have := anc0_e0_lt h (Ne.symm hne); omega

theorem entry_out' {M : Mat} {k : Nat} (hk : M.length ≤ k) (i : Nat) : entry M i k = 0 := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  split_ifs <;> rfl

/-- A column beyond the matrix has no parent. -/
theorem par0_out' {M : Mat} {c : Nat} (hc : M.length ≤ c) : par M 0 c = none := by
  cases h : par M 0 c with
  | none => rfl
  | some p =>
    have := ((par0_spec M).mp h).2.1
    rw [entry_out' hc] at this; omega

theorem anc0_lt_len {M : Mat} {a b : Nat} (h : Anc0 M a b) (hne : a ≠ b) : b < M.length := by
  cases h with
  | refl => exact absurd rfl hne
  | step hp _ =>
    by_contra hc
    rw [par0_out' (by omega)] at hp; cases hp

/-- The first column after an ancestor with children is its child. -/
theorem child_succ {M : Mat} {i d : Nat} (h : Anc0 M i d) (hne : i ≠ d) : par M 0 (i + 1) = some i := by
  have hid : i < d := lt_of_le_of_ne h.le hne
  have hA := anc_between h (i + 1) (by omega) (by omega)
  cases hA with
  | @step b _ hp hA' =>
    have := hA'.le; have := par_lt M 0 _ _ hp
    have hb : b = i := by omega
    rw [hb] at hp; exact hp

/-! ## 上げの先 -/

/-- **The shape of an upgrade target**: same row-1 parent, row 0 and row 2 one above it,
and it is the next column or an ancestor. -/
theorem upg_spec {M : Mat} {n k : Nat} (h : upg M n = some k) :
    ∃ m, par M 1 n = some m ∧ par M 1 k = some m ∧
      col M k = (entry M 0 m + 1, entry M 1 n, entry M 2 m + 1) ∧
      (k = n + 1 ∨ (Anc0 M k n ∧ k < n)) := by
  unfold upg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i m hm
      simp only at h
      split at h
      · rename_i hcl
        have hc : n + 1 = k := Option.some.inj h
        subst hc
        exact ⟨m, hm, hcl.1, hcl.2, Or.inl rfl⟩
      · rw [upgClimb_find] at h
        have hp := List.find?_some h
        simp only [decide_eq_true_eq] at hp
        have hmem := List.mem_of_find?_eq_some h
        exact ⟨m, hm, hp.1, hp.2.1, Or.inr ⟨anc0_of_mem_ancL hmem, mem_ancL_lt hmem⟩⟩

/-- **An upgrade to the next column comes from a leaf.** -/
theorem leaf_of_upg_next {M : Mat} (hR0 : R0P M) {i : Nat} (h : upg M i = some (i + 1)) :
    ∀ d, Anc0 M i d → d = i := by
  intro d hd
  by_contra hne
  have hp := child_succ hd (Ne.symm hne)
  obtain ⟨m, hm, _, hcol, _⟩ := upg_spec h
  have h0 := hR0 _ _ hp
  have e0 : entry M 0 (i + 1) = (col M (i + 1)).1 := rfl
  rw [hcol] at e0
  simp only at e0
  have hmi := anc0_e0_lt (anc0_of_par M 1 m i hm) (by have := par_lt M 1 i m hm; omega)
  omega

theorem upg_succ_lt {M : Mat} {n k : Nat} (h : upg M n = some k) : n + 1 < M.length := by
  unfold upg at h
  split at h
  · cases h
  · rename_i hc
    have h1 : entry M 1 n ≠ 0 := fun e => hc (Or.inl e)
    have h3 : n + 1 ≠ M.length := fun e => hc (Or.inr (Or.inr e))
    have hn : n < M.length := by
      by_contra hn; exact h1 (entry_out' (by omega) 1)
    omega

/-! ## x を落とすときの構造の変化 -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
include hx

/-- The ancestors of `x` other than `x` are ancestors of `x − 1`. -/
theorem anc_xm1 {c : Nat} (h : Anc0 M c x) (hc : c < x) : Anc0 M c (x - 1) := by
  cases h with
  | refl => omega
  | @step b _ hp hA =>
    have hbx := par_lt M 0 x b hp
    exact Anc0.trans hA (anc_between (Anc0.step hp (Anc0.refl b)) (x - 1) (by omega) (by omega))

/-- `topped` changes only where `x` is a child. -/
theorem topped_take_eq {i : Nat} (hi : i < x) (h : x ∉ children M i) :
    topped (M.take x) i = topped M i := by
  unfold topped
  rw [children_take, children_filter_x hx h]
  cases hl : (children M i).getLast? with
  | none => rfl
  | some c =>
    have hcm := List.mem_of_getLast? hl
    have hcx : c < x := by
      have := (mem_children hcm).2
      have hne : c ≠ x := fun e => h (e ▸ hcm)
      omega
    simp only [col_take M hcx, bump_take M hi]

/-- **Where the counting changes**: at the parent of `x`, or at the target of the upgrade of `x − 1`. -/
theorem cnt_change {i c : Nat} (hi : i < x) (hcx : c < x)
    (h : ¬ (Counted (M.take x) i c ↔ Counted M i c)) : x ∈ children M c ∨ upg M (x - 1) = some c := by
  by_contra hn
  rw [not_or] at hn
  obtain ⟨hxc, hu⟩ := hn
  apply h
  have htop := topped_take_eq hx hcx hxc
  have hup : isUpg (M.take x) c = isUpg M c := by
    apply Bool.eq_iff_iff.mpr
    rw [isUpg_take M (by omega) c]
    unfold isUpg
    rw [List.any_eq_true]
    constructor
    · rintro ⟨j, hj, hjc⟩
      exact ⟨j, List.mem_range.mpr (by omega), decide_eq_true hjc⟩
    · rintro ⟨j, hj, hjc⟩
      have hjc' : upg M j = some c := of_decide_eq_true hjc
      have := upg_succ_lt hjc'
      refine ⟨j, ?_, hjc'⟩
      by_contra hjx
      have : j = x - 1 := by omega
      exact hu (this ▸ hjc')
  unfold Counted
  rw [col_take M hcx, bump_take M hi, htop, hup]

end

/-! ## C の構造の帰納法 -/

/-- The shape of a column whose `v` may change: topped in `M.take x`, no counted child there,
and no column points to it by `P_1`. -/
def TopC (M : Mat) (x i : Nat) : Prop :=
  topped (M.take x) i = true ∧ (∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c) ∧
    (∀ d, d < x → par M 1 d ≠ some i)

/-- `c′` is the first column after the subtree of `c`. -/
def NextC (M : Mat) (c c' : Nat) : Prop :=
  c < c' ∧ (∀ e, c ≤ e → e < c' → Anc0 M c e) ∧ ¬ Anc0 M c c'

/-- **The interval condition**: a change below a column off the path to `x − 1` enters only through
an upgrade into the next column after its subtree. -/
def ICC (M : Mat) (x d : Nat) : Prop :=
  ∀ c, c < x → Anc0 M c d → ¬ Anc0 M c (x - 1) →
    ∃ c', NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧ ChgX M x false c'

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **No ancestor-type upgrade into a column whose `v` may change.** -/
theorem no_anc_upg {i k : Nat} (hT : TopC M x k) (hk : k < x) (hu : upg M i = some k)
    (hA : Anc0 M k i) (hki : k < i) : False := by
  have hix : i < x := by have := upg_succ_lt hu; omega
  have hUk := hUAT i k hu (by omega)
  by_cases hxk : x ∈ children M k
  · -- `k` is the parent of `x`
    have hsplit := children_split_x hx hxk
    obtain ⟨p, hpk, hpi⟩ := anc0_child hA (by omega)
    have hpl : p < M.length := by have := hpi.le; omega
    have hpx : p < x := by have := hpi.le; omega
    have hpM : p ∈ children M k := mem_children_iff.mpr ⟨hpl, hpk⟩
    have hpT : p ∈ children (M.take x) k := by
      rw [children_take, List.mem_filter]; exact ⟨hpM, by simpa using hpx⟩
    -- the last child of `k` in `M.take x` is the bump column
    have htop := hT.1
    unfold topped at htop
    cases hl : (children (M.take x) k).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hpT; simp at hpT
    | some ℓ =>
      rw [hl] at htop
      simp only [decide_eq_true_eq] at htop
      have he2 : entry M 2 k = 1 := by have := upg_target_e2 hu; have := hZ2 k; omega
      have hlast : children (M.take x) k = (children (M.take x) k).dropLast ++ [ℓ] := by
        rw [List.dropLast_append_getLast? _ hl]
      have hall := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x)
        (Z1C_take hZ1 x) (by rw [entry_take M 2 hk]; exact he2) hlast htop p hpT
      rw [col_take M hpx, bump_take M hk] at hall
      exact hUAB i k hu (by omega) p hpM hall hpi
  · have h1 := hT.1
    rw [topped_take_eq hx hk hxk, hUk] at h1; cases h1

/-- **The structure of `C`**: a changed `v` sits on a topped column with no counted child and no
`P_1`-child; a change below a column off the path to `x − 1` enters through the next column. -/
theorem chg_struct {b : Bool} {d : Nat} (h : ChgX M x b d) :
    (b = false → d < x → TopC M x d) ∧ ICC M x d := by
  induction h with
  | leaf =>
    exact ⟨(fun h => nomatch h), fun c hc hcd hcn => (hcn (anc_xm1 hx hcd hc)).elim⟩
  | supg hne =>
    refine ⟨fun _ _ => ?_, fun c _ hcd hcn => absurd hcd hcn⟩
    have hnil : children (M.take x) (x - 1) = [] := by
      rw [children_take, List.filter_eq_nil_iff]
      intro c hc hcx
      have := (mem_children hc).1
      simp at hcx; omega
    refine ⟨by unfold topped; rw [hnil]; rfl, by rw [hnil]; simp, ?_⟩
    intro e he hp
    have := par_lt M 1 e (x - 1) hp
    omega
  | @scnt i c hc hcx hne =>
    refine ⟨(fun h => nomatch h), ?_⟩
    intro c' _ hcd hcn
    have hic := (mem_children hc).1
    have hpc : par M 0 c = some i := (mem_children_iff.mp hc).2
    have hAc : Anc0 M c (x - 1) := by
      rcases cnt_change hx (by omega) hcx hne with hxc | hu
      · exact anc_xm1 hx (Anc0.step (mem_children_iff.mp hxc).2 (Anc0.refl c)) hcx
      · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
        rcases hcase with h | ⟨hA, _⟩
        · omega
        · exact hA
    exact (hcn (Anc0.trans hcd (Anc0.step hpc (Anc0.refl i) |>.trans hAc))).elim
  | @snb i h1 h2 hxi hxb =>
    have he2 : entry M 2 i = 1 := by have := hZ2 i; omega
    have hpx : par M 0 x = some i := (mem_children_iff.mp hxi).2
    have hix : i < x := (mem_children hxi).1
    refine ⟨fun _ _ => ?_, fun c hc hcd hcn => (hcn (anc_xm1 hx (Anc0.step hpx hcd) hc)).elim⟩
    have hall := all_bump_of_last hR0 hZ2 hSD hZ1 he2 (children_split_x hx hxi) hxb
    have hT : ∀ c ∈ children (M.take x) i, col (M.take x) c = bump (M.take x) i := by
      intro c hc
      rw [children_take, List.mem_filter] at hc
      have hcx : c < x := by simpa using hc.2
      rw [col_take M hcx, bump_take M hix]
      exact hall c hc.1
    refine ⟨?_, fun c hc hcnt => hcnt.1 (hT c hc), fun e he hp => no_par1_of_e2 hZ1 (by omega) he2 hp⟩
    unfold topped
    cases hl : (children (M.take x) i).getLast? with
    | none => rfl
    | some ℓ => simpa using hT ℓ (List.mem_of_getLast? hl)
  | @ochild i c hc _ _ _ ih =>
    exact ⟨(fun h => nomatch h),
      fun c' hc' hcd hcn => ih.2 c' hc' (Anc0.step (mem_children_iff.mp hc).2 hcd) hcn⟩
  | @ov i _ ih => exact ⟨(fun h => nomatch h), ih.2⟩
  | @vpar i m _ hp _ ih =>
    have hmi := par_lt M 1 i m hp
    refine ⟨fun _ hi => absurd hp ((ih.1 rfl (by omega)).2.2 i hi), ?_⟩
    intro c hc hci hcn
    have hAm := anc0_of_par M 1 m i hp
    rcases anc0_total hci hAm with h | h
    · exact ih.2 c hc h hcn
    · by_cases hmc : m = c
      · subst hmc; exact ih.2 m hc (Anc0.refl m) hcn
      · have hix : i < x := by
          by_cases hci' : c = i
          · omega
          · have := anc0_lt_len hci hci'
            have hne : i ≠ x := fun e => hcn (anc_xm1 hx (e ▸ hci) hc)
            omega
        exact absurd hp ((ih.1 rfl (by omega)).2.2 i hix)
  | @vupg i k _ _ hu _ ih =>
    have hix : i < x := by have := upg_succ_lt hu; omega
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    refine ⟨fun _ _ => ?_, ?_⟩
    · rcases hcase with rfl | ⟨hA, hki⟩
      · have hleaf := leaf_of_upg_next hR0 hu
        have hnil : children M i = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro c hc
          have := hleaf c (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl i))
          have := (mem_children hc).1; omega
        have hnilT : children (M.take x) i = [] := by rw [children_take, hnil]; rfl
        refine ⟨by unfold topped; rw [hnilT]; rfl, by rw [hnilT]; simp, ?_⟩
        intro e _ hp
        have := hleaf e (anc0_of_par M 1 i e hp)
        have := par_lt M 1 e i hp; omega
      · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB (ih.1 rfl (by omega)) (by omega) hu hA hki).elim
    · intro c hc hci hcn
      rcases hcase with rfl | ⟨hA, hki⟩
      · by_cases hck : Anc0 M c (i + 1)
        · exact ih.2 c hc hck hcn
        · have hi1 : i + 1 < x := by
            by_contra hn
            have : i = x - 1 := by omega
            exact hcn (this ▸ hci)
          refine ⟨i + 1, ⟨by have := hci.le; omega, fun e h1 h2 => anc_between hci e h1 (by omega), hck⟩,
            hi1, by simpa using hu, by assumption⟩
      · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB (ih.1 rfl (by omega)) (by omega) hu hA hki).elim
  | @vbump i j k _ h2 hj hjb hk _ ih =>
    have hij := (mem_children hj).1
    have hjk := (mem_children hk).1
    have hkl := (mem_children hk).2
    have hjx : j < x := by omega
    have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
    have hpk : par M 0 k = some j := (mem_children_iff.mp hk).2
    refine ⟨fun _ hix => ?_, fun c hc hci hcn => ih.2 c hc (Anc0.step hpk (Anc0.step hpj hci)) hcn⟩
    have he2 : entry M 2 i = 1 := by have := hZ2 i; omega
    -- `j` is the last child of `i` in `M.take x`
    have hmax : ∀ j' ∈ children (M.take x) i, j' ≤ j := by
      intro j' hj'
      by_contra hjj
      rw [children_take, List.mem_filter] at hj'
      have hj'x : j' < x := by simpa using hj'.2
      have hpj' : par M 0 j' = some i := (mem_children_iff.mp hj'.1).2
      have hnj : ¬ Anc0 M j (x - 1) := by
        intro hA
        have h1 := anc_between hA j' (by omega) (by omega)
        have := (anc0_par h1 (by omega) hpj').le; omega
      obtain ⟨c', ⟨hjc', hall', hnot'⟩, hc'x, hup', _⟩ := ih.2 j hjx (Anc0.step hpk (Anc0.refl j)) hnj
      have hA1 : Anc0 M j (c' - 1) := hall' (c' - 1) (by omega) (by omega)
      obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hup'
      have he0 : entry M 0 c' = entry M 0 m + 1 := by
        have : entry M 0 c' = (col M c').1 := rfl
        rw [this, hcol]
      have he2c : entry M 2 c' = entry M 2 m + 1 := by
        have : entry M 2 c' = (col M c').2.2 := rfl
        rw [this, hcol]
      have hmc := par_lt M 1 _ _ hm2
      obtain ⟨hh, hph⟩ := par0_some_of (M := M) hmc (by omega)
      have hR := hR0 c' hh hph
      have hhc := par_lt M 0 c' hh hph
      have hAh : Anc0 M hh (c' - 1) :=
        anc_between (Anc0.step hph (Anc0.refl hh)) (c' - 1) (by omega) (by omega)
      have hAm : Anc0 M m (c' - 1) := anc0_of_par M 1 m (c' - 1) hm1
      have hhm : hh = m := anc0_eq_of_e0 hAh hAm (by omega)
      have hz := hZ2 c'
      have hh0 : entry M 2 hh = 0 := by rw [hhm]; omega
      have hAi : Anc0 M i (c' - 1) := Anc0.trans (Anc0.step hpj (Anc0.refl i)) hA1
      rcases anc0_total hAh hAi with hhi | hih
      · by_cases hhi' : hh = i
        · rw [hhi'] at hh0; omega
        · have hc'j' : c' ≤ j' := by
            by_contra hlt
            have := (anc0_par (hall' j' (by omega) (by omega)) (by omega) hpj').le; omega
          have hAic : Anc0 M i c' :=
            anc_between (Anc0.step hpj' (Anc0.refl i)) c' (by omega) hc'j'
          have hih := anc0_par hAic (by omega) hph
          exact hhi' (Nat.le_antisymm hhi.le hih.le)
      · rcases anc0_total hAh hA1 with hhj | hjh
        · by_cases hhj' : hh = j
          · exact hnot' (Anc0.step hph (hhj' ▸ Anc0.refl hh))
          · have hhi := anc0_par hhj hhj' hpj
            have : hh = i := Nat.le_antisymm hhi.le hih.le
            rw [this] at hh0; omega
        · exact hnot' (Anc0.step hph hjh)
    have hjT : j ∈ children (M.take x) i := by
      rw [children_take, List.mem_filter]; exact ⟨hj, by simpa using hjx⟩
    have hsplit := split_last_max _ _ (children_sorted (M.take x) i) hjT hmax
    have hall := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x)
      (Z1C_take hZ1 x) (by rw [entry_take M 2 hix]; exact he2) hsplit
      (by rw [col_take M hjx, bump_take M hix]; exact hjb)
    refine ⟨?_, fun c hc hcnt => hcnt.1 (hall c hc),
      fun e he hp => no_par1_of_e2 hZ1 (by omega) he2 hp⟩
    unfold topped
    rw [hsplit]
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, decide_eq_true_eq]
    exact hall j hjT

end

/-- The first column after the subtree of a child `s` of `i`, if it is not beyond a later child `y`
of `i`, is a child of `i`. -/
theorem next_parent {M : Mat} {i s c' y h : Nat} (hps : par M 0 s = some i) (hpy : par M 0 y = some i)
    (hsy : s < y) (hN : NextC M s c') (hph : par M 0 c' = some h) : c' ≤ y ∧ h = i := by
  obtain ⟨hsc, hall, hnot⟩ := hN
  have hyn : ¬ Anc0 M s y := fun hA => by have := (anc0_par hA (by omega) hpy).le; have := par_lt M 0 s i hps; omega
  have hc'y : c' ≤ y := by
    by_contra hlt
    exact hyn (hall y (by omega) (by omega))
  refine ⟨hc'y, ?_⟩
  have hhc := par_lt M 0 c' h hph
  have hAh : Anc0 M h (c' - 1) := anc_between (Anc0.step hph (Anc0.refl h)) (c' - 1) (by omega) (by omega)
  have hAs : Anc0 M s (c' - 1) := hall (c' - 1) (by omega) (by omega)
  rcases anc0_total hAh hAs with hhs | hsh
  · by_cases hhs' : h = s
    · exact absurd (Anc0.step hph (hhs' ▸ Anc0.refl h)) hnot
    · have hhi := anc0_par hhs hhs' hps
      by_contra hne
      have hAiy : Anc0 M i y := Anc0.step hpy (Anc0.refl i)
      have hsi := par_lt M 0 s i hps
      have hAic : Anc0 M i c' := anc_between hAiy c' (by omega) hc'y
      have hih := anc0_par hAic (by omega) hph
      exact hne (Nat.le_antisymm hhi.le hih.le)
  · exact absurd (Anc0.step hph hsh) hnot

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **(P1) After a changed child, no sibling counts** (in `M.take x`). -/
theorem chg_last {i c : Nat} (hc : c ∈ children (M.take x) i) (hC : ChgX M x true c) :
    ∀ c₂ ∈ children (M.take x) i, c < c₂ → ¬ Counted (M.take x) i c₂ := by
  intro c₂ hc₂ hcc₂ hcnt
  rw [children_take, List.mem_filter] at hc₂
  have hc₂x : c₂ < x := by simpa using hc₂.2
  have hp₂ : par M 0 c₂ = some i := (mem_children_iff.mp hc₂.1).2
  have key : ∀ n s, c₂ - s ≤ n → s ∈ children (M.take x) i → ChgX M x true s → s < c₂ → False := by
    intro n
    induction n with
    | zero => intro s hn _ _ hs; omega
    | succ n ih =>
      intro s hn hsT hCs hs
      rw [children_take, List.mem_filter] at hsT
      have hsx : s < x := by simpa using hsT.2
      have hps : par M 0 s = some i := (mem_children_iff.mp hsT.1).2
      have hnot : ¬ Anc0 M s (x - 1) := by
        intro hA
        have h1 := anc_between hA c₂ (by omega) (by omega)
        have := (anc0_par h1 (by omega) hp₂).le; have := par_lt M 0 s i hps; omega
      obtain ⟨c', hN, hc'x, hup, hCc'⟩ :=
        (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCs).2 s hsx (Anc0.refl s) hnot
      obtain ⟨m, _, hm2, hcol, _⟩ := upg_spec hup
      have he0 : entry M 0 c' = entry M 0 m + 1 := by
        have : entry M 0 c' = (col M c').1 := rfl
        rw [this, hcol]
      obtain ⟨hh, hph⟩ := par0_some_of (M := M) (par_lt M 1 _ _ hm2) (by omega)
      obtain ⟨hc'c₂, hhi⟩ := next_parent hps hp₂ hs hN hph
      rw [hhi] at hph
      have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCc').1 rfl hc'x
      have hup' : isUpg (M.take x) c' = true :=
        (isUpg_take M (by omega) c').mpr ⟨c' - 1, by have := hN.1; omega, hup⟩
      have hnc : ¬ Counted (M.take x) i c' := fun h => h.2 ⟨hup', hT.1⟩
      rcases Nat.eq_or_lt_of_le hc'c₂ with heq | hlt
      · rw [heq] at hnc; exact hnc hcnt
      · have hc'T : c' ∈ children (M.take x) i := by
          rw [children_take, List.mem_filter]
          exact ⟨mem_children_iff.mpr ⟨by omega, hph⟩, by simpa using hc'x⟩
        exact ih c' (by have := hN.1; omega) hc'T (ChgX.ov hCc') hlt
  exact key _ c (Nat.le_refl _) hc hC hcc₂

end

end Ytosk
