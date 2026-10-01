/-
**3 行・t = 1・q ≠ r: t1_main2 の構造の仮定を構造の不変条件から出す。**

x = r + L が最後の列、r = P_1(x)、q = P_0(x) ≠ r、x の行 2 は 0。依存の閉包 D = `DepX M x` について:
- D の部分木からの出口は、部分木の直後の列への上げ（その列の v が D）だけ（`dep_exit`）。
- 経路の子 p より前にある兄弟の部分木には D がない（`nodep_sib`）。とくに v(q) は D でない（`nodep_v_q`）。
- これから o の呼び出しの形 OShape（`hOS_t1`）。
- 経路を上ると D が続く（`path_up`）: r と根 Rt の o は D（`hrD_t1`・`hRd_t1`）。
- hS2・hS3 は D によらず構造だけから（`hS2_t1`・`hS3_t1`）。
新しい不変条件: 行 1 が 0 なら行 2 も 0（`R12`）、のりしろの子の親は行 2 が 1（`BumpE2`）。
-/
import Ytosk.V3ChgS
import Ytosk.V3BaseT1

namespace Ytosk

open T

/-- Row 1 zero forces row 2 zero. -/
def R12 (M : Mat) : Prop := ∀ i, entry M 1 i = 0 → entry M 2 i = 0

/-- A bump child sits only under a column with row 2 equal to `1`. -/
def BumpE2 (M : Mat) : Prop := ∀ p c, c ∈ children M p → col M c = bump M p → entry M 2 p = 1

/-- Every dependency is a change. -/
theorem depX_chgX {M : Mat} {x : Nat} {b : Bool} {i : Nat} (h : DepX M x b i) : ChgX M x b i := by
  induction h with
  | leaf => exact ChgX.leaf
  | ochild hc hb hu _ ih => exact ChgX.ochild hc hb hu ih
  | ov _ ih => exact ChgX.ov ih
  | vpar h1 hp _ ih => exact ChgX.vpar h1 hp ih
  | vupg h1 h2 hu _ ih => exact ChgX.vupg h1 h2 hu ih
  | vbump h1 h2 hj hjb hk _ ih => exact ChgX.vbump h1 h2 hj hjb hk ih

/-- An upgraded column has row 1 nonzero and row 2 not `1`. -/
theorem upg_e12 {M : Mat} {n k : Nat} (h : upg M n = some k) : entry M 1 n ≠ 0 ∧ entry M 2 n ≠ 1 := by
  unfold upg at h
  split at h
  · cases h
  · rename_i hc
    exact ⟨fun e => hc (Or.inl e), fun e => hc (Or.inr (Or.inl e))⟩

theorem e2_of_col {M : Mat} {i : Nat} {a b c : Nat} (h : col M i = (a, b, c)) : entry M 2 i = c := by
  have : entry M 2 i = (col M i).2.2 := rfl
  rw [this, h]

theorem e1_of_col {M : Mat} {i : Nat} {a b c : Nat} (h : col M i = (a, b, c)) : entry M 1 i = b := by
  have : entry M 1 i = (col M i).2.1 := rfl
  rw [this, h]

theorem e0_of_col {M : Mat} {i : Nat} {a b c : Nat} (h : col M i = (a, b, c)) : entry M 0 i = a := by
  have : entry M 0 i = (col M i).1 := rfl
  rw [this, h]

/-- An upgrade target never has row 2 zero. -/
theorem upg_ne_e2z {M : Mat} {n k : Nat} (h : upg M n = some k) (hk : entry M 2 k = 0) : False := by
  have := upg_target_e2 h; omega

/-- Nothing is an ancestor of a column beyond the matrix. -/
theorem not_anc_out {M : Mat} {t k : Nat} (hk : M.length ≤ k) (ht : t < M.length) : ¬ Anc0 M t k := by
  intro h
  cases h with
  | refl => omega
  | step hp _ => rw [par0_out' hk] at hp; cases hp

/-- A parent from an ancestor of the parent's child. -/
theorem par0_of_anc {M : Mat} {a c : Nat} (h : Anc0 M a c) (hne : a ≠ c) : ∃ p, par M 0 c = some p := by
  cases h with
  | refl => exact absurd rfl hne
  | step hp _ => exact ⟨_, hp⟩

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2

/-- **The exit of `D` from a subtree** not containing `x`: an upgrade into the next column after the
subtree, whose `v` is in `D`. -/
theorem dep_exit {b : Bool} {d : Nat} (h : DepX M x b d) :
    ∀ c, Anc0 M c d → ¬ Anc0 M c x →
      ∃ c', NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧ DepX M x false c' := by
  induction h with
  | leaf => intro c hc hn; exact absurd hc hn
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
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i hix hp
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
            exact upg_ne_e2z hu hx2
        exact ⟨i + 1, ⟨by have := hci.le; omega, fun e h1 h2 => anc_between hci e h1 (by omega), hck⟩,
          hi1, by simpa using hu, hdk⟩
      · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
          ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl (by omega))
          (by omega) hu hA hki).elim
  | @vbump i j k _ _ hj _ hk _ ih =>
    intro c hci hn
    exact ih c (Anc0.step (mem_children_iff.mp hk).2 (Anc0.step (mem_children_iff.mp hj).2 hci)) hn

/-- **No `D` below an earlier sibling of a column on the path to `x`**, if that column's `v` is not
in `D`. -/
theorem nodep_sib {p a : Nat} (hpa : par M 0 p = some a) (hpx : Anc0 M p x)
    (hnp : p < x → ¬ DepX M x false p) :
    ∀ n c, p - c ≤ n → c ∈ children M a → c < p → ∀ b d, DepX M x b d → ¬ Anc0 M c d := by
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
    obtain ⟨c', hN, hc'x, _, hdc'⟩ := dep_exit hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hd c hcd hcx
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

/-- **`v(q)` is not in `D`** (`q` the parent of `x`). -/
theorem nodep_v_q {q : Nat} (hq : par M 0 x = some q) : ¬ DepX M x false q := by
  intro h
  have hqx := par_lt M 0 x q hq
  have hxq : x ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  cases h with
  | vpar _ hp hdm =>
    have hmq := par_lt M 1 q _ hp
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 q hqx hp
  | @vupg _ k _ _ hu hdk =>
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with rfl | ⟨hA, hki⟩
    · have := leaf_of_upg_next hR0 hu x (Anc0.step hq (Anc0.refl q)); omega
    · exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
        ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl (by omega)) (by omega) hu hA hki
  | @vbump _ j k _ _ hj hjb hk hdk =>
    have hjx : j < x := by
      have := (mem_children hj).2
      rcases Nat.lt_or_ge j x with h | h
      · exact h
      · exfalso
        have : j = x := by omega
        subst this
        have := e2_of_col hjb; omega
    exact nodep_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq (Anc0.refl x) (fun h => absurd h (lt_irrefl _))
      _ j (Nat.le_refl _) hj hjx true k hdk (Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j))

end

/-- Counting in `M` gives counting in `M.take x`, away from the parent of `x`. -/
theorem cnt_take_of_M {M : Mat} {x : Nat} (hx : x + 1 = M.length) {i c : Nat} (hi : i < x) (hcx : c < x)
    (hxc : x ∉ children M c) (h : Counted M i c) : Counted (M.take x) i c := by
  obtain ⟨hb, hu⟩ := h
  refine ⟨by rw [col_take M hcx, bump_take M hi]; exact hb, ?_⟩
  rintro ⟨hiu, htop⟩
  apply hu
  refine ⟨?_, by rw [← topped_take_eq hx hcx hxc]; exact htop⟩
  obtain ⟨k, hk, hkc⟩ := (isUpg_take M (by omega) c).mp hiu
  unfold isUpg
  rw [List.any_eq_true]
  exact ⟨k, List.mem_range.mpr (by omega), decide_eq_true hkc⟩

/-- The order of a sibling list split at `c`. -/
theorem sib_order {l L R : List Nat} {c : Nat} (hs : l.Pairwise (· < ·)) (h : l = L ++ c :: R) :
    (∀ d ∈ L, d < c) ∧ (∀ d ∈ R, c < d) := by
  rw [h, List.pairwise_append] at hs
  obtain ⟨_, hcR, hLc⟩ := hs
  rw [List.pairwise_cons] at hcR
  exact ⟨fun d hd => hLc d hd c List.mem_cons_self, hcR.1⟩

/-- Not counted, as the disjunction in `OShape`. -/
theorem not_counted_iff {M : Mat} {i d : Nat} (h : ¬ Counted M i d) :
    col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
  by_cases h1 : col M d = bump M i
  · exact Or.inl h1
  · exact Or.inr (by by_contra h2; exact h ⟨h1, h2⟩)

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq

/-- **(P1 in `M`)** After a child in `D`, no sibling counts. -/
theorem p1_dep {i c c₂ : Nat} (hi : i < x) (hc : c ∈ children M i) (hc₂ : c₂ ∈ children M i)
    (hcc : c < c₂) (hD : DepX M x true c) (hcnt : Counted M i c₂) : False := by
  have hc₂l := (mem_children hc₂).2
  have hpc₂ : par M 0 c₂ = some i := (mem_children_iff.mp hc₂).2
  rcases Nat.lt_or_ge c₂ x with hc₂x | hc₂x
  · by_cases hxc : x ∈ children M c₂
    · have hqc : q = c₂ := by rw [(mem_children_iff.mp hxc).2] at hq; exact (Option.some.inj hq).symm
      subst hqc
      exact nodep_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hpc₂ (Anc0.step hq (Anc0.refl q))
        (fun _ => nodep_v_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq) _ c (Nat.le_refl _) hc hcc true c hD
        (Anc0.refl c)
    · have hcT : c ∈ children (M.take x) i := by
        rw [children_take, List.mem_filter]; exact ⟨hc, by simpa using (show c < x by omega)⟩
      have hc₂T : c₂ ∈ children (M.take x) i := by
        rw [children_take, List.mem_filter]; exact ⟨hc₂, by simpa using hc₂x⟩
      exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hcT (depX_chgX hD) c₂ hc₂T hcc
        (cnt_take_of_M hx hi hc₂x hxc hcnt)
  · have hc₂e : c₂ = x := by omega
    subst hc₂e
    have hiq : i = q := by rw [hpc₂] at hq; exact Option.some.inj hq
    subst hiq
    exact nodep_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq (Anc0.refl c₂) (fun h => absurd h (lt_irrefl _))
      _ c (Nat.le_refl _) hc hcc true c hD (Anc0.refl c)

/-- **A column whose `v` is in `D` counts no child** (in `M`). -/
theorem uncnt_of_depv {i d : Nat} (hi : i < x) (hv : DepX M x false i) (hd : d ∈ children M i) :
    ¬ Counted M i d := by
  have hdl := (mem_children hd).2
  have hpd : par M 0 d = some i := (mem_children_iff.mp hd).2
  have hid := (mem_children hd).1
  rcases Nat.lt_or_ge d x with hdx | hdx
  · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hv)).1 rfl hi
    have hdT : d ∈ children (M.take x) i := by
      rw [children_take, List.mem_filter]; exact ⟨hd, by simpa using hdx⟩
    by_cases hxd : x ∈ children M d
    · -- `d = q` is the last child of `i` in `M.take x`
      have hAdx : Anc0 M d x := Anc0.step (mem_children_iff.mp hxd).2 (Anc0.refl d)
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
    have hiq : i = q := by rw [hpd] at hq; exact Option.some.inj hq
    subst hiq
    exact absurd hv (nodep_v_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq)

/-- **`hOS`: the shape at every `o` call in `D`.** -/
theorem hOS_t1 : ∀ i, i < x → DepX M x true i → OShape M x i := by
  intro i hi hD
  by_cases hv : DepX M x false i
  · exact Or.inl ⟨hv, fun d hd =>
      not_counted_iff (uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv hd)⟩
  · refine Or.inr ⟨hv, ?_⟩
    cases hD with
    | leaf => exact absurd hi (lt_irrefl _)
    | @ochild _ c hc hcb hcu hdc =>
      obtain ⟨L, R, hLR⟩ := List.append_of_mem hc
      obtain ⟨hL, hR⟩ := sib_order (children_sorted M i) hLR
      refine ⟨L, c, R, hLR, hcb, hcu, fun d hd => ?_, fun d hd hcnt hdD => ?_⟩
      · have hdM : d ∈ children M i := by rw [hLR]; simp [hd]
        exact not_counted_iff (fun h => p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hc hdM (hR d hd) hdc h)
      · have hdM : d ∈ children M i := by rw [hLR]; simp [hd]
        exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hdM hc (hL d hd) hdD ⟨hcb, hcu⟩
    | ov h => exact (hv h).elim

end

end Ytosk
