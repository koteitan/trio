/-
**3 行・t = 2: D の形の補題（x の行 2 が 1 でもよい形）。**

V3StructT1・V3VLocT1 の補題（`dep_exit`・`nodep_sib`・`nodep_v_q`・`p1_dep`・`uncnt_of_depv`・`hOS_t1`・
`nodep_not_last`・`dv_shape`）は x の行 2 が 0 であること（hx2）を 3 か所でしか使わない:
x へ上げる列がないこと（2 か所）と、x がのりしろの子でないこと（1 か所）。
ここではこの 2 つ（hXu・hXb）を仮定にした写し（名前の末尾 X）を置く。証明は同じ。
-/
import Ytosk.V3MainT1F

namespace Ytosk

open T

set_option linter.unusedSectionVars false


section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hXu : ∀ i, upg M i ≠ some x) (hXb : ∀ p, col M x ≠ bump M p)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb

/-- **The exit of `D` from a subtree** not containing `x`: an upgrade into the next column after the
subtree, whose `v` is in `D`. -/
theorem dep_exitX {b : Bool} {d : Nat} (h : DepX M x b d) :
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
            exact absurd hu (hXu _)
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
theorem nodep_sibX {p a : Nat} (hpa : par M 0 p = some a) (hpx : Anc0 M p x)
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
    obtain ⟨c', hN, hc'x, _, hdc'⟩ := dep_exitX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hd c hcd hcx
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
theorem nodep_v_qX {q : Nat} (hq : par M 0 x = some q) : ¬ DepX M x false q := by
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
        exact hXb _ hjb
    exact nodep_sibX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq (Anc0.refl x) (fun h => absurd h (lt_irrefl _))
      _ j (Nat.le_refl _) hj hjx true k hdk (Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j))

end

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hXu : ∀ i, upg M i ≠ some x) (hXb : ∀ p, col M x ≠ bump M p) {q : Nat} (hq : par M 0 x = some q)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq

/-- **(P1 in `M`)** After a child in `D`, no sibling counts. -/
theorem p1_depX {i c c₂ : Nat} (hi : i < x) (hc : c ∈ children M i) (hc₂ : c₂ ∈ children M i)
    (hcc : c < c₂) (hD : DepX M x true c) (hcnt : Counted M i c₂) : False := by
  have hc₂l := (mem_children hc₂).2
  have hpc₂ : par M 0 c₂ = some i := (mem_children_iff.mp hc₂).2
  rcases Nat.lt_or_ge c₂ x with hc₂x | hc₂x
  · by_cases hxc : x ∈ children M c₂
    · have hqc : q = c₂ := by rw [(mem_children_iff.mp hxc).2] at hq; exact (Option.some.inj hq).symm
      subst hqc
      exact nodep_sibX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hpc₂ (Anc0.step hq (Anc0.refl q))
        (fun _ => nodep_v_qX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq) _ c (Nat.le_refl _) hc hcc true c hD
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
    exact nodep_sibX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq (Anc0.refl c₂) (fun h => absurd h (lt_irrefl _))
      _ c (Nat.le_refl _) hc hcc true c hD (Anc0.refl c)

/-- **A column whose `v` is in `D` counts no child** (in `M`). -/
theorem uncnt_of_depvX {i d : Nat} (hi : i < x) (hv : DepX M x false i) (hd : d ∈ children M i) :
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
    exact absurd hv (nodep_v_qX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq)

/-- **`hOS`: the shape at every `o` call in `D`.** -/
theorem hOS_t1X : ∀ i, i < x → DepX M x true i → OShape M x i := by
  intro i hi hD
  by_cases hv : DepX M x false i
  · exact Or.inl ⟨hv, fun d hd =>
      not_counted_iff (uncnt_of_depvX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq hi hv hd)⟩
  · refine Or.inr ⟨hv, ?_⟩
    cases hD with
    | leaf => exact absurd hi (lt_irrefl _)
    | @ochild _ c hc hcb hcu hdc =>
      obtain ⟨L, R, hLR⟩ := List.append_of_mem hc
      obtain ⟨hL, hR⟩ := sib_order (children_sorted M i) hLR
      refine ⟨L, c, R, hLR, hcb, hcu, fun d hd => ?_, fun d hd hcnt hdD => ?_⟩
      · have hdM : d ∈ children M i := by rw [hLR]; simp [hd]
        exact not_counted_iff (fun h => p1_depX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq hi hc hdM (hR d hd) hdc h)
      · have hdM : d ∈ children M i := by rw [hLR]; simp [hd]
        exact p1_depX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq hi hdM hc (hL d hd) hdD ⟨hcb, hcu⟩
    | ov h => exact (hv h).elim

end

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hXu : ∀ i, upg M i ≠ some x) (hXb : ∀ p, col M x ≠ bump M p) {q : Nat} (hq : par M 0 x = some q)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq

/-- No `o` in `D` below a child of `p` (a column with row 2 nonzero) that has a later child,
counting `x` as a later child of `q`. -/
theorem nodep_not_lastX {p d d' : Nat} (h2 : entry M 2 p ≠ 0) (hd : d ∈ children M p)
    (hd' : d' ∈ children M p) (hdd : d < d') {b : Bool} {e : Nat} (hD : DepX M x b e)
    (hde : Anc0 M d e) : False := by
  have hd'l := (mem_children hd').2
  rcases Nat.lt_or_ge d' x with hd'x | hd'x
  · exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hd (mem_take_children hd' hd'x) hdd
      (depX_chgX hD) hde
  · have hd'e : d' = x := by omega
    subst hd'e
    have hpq : p = q := by
      rw [(mem_children_iff.mp hd').2] at hq; exact Option.some.inj hq
    subst hpq
    exact nodep_sibX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq (Anc0.refl d') (fun h => absurd h (lt_irrefl _))
      _ d (Nat.le_refl _) hd hdd b e hD hde

/-- **The shape of a `v` call in `D`.** -/
theorem dv_shapeX {i : Nat} (hi : i < x) (hv : DepX M x false i) :
    entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
    ((entry M 2 i = 0 ∧ upg M i = some (i + 1) ∧ i + 1 < x ∧ DepX M x false (i + 1)) ∨
     (entry M 2 i ≠ 0 ∧ ∃ L K j k, children M i = L ++ [j] ∧ col M j = bump M i ∧
        children M j = K ++ [k] ∧ DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
        (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e))) := by
  have hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m := by
    intro m hp hdm
    have hmi := par_lt M 1 i m hp
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i hi hp
  cases hv with
  | vpar h1 hp hdm => exact absurd hdm (hpd _ hp)
  | @vupg _ k h1 h2 hu hdk =>
    refine ⟨h1, hpd, Or.inl ⟨h2, ?_⟩⟩
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with rfl | ⟨hA, hki⟩
    · refine ⟨hu, ?_, hdk⟩
      have := upg_succ_lt hu
      rcases Nat.lt_or_ge (i + 1) x with h | h
      · exact h
      · exfalso
        have hix : i + 1 = x := by omega
        rw [hix] at hu; exact absurd hu (hXu _)
    · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
        ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl (by omega)) (by omega)
        hu hA hki).elim
  | @vbump _ j k h1 h2 hj hjb hk hdk =>
    refine ⟨h1, hpd, Or.inr ⟨h2, ?_⟩⟩
    have hj2 : entry M 2 j ≠ 0 := by
      have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
    have hAjk : Anc0 M j k := Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j)
    -- `j` is the last child of `i`
    have hjmax : ∀ j' ∈ children M i, j' ≤ j := by
      intro j' hj'; by_contra hlt
      exact nodep_not_lastX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq h2 hj hj' (by omega) hdk hAjk
    have hchi := split_last_max _ _ (children_sorted M i) hj hjmax
    -- `k` is the last child of `j`
    have hkmax : ∀ k' ∈ children M j, k' ≤ k := by
      intro k' hk'; by_contra hlt
      exact nodep_not_lastX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq hj2 hk hk' (by omega) hdk (Anc0.refl k)
    have hchj := split_last_max _ _ (children_sorted M j) hk hkmax
    refine ⟨_, _, j, k, hchi, hjb, hchj, hdk, ?_, ?_⟩
    · intro d hd hdD
      have hdM : d ∈ children M j := (List.mem_filter.mp hd).1
      have hdk' : d < k := by simpa using (List.mem_filter.mp hd).2
      exact nodep_not_lastX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq hj2 hdM hk hdk' hdD (Anc0.refl d)
    · intro d hd e he
      have hdM : d ∈ children M i := (List.mem_filter.mp hd).1
      have hdj : d < j := by simpa using (List.mem_filter.mp hd).2
      have hpe : par M 0 e = some d := (mem_children_iff.mp he).2
      have hAde : Anc0 M d e := Anc0.step hpe (Anc0.refl d)
      have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
      have hjx : j < x := by
        rcases Nat.lt_or_ge j x with h | h
        · exact h
        · exfalso
          have : j = x := by have := (mem_children hj).2; omega
          subst this
          exact hXb _ hjb
      have hej : e < j := by
        by_contra hge
        have hA := anc_between hAde j (by omega) (by omega)
        have := (anc0_par hA (by omega) hpj).le
        have := (mem_children hdM).1
        omega
      exact ⟨by omega, fun hD =>
        nodep_not_lastX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hq h2 hdM hj hdj hD hAde⟩

end

/-- A column with row 2 zero is neither a bump child nor an upgrade target. -/
theorem ne_of_e2z {M : Mat} {d : Nat} (h : entry M 2 d = 0) :
    ∀ p, ((∃ t, col M p = bump M t) ∨ isUpg M p = true) → p ≠ d := by
  intro p hp e
  subst e
  rcases hp with ⟨t, hb⟩ | hu
  · have := e2_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb); omega
  · unfold isUpg at hu
    rw [List.any_eq_true] at hu
    obtain ⟨k, _, hk⟩ := hu
    have := upg_target_e2 (of_decide_eq_true hk); omega

section
variable {M : Mat} {x : Nat} (hUAT : UAT M) (hZ2 : Z2 M) (hR12 : R12 M) (hBE : BumpE2 M)
include hUAT hZ2 hR12 hBE

/-- **Up the path, `D` continues** (general start): if `o(d)` is in `D`, `d` is neither a bump child nor upgraded, and the subtree of every
column strictly between `a` and `d` on the path ends at `d`, then `o(a)` is in `D`. -/
theorem path_upG (n : Nat) : ∀ a d, d - a ≤ n → d < M.length → Anc0 M a d →
    (∀ p, ((∃ t, col M p = bump M t) ∨ isUpg M p = true) → p ≠ d) →
    DepX M x true d → (∀ t, a < t → Anc0 M t d → ¬ Anc0 M t (d + 1)) → DepX M x true a := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro a d hn hdl had hd2 hD hend
  have key : ∀ m t, d - t ≤ m → Anc0 M a t → Anc0 M t d → DepX M x true t := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro t hm hat htd
    by_cases htd' : t = d
    · subst htd'; exact hD
    obtain ⟨p, hpt, hpd⟩ := anc0_child htd htd'
    have htp := par_lt M 0 p t hpt
    have hpdl := hpd.le
    have hpl : p < M.length := by omega
    have hpM : p ∈ children M t := mem_children_iff.mpr ⟨hpl, hpt⟩
    have hat' := hat.le
    have hap : Anc0 M a p := Anc0.trans hat (Anc0.step hpt (Anc0.refl t))
    have hDp : DepX M x true p := ihm (d - p) (by omega) p (Nat.le_refl _) hap hpd
    by_cases hc : Counted M t p
    · exact DepX.ochild hpM hc.1 hc.2 hDp
    · rcases not_counted_iff hc with hb | ⟨hiu, htop⟩
      · -- a bump edge: `v(t)` reads the grandchild on the path
        have hp2 : entry M 2 p = 1 := e2_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb)
        have hpd' : p ≠ d := hd2 p (Or.inl ⟨t, hb⟩)
        obtain ⟨p', hpp', hp'd⟩ := anc0_child hpd hpd'
        have hp'dl := hp'd.le
        have hp'M : p' ∈ children M p := mem_children_iff.mpr ⟨by omega, hpp'⟩
        have hpp'lt := par_lt M 0 p' p hpp'
        have hDp' : DepX M x true p' := ihm (d - p') (by omega) p' (Nat.le_refl _)
          (Anc0.trans hap (Anc0.step hpp' (Anc0.refl p))) hp'd
        have he1 : entry M 1 t ≠ 0 := by
          have h1 : entry M 1 p = entry M 1 t :=
            e1_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb)
          intro h0
          rw [← h1] at h0
          have := hR12 p h0
          omega
        have he2 : entry M 2 t ≠ 0 := by rw [hBE t p hpM hb]; omega
        exact DepX.ov (DepX.vbump he1 he2 hpM hb hp'M hDp')
      · -- an upgraded, topped child: around through `p − 1`
        have hiu0 := hiu
        unfold isUpg at hiu
        rw [List.any_eq_true] at hiu
        obtain ⟨k0, _, hk0⟩ := hiu
        have hu : upg M k0 = some p := of_decide_eq_true hk0
        have hk0p : k0 = p - 1 := by
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
          rcases hcase with h | ⟨hA, hlt⟩
          · omega
          · exfalso
            have := hUAT k0 p hu (by have := hA.le; omega)
            rw [this] at htop; cases htop
        rw [hk0p] at hu
        obtain ⟨_, _, _, hcol, _⟩ := upg_spec hu
        have hp2 := upg_target_e2 hu
        have hpd' : p ≠ d := hd2 p (Or.inr hiu0)
        have hpd2 : p < d := by omega
        obtain ⟨p', hpp', hp'd⟩ := anc0_child hpd hpd'
        have hp'dl := hp'd.le
        have hpp'lt := par_lt M 0 p' p hpp'
        have hp'M : p' ∈ children M p := mem_children_iff.mpr ⟨by omega, hpp'⟩
        have hlast := last_child_path hdl hpp' hp'd (hend p (by omega) hpd)
        unfold topped at htop
        rw [hlast] at htop
        have hb' : col M p' = bump M p := by simpa using htop
        have hp'2 : entry M 2 p' = 1 :=
          e2_of_col (show col M p' = (entry M 0 p + 1, entry M 1 p, 1) from hb')
        have hp'd' : p' ≠ d := hd2 p' (Or.inl ⟨p, hb'⟩)
        obtain ⟨p'', hpp'', hp''d⟩ := anc0_child hp'd hp'd'
        have hp''dl := hp''d.le
        have hpp''lt := par_lt M 0 p'' p' hpp''
        have hp''M : p'' ∈ children M p' := mem_children_iff.mpr ⟨by omega, hpp''⟩
        have hDp'' : DepX M x true p'' := ihm (d - p'') (by omega) p'' (Nat.le_refl _)
          (Anc0.trans hap (Anc0.step hpp'' (Anc0.step hpp' (Anc0.refl p)))) hp''d
        obtain ⟨he1, he2⟩ := upg_e12 hu
        have he2z : entry M 2 (p - 1) = 0 := by have := hZ2 (p - 1); omega
        have hp1 : entry M 1 p = entry M 1 (p - 1) := e1_of_col hcol
        have hvp : DepX M x false p :=
          DepX.vbump (by rw [hp1]; exact he1) (by omega) hp'M hb' hp''M hDp''
        have hvp1 : DepX M x true (p - 1) := DepX.ov (DepX.vupg he1 he2z hu hvp)
        have hAt : Anc0 M t (p - 1) :=
          anc_between (Anc0.step hpt (Anc0.refl t)) (p - 1) (by omega) (by omega)
        refine ihn ((p - 1) - t) (by omega) t (p - 1) (Nat.le_refl _) (by omega) hAt (ne_of_e2z he2z) hvp1 ?_
        intro u htu hup hup'
        rw [show p - 1 + 1 = p by omega] at hup'
        by_cases hup2 : u = p
        · have := hup.le; omega
        · have := (anc0_par hup' hup2 hpt).le; omega
  exact key (d - a) a (Nat.le_refl _) (Anc0.refl a) had

/-- **Every ancestor of `x` has its `o` in `D`** when `x` is neither a bump child nor upgraded. -/
theorem dep_anc_xG (hx : x + 1 = M.length)
    (hxn : ∀ p, ((∃ t, col M p = bump M t) ∨ isUpg M p = true) → p ≠ x) {a : Nat} (ha : Anc0 M a x) :
    DepX M x true a :=
  path_upG hUAT hZ2 hR12 hBE (x - a) a x (Nat.le_refl _) (by omega) ha hxn DepX.leaf
    (fun t _ htx => not_anc_out (by omega) (by have := htx.le; omega))

end

end Ytosk
