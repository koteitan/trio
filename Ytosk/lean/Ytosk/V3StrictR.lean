/-
**3 行・t = 1・q ≠ r: o(r) は M.take x で実際に変わる（狭義性、仮定 hne を外す）。**

D = DepX M x の呼び出しは、M′ = M.take x で値が真に下がる（`dep_strict`、D の導出についての帰納法）。
- o の枠（ochild）: 最後の数える子 c。M′ に数える子がなければ ψ_{v′}(0) < ψ_v(X)（X ≠ 0）。
  c が M′ でも最後の数える子なら、step の狭義単調性（`step_lt`）。新しい子だけが書き換える枠は
  M 側の子の引数が 0 の場合だけで、そのとき M′ 側の引数も 0（`arg0_take`）なので起きない。
  c が M′ で数えられないなら、末尾を落とすと真に下がる（`lt_spArg`）。
- ov: v が下がれば ψ_{v′}(0) < ψ_v(X)。vpar は起きない（TopC）。vupg は v(i) = v(k)。
- vbump: V + ω^{P + ω^G} の G の最後の項が下がる（和・ω^・加法の狭義単調性）。
まとめ: o′(r) ≠ o(r)（`o_r_strict`）。hne を外した `t1_main_strict`。新しい仮定は要らない。
-/
import Ytosk.V3ValT1R

namespace Ytosk

open T

/-! ## H・step・spArg の狭義単調性 -/

/-- In the frame where only `c` rewrites, `B + c' < H(s, y)`. -/
theorem lt_tn {a B s' y' s y : T} (hc : isOT (psi s y z) = true)
    (hl : psi s' y' z < psi s y z)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) :
    app B (psi s' y' z) < H s y := by
  rw [H_eq hc]
  have hBhi := B_le_hi hc ht.1 hB
  have hss : s' ≤ s := by
    rcases psi_lt_psi_z_iff.mp hl with h | ⟨rfl, _⟩
    · exact le_of_lt h
    · exact le_refl _
  have hcθ : psi s' y' z < psi (succ s) z z :=
    psi_lt_psi_z_iff.mpr (Or.inl (lt_of_le_of_lt hss (lt_succ_self s)))
  rcases (le_iff _ _).mp hBhi with h | h
  · exact lt_of_lt_of_le (app_lt_of_lt_hi h (split_fst_ge _ y) (Or.inr (by simpa [head] using hcθ)))
      (le_app_self _ _)
  · have hlo : (split y (psi (succ s) z z)).2 ≠ z := by
      intro hlo
      have e := split_app (psi (succ s) z z) y
      rw [hlo, app_z_right, ← h] at e
      have := ht.1; rw [← e] at this; exact lt_irrefl' _ this
    rw [if_neg hlo, ← h]
    exact app_lt_app_left B hl

/-- **One frame is strictly monotone in the appended child**, when the child drops by `◁` (or has
argument `0`), its subscript is small, and an old child with argument `0` has a new child with
argument `0`. -/
theorem step_lt {a B s' y' s y : T} (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hrel : Lhd z (psi s' y' z) (psi s y z) ∨ (y' = z ∧ psi s' y' z < psi s y z))
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hsub' : SubSmall a s') (hy : y = z → y' = z) :
    step a B s' y' z < step a B s y z := by
  have hl : psi s' y' z < psi s y z := by
    rcases hrel with h | h
    · exact h.1
    · exact h.2
  by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
  · have hLhd : Lhd z (psi s' y' z) (psi s y z) := by
      rcases hrel with h | ⟨hz, _⟩
      · exact h
      · exfalso; have := ht'.1; rw [hz] at this; exact T.not_lt_z _ this
    have hac : psi a z z < psi s y z := lt_trans (show psi a z z < psi s' y' z from ht'.2) hl
    by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · unfold step
      rw [if_pos ht', if_pos ht]
      rcases psi_lt_psi_z_iff.mp hl with hss | ⟨rfl, hyy⟩
      · obtain ⟨_, hyle⟩ := comps_le_of_sub_lt hLhd hss hsub'
        rw [H_of_le_om hc' (ne_z_of_lt ht'.1) hyle]
        have h1 : psi s' y' z < psi (succ s') z z :=
          psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s'))
        exact lt_of_lt_of_le (lt_of_lt_of_le h1 (psi_le_psi_z (succ_le_of_lt hss)))
          (om_le_H hc (ne_z_of_lt ht.1))
      · exact H_lt_H hc' hc hyy
    · exfalso
      have hyB : ¬ B < y := fun h => ht ⟨h, hac⟩
      rcases psi_lt_psi_z_iff.mp hl with hss | ⟨rfl, hyy⟩
      · obtain ⟨_, hyle⟩ := comps_le_of_sub_lt hLhd hss hsub'
        by_cases hBz : B = z
        · subst hBz
          have hyz : y = z := by
            by_contra h; exact hyB (lt_of_le_of_ne (z_le _) (Ne.symm h))
          have h0 := ht'.1
          rw [hy hyz] at h0; exact T.not_lt_z _ h0
        · have hcB : psi s y z ≤ B := le_trans (hBc _ (head_mem_summands hBz)) (head_le_self B)
          have hy'c : y' ≤ psi s y z :=
            le_trans hyle (le_trans (psi_le_psi_arg (z_le y')) (le_of_lt hl))
          exact lt_irrefl' B (lt_of_lt_of_le (show B < y' from ht'.1) (le_trans hy'c hcB))
      · exact hyB (lt_trans ht'.1 hyy)
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · unfold step
      rw [if_neg ht', if_pos ht]
      have hadd : add B (psi s' y' z) = app B (psi s' y' z) := by
        have := add_app_drop (lo := z) (B := B) (s := s') (y := y')
          (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le (lt_trans hlt hl) (hBc q hq))) (Or.inl rfl)
        rwa [app_z_right] at this
      rw [hadd]
      exact lt_tn hc hl ht hBc
    · unfold step
      rw [if_neg ht', if_neg ht]
      exact add_lt_add_left B hl

/-- One step strictly grows the state. -/
theorem lt_step {a B s y : T} (hc : isOT (psi s y z) = true) (c : T) : B < step a B s y c := by
  unfold step
  split_ifs with ht
  · exact lt_of_lt_of_le ht.1 (le_H hc)
  · have := add_lt_add_left B (T.z_lt_psi s y z)
    rwa [add_z_right] at this

/-- The state only grows. -/
theorem le_spArg (a : T) : ∀ (c b : T), isOT c = true → b ≤ spArg a b c
  | z, b, _ => le_refl _
  | psi s y c, b, h => by
    rw [spArg_cons]
    exact le_trans (le_of_lt (lt_step (isOT_head h) c)) (le_spArg a c _ (isOT_rest h))

/-- **A nonzero tail strictly grows the state.** -/
theorem lt_spArg (a : T) {b c : T} (hc : isOT c = true) (hne : c ≠ z) : b < spArg a b c := by
  cases c with
  | z => exact absurd rfl hne
  | psi s y c =>
    rw [spArg_cons]
    exact lt_of_lt_of_le (lt_step (isOT_head hc) c) (le_spArg a c _ (isOT_rest hc))

/-! ## 和の単調性 -/

theorem foldl_sf_le : ∀ {l' l : List T}, List.Forall₂ (· ≤ ·) l' l → ∀ (acc' acc : T),
    isOT acc' = true → isOT acc = true → (∀ t ∈ l', isOT t = true) → (∀ t ∈ l, isOT t = true) →
    acc' ≤ acc → l'.foldl (fun a b => sf (add a b)) acc' ≤ l.foldl (fun a b => sf (add a b)) acc
  | _, _, .nil, _, _, _, _, _, _, h => h
  | _, _, .cons (a := t') (b := t) htt hrest, acc', acc, h1, h2, hl', hl, hle => by
    simp only [List.foldl_cons]
    have ht' := hl' t' List.mem_cons_self
    have ht := hl t List.mem_cons_self
    apply foldl_sf_le hrest
    · rw [sf_ot (isOT_add h1 ht')]; exact isOT_add h1 ht'
    · rw [sf_ot (isOT_add h2 ht)]; exact isOT_add h2 ht
    · exact fun u hu => hl' u (List.mem_cons_of_mem _ hu)
    · exact fun u hu => hl u (List.mem_cons_of_mem _ hu)
    · rw [sf_ot (isOT_add h1 ht'), sf_ot (isOT_add h2 ht)]
      exact le_trans (add_le_add_left acc' htt) (add_le_add_right t h2 ht hle)

/-- **The sum is monotone in each summand.** -/
theorem sumN_le2 {l' l : List T} (h : List.Forall₂ (· ≤ ·) l' l)
    (hl' : ∀ t ∈ l', isOT t = true) (hl : ∀ t ∈ l, isOT t = true) : sumN l' ≤ sumN l :=
  foldl_sf_le h z z rfl rfl hl' hl (le_refl _)

/-- **A smaller last summand gives a smaller sum.** -/
theorem sumN_snoc_lt {l' l : List T} {a' a : T} (hl' : ∀ t ∈ l', isOT t = true)
    (hl : ∀ t ∈ l, isOT t = true) (ha' : isOT a' = true) (ha : isOT a = true)
    (hle : sumN l' ≤ sumN l) (hlt : a' < a) : sumN (l' ++ [a']) < sumN (l ++ [a]) := by
  rw [sumN_snoc, sumN_snoc, sf_ot (isOT_add (isOT_sumN _ hl') ha'), sf_ot (isOT_add (isOT_sumN _ hl) ha)]
  exact lt_of_le_of_lt (add_le_add_right a' (isOT_sumN _ hl) ha' hle) (add_lt_add_left _ hlt)

/-- **A dropped last summand gives a smaller sum.** -/
theorem sumN_lt_snoc {l' l : List T} {a : T} (hl : ∀ t ∈ l, isOT t = true) (ha : isOT a = true) (hle : sumN l' ≤ sumN l) (hlt : z < a) :
    sumN l' < sumN (l ++ [a]) := by
  rw [sumN_snoc, sf_ot (isOT_add (isOT_sumN _ hl) ha)]
  have := add_lt_add_left (sumN l) hlt
  rw [add_z_right] at this
  exact lt_of_le_of_lt hle this

/-! ## 数える子の列についての補助 -/

theorem o_cl_eq {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) {i : Nat} (hi : i < N.length) :
    σ.o i = psi (σ.v i) (spArg (σ.v i) z (sumN ((CL N i).map σ.o))) z := by
  rw [o_spArg hC hG hi, cvals_eq_map hC hG i]

theorem arg_lt_of_cl {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) {i : Nat} (hi : i < N.length)
    (hne : CL N i ≠ []) : z < spArg (σ.v i) z (sumN ((CL N i).map σ.o)) := by
  obtain ⟨hs, hp⟩ := cl_vals hC hG hi
  apply lt_spArg
  · exact isOT_sumN _ (fun t ht => (hs t ht).1)
  · exact sumN_ne_z hs hp (by simpa using hne)

theorem no_cnt_of_cl_nil {N : Mat} {i : Nat} (h : CL N i = []) : ∀ c ∈ children N i, ¬ Counted N i c := by
  intro c hc hcnt
  have : c ∈ CL N i := by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
  rw [h] at this; simp at this

theorem cl_sorted (N : Mat) (i : Nat) : (CL N i).Pairwise (· < ·) :=
  (children_sorted N i).filter _

theorem PO.le {ρ ρ' : Valn} {i : Nat} (h : PO ρ ρ' i) : ρ'.o i ≤ ρ.o i := by
  rcases h.1 with h | ⟨h, _⟩
  · exact h.le
  · exact DRelO.le (Or.inr h)

theorem PV.le {M : Mat} {ρ ρ' : Valn} {i : Nat} (h : PV M ρ ρ' i) : ρ'.v i ≤ ρ.v i := by
  rcases h.1 with h | ⟨h, _⟩
  · exact h.le
  · exact le_of_lt h.1

theorem forall2_map_le {f g : Nat → T} : ∀ {l : List Nat}, (∀ d ∈ l, f d ≤ g d) →
    List.Forall₂ (· ≤ ·) (l.map f) (l.map g)
  | [], _ => .nil
  | d :: _, h => .cons (h d List.mem_cons_self) (forall2_map_le (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')))

/-- `ψ_{v′}(0) < ψ_v(X)` when `v′ ≤ v` and `X ≠ 0`. -/
theorem psi_z_lt_of_le {v' v X : T} (hv : v' ≤ v) (hX : z < X) : psi v' z z < psi v X z := by
  rcases (le_iff _ _).mp hv with h | h
  · exact psi_lt_psi_z_iff.mpr (Or.inl h)
  · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨h, hX⟩)

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

omit hRk' hUAB in
/-- **An argument `0` stays `0`** in `M.take x`. -/
theorem arg0_take {d : Nat} (hd : d < x) {s : T} (h : ρ.o d = psi s z z) : ∃ s', ρ'.o d = psi s' z z := by
  have hdM : d < M.length := by omega
  have hdT : d < (M.take x).length := by rw [List.length_take]; omega
  have hnil : CL M d = [] := by
    by_contra hne
    have hlt := arg_lt_of_cl (σ := ρ) hC hG hdM hne
    rw [o_cl_eq hC hG hdM] at h
    simp only [psi.injEq] at h
    rw [h.2.1] at hlt; exact lt_irrefl' _ hlt
  obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hd
  have hT : CL (M.take x) d = [] := by
    rw [hnil] at hTl; exact (List.append_eq_nil_iff.mp hTl.symm).1
  exact ⟨ρ'.v d, o_of_no_counted hC' hdT (hdrop d hd).2.2.1 (no_cnt_of_cl_nil hT)⟩

/-- **The `o` frame is strict**: `c` is the last counted child of `i` in `M`, and it drops strictly
when it stays in `M.take x`. -/
theorem o_strict_frame {i c : Nat} (hi : i < x) (hcCL : c ∈ CL M i) (hlast : ∀ d ∈ CL M i, d ≤ c)
    (hIH : c < x → ρ'.o c < ρ.o c) : ρ'.o i < ρ.o i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hi
  have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
  rcases List.eq_nil_or_concat (CL (M.take x) i) with hnil | ⟨Lc, cs, hcl⟩
  · rw [o_of_no_counted hC' hiT (hdrop i hi).2.2.1 (no_cnt_of_cl_nil hnil), o_cl_eq hC hG hiM]
    exact psi_z_lt_of_le (hdrop i hi).2.le (arg_lt_of_cl hC hG hiM (List.ne_nil_of_mem hcCL))
  rw [List.concat_eq_append] at hcl
  have hcsT : cs ∈ children (M.take x) i ∧ Counted (M.take x) i cs := by
    have : cs ∈ CL (M.take x) i := by rw [hcl]; simp
    unfold CL at this; rw [List.mem_filter] at this; exact ⟨this.1, by simpa using this.2⟩
  have hcsx : cs < x := by have := (mem_children hcsT.1).2; omega
  have hcsM : cs < M.length := by omega
  have hCv : ¬ ChgX M x false i := fun h =>
    ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB h).1 rfl hi).2.1 cs hcsT.1 hcsT.2
  have hv' : ρ'.v i = ρ.v i := (hoff i hi).2 hCv
  set a := ρ.v i with ha
  -- the earlier counted children do not change
  have hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d := by
    intro d hd
    have hdT : d ∈ CL (M.take x) i := by rw [hcl]; simp [hd]
    have hdc : d ∈ children (M.take x) i := by unfold CL at hdT; exact (List.mem_filter.mp hdT).1
    have hdcs : d < cs := by
      have hs := cl_sorted (M.take x) i
      rw [hcl] at hs
      exact (List.pairwise_append.mp hs).2.2 d hd cs (by simp)
    have hdx : d < x := by
      rw [children_take, List.mem_filter] at hdc; simpa using hdc.2
    by_contra hne
    have hCd : ChgX M x true d := by
      by_contra hn; exact hne ((hoff d hdx).1 hn)
    exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hdc hCd cs hcsT.1 hdcs hcsT.2
  have hclM : CL M i = Lc ++ [cs] ++ Tl := by rw [hTl, hcl]
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  rw [hclM] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  set Lv := Lc.map ρ.o with hLv
  set Tv := Tl.map ρ.o with hTv
  have hsL : ∀ t ∈ Lv, Single t := fun t ht => hsM t (by simp [ht])
  have hcsS : Single (ρ.o cs) := hsM _ (by simp)
  have hsTv : ∀ t ∈ Tv, Single t := fun t ht => hsM t (by simp [ht])
  have hp1 := List.pairwise_append.mp hpM
  have hpL : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp1.1).1
  have hLc : ∀ t ∈ Lv, ρ.o cs ≤ t := fun t ht =>
    (List.pairwise_append.mp hp1.1).2.2 t ht _ (by simp)
  have hsLc : ∀ t ∈ Lv ++ [ρ.o cs], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsL t h
    · simp at h; rw [h]; exact hcsS
  have hpLc : (Lv ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by simp at hb; rw [hb]; exact hLc t ht⟩
  -- `M.take x` side
  have hPOc := (hdrop cs hcsx).1
  have hPVc := (hdrop cs hcsx).2
  have hle' : ρ'.o cs ≤ ρ.o cs := hPOc.le
  have hmapT : (CL (M.take x) i).map ρ'.o = Lv ++ [ρ'.o cs] := by
    rw [hcl, List.map_append, List.map_singleton, hLv]
    congr 1; exact List.map_congr_left hsame
  have hsT : ∀ c ∈ CL (M.take x) i, Single (ρ'.o c) := by
    intro d hd
    have : ρ'.o d ∈ (CL (M.take x) i).map ρ'.o := List.mem_map_of_mem hd
    rw [hmapT] at this
    rcases List.mem_append.mp this with h | h
    · exact hsL _ h
    · simp at h; rw [h]; exact hPOc.2
  have hpT : ((CL (M.take x) i).map ρ'.o).Pairwise (fun a b => b ≤ a) := by
    rw [hmapT]
    exact List.pairwise_append.mpr ⟨hpL, by simp,
      fun t ht b hb => by simp at hb; rw [hb]; exact le_trans hle' (hLc t ht)⟩
  obtain ⟨s', y', hs'y'⟩ := hPOc.2.2
  obtain ⟨s, y, hsy⟩ := hcsS.2
  have hform := o_last_form hC' hiT (by rw [hv']; exact hvot) hcl hsT hpT hs'y'
  have hLm : Lc.map ρ'.o = Lv := List.map_congr_left hsame
  rw [hLm, hv'] at hform
  set B := spArg a z (sumN Lv) with hB
  have hLs := sumN_dec Lv hsL hpL
  -- the old side
  have hstate : spArg a z (sumN (Lv ++ [ρ.o cs])) = step a B s y z := by
    rw [sumN_append_dec hsLc hpLc, sumN_singleton hcsS, spArg_app, hsy, spArg_single]
  have hold : ρ.o i = psi a (spArg a (step a B s y z) (sumN Tv)) z := by
    rw [o_cl_eq hC hG hiM, hclM, ← ha]
    simp only [List.map_append, List.map_singleton]
    rw [← hLv, ← hTv, ← hstate, ← spArg_app,
      ← sumN_append_dec (fun t ht => hsM t (by simpa using ht)) (by simpa using hpM)]
  -- the step on the child
  have hstep : ρ'.o cs < ρ.o cs → step a B s' y' z < step a B s y z := by
    intro hlt
    have hc : isOT (psi s y z) = true := by rw [← hsy]; exact hcsS.1
    have hc' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hPOc.2.1
    apply step_lt hc hc'
    · rcases hPOc.1 with h | ⟨⟨w', w, X, hw', _, _⟩, _⟩
      · rcases h with h | h
        · exact absurd (h ▸ hlt) (lt_irrefl' _)
        · left; rw [← hsy, ← hs'y']; exact h
      · right
        rw [hs'y'] at hw'; simp only [psi.injEq] at hw'
        refine ⟨hw'.2.1, ?_⟩
        rw [← hsy, ← hs'y']; exact hlt
    · intro q hq
      apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN Lv) z hLs.1
      · rw [hLs.2]; intro q hq; rw [← hsy]; exact hLc q hq
      · simp [summands]
      · exact hq
    · obtain ⟨y0, hy0⟩ := o_psi_sub hC' (show cs < (M.take x).length by omega)
      rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
      rw [hy0.1, sf_ot hPVc.2.1]; exact hPVc.2.2.subSmall _
    · intro hy
      rw [hy] at hsy
      obtain ⟨s'', h''⟩ := arg0_take hx hR0 hZ2 hSD hZ1 hUAT hC hG hC' hdrop hcsx hsy
      rw [hs'y'] at h''; simp only [psi.injEq] at h''; exact h''.2.1
  have hle : step a B s' y' z ≤ step a B s y z := by
    rcases (le_iff _ _).mp hle' with h | h
    · exact le_of_lt (hstep h)
    · rw [hs'y', hsy] at h; simp only [psi.injEq] at h; rw [h.1, h.2.1]
  rw [hform, hold]
  apply psi_lt_psi_z_iff.mpr; right; refine ⟨rfl, ?_⟩
  by_cases hTl0 : Tl = []
  · -- `c = cs`
    have hTv0 : Tv = [] := by rw [hTv, hTl0]; rfl
    rw [hTv0, show sumN ([] : List T) = z from rfl, show spArg a (step a B s y z) z = step a B s y z from rfl]
    have hccs : c = cs := by
      have hc2 : c ∈ Lc ++ [cs] := by rw [hclM, hTl0, List.append_nil] at hcCL; exact hcCL
      rcases List.mem_append.mp hc2 with h | h
      · exfalso
        have hs := cl_sorted M i
        rw [hclM, hTl0, List.append_nil] at hs
        have h1 := (List.pairwise_append.mp hs).2.2 c h cs (by simp)
        have h2 := hlast cs (by rw [hclM]; simp)
        omega
      · simpa using h
    subst hccs
    exact hstep (hIH hcsx)
  · have hTvne : Tv ≠ [] := by rw [hTv]; simpa using hTl0
    apply lt_of_le_of_lt hle
    apply lt_spArg
    · exact isOT_sumN _ (fun t ht => (hsTv t ht).1)
    · exact sumN_ne_z hsTv hp1.2.1 hTvne

/-- **The `v` frame of a bump column is strict**: the last child `k` of the bump child `j` (the last
child of `i`) drops strictly or is `x`. -/
theorem v_strict_bump {i j k : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K : List Nat} (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k]) (hLx : ∀ d ∈ L, ∀ e ∈ children M d, e < x)
    (hIH : k < x → ρ'.o k < ρ.o k) : ρ'.v i < ρ.v i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  have hjM : j ∈ children M i := by rw [hch]; simp
  have hkM : k ∈ children M j := by rw [hchj]; simp
  have hij := (mem_children hjM).1
  have hjk := (mem_children hkM).1
  have hkl := (mem_children hkM).2
  have hjx : j < x := by omega
  -- the row-1 parent does not change
  have hV : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
    rw [par_take M 1 i hi]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      show ρ'.v m = ρ.v m
      have hm := par_lt M 1 i m hp
      apply (hoff m (by omega)).2
      intro hCm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  -- the children of `i` in `M.take x`
  have hLj : ∀ d ∈ L, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
  have hchT : children (M.take x) i = L ++ [j] := by
    rw [children_take, hch, List.filter_eq_self]
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · have := hLj d h; simp only [decide_eq_true_eq]; omega
    · simp at h; subst h; simp only [decide_eq_true_eq]; omega
  have hjT : j ∈ children (M.take x) i := by rw [hchT]; simp
  -- the earlier bump terms do not change
  have hbtL : ∀ d ∈ L, bumpTerm (M.take x) ρ' i d = bumpTerm M ρ i d := by
    intro d hd
    have hdx : d < x := by have := hLj d hd; omega
    have hdM : d ∈ children M i := by rw [hch]; simp [hd]
    unfold bumpTerm
    rw [col_take M hdx, bump_take M hi]
    split
    · have hchd : children (M.take x) d = children M d := by
        rw [children_take, List.filter_eq_self]
        intro e he; simp only [decide_eq_true_eq]; exact hLx d hd e he
      rw [hchd]
      congr 2
      apply List.map_congr_left
      intro e he
      have hex := hLx d hd e he
      apply (hoff e hex).1
      intro hCe
      exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hdM hjT (hLj d hd) hCe
        (Anc0.step (mem_children_iff.mp he).2 (Anc0.refl d))
    · rfl
  -- the values
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  have hKk : ∀ d ∈ K, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
  have hKx : ∀ d ∈ K, d < x := fun d hd => by have := hKk d hd; omega
  have hKot : ∀ t ∈ K.map ρ.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o d (by have := hKx d hd; omega)
  have hKot' : ∀ t ∈ K.map ρ'.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact (hdrop d (hKx d hd)).1.2.1
  have hKle : sumN (K.map ρ'.o) ≤ sumN (K.map ρ.o) := by
    exact sumN_le2 (forall2_map_le (fun d hd => (hdrop d (hKx d hd)).1.le)) hKot' hKot
  have hkot : isOT (ρ.o k) = true := hG.ot_o k hkl
  have hGot : isOT G = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hKot t h
    · simp at h; rw [h]; exact hkot)
  -- `G′ < G`
  obtain ⟨G', hG'ot, hG'lt, hbtj⟩ : ∃ G', isOT G' = true ∧ G' < G ∧
      bumpTerm (M.take x) ρ' i j = omega G' := by
    have hbt : bumpTerm (M.take x) ρ' i j = omega (sumN ((children (M.take x) j).map ρ'.o)) := by
      unfold bumpTerm; rw [col_take M hjx, bump_take M hi, if_pos hjb]
    rw [hbt]
    by_cases hkx : k < x
    · have hchjT : children (M.take x) j = K ++ [k] := by
        rw [children_take, hchj, List.filter_eq_self]
        intro d hd
        rcases List.mem_append.mp hd with h | h
        · simp only [decide_eq_true_eq]; exact hKx d h
        · simp at h; subst h; simp only [decide_eq_true_eq]; exact hkx
      have hk' : isOT (ρ'.o k) = true := (hdrop k hkx).1.2.1
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hchjT, List.map_append, List.map_singleton]
        exact isOT_sumN _ (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hKot' t h
          · simp at h; rw [h]; exact hk')
      · rw [hchjT, List.map_append, List.map_singleton]
        exact sumN_snoc_lt hKot' hKot hk' hkot hKle (hIH hkx)
    · have hkx' : k = x := by omega
      have hchjT : children (M.take x) j = K := by
        rw [children_take, hchj, List.filter_append, List.filter_eq_self.mpr
          (fun d hd => by simp only [decide_eq_true_eq]; exact hKx d hd)]
        simp [hkx']
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hchjT]; exact isOT_sumN _ hKot'
      · rw [hchjT]
        exact sumN_lt_snoc hKot hkot hKle (by
          obtain ⟨s0, y0, h0⟩ := o_psi_form hC hkl; rw [h0]; exact T.z_lt_psi _ _ _)
  -- assemble
  set Pl := one :: L.map (bumpTerm M ρ i) with hPl
  have hPlot : ∀ t ∈ Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hbtjM : bumpTerm M ρ i j = omega G := by
    unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
  have hvM : ρ.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [omega G])))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hch, List.map_append, List.map_singleton, hbtjM, ← List.cons_append]
  have hvT : ρ'.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [omega G'])))) := by
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_neg h2, hV, hchT, List.map_append,
      List.map_singleton, hbtj, List.map_congr_left hbtL, ← List.cons_append]
  have hP'ot : isOT (sumN (Pl ++ [omega G'])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot)
  have hPot : isOT (sumN (Pl ++ [omega G])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hGot)
  have hP : sumN (Pl ++ [omega G']) < sumN (Pl ++ [omega G]) :=
    sumN_snoc_lt hPlot hPlot (isOT_omega hG'ot) (isOT_omega hGot) (le_refl _)
      (omega_lt_omega hG'ot hGot hG'lt)
  rw [hvM, hvT, sf_ot (isOT_add hVot (isOT_omega hP'ot)), sf_ot (isOT_add hVot (isOT_omega hPot))]
  exact add_lt_add_left _ (omega_lt_omega hP'ot hPot hP)

/-- **Every call of `D` drops strictly** in `M.take x` (`t = 1`: `x` has row 2 zero and `v(x) ∉ D`). -/
theorem dep_strict {q : Nat} {ζ μ : T} (hx2 : entry M 2 x = 0) (hq : par M 0 x = some q)
    (hnx : ¬ DepX M x false x) (hVL : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i) :
    ∀ b i, DepX M x b i → i < x → valB ρ' b i < valB ρ b i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  intro b i hD
  induction hD with
  | leaf => intro h; exact absurd h (lt_irrefl _)
  | @ochild i c hc hcb hcu hdc ih =>
    intro hi
    show ρ'.o i < ρ.o i
    rcases hOS_t1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq i hi (DepX.ochild hc hcb hcu hdc) with
      ⟨_, hnc⟩ | ⟨_, L, c0, R, hch, _, _, hR, hLnd⟩
    · exfalso
      rcases hnc c hc with h | h
      · exact hcb h
      · exact hcu h
    · have hcnt : Counted M i c := ⟨hcb, hcu⟩
      have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
        rcases hR d h with h' | h'
        · exact hd.1 h'
        · exact hd.2 h'
      have hcCL : c ∈ CL M i := by
        unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
      obtain ⟨hL, hRo⟩ := sib_order (children_sorted M i) hch
      have hcc0 : c = c0 := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h hcnt)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · exact absurd hcnt (hcR c h)
      subst hcc0
      apply o_strict_frame hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi hcCL
      · intro d hd
        have hdc : d ∈ children M i := (List.mem_filter.mp hd).1
        have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hd).2
        rw [hch] at hdc
        rcases List.mem_append.mp hdc with h | h
        · exact le_of_lt (hL d h)
        · rcases List.mem_cons.mp h with h | h
          · rw [h]
          · exact absurd hdcnt (hcR d h)
      · exact ih
  | @ov i hv ih =>
    intro hi
    show ρ'.o i < ρ.o i
    have hiT : i < (M.take x).length := by omega
    have hiM : i < M.length := by omega
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hv)).1 rfl hi
    have hvlt : ρ'.v i < ρ.v i := ih hi
    rw [o_of_no_counted hC' hiT (hdrop i hi).2.2.1 hT.2.1, o_cl_eq hC hG hiM]
    exact psi_lt_psi_z_iff.mpr (Or.inl hvlt)
  | @vpar i m h1 hp hdm _ =>
    intro hi
    exfalso
    have hm := par_lt M 1 i m hp
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i hi hp
  | @vupg i k h1 h2 hu hdk ih =>
    intro hi
    show ρ'.v i < ρ.v i
    have hiM : i < M.length := by omega
    have hiT : i < (M.take x).length := by omega
    have hkl := upg_lt hiM hu
    have hkx : k < x := by
      rcases Nat.lt_or_ge k x with h | h
      · exact h
      · exfalso
        have : k = x := by omega
        subst this; exact hnx hdk
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl hkx
    obtain ⟨m, hm1, _, _, hcase⟩ := upg_spec hu
    have hik : k = i + 1 := by
      rcases hcase with h | ⟨hA, hki⟩
      · exact h
      · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT hkx hu hA hki).elim
    have hi1 : i + 1 < x := by omega
    have hmi := par_lt M 1 i m hm1
    have huT : upg (M.take x) i = some k := by rw [upg_take M hi1]; exact hu
    have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
      rw [hm1]; exact hG.ot_v m (by omega)
    have ek : ρ.v i = ρ.v k :=
      v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
    have ek' : ρ'.v i = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hi]; exact h1)
      (by rw [entry_take M 2 hi]; exact h2) huT
      (by rw [par_take M 1 i hi, hm1]; exact (hdrop m (by omega)).2.2.1)
      (fun _ _ _ k' hk' => (hdrop k' (by have := (mem_children hk').2; omega)).1.2.1)
    rw [ek, ek']
    exact ih hkx
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hi
    show ρ'.v i < ρ.v i
    obtain ⟨_, _, hcase⟩ := hVL i hi (DepX.vbump h1 h2 hj hjb hk hdk)
    rcases hcase with ⟨_, h2', _⟩ | ⟨L, K, j', k', _, hch, _, hchj, hKnd, hLnd, _⟩
    · exact absurd h2' h2
    · have hjj : j = j' := by
        rw [hch] at hj
        rcases List.mem_append.mp hj with h | h
        · exact absurd hdk (hLnd j h k hk).2
        · exact List.mem_singleton.mp h
      subst hjj
      have hkk : k = k' := by
        rw [hchj] at hk
        rcases List.mem_append.mp hk with h | h
        · exact absurd hdk (hKnd k h)
        · exact List.mem_singleton.mp h
      subst hkk
      exact v_strict_bump hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi h1 h2 hch hjb hchj
        (fun d hd e he => (hLnd d hd e he).1) ih

end

/-! ## まとめ: o(r) は実際に変わる、hne を外した t1_main_val -/

/-- **`o(r)` drops strictly** (`t = 1`, `q ≠ r`), from the drop lemma's conclusion. -/
theorem o_r_strict {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M)
    (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hqr : par M 0 x ≠ some r)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat} {ζ μ : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
    (hVL : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i) :
    ρ'.o r < ρ.o r := by
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  have hr : r < x := par_lt M 1 x r h1
  have hrx : r ≠ x := by omega
  have hpath := hpath_of_par1 h1 hA hrx
  obtain ⟨q, hq⟩ := par0_of_anc hA hrx
  have hnx : ¬ DepX M x false x := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact v_r_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hA hrx hqr hpath (depX_chgX hdm)
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  exact dep_strict hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hx2 hq hnx hVL true r
    (dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hA) hr

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**, without the hypothesis `hne` (`o(r)` changes). -/
theorem t1_main_strict {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbs M ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : BumpVSmallTake M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbs M ρ)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true)
    (hLo : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2 (gamS μ br ((drop1 M (r + L) rkM).o r) m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) (psi (succ s) z z)).2 = z))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hKD hTD hAbs hWS hVSt)
    (fun i k W _ hu hv hW => hUA i k W hu hv hW)
  have hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r :=
    ne_of_lt (o_r_strict (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE h1 hx2 hqr hC hG hC1 hRk1
      hdrop (hV 0))
  exact t1_main_val hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA hne hμr hro hV hW hLo hsM hpM

end Ytosk
