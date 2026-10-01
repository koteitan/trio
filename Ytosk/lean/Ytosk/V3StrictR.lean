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

end

end Ytosk
