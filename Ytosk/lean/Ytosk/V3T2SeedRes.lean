/-
**t = 2 の種の残りの欄を外す（2026-10-16、t2）。**

- qr（q = r、x への上げなし）: x は最後の列で行 2 が 1、P_1(x) = r なので v(x) = v(r) + ω（`v_x_qr`）。
  よって `T2SeedQRRes.ks`（v(r) + k < v(x)）と `vs`（v(r) + 1 ◁ v(x)）は証明できる（`app_natT_lt_add_w`・
  `lhd_succ_add_w`）。残りは `T2SeedQRResR`（w1・dom）。
-/
import Ytosk.V3T2SeedQRL
import Ytosk.V3T2SeedQNV
import Ytosk.V3T2SeedSV
import Ytosk.V3Tame
import Ytosk.V3PSeedAllG
import Ytosk.V3T2SeedWire
import Ytosk.V3InvW

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem eq_z_of_lt_one : ∀ {b : T}, lt b one = true → b = z
  | z, _ => rfl
  | psi a' b' c', h => by
    unfold one at h
    cases a' <;> cases b' <;> simp [lt] at h

/-- `V + k < V + ω` (no standard form needed). -/
theorem app_natT_lt_add_w : ∀ (V : T) (k : Nat), app V (natT k) < add V (psi z one z)
  | z, 0 => by show lt z (psi z one z) = true; rfl
  | z, k + 1 => by show lt (psi z z (natT k)) (psi z one z) = true; rfl
  | psi a b c, k => by
    show lt (app (psi a b c) (natT k)) (add (psi a b c) (psi z one z)) = true
    by_cases h : lt (psi a b z) (psi z one z) = true
    · have hab : a = z ∧ b = z := by
        cases a with
        | psi _ _ _ => simp [lt] at h
        | z =>
          refine ⟨rfl, ?_⟩
          simp [lt] at h
          exact eq_z_of_lt_one h.2
      obtain ⟨rfl, rfl⟩ := hab
      simp only [app, add, h, if_true]
      rfl
    · simp only [app, add, h]
      simp only [Bool.false_eq_true, if_false]
      have ih := app_natT_lt_add_w c k
      show lt (psi a b (app c (natT k))) (psi a b (add c (psi z one z))) = true
      simp only [lt, if_true]
      exact ih

/-- `V + 1 ◁ V + ω`. -/
theorem lhd_succ_add_w : ∀ (V : T), isOT V = true → Lhd z (succ V) (add V (psi z one z))
  | z, _ => lhd_one (by show lt one (psi z one z) = true; rfl)
  | psi a b c, hV => by
    by_cases h : lt (psi a b z) (psi z one z) = true
    · have hlt := app_natT_lt_add_w (psi a b c) 1
      have hw : add (psi a b c) (psi z one z) = psi z one z := by simp only [add, h, if_true]
      rw [hw] at hlt ⊢
      refine lhd_lt_small (isOT_succ hV) ?_ hlt
      rw [lt_E0_iff]; exact ⟨rfl, by show lt one (Om one) = true; rfl⟩
    · have hw : add (psi a b c) (psi z one z) = psi a b (add c (psi z one z)) := by
        simp only [add, h]; simp
      rw [hw]
      have ih := lhd_succ_add_w c (isOT_rest hV)
      have := lhd_app (psi a b z) ih
      simpa [app, succ] using this

/-- The `v` of the last column at `t = 2`, `q = r`: `v(x) = v(r) + ω`. -/
theorem v_x_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) :
    ρ.v (r + L) = add (ρ.v r) (psi z one z) := by
  have hxM : r + L < M.length := by omega
  have he2x : entry M 2 (r + L) = 1 := by
    obtain ⟨_, _, _, he2, _, _⟩ := (par2_iff M hxM).mp hr
    have h' : entry M 2 r < entry M 2 (r + L) := he2
    have := I.z2 (r + L); omega
  have h1x : entry M 1 (r + L) ≠ 0 := by
    have := (par2_facts I.z2 hxM hr).2; omega
  have hp1 := par1_of_par2 I.z2 I.z1 hxM hr
  have hch : children M (r + L) = [] := children_last (by omega)
  have hv := (I.cons (r + L) hxM).2
  have hrhs : vRhs M ρ (r + L) = sf (add (ρ.v r) (psi z one z)) := by
    unfold vRhs
    rw [if_neg h1x, if_neg (by omega), hp1, hch]
    rfl
  rw [hrhs] at hv
  have hot := I.good.ot_v (r + L) hxM
  rw [hv] at hot ⊢
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  exact sf_ot (isOT_add hVot (by rfl))

/-- **The remaining fields of `T2SeedQRRes`** (`ks`・`vs` are proved). -/
structure T2SeedQRResR (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop where
  w1 : ∀ τ, Cons (M.take (r + L)) τ → ¬ t2B (ρ.v r) ρ Lc < t2W1 (M.take (r + L)) (ρ.v r) τ r
  dom : ∀ τ, Cons (M.take (r + L)) τ → ∀ k u, ¬ lt (ρ.v r) u = true →
    ∀ g ∈ comps u (app (t2B (ρ.v r) ρ Lc)
      (psi (addN (ρ.v r) (k + 1)) (shN (ρ.v r) k (t2W1 (M.take (r + L)) (ρ.v r) τ r)) z)),
      g ≤ app (t2B (ρ.v r) ρ Lc)
        (psi (addN (ρ.v r) (k + 1)) (shN (ρ.v r) k (t2W1 (M.take (r + L)) (ρ.v r) τ r)) z) ∨
      ∃ d ∈ comps u (t2B (ρ.v r) ρ Lc) ++ comps u (ρ.v r) ++ comps u (succ (ρ.v r)), g ≤ d

/-- **`T2SeedQRRes` from its two remaining fields.** -/
theorem t2SeedQRRes_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) {Lc : List Nat}
    (h : T2SeedQRResR M ρ r L Lc) : T2SeedQRRes M ρ r L Lc := by
  have hvx := v_x_qr I hlen hr
  refine ⟨fun k => ?_, Or.inr ?_, h.w1, h.dom⟩
  · rw [hvx]; exact app_natT_lt_add_w _ k
  · rw [hvx]; exact lhd_succ_add_w _ (I.good.ot_v r (by omega))

/-! ## qn: `s′ < v(q)` -/

/-- **`T2SeedQNRes.vqlt`**: `s′ = V + ω^S < V + ω^{S+1} = v_M(q)` (`x` is the last bump child of `q`, and it has
no children, so its bump term is `1`). -/
theorem qn_vqlt {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) : qnS M ρ r L q < ρ.v q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have h1lt := (par2_facts I.z2 (show r + L < M.length by omega) hr).2
  have hp1q : par M 1 q = some r := par1_of_child hpq (by omega)
  have hsplit := split_last_max _ _ (children_sorted M q) hxq
    (fun d hd => by have := (mem_children hd).2; omega)
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLqd
  have hbx : bumpTerm M ρ q (r + L) = one := by
    unfold bumpTerm; rw [if_pos Txb, children_last (by omega)]; rfl
  have hqM : q < M.length := by omega
  have hv := (I.cons q hqM).2
  unfold vRhs at hv
  rw [if_neg (by omega), if_neg (by omega), hp1q, hsplit, List.map_append, List.map_singleton, hbx] at hv
  change ρ.v q = sf (add (ρ.v r) (omega (sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [one]))))) at hv
  set S := sumN (one :: Lq.map (bumpTerm M ρ q)) with hSdef
  have hOT : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  have hSot : isOT S = true := isOT_sumN _ hOT
  have hS1 : sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [one])) = sf (add S one) := by
    simp only [hSdef, sumN, List.foldl_cons, List.foldl_append, List.foldl_nil]
  rw [hS1] at hv
  have hA1 : isOT (add S one) = true := isOT_add hSot rfl
  rw [sf_ot hA1] at hv
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hW : isOT (add (ρ.v r) (omega (add S one))) = true := isOT_add hVot (isOT_omega hA1)
  rw [sf_ot hW] at hv
  rw [hv]
  show add (ρ.v r) (omega S) < add (ρ.v r) (omega (add S one))
  apply add_lt_add_left
  apply omega_lt_omega hSot hA1
  have := add_lt_add_left S (show z < one from rfl)
  rwa [add_z_right] at this

/-- **`T2SeedQNRes.Bc`**: the summands of the state `B` before `q` are at least `Ω_{s′+1}` (they are at least
`o(q) = ψ_{v(q)}(…)` and `s′ < v(q)`). -/
theorem qn_Bc {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q]) :
    ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), ¬ g < psi (succ (qnS M ρ r L q)) z z := by
  have hrM : r < M.length := by have := par_lt M 2 _ _ hr; omega
  have hqM : q < M.length := by have := par_lt M 0 _ _ hq; omega
  have hlt := qn_vqlt hM hS I hlen hr hq hqr
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hLs : ∀ t ∈ Lc.map ρ.o, Single t := fun t ht => hsM t (List.mem_append_left _ ht)
  obtain ⟨yq, hyq⟩ := o_psi_sub I.cons hqM
  rw [sf_ot (I.good.ot_v q hqM)] at hyq
  have hcq : psi (succ (qnS M ρ r L q)) z z ≤ ρ.o q := by
    rw [hyq]
    rcases (le_iff _ _).mp (succ_le_of_lt hlt) with h | h
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
    · rw [h]; exact psi_le_psi_arg (z_le _)
  have hge : ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), psi (succ (qnS M ρ r L q)) z z ≤ g := by
    apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z (isOT_sumN _ (fun t ht => (hLs t ht).1))
    · intro g hg
      have hgL := summands_sumN_sub hLs g hg
      exact le_trans hcq ((List.pairwise_append.mp hpM).2.2 g hgL _ (by simp))
    · simp [summands]
  intro g hg hlt'
  exact lt_irrefl' _ (lt_of_le_of_lt (hge g hg) hlt')

/-! ## sv: the last counted child of `r` in `M.take x` -/

/-- A row-2-one child `d` with `P_1 = r` has `v(d) = v(r) + ω^W > v(r) + 1`. -/
theorem v_child_gt {N : Mat} {τ : Valn} (hC : Cons N τ) (hG : Good3 N τ) {r d : Nat}
    (hrN : r < N.length) (hdN : d < N.length) (hp1 : par N 1 d = some r) (he1 : entry N 1 d ≠ 0)
    (he2 : entry N 2 d = 1) : succ (τ.v r) < τ.v d := by
  have hV : isOT (τ.v r) = true := hG.ot_v r hrN
  have hWot : isOT (sumN (one :: (children N d).map (bumpTerm N τ d))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG d j
  have hvd : τ.v d = add (τ.v r) (omega (sumN (one :: (children N d).map (bumpTerm N τ d)))) := by
    rw [(hC d hdN).2]; unfold vRhs; rw [if_neg he1, if_neg (by omega), hp1]
    exact sf_ot (isOT_add hV (isOT_omega hWot))
  obtain ⟨s', y', hsy⟩ := omega_psi_form (sumN (one :: (children N d).map (bumpTerm N τ d)))
  rw [hvd, ← t_add_succ hV (omega_psi_form _) (bumpOmega_ne_one hC hG d), hsy]
  exact lt_add_principal s' y' _

/-- `Good3` of `M.take x` for every consistent valuation, from the drop residual. -/
theorem good3_take_any {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hl : 1 ≤ M.length) {τ : Valn} (hτ : Cons (M.take (M.length - 1)) τ) : Good3 (M.take (M.length - 1)) τ := by
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  exact good3_congr hG1 (agree_of_cons hC1 hτ hRk1)

/-- **The children of `r` in `M.take x`** (sv): `Good3`, `v(r)` is unchanged, and every child has `v > V + 1`. -/
theorem sv_children_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    Good3 (M.take (r + L)) τ ∧ τ.v r = ρ.v r ∧
      ∀ d ∈ children (M.take (r + L)) r, succ (ρ.v r) < τ.v d := by
  obtain ⟨hX, _⟩ := sInvXJ_std hM hS
  have hxM : r + L < M.length := by omega
  have hrx : r < r + L := par_lt M 0 _ _ hq
  obtain ⟨he2r, he1x⟩ := par2_facts I.z2 hxM hr
  have he2x : entry M 2 (r + L) = 1 := by
    obtain ⟨_, _, _, he2, _, _⟩ := (par2_iff M hxM).mp hr
    have h' : entry M 2 r < entry M 2 (r + L) := he2
    have := I.z2 (r + L); omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [show M.length - 1 = r + L by omega]; exact hτ
  have hG := good3_take_any I R (by omega) hτ'
  rw [show M.length - 1 = r + L by omega] at hG
  have hvr : τ.v r = ρ.v r :=
    v_take_of_untopped I (by omega) hrx (topP_sv hlen I.z2 I.z1 hr hq hux) hτ
  refine ⟨hG, hvr, fun c0 hc0 => ?_⟩
  have hc0x : c0 < r + L := by have := (mem_children hc0).2; rw [List.length_take] at this; omega
  have hpc : par M 0 c0 = some r := by
    have := (mem_children_iff.mp hc0).2; rwa [par_take M 0 c0 hc0x] at this
  have hcM : c0 ∈ children M r := mem_children_iff.mpr ⟨by omega, hpc⟩
  have hcol := t_child_col hX hq hxM he2x he1x hcM (le_of_lt hc0x)
  have hcx := t_col_x hX hq hxM he2x he1x
  have h1 : entry M 1 c0 = entry M 1 r + 1 := by
    have : entry M 1 c0 = (col M c0).2.1 := rfl; rw [this, hcol, hcx]
  have h2 : entry M 2 c0 = 1 := by
    have : entry M 2 c0 = (col M c0).2.2 := rfl; rw [this, hcol, hcx]
  have hp1 : par (M.take (r + L)) 1 c0 = some r := by
    rw [par_take M 1 c0 hc0x]; exact par1_of_child hpc (by omega)
  have hlt := v_child_gt hτ hG (by rw [List.length_take]; omega) (by rw [List.length_take]; omega) hp1
    (by rw [entry_take M 1 hc0x]; omega) (by rw [entry_take M 2 hc0x]; exact h2)
  rwa [hvr] at hlt

/-- **`T2SeedSVRes.decP`**: in `M.take x` the last counted child `c0` of `r` has subscript above `V + 1`. -/
theorem sv_decP {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L)) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
      ∃ s y, τ.o c0 = psi s y z ∧ succ (ρ.v r) < s := by
  intro τ hτ Lc c0 hCL
  obtain ⟨hG, _, hch⟩ := sv_children_ctx hM hS I R hlen hr hq hux hτ
  have hc0 : c0 ∈ children (M.take (r + L)) r := cl_mem_children (by rw [hCL]; simp)
  have hcT := (mem_children hc0).2
  obtain ⟨y, hy⟩ := o_psi_sub hτ hcT
  rw [sf_ot (hG.ot_v c0 hcT)] at hy
  exact ⟨_, y, hy, hch c0 hc0⟩

/-! ## 残りを減らした形と接続 -/

/-- **The remaining fields of `T2SeedQNRes`** (`vqlt`・`Bc` are proved). -/
structure T2SeedQNResR (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  σB : sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc
  base : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
      ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q) ∧
      (1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
        (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q)))

theorem t2SeedQNRes_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (h : T2SeedQNResR M ρ r L q Lc) : T2SeedQNRes M ρ r L q Lc :=
  ⟨qn_vqlt hM hS I hlen hr hq hqr, h.σB, qn_Bc hM hS I hlen hr hq hqr hCL, h.base⟩

/-- **The remaining fields of `T2SeedSVRes`** (`decP` is proved). -/
structure T2SeedSVResR (M : Mat) (ρ : Valn) (r L : Nat) : Prop where
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (succ (ρ.v r))
      (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)) z =
    sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)
  lhd : ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
    Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)

theorem t2SeedSVRes_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) {r L : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (h : T2SeedSVResR M ρ r L) : T2SeedSVRes M ρ r L :=
  ⟨sv_decP hM hS I R hlen hr hq hux, h.rw, h.lhd⟩

/-- **`T2SeedPRes` with the reduced residuals** (the C case unchanged). -/
structure T2SeedPResR (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SeedSVResR M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNResR M ρ r L q Lc
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCRes M ρ r L q ∧ G.T2SeedCBig M ρ r L q

theorem t2SeedPRes_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (h : T2SeedPResR M ρ) : G.T2SeedPRes M ρ where
  qr := fun r L hlen hr hq hXu Lc hCL => t2SeedQRRes_of I hlen hr (h.qr r L hlen hr hq hXu Lc hCL)
  sv := fun r L hlen hr hq hux => t2SeedSVRes_of hM hS I R hlen hr hq hux (h.sv r L hlen hr hq hux)
  qn := fun r L q hlen hr hq hqr Lc hCL =>
    t2SeedQNRes_of hM hS I hlen hr hq hqr hCL (h.qn r L q hlen hr hq hqr Lc hCL)
  C := h.C

/-- The reduced residual of `T2SeedQRAll`. -/
def T2SeedQRAllR : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2QRNoUpg M r L → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc

theorem t2SeedQRAll_of (h : T2SeedQRAllR) : T2SeedQRAll :=
  fun M ρ rk hM hS I R hz h2 r L hlen hr hN Lc hCL =>
    t2SeedQRRes_of I hlen hr (h M ρ rk hM hS I R hz h2 r L hlen hr hN Lc hCL)

/-- The reduced residual of `T2SeedQNAll`. -/
def T2SeedQNAllR : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      ∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNResR M ρ r L q Lc

theorem t2SeedQNAll_of (h : T2SeedQNAllR) : T2SeedQNAll :=
  fun M ρ rk hM hS I R hz h2 r L hlen hr q Lc hq hqr hCL =>
    t2SeedQNRes_of hM hS I hlen hr hq hqr hCL (h M ρ rk hM hS I R hz h2 r L hlen hr q Lc hq hqr hCL)

/-- The reduced residual of `T2SeedSVAll`. -/
def T2SeedSVAllR : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2SVCase M r L → T2SeedSVResR M ρ r L

theorem t2SeedSVAll_of (h : T2SeedSVAllR) : T2SeedSVAll :=
  fun M ρ rk hM hS I R hz h2 r L hlen hr hsv =>
    t2SeedSVRes_of hM hS I R hlen hr hsv.1 hsv.2 (h M ρ rk hM hS I R hz h2 r L hlen hr hsv)

end Ytosk
