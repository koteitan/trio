/-
**3 行・t = 2・qn: M.take x での r の引数（Lc 一般）。**

`qn_take_t1`（V3QNFC、`CL_M(r) = [q]`）を `CL_M(r) = Lc ++ [q]` に広げる。M.take x でも q は r の数える子
（M で q は topped なので上げの的でない。`isUpg_take_eq`）なので `CL_T(r) = Lc ++ [q]`。`frame_take` で Lc の o と
v(r) は変わらない。o_T(q) = Ω_{v_T(q)}、o_T(q) ≤ o_M(q)（落とす補題）と `leaf_M_side`（B の加数は Ω_{v_M(q)} 以上）から
r の引数は B ++ Ω_{t1}（t1 = v_T(q) = V + ω^{W_T}）。
-/
import Ytosk.V3QNFC
import Ytosk.V3T2SeedQNV
import Ytosk.V3T2T
import Ytosk.V3T2SeedSVCl
import Ytosk.V3T2SeedQNK

namespace Ytosk

open T

set_option linter.unusedSectionVars false

open Classical in
/-- **`t1` in `M.take x`** (qn, `CL_M(r) = Lc ++ [q]`, any `Lc`): the argument of `r` in `M.take x` is
`B + Ω_{t1}` with `t1 = v_T(q) = V + ω^{W_T}` and `ω^{W_T} ≤ ω^W`. -/
theorem qn_take_t1L {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    ∃ ωT, spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) =
        app (t2B (ρ.v r) ρ Lc) (psi (add (ρ.v r) ωT) z z) ∧ τ.v q = add (ρ.v r) ωT ∧
      isOT ωT = true ∧ (∃ a b, ωT = psi a b z) ∧
      ωT ≤ omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))) ∧
      ρ.v q = add (ρ.v r)
        (omega (succ (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, _, TCLq, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb Tqb TCLq
  have hqb : ∀ a, par M 0 q = some a → col M q ≠ bump M a := by
    intro a ha; rw [hpq] at ha; cases ha; exact Tqb
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he0lt := anc0_e0_lt hA (by omega)
  have hpar1q : par M 1 q = some r :=
    par1_q (n := 2) (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r)
      hlen hL0 hA hq (by omega) (le_refl 2) (by omega) he2r h1lt hqb hr1 hqr Txb
  -- the drop
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := R.hdrop
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  have hpre : ∀ i, i < M.length - 1 → ∃ Tl, CL M i = CL (M.take (M.length - 1)) i ++ Tl :=
    fun i hi => cl_prefix hx1 I.r0p I.z2 I.sd I.z1 I.uat hi
  have hfr := fun i (hi : i < M.length - 1) (h : CL (M.take (M.length - 1)) i = Lc ++ q :: []) =>
    frame_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hi h
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hdrop hG1 hpre hfr
  set ρ' := rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk) with hρ'
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hag := agree_of_cons hτ hC1 hRk1
  -- `CL_T(q) = []`
  obtain ⟨Tl, hTl⟩ := hpre q hqx
  rw [TCLq] at hTl
  have hCLTq : CL (M.take (r + L)) q = [] := (List.append_eq_nil_iff.mp hTl.symm).1
  -- `q` is counted in `M.take x` too: it is topped in `M`, so not upgraded
  have hcqM : children M q = (children M q).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have htopM : topped M q = true := by
    unfold topped; rw [hcqM, List.getLast?_append]; simp [Txb]
  have hcntM : Counted M r q := by
    unfold CL at hqcl; simpa using (List.mem_filter.mp hqcl).2
  have hupM : isUpg M q = false := by
    cases h : isUpg M q
    · rfl
    · exact absurd ⟨h, htopM⟩ hcntM.2
  have hux : upg M (r + L - 1) ≠ some q := by
    intro hu
    have h' : isUpg M q = true := by
      unfold isUpg; rw [List.any_eq_true]
      exact ⟨r + L - 1, List.mem_range.mpr (by omega), by simp [hu]⟩
    rw [hupM] at h'; cases h'
  have hupT : isUpg (M.take (r + L)) q = false := by
    rw [isUpg_take_eq hlen hux hqx]; exact hupM
  have hcntT : Counted (M.take (r + L)) r q := by
    refine ⟨?_, fun h => by rw [hupT] at h; cases h.1⟩
    rw [col_take M hqx, bump_take M (show r < r + L by omega)]; exact hcntM.1
  have hqclT : q ∈ CL (M.take (r + L)) r := by
    unfold CL
    refine List.mem_filter.mpr ⟨?_, by simpa using hcntT⟩
    rw [children_take]; exact List.mem_filter.mpr ⟨cl_mem_children hqcl, by simpa using hqx⟩
  -- `CL_T(r) = Lc ++ [q]`
  obtain ⟨Tl', hTl'⟩ := hpre r (by omega)
  rw [hCLM] at hTl'
  have hnd : (Lc ++ [q]).Nodup := by
    rw [← hCLM]; unfold CL children; exact (List.nodup_range.filter _).filter _
  have hCLTr : CL (M.take (r + L)) r = Lc ++ [q] := by
    rcases List.eq_nil_or_concat Tl' with h | ⟨T0, a, h⟩
    · rw [h, List.append_nil] at hTl'; exact hTl'.symm
    · exfalso
      rw [h, List.concat_eq_append, ← List.append_assoc] at hTl'
      obtain ⟨hLc, -⟩ := List.append_inj' hTl' rfl
      have hqLc : q ∈ Lc := by rw [hLc]; exact List.mem_append_left _ hqclT
      rw [List.nodup_append] at hnd
      exact absurd rfl (hnd.2.2 q hqLc q (by simp))
  obtain ⟨hvr, hLo, -⟩ := hfr r (by omega) hCLTr
  have hqT : q < (M.take (r + L)).length := by omega
  have hoq : ρ'.o q = psi (ρ'.v q) z z := by
    rw [o_cl_eq hC1 hG1 hqT, hCLTq]; rfl
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLq
  have hbT : ∀ j ∈ Lq, bumpTerm (M.take (r + L)) ρ' q j ≤ bumpTerm M ρ q j := by
    intro j hjL
    have hjq : j ∈ children M q := (List.mem_filter.mp hjL).1
    have hjx : j < r + L := by simpa using (List.mem_filter.mp hjL).2
    have hpj : par M 0 j = some q := (mem_children_iff.mp hjq).2
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hqx]
    split
    · have hch : children (M.take (r + L)) j = children M j := by
        rw [children_take, List.filter_eq_self]
        intro c hc
        simpa using kid_lt_x hpj hq hjx (mem_children_iff.mp hc).2
      rw [hch]
      have hcx : ∀ c ∈ children M j, c < r + L := fun c hc => kid_lt_x hpj hq hjx (mem_children_iff.mp hc).2
      apply omega_le_omega
      · exact isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hG1.ot_o c (by have := hcx c hc; omega))
      · exact isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact I.good.ot_o c (mem_children hc).2)
      · apply sumN_le2 (forall₂_map_le _ (fun c hc => po_le (hdrop c (hcx c hc)).1))
        · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hG1.ot_o c (by have := hcx c hc; omega)
        · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact I.good.ot_o c (mem_children hc).2
    · exact le_refl _
  have hOT1 : ∀ t ∈ one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG1 q j
  have hOT2 : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  have hvq : ρ'.v q = add (ρ.v r) (omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q)))) := by
    rw [(hC1 q hqT).2]; unfold vRhs
    rw [entry_take M 1 hqx, entry_take M 2 hqx, if_neg (by omega), if_neg (by omega), par_take M 1 q hqx,
      hpar1q, children_take]
    show sf (add (ρ'.v r) _) = _
    rw [hvr, sf_ot (isOT_add (I.good.ot_v r (by omega)) (isOT_omega (isOT_sumN _ hOT1)))]
  -- `v_M(q) = V + ω^{S+1}`: the bump term of `x` is `1`
  have hSot : isOT (sumN (one :: Lq.map (bumpTerm M ρ q))) = true := isOT_sumN _ hOT2
  have hbx : bumpTerm M ρ q (r + L) = one := by
    unfold bumpTerm; rw [if_pos Txb]
    have hnil : children M (r + L) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro c hc
      have h1 := (mem_children hc).2
      have h2 := par_lt M 0 c (r + L) (mem_children_iff.mp hc).2
      omega
    rw [hnil]; rfl
  have hvqM : ρ.v q = add (ρ.v r) (omega (succ (sumN (one :: Lq.map (bumpTerm M ρ q))))) := by
    rw [(I.cons q (by omega)).2]; unfold vRhs
    rw [if_neg (by omega), if_neg (by omega), hpar1q, hcqM, List.map_append, List.map_singleton, hbx,
      ← List.cons_append, sumN_snoc, add_one_eq_succ hSot, sf_ot (isOT_succ hSot)]
    show sf (add (ρ.v r) _) = _
    rw [sf_ot (isOT_add (I.good.ot_v r (by omega)) (isOT_omega (isOT_succ hSot)))]
  -- the argument of `r` in `M.take x`
  have hvalsT := cl_vals hC1 hG1 (show r < (M.take (r + L)).length by omega)
  rw [hCLTr, List.map_append, List.map_singleton] at hvalsT
  have hτL : Lc.map τ.o = Lc.map ρ'.o := List.map_congr_left (fun c hc => (hag c (by
    have hcT : c ∈ CL (M.take (r + L)) r := by rw [hCLTr]; exact List.mem_append_left _ hc
    exact (mem_children (cl_mem_children hcT)).2)).1)
  have hB : spArg (ρ.v r) z (sumN (Lc.map ρ'.o)) = t2B (ρ.v r) ρ Lc := by unfold t2B; rw [hLo]
  have hoqM : ρ.o q = psi (ρ.v q) z z := by
    rw [o_cl_eq I.cons I.good (show q < M.length by omega), TCLq]; rfl
  obtain ⟨hBc, hBot, -⟩ := leaf_M_side I (show r < M.length by omega) hCLM hoqM
  have hoqle : ρ'.o q ≤ ρ.o q := po_le (hdrop q hqx).1
  refine ⟨omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q))), ?_, by rw [(hag q hqT).2, hvq],
    isOT_omega (isOT_sumN _ hOT1), omega_psi_form _, ?_, ?_⟩
  · rw [hCLTr, List.map_append, List.map_singleton, hτL, (hag q hqT).1, (hag r (by omega)).2, hvr,
      sumN_append_dec hvalsT.1 hvalsT.2, sumN_singleton (hvalsT.1 _ (by simp)), spArg_app, hB, hoq,
      spArg_single, ← hvq]
    apply step_app_leaf hBot (T.not_lt_z _)
    intro hBz
    rw [← hoq]
    exact le_trans hoqle (hoqM ▸ hBc _ (last_mem_summands hBz))
  · apply omega_le_omega (isOT_sumN _ hOT1) (isOT_sumN _ hOT2)
    exact sumN_le2 (List.Forall₂.cons (le_refl _) (forall₂_map_le Lq hbT)) hOT1 hOT2
  · exact hvqM


/-- `V + (ψ ++ Z) = (V + ψ) ++ Z` for a single `ψ`. -/
theorem add_app_single {s y : T} (Zt : T) : ∀ V : T, add V (app (psi s y z) Zt) = app (add V (psi s y z)) Zt
  | z => by simp [add]
  | psi a b c => by
    have ih := add_app_single (s := s) (y := y) Zt c
    simp only [app_psi, app_z] at ih ⊢
    rw [add_psi_psi, add_psi_psi]
    split
    · simp
    · rw [app_psi, ih]

/-- **The qn subscripts `t_k` (`k ≥ 1`) are `◁ v(q)`** when `t₁ = V + ω_T ⊴ v(q) = V + ω^{S+1}`
(`s′ = V + ω^S`, `ω_T ≤ ω^S`, the subscript of `ω^S` at most `V`). `t_{k+1} = s′ ++ X` with the summands of `X` equal to
`ω^S` or `ω_T`, so a component of `t_{k+1}` is one of `s′` (`s′ ◁ v(q)`, `add_omega_succ_lhd`) or of `t₁`. -/
theorem qn_tqN_lhd {V S ωT : T} (hV : isOT V = true) (hS : isOT S = true) (hωlev : ¬ V < lev (omega S))
    (hωTot : isOT ωT = true) (hωTf : ∃ a b, ωT = psi a b z) (hωT : ωT ≤ omega S)
    (hD : LhdE (add V ωT) (add V (omega (succ S)))) :
    ∀ k, 1 ≤ k → tqN V (add V (omega S)) (add V ωT) k < add V (omega (succ S)) ∧
      (tqN V (add V (omega S)) (add V ωT) k = add V (omega (succ S)) ∨
        Lhd z (tqN V (add V (omega S)) (add V ωT) k) (add V (omega (succ S)))) := by
  set ω := omega S with hωdef
  have hωot : isOT ω = true := isOT_omega hS
  obtain ⟨a, b, hωf⟩ := omega_psi_form S
  rw [← hωdef] at hωf
  obtain ⟨a1, b1, hωTf⟩ := hωTf
  have hs'ot : isOT (add V ω) = true := isOT_add hV hωot
  have hVs : V < add V ω := by rw [hωf]; exact lt_add_principal a b V
  have hlast : last (add V ω) = ω := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, last_app P (by rw [hωf]; simp), hωf]; rfl
  have hωlast : last ω = ω := by rw [hωf]; rfl
  have hωTlev : ¬ V < lev ωT := fun h => hωlev (lt_of_lt_of_le h (lev_le_of_le hωT))
  have hshω : sh V (add V ω) ω = ω := sh_fix hωot hωlev
  have hshωT : sh V (add V ω) ωT = ωT := sh_fix hωTot hωTlev
  have hsubV : ∀ Y, sub (add V Y) V = Y := fun Y => by
    rw [sub_add_dist Y hV hV (le_refl _), sub_self_T]; rfl
  have hheadT : head ωT ≤ ω := by rw [hωTf]; show psi a1 b1 z ≤ ω; rw [← hωTf]; exact hωT
  have key : ∀ k, ∃ X, X ≠ z ∧ isOT X = true ∧ head X ≤ ω ∧ (∀ t ∈ summands X, t = ω ∨ t = ωT) ∧
      sh V (add V ω) X = X ∧ tqN V (add V ω) (add V ωT) (k + 1) = app (add V ω) X := by
    intro k
    induction k with
    | zero =>
      have hsT : ∀ t ∈ summands ωT, t = ω ∨ t = ωT := by
        intro t ht; rw [hωTf] at ht ⊢; simp [summands] at ht; exact Or.inr ht
      refine ⟨ωT, by rw [hωTf]; simp, hωTot, hheadT, hsT, hshωT, ?_⟩
      show add (add V ω) (sh V (add V ω) (sub (add V ωT) V)) = _
      rw [hsubV, hshωT]
      exact add_eq_app_of_last hs'ot (by rw [hlast]; exact hheadT)
    | succ k ih =>
      obtain ⟨X, _, hXot, hXh, hXs, hXfix, hXe⟩ := ih
      have happ : add ω X = app ω X := add_eq_app_of_last hωot (by rw [hωlast]; exact hXh)
      have hhd : head (app ω X) = ω := by rw [hωf]; rfl
      refine ⟨app ω X, by rw [hωf]; simp [app], by rw [← happ]; exact isOT_add hωot hXot, by rw [hhd], ?_,
        by rw [sh_app, hshω, hXfix], ?_⟩
      · intro t ht
        rw [summands_app] at ht
        rcases List.mem_append.mp ht with ht | ht
        · rw [hωf] at ht ⊢; simp [summands] at ht; exact Or.inl ht
        · exact hXs t ht
      show add (add V ω) (sh V (add V ω) (sub (tqN V (add V ω) (add V ωT) (k + 1)) V)) = _
      rw [hXe, ← add_eq_app_of_last hs'ot (by rw [hlast]; exact hXh),
        sub_add_dist X hV hs'ot (le_of_lt hVs), hsubV, happ, sh_app, hshω, hXfix]
      exact add_eq_app_of_last hs'ot (by rw [hlast, hhd])
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨X, hX0, _, _, hXs, _, hXe⟩ := key j
  rw [hXe]
  have hSs : isOT (succ S) = true := isOT_succ hS
  obtain ⟨a', b', hω'f⟩ := omega_psi_form (succ S)
  have hωω' : ω < omega (succ S) := omega_lt_omega hS hSs (lt_succ_self S)
  have hlt : app (add V ω) X < add V (omega (succ S)) := by
    rw [hωf, ← add_app_single X V, ← hωf]
    apply add_lt_add_left V
    rw [hωf, hω'f] at hωω' ⊢
    simp only [app_psi, app_z]
    rw [T.psi_lt_psi] at hωω' ⊢
    rcases hωω' with h | ⟨h1, h⟩ | ⟨h1, h2, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h⟩)
    · exact absurd h (T.not_lt_z _)
  refine ⟨hlt, Or.inr ⟨hlt, fun u c h1 h2 g hg => ?_⟩⟩
  have hs'c : add V ω < c := lt_trans (lhd_prefix (η := z) hX0).1 h1
  have hLs := add_omega_succ_lhd hV hS
  have hωmem : ω ∈ summands (add V ω) := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, summands_app, hωf]; simp [summands]
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hLs.2 u c hs'c h2 g hg
  · obtain ⟨t, ht, hgt⟩ := comps_sub_summands u X g hg
    rcases hXs t ht with rfl | rfl
    · exact hLs.2 u c hs'c h2 g (comps_summand_sub u hωmem g hgt)
    · have hTmem : t ∈ summands (add V t) := by
        obtain ⟨P, hP, _⟩ := add_eq_app_prefix V t
        rw [hP, summands_app, hωTf]; simp [summands]
      have ht1c : add V t < c := lt_of_le_of_lt (add_le_add_left V hωT) hs'c
      rcases hD with he | hl
      · rw [he] at ht1c; exact absurd (lt_of_lt_of_le ht1c h2) (lt_irrefl' _)
      · exact hl.2 u c ht1c h2 g (comps_summand_sub u hTmem g hgt)

/-- **The qn subscripts `t_k` (`k ≥ 1`) are `◁ v(q)`** when the first one is (2026-10-25: on `Bad2` the drop
`t₁ = V + ω_T ⊴ v(q)` of `qn_tqN_lhd` is false, b2grow1 319 of 587, while `t_1 ◁ v(q)` holds). `v(q) = V + ω^{S+1}`
(`s′ = V + ω^S`, `ω_T ≤ ω^S`, the subscript of `ω^S` at most `V`). `t_{k+1} = s′ ++ X` with the summands of `X` equal to
`ω^S` or `ω_T`, so a component of `t_{k+1}` is one of `s′` (`s′ ◁ v(q)`, `add_omega_succ_lhd`) or of `t₁`. -/
theorem qn_tqN_lhd1 {V S ωT : T} (hV : isOT V = true) (hS : isOT S = true) (hωlev : ¬ V < lev (omega S))
    (hωTot : isOT ωT = true) (hωTf : ∃ a b, ωT = psi a b z) (hωT : ωT ≤ omega S)
    (hD1 : Lhd z (tqN V (add V (omega S)) (add V ωT) 1) (add V (omega (succ S)))) :
    ∀ k, 1 ≤ k → tqN V (add V (omega S)) (add V ωT) k < add V (omega (succ S)) ∧
      (tqN V (add V (omega S)) (add V ωT) k = add V (omega (succ S)) ∨
        Lhd z (tqN V (add V (omega S)) (add V ωT) k) (add V (omega (succ S)))) := by
  set ω := omega S with hωdef
  have hωot : isOT ω = true := isOT_omega hS
  obtain ⟨a, b, hωf⟩ := omega_psi_form S
  rw [← hωdef] at hωf
  obtain ⟨a1, b1, hωTf⟩ := hωTf
  have hs'ot : isOT (add V ω) = true := isOT_add hV hωot
  have hVs : V < add V ω := by rw [hωf]; exact lt_add_principal a b V
  have hlast : last (add V ω) = ω := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, last_app P (by rw [hωf]; simp), hωf]; rfl
  have hωlast : last ω = ω := by rw [hωf]; rfl
  have hωTlev : ¬ V < lev ωT := fun h => hωlev (lt_of_lt_of_le h (lev_le_of_le hωT))
  have hshω : sh V (add V ω) ω = ω := sh_fix hωot hωlev
  have hshωT : sh V (add V ω) ωT = ωT := sh_fix hωTot hωTlev
  have hsubV : ∀ Y, sub (add V Y) V = Y := fun Y => by
    rw [sub_add_dist Y hV hV (le_refl _), sub_self_T]; rfl
  have hheadT : head ωT ≤ ω := by rw [hωTf]; show psi a1 b1 z ≤ ω; rw [← hωTf]; exact hωT
  have key : ∀ k, ∃ X, X ≠ z ∧ isOT X = true ∧ head X ≤ ω ∧ (∀ t ∈ summands X, t = ω ∨ t = ωT) ∧
      sh V (add V ω) X = X ∧ tqN V (add V ω) (add V ωT) (k + 1) = app (add V ω) X := by
    intro k
    induction k with
    | zero =>
      have hsT : ∀ t ∈ summands ωT, t = ω ∨ t = ωT := by
        intro t ht; rw [hωTf] at ht ⊢; simp [summands] at ht; exact Or.inr ht
      refine ⟨ωT, by rw [hωTf]; simp, hωTot, hheadT, hsT, hshωT, ?_⟩
      show add (add V ω) (sh V (add V ω) (sub (add V ωT) V)) = _
      rw [hsubV, hshωT]
      exact add_eq_app_of_last hs'ot (by rw [hlast]; exact hheadT)
    | succ k ih =>
      obtain ⟨X, _, hXot, hXh, hXs, hXfix, hXe⟩ := ih
      have happ : add ω X = app ω X := add_eq_app_of_last hωot (by rw [hωlast]; exact hXh)
      have hhd : head (app ω X) = ω := by rw [hωf]; rfl
      refine ⟨app ω X, by rw [hωf]; simp [app], by rw [← happ]; exact isOT_add hωot hXot, by rw [hhd], ?_,
        by rw [sh_app, hshω, hXfix], ?_⟩
      · intro t ht
        rw [summands_app] at ht
        rcases List.mem_append.mp ht with ht | ht
        · rw [hωf] at ht ⊢; simp [summands] at ht; exact Or.inl ht
        · exact hXs t ht
      show add (add V ω) (sh V (add V ω) (sub (tqN V (add V ω) (add V ωT) (k + 1)) V)) = _
      rw [hXe, ← add_eq_app_of_last hs'ot (by rw [hlast]; exact hXh),
        sub_add_dist X hV hs'ot (le_of_lt hVs), hsubV, happ, sh_app, hshω, hXfix]
      exact add_eq_app_of_last hs'ot (by rw [hlast, hhd])
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨X, hX0, _, _, hXs, _, hXe⟩ := key j
  rw [hXe]
  have hSs : isOT (succ S) = true := isOT_succ hS
  obtain ⟨a', b', hω'f⟩ := omega_psi_form (succ S)
  have hωω' : ω < omega (succ S) := omega_lt_omega hS hSs (lt_succ_self S)
  have hlt : app (add V ω) X < add V (omega (succ S)) := by
    rw [hωf, ← add_app_single X V, ← hωf]
    apply add_lt_add_left V
    rw [hωf, hω'f] at hωω' ⊢
    simp only [app_psi, app_z]
    rw [T.psi_lt_psi] at hωω' ⊢
    rcases hωω' with h | ⟨h1, h⟩ | ⟨h1, h2, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h⟩)
    · exact absurd h (T.not_lt_z _)
  refine ⟨hlt, Or.inr ⟨hlt, fun u c h1 h2 g hg => ?_⟩⟩
  have hs'c : add V ω < c := lt_trans (lhd_prefix (η := z) hX0).1 h1
  have hLs := add_omega_succ_lhd hV hS
  have hωmem : ω ∈ summands (add V ω) := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, summands_app, hωf]; simp [summands]
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hLs.2 u c hs'c h2 g hg
  · obtain ⟨t, ht, hgt⟩ := comps_sub_summands u X g hg
    rcases hXs t ht with h | h
    · rw [h] at hgt
      exact hLs.2 u c hs'c h2 g (comps_summand_sub u hωmem g hgt)
    · rw [h] at hgt
      have h1e : tqN V (add V ω) (add V ωT) 1 = app (add V ω) ωT := by
        show add (add V ω) (sh V (add V ω) (sub (add V ωT) V)) = _
        rw [hsubV, hshωT]
        exact add_eq_app_of_last hs'ot (by rw [hlast]; exact hheadT)
      rw [h1e] at hD1
      have hX1 : app (add V ω) ωT ≤ app (add V ω) X := by
        apply app_le_app_left
        cases X with
        | z => exact absurd rfl hX0
        | psi a0 b0 c0 =>
          refine le_trans ?_ (head_le_self (psi a0 b0 c0))
          rcases hXs (psi a0 b0 z) (by simp [summands]) with h' | h'
          · show ωT ≤ psi a0 b0 z; rw [h']; exact hωT
          · show ωT ≤ psi a0 b0 z; exact le_of_eq h'.symm
      exact hD1.2 u c (lt_of_le_of_lt hX1 h1) h2 g (by rw [comps_app]; exact List.mem_append_right _ hgt)

/-- **The qn field of `T2SeedPResRC2`** from the first subscript: `t_1 ◁ v_M(q)` (`t_0 = v_T(q)`, `T = M.take x`). -/
theorem t2SeedPResQN1_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (hD1 : ∀ τ, Cons (M.take (r + L)) τ → Lhd z (tqN (ρ.v r) (qnS M ρ r L q) (τ.v q) 1) (ρ.v q)) :
    ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
      ρ.v r < t1 ∧ isOT t1 = true ∧
      ∀ k, 1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
        (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q)) := by
  intro τ hτ
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨ωT, hsp, hvq, hωTot, hωTf, hωT, hvqM⟩ := qn_take_t1L hM hS I R hlen hr hq hqr hCL hτ
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, -⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hωlev := qn_omega_lev hX hJ I.cons I.good I.rank (by omega) hr hq hpq Txb
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hSot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  refine ⟨add (ρ.v r) ωT, hsp, ?_, isOT_add hV hωTot, ?_⟩
  · obtain ⟨a1, b1, h⟩ := hωTf; rw [h]; exact lt_add_principal a1 b1 _
  · have hD' := hD1 τ hτ
    unfold qnS at hD'
    rw [hvq, hvqM] at hD'
    have := qn_tqN_lhd1 hV hSot hωlev hωTot hωTf hωT hD'
    unfold qnS; rw [hvqM]; exact this

/-- **The first qn subscript from the drop at `q`**: `v_T(q) ⊴ v_M(q)` gives `t_1 ◁ v_M(q)`. -/
theorem qn1_of_lhdE {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (hD : ∀ τ, Cons (M.take (r + L)) τ → LhdE (τ.v q) (ρ.v q)) :
    ∀ τ, Cons (M.take (r + L)) τ → Lhd z (tqN (ρ.v r) (qnS M ρ r L q) (τ.v q) 1) (ρ.v q) := by
  intro τ hτ
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨ωT, hsp, hvq, hωTot, hωTf, hωT, hvqM⟩ := qn_take_t1L hM hS I R hlen hr hq hqr hCL hτ
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, -⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hωlev := qn_omega_lev hX hJ I.cons I.good I.rank (by omega) hr hq hpq Txb
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hSot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  have hD' := hD τ hτ
  rw [hvq, hvqM] at hD'
  have h := qn_tqN_lhd hV hSot hωlev hωTot hωTf hωT hD' 1 le_rfl
  unfold qnS; rw [hvq, hvqM]
  rcases h.2 with he | hl
  · exact absurd he (ne_of_lt h.1)
  · exact hl

/-- **The first qn subscript from the components** (2026-10-25): `t_1 = V + ω^S + ω_T ◁ V + ω^{S+1}` when every
component of `ω_T` is at most a component of `V + ω^S` or `0`. A `c ∈ (t_1, V + ω^{S+1}]` is above `V + ω^S`, so its
components bound those of `V + ω^S` (`add_omega_succ_lhd`). -/
theorem qn_t1_lhd_of_dom {V S ωT : T} (hV : isOT V = true) (hS : isOT S = true) (hωlev : ¬ V < lev (omega S))
    (hωTot : isOT ωT = true) (hωTf : ∃ a b, ωT = psi a b z) (hωT : ωT ≤ omega S)
    (hDom : ∀ u, Dom (comps u ωT) (comps u (add V (omega S)) ++ [z])) :
    Lhd z (tqN V (add V (omega S)) (add V ωT) 1) (add V (omega (succ S))) := by
  set ω := omega S with hωdef
  have hωot : isOT ω = true := isOT_omega hS
  obtain ⟨a, b, hωf⟩ := omega_psi_form S
  rw [← hωdef] at hωf
  obtain ⟨a1, b1, hωTf⟩ := hωTf
  have hs'ot : isOT (add V ω) = true := isOT_add hV hωot
  have hlast : last (add V ω) = ω := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, last_app P (by rw [hωf]; simp), hωf]; rfl
  have hωTlev : ¬ V < lev ωT := fun h => hωlev (lt_of_lt_of_le h (lev_le_of_le hωT))
  have hshωT : sh V (add V ω) ωT = ωT := sh_fix hωTot hωTlev
  have hsubV : ∀ Y, sub (add V Y) V = Y := fun Y => by
    rw [sub_add_dist Y hV hV (le_refl _), sub_self_T]; rfl
  have hheadT : head ωT ≤ ω := by rw [hωTf]; show psi a1 b1 z ≤ ω; rw [← hωTf]; exact hωT
  have h1e : tqN V (add V ω) (add V ωT) 1 = app (add V ω) ωT := by
    show add (add V ω) (sh V (add V ω) (sub (add V ωT) V)) = _
    rw [hsubV, hshωT]
    exact add_eq_app_of_last hs'ot (by rw [hlast]; exact hheadT)
  rw [h1e]
  have hX0 : ωT ≠ z := by rw [hωTf]; simp
  have hSs : isOT (succ S) = true := isOT_succ hS
  obtain ⟨a', b', hω'f⟩ := omega_psi_form (succ S)
  have hωω' : ω < omega (succ S) := omega_lt_omega hS hSs (lt_succ_self S)
  have hlt : app (add V ω) ωT < add V (omega (succ S)) := by
    rw [hωf, ← add_app_single ωT V, ← hωf]
    apply add_lt_add_left V
    rw [hωf, hω'f] at hωω' ⊢
    simp only [app_psi, app_z]
    rw [T.psi_lt_psi] at hωω' ⊢
    rcases hωω' with h | ⟨h1, h⟩ | ⟨h1, h2, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h⟩)
    · exact absurd h (T.not_lt_z _)
  refine ⟨hlt, fun u c h1 h2 g hg => ?_⟩
  have hs'c : add V ω < c := lt_trans (lhd_prefix (η := z) hX0).1 h1
  have hLs := add_omega_succ_lhd hV hS
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hLs.2 u c hs'c h2 g hg
  · obtain ⟨d, hd, hgd⟩ := hDom u g hg
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨d', hd', hdd'⟩ := hLs.2 u c hs'c h2 d hd
      exact ⟨d', hd', le_trans hgd hdd'⟩
    · rw [List.mem_singleton] at hd
      subst hd
      exact ⟨z, List.mem_append_right _ (List.mem_cons_self ..), hgd⟩

/-- **The first qn subscript** from the drop `v_T(q) ⊴ v_M(q)` (`qn_tqN_lhd`) or, where it fails, from the components
of the top summand `ω_T` of `v_T(q)` (`qn_t1_lhd_of_dom`). -/
theorem qn1_of_dom {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (hDom : ∀ τ, Cons (M.take (r + L)) τ → ¬ LhdE (τ.v q) (ρ.v q) → ∀ ωT, τ.v q = add (ρ.v r) ωT →
      (∃ a b, ωT = psi a b z) → ∀ u, Dom (comps u ωT) (comps u (qnS M ρ r L q) ++ [z])) :
    ∀ τ, Cons (M.take (r + L)) τ → Lhd z (tqN (ρ.v r) (qnS M ρ r L q) (τ.v q) 1) (ρ.v q) := by
  intro τ hτ
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨ωT, hsp, hvq, hωTot, hωTf, hωT, hvqM⟩ := qn_take_t1L hM hS I R hlen hr hq hqr hCL hτ
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, -⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hωlev := qn_omega_lev hX hJ I.cons I.good I.rank (by omega) hr hq hpq Txb
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hSot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  by_cases hE : LhdE (τ.v q) (ρ.v q)
  · rw [hvq, hvqM] at hE
    have h := qn_tqN_lhd hV hSot hωlev hωTot hωTf hωT hE 1 le_rfl
    unfold qnS; rw [hvq, hvqM]
    rcases h.2 with he | hl
    · exact absurd he (ne_of_lt h.1)
    · exact hl
  have hD := hDom τ hτ hE ωT hvq hωTf
  unfold qnS at hD
  unfold qnS; rw [hvq, hvqM]
  exact qn_t1_lhd_of_dom hV hSot hωlev hωTot hωTf hωT hD

/-- **The qn field of `T2SeedPResRC2`** from the drop at `q`: `v_T(q) ⊴ v_M(q)` (`T = M.take x`). -/
theorem t2SeedPResQN_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (hD : ∀ τ, Cons (M.take (r + L)) τ → LhdE (τ.v q) (ρ.v q)) :
    ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
      ρ.v r < t1 ∧ isOT t1 = true ∧
      ∀ k, 1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
        (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q)) :=
  t2SeedPResQN1_of hM hS I R hlen hr hq hqr hCL (qn1_of_lhdE hM hS I R hlen hr hq hqr hCL hD)

/-- **The seed residuals with the qn field reduced to the first subscript** (`t_1 ◁ v_M(q)`). -/
structure T2SeedPResRC3 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SVStrict M ρ r L ∧
      ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
        Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → ∀ τ, Cons (M.take (r + L)) τ →
      Lhd z (tqN (ρ.v r) (qnS M ρ r L q) (τ.v q) 1) (ρ.v q)
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCResR2 M ρ r L q

/-- **Residual (t2): the seed residuals with the qn field `t_1 ◁ v_M(q)`** (2026-10-25: was `v_T(q) ⊴ v_M(q)`, false on
`Bad2`). -/
def T2SeedPResRCV2C : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC3 M ρ

theorem t2SeedPResRCV2B_of_C (h : T2SeedPResRCV2C) : T2SeedPResRCV2B := fun M ρ rk C hz h2 =>
  have H := h M ρ rk C hz h2
  ⟨H.qr, H.sv, fun r L q hlen hr hq hqr Lc hCL τ hτ =>
    t2SeedPResQN1_of C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hlen hr hq hqr hCL
      (H.qn r L q hlen hr hq hqr Lc hCL) τ hτ, H.C⟩

end Ytosk
