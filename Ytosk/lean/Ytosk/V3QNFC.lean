/-
**t = 2・qn の種 q の枠の FC3 の残り `T2SeedQNFC` の証明（closure、2026-10-12）。**

場面: x = r + L、q = P_0(x) ≠ r、P_0(q) = r、CL_M(r) = [q]（Lc = []）。V = v(r)、
s′ = v_N(q) = V + ω^W（W = 1 + Σ_{j < x} bumpTerm(q, j)、`qnS`）、T = M.take x、τ は T の評価。
示すこと: r の T での引数 Ω_{t1} について、どの k でも f^{k+1}(t1) = s′ + X（X ≠ 0、f = shf V s′）。

証明の筋:
- 構造: q の x より前の bump 子 j の子 c は e2 c = 0・e1 c ≤ e1 r で、e1 c ≠ 0 なら P_1(c) は r の真の祖先
  （BumpLeaf: j は q の最後の子でないので e1 c < e1 q、R1S: e1 q = e1 r + 1、RowJ: e2 c ≠ 0 なら e1 j ≤ e1 c）。
  よって v(c) ≤ V（`t_above0A`: V3Tame の t_above0 を「x は r の子孫」に一般化したもの）。
- したがって ω^W の添字は V 以下で、σ = σ_{V,s′} は ω^W を動かさない（`sh_fix`）。
- T では CL_T(q) = []・CL_T(r) = [q]（cl_prefix）なので o_T(q) = Ω_{v_T(q)}、t1 = v_T(q) = V + ω^{W_T}。
  落とす補題（drop_all）で o_T ≤ o_M なので W_T ≤ W、ω^{W_T} ≤ ω^W。
- f(t1) = s′ ⊕ σ(ω^{W_T}) = s′ + ω^{W_T}、以後 f(s′ + X) = s′ + ω^W + σX。
-/
import Ytosk.V3PSeedQNG
import Ytosk.V3Tame
import Ytosk.V3DropPres
import Ytosk.V3BumpDrop
import Ytosk.V3InvW

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## `P_1(c)` が r より上: v(c) ≤ v(r)（x は r の子孫） -/

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x : Nat} (hA : Anc0 M r x)
  (hxM : x < M.length) (he2r : entry M 2 r = 0)
include hX hJ hC hG hR hA hxM he2r

/-- **Row 2 zero, `P_1(c)` above `r`**: `v(c) ≤ v(r)` (`x` a descendant of `r`). -/
theorem t_above0A {c m : Nat} (h1 : r < c) (h2 : c < x) (he1 : entry M 1 c ≠ 0) (he2 : entry M 2 c = 0)
    (hm : par M 1 c = some m) (hmr : m < r) : ¬ ρ.v r < ρ.v c := by
  have hcM : c < M.length := by omega
  have hrM : r < M.length := by omega
  have hAr : Anc0 M r c := anc_between hA c (le_of_lt h1) (le_of_lt h2)
  obtain ⟨hmc, _, he1m, hbet⟩ := par1_facts hm
  have hAmr : Anc0 M m r := by
    rcases anc0_total hmc hAr with h | h
    · exact h
    · have := h.le; omega
  have hre1 : entry M 1 c ≤ entry M 1 r := hbet r hAmr hAr (by omega) (by omega)
  have hvm : isOT (vOpt ρ (par M 1 c)) = true := vOpt_ot hG hcM
  have hbk : ∀ k, ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun k j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  cases hu : upg M c with
  | none =>
    have hvc : ρ.v c = succ (ρ.v m) := by
      rw [(hC c hcM).2]; unfold vRhs
      rw [if_neg he1, if_pos he2, hm, hu]
      have hmot := hG.ot_v m (by have := hmc.le; omega)
      show sf (add (ρ.v m) one) = _
      rw [sf_ot (isOT_add hmot isOT_one), add_one_eq_succ hmot]
    have hfind : (ancL M r).find? (fun q => decide (entry M 1 q < entry M 1 c)) = some m := by
      have hp := hm
      rw [par1_find] at hp
      obtain ⟨S, hS, hSp⟩ := ancL_through hAr (by omega)
      rw [hS, List.find?_append, List.find?_cons] at hp
      have hSn : S.find? (fun q => decide (entry M 1 q < entry M 1 c)) = none := by
        rw [List.find?_eq_none]
        intro s hs
        obtain ⟨hrs, hsc, hArs, hAsc⟩ := hSp s hs
        have := hbet s (Anc0.trans hAmr hArs) hAsc (by omega) (by omega)
        simp; omega
      rw [hSn, Option.none_or, decide_eq_false (by omega)] at hp
      exact hp
    have hlt := v_find_lt hC hG hR r hrM (entry M 1 c) m hre1 hfind
    rw [hvc]
    exact not_lt_of_ge (succ_le_of_lt hlt)
  | some k =>
    have hvck := v_upg_eq hC hcM he1 he2 hu hvm (hbk k)
    obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
    rw [hm] at hm'; cases hm'
    have he0m : entry M 0 m < entry M 0 r := anc0_e0_lt hAmr (by omega)
    have he0k : entry M 0 k = entry M 0 m + 1 := hX.r0p k m hpk
    rcases hcase with hk | ⟨hAkc, hkc⟩
    · exfalso
      subst hk
      have hc1M : c + 1 ≤ x := by omega
      have hAc1 : Anc0 M r (c + 1) := anc_between hA (c + 1) (by omega) hc1M
      have := anc0_e0_lt hAc1 (by omega)
      omega
    · have hAkr : Anc0 M k r := by
        rcases anc0_total hAkc hAr with h | h
        · exact h
        · exfalso
          by_cases hrk : r = k
          · subst hrk
            have := upg_target_e2 hu; omega
          · have := anc0_e0_lt h hrk; omega
      have hsp := (upg_anc_spine hX.r0p hX.z2 (uab_of_bumpLeaf hX.loc.2.2.2) hX.loc.2.2.1 hJ hC hG hR
        hcM hu hAkc hkc r hAkr hAr (by omega)).2
      rw [hvck]
      exact not_lt_of_ge hsp

end

/-! ## q の x より前の bump 子の子 -/

/-- A child of an earlier child of `q` comes before `x`. -/
theorem kid_lt_x {M : Mat} {q j c x : Nat} (hjq : par M 0 j = some q) (hxq : par M 0 x = some q)
    (hjx : j < x) (hc : par M 0 c = some j) : c < x := by
  have hjc := par_lt M 0 c j hc
  have hqj := par_lt M 0 j q hjq
  by_contra hcx
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hcx) with h | h
  · subst h; rw [hxq] at hc; cases hc; omega
  · have hAjc : Anc0 M j c := anc0_of_par M 0 j c hc
    have hAjx : Anc0 M j x := anc_between hAjc x (by omega) (by omega)
    have := (anc0_par hAjx (by omega) hxq).le
    omega

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk)
include hX hJ hC hG hR

/-- **The kids of the earlier bump children of `q`** (`q ≠ r` at `t = 2`): `v(c) ≤ v(r)`. -/
theorem qn_kid_v {r x q : Nat} (hxM : x < M.length) (hr : par M 2 x = some r) (hq : par M 0 x = some q)
    (hpq : par M 0 q = some r) (hxb : col M x = bump M q) {j c : Nat} (hjq : j ∈ children M q) (hjx : j < x)
    (hjb : col M j = bump M q) (hc : c ∈ children M j) : ¬ ρ.v r < ρ.v c := by
  have hA : Anc0 M r x := anc0_of_par M 2 r x hr
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 hxM hr
  have he1x : entry M 1 x = entry M 1 q := e1_of_col (show col M x = (entry M 0 q + 1, entry M 1 q, 1) from hxb)
  have hq1 : entry M 1 q ≤ entry M 1 r + 1 := hX.r1s q r hpq
  have he1j : entry M 1 j = entry M 1 q := e1_of_col (show col M j = (entry M 0 q + 1, entry M 1 q, 1) from hjb)
  have hpj : par M 0 j = some q := (mem_children_iff.mp hjq).2
  have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
  have hcx : c < x := kid_lt_x hpj hq hjx hpc
  have hcM : c < M.length := by omega
  have hrq := par_lt M 0 q r hpq
  have hqj := par_lt M 0 j q hpj
  have hjc := par_lt M 0 c j hpc
  -- `e1 c < e1 q` (BumpLeaf: `j` is not the last child of `q`)
  have hlt_c : entry M 1 c < entry M 1 q := by
    by_contra hge
    obtain ⟨_, _, _, hlast⟩ := hX.loc.2.2.2 q j c hjq hjb hc (by omega)
    have hxc : x ∈ children M q := mem_children_iff.mpr ⟨hxM, hq⟩
    obtain ⟨l, hl⟩ : ∃ l, children M q = l ++ [j] := ⟨_, (List.dropLast_append_getLast? _ hlast).symm⟩
    have hsorted := children_sorted M q
    rw [hl] at hxc hsorted
    rcases List.mem_append.mp hxc with h | h
    · have := (List.pairwise_append.mp hsorted).2.2 x h j (by simp)
      omega
    · simp at h; omega
  have hc1r : entry M 1 c ≤ entry M 1 r := by omega
  -- `e2 c = 0` (RowJ)
  have he2c : entry M 2 c = 0 := by
    by_contra h2
    have := hJ c j h2 hpc
    omega
  by_cases he1 : entry M 1 c = 0
  · rw [(hC c hcM).2]; unfold vRhs; rw [if_pos he1]; exact not_lt_z _
  obtain ⟨m, hm⟩ := par1_exists hX.e00 hX.r01 (j := c) (by omega)
  obtain ⟨hmc, _, he1m, hbet⟩ := par1_facts hm
  have hArc : Anc0 M r c := anc_between hA c (by omega) (by omega)
  have hmr : m < r := by
    rcases anc0_total hmc hArc with h | h
    · rcases Nat.eq_or_lt_of_le h.le with h' | h'
      · subst h'; omega
      · exact h'
    · exfalso
      have hmj : Anc0 M m j := anc0_par hmc (by omega) hpc
      by_cases hmj' : m = j
      · subst hmj'; omega
      have hmq : Anc0 M m q := anc0_par hmj hmj' hpj
      by_cases hmq' : m = q
      · subst hmq'; omega
      have hmr' : Anc0 M m r := anc0_par hmq hmq' hpq
      have := hmr'.le; have := h.le
      have hmeq : m = r := by omega
      subst hmeq; omega
  exact t_above0A hX hJ hC hG hR hA hxM he2r (by omega) hcx he1 he2c hm hmr

end

/-! ## lev -/

theorem lev_add_cases : ∀ a b : T, lev (add a b) = lev a ∨ lev (add a b) = lev b
  | z, b => Or.inr (by simp [add])
  | psi a1 b1 c1, z => Or.inl rfl
  | psi a1 b1 c1, psi d e f => by
    simp only [add]
    split <;> simp [lev]

theorem lev_omega_le (x : T) : lev (omega x) ≤ lev x := by
  unfold omega
  split
  · exact z_le _
  · cases x with
    | z => exact le_refl _
    | psi s b c => exact le_refl _

theorem not_lt_lev_sumN {V : T} (l : List T) (hl : ∀ t ∈ l, isOT t = true ∧ ¬ V < lev t) :
    ¬ V < lev (sumN l) := by
  unfold sumN
  suffices h : ∀ acc, isOT acc = true → ¬ V < lev acc → ¬ V < lev (l.foldl (fun a b => sf (add a b)) acc) from
    h z rfl (not_lt_z _)
  induction l with
  | nil => intro acc _ h; exact h
  | cons t l ih =>
    intro acc hacc hlev
    simp only [List.foldl_cons]
    have ht := hl t (by simp)
    have hadd : isOT (add acc t) = true := isOT_add hacc ht.1
    apply ih (fun u hu => hl u (by simp [hu])) _ (by rw [sf_ot hadd]; exact hadd)
    rw [sf_ot hadd]
    rcases lev_add_cases acc t with h | h <;> rw [h]
    · exact hlev
    · exact ht.2

/-- **The subscript of `ω^W` is at most `V`** (`W` from the earlier children of `q`). -/
theorem qn_omega_lev {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x q : Nat} (hxM : x < M.length)
    (hr : par M 2 x = some r) (hq : par M 0 x = some q) (hpq : par M 0 q = some r)
    (hxb : col M x = bump M q) :
    ¬ ρ.v r < lev (omega (sumN (one :: ((children M q).filter (fun d => decide (d < x))).map
      (bumpTerm M ρ q)))) := by
  intro h
  apply not_lt_lev_sumN _ ?_ (lt_of_lt_of_le h (lev_omega_le _))
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨isOT_one, not_lt_z _⟩
  obtain ⟨j, hjL, rfl⟩ := List.mem_map.mp ht
  refine ⟨isOT_bumpTerm hG q j, ?_⟩
  have hjq : j ∈ children M q := (List.mem_filter.mp hjL).1
  have hjx : j < x := by simpa using (List.mem_filter.mp hjL).2
  unfold bumpTerm
  split
  · rename_i hjb
    intro h'
    apply not_lt_lev_sumN _ ?_ (lt_of_lt_of_le h' (lev_omega_le _))
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    have hcM : c < M.length := (mem_children hc).2
    refine ⟨hG.ot_o c hcM, ?_⟩
    rw [o_cl_eq hC hG hcM]
    exact qn_kid_v hX hJ hC hG hR hxM hr hq hpq hxb hjq hjx hjb hc
  · exact not_lt_z _

/-! ## T 側: t1 = V + ω^{W_T}、ω^{W_T} ≤ ω^W -/

theorem forall₂_map_le {α : Type} {f g : α → T} : ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) →
    List.Forall₂ (· ≤ ·) (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | a :: l, h => List.Forall₂.cons (h a (by simp)) (forall₂_map_le l (fun b hb => h b (by simp [hb])))

theorem po_le {ρ ρ' : Valn} {i : Nat} (h : PO ρ ρ' i) : ρ'.o i ≤ ρ.o i := by
  rcases h.1 with h1 | ⟨⟨w', w, X, h1, h2, hw⟩, _⟩
  · exact h1.le
  · rw [h1, h2]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hw.1))

open Classical in
/-- **`t1` in `M.take x`** (qn, `CL_M(r) = [q]`): `t1 = V + ω^{W_T}` with `ω^{W_T} ≤ ω^W`. -/
theorem qn_take_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hCLM : CL M r = [q])
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) {t1 : T}
    (ht1 : spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = psi t1 z z) :
    ∃ ωT, t1 = add (ρ.v r) ωT ∧ isOT ωT = true ∧ (∃ a b, ωT = psi a b z) ∧
      ωT ≤ omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))) := by
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
  have hdrop := drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  have hpre : ∀ i, i < M.length - 1 → ∃ Tl, CL M i = CL (M.take (M.length - 1)) i ++ Tl :=
    fun i hi => cl_prefix hx1 I.r0p I.z2 I.sd I.z1 I.uat hi
  have hfr := fun i (hi : i < M.length - 1) (h : CL (M.take (M.length - 1)) i = [] ++ q :: []) =>
    (frame_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hi h).1
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hdrop hG1 hpre hfr
  set ρ' := rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk) with hρ'
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hag := agree_of_cons hτ hC1 hRk1
  -- `CL_T(q) = []`, `CL_T(r) = [q]`
  obtain ⟨Tl, hTl⟩ := hpre q hqx
  rw [TCLq] at hTl
  have hCLTq : CL (M.take (r + L)) q = [] := (List.append_eq_nil_iff.mp hTl.symm).1
  obtain ⟨Tl', hTl'⟩ := hpre r (by omega)
  rw [hCLM] at hTl'
  have hCLTr : CL (M.take (r + L)) r = [q] := by
    rcases hc : CL (M.take (r + L)) r with _ | ⟨a, l⟩
    · rw [hc] at ht1; exact absurd ht1 (by simp [sumN, spArg])
    · rw [hc] at hTl'
      simp only [List.cons_append, List.cons.injEq] at hTl'
      obtain ⟨rfl, hl⟩ := hTl'
      rw [(List.append_eq_nil_iff.mp hl.symm).1]
  -- `o_T(q) = Ω_{v_T(q)}`, so `t1 = v_T(q)`
  have hqT : q < (M.take (r + L)).length := by omega
  have hoq : ρ'.o q = psi (ρ'.v q) z z := by
    rw [o_cl_eq hC1 hG1 hqT, hCLTq]; rfl
  rw [hCLTr, List.map_singleton, (hag q hqT).1, hoq, sumN_single (by rw [← hoq]; exact hG1.ot_o q hqT),
    spArg_cons] at ht1
  have hst : step (τ.v r) z (ρ'.v q) z z = psi (ρ'.v q) z z := by
    unfold step; rw [if_neg (fun h => T.not_lt_z _ h.1)]; rfl
  rw [hst] at ht1
  have ht1q : t1 = ρ'.v q := by
    have : psi (ρ'.v q) z z = psi t1 z z := ht1
    simp only [psi.injEq] at this; exact this.1.symm
  -- `v_T(q)`
  have hvr : ρ'.v r = ρ.v r := hfr r (by omega) (by rw [hCLTr]; rfl)
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
  refine ⟨omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q))), by rw [ht1q, hvq],
    isOT_omega (isOT_sumN _ hOT1), omega_psi_form _, ?_⟩
  apply omega_le_omega (isOT_sumN _ hOT1) (isOT_sumN _ hOT2)
  exact sumN_le2 (List.Forall₂.cons (le_refl _) (forall₂_map_le Lq hbT)) hOT1 hOT2

theorem sub_self_T : ∀ x : T, sub x x = z
  | z => rfl
  | psi a b c => by rw [sub_psi_self]; exact sub_self_T c

namespace G

/-- **`T2SeedQNFC` holds** (qn, from `Inv3`・`Res3A` of `M`). -/
theorem t2SeedQNFC_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) :
    T2SeedQNFC M ρ r L q Lc := by
  intro hLc0 τ hτ t1 ht1 k
  subst hLc0
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have ht1' : spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = psi t1 z z := by
    rw [ht1]; rfl
  obtain ⟨ωT, ht1e, hωTot, ⟨a1, b1, hωTf⟩, hωT⟩ :=
    qn_take_t1 hM hS I R hlen hr hq hqr (by simpa using hCLM) hτ ht1'
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  set V := ρ.v r with hVdef
  have hWot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  set ω := omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) with hωdef
  have hωot : isOT ω = true := isOT_omega hWot
  obtain ⟨a, b, hωf⟩ := omega_psi_form (sumN (one :: ((children M q).filter
    (fun d => decide (d < r + L))).map (bumpTerm M ρ q)))
  rw [← hωdef] at hωf
  have hV : isOT V = true := I.good.ot_v r hrM
  have hs'ot : isOT (add V ω) = true := isOT_add hV hωot
  have hVs : V < add V ω := qnS_gt M ρ r L q
  have hlast : last (add V ω) = ω := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, last_app P (by rw [hωf]; simp), hωf]; rfl
  have hωlast : last ω = ω := by rw [hωf]; rfl
  have hωlev : ¬ V < lev ω := qn_omega_lev hX hJ I.cons I.good I.rank (by omega) hr hq hpq Txb
  have hωTlev : ¬ V < lev ωT := fun h => hωlev (lt_of_lt_of_le h (lev_le_of_le hωT))
  have hshω : sh V (add V ω) ω = ω := sh_fix hωot hωlev
  have hshωT : sh V (add V ω) ωT = ωT := sh_fix hωTot hωTlev
  have hsubV : ∀ Y, sub (add V Y) V = Y := fun Y => by
    rw [sub_add_dist Y hV hV (le_refl _), sub_self_T]; rfl
  have hheadT : head ωT ≤ ω := by rw [hωTf]; show psi a1 b1 z ≤ ω; rw [← hωTf]; exact hωT
  have key : ∀ k, ∃ X, X ≠ z ∧ isOT X = true ∧ head X ≤ ω ∧
      tqN V (add V ω) t1 (k + 1) = app (add V ω) X := by
    intro k
    induction k with
    | zero =>
      refine ⟨ωT, by rw [hωTf]; simp, hωTot, hheadT, ?_⟩
      show add (add V ω) (sh V (add V ω) (sub t1 V)) = _
      rw [ht1e, hsubV, hshωT]
      exact add_eq_app_of_last hs'ot (by rw [hlast]; exact hheadT)
    | succ k ih =>
      obtain ⟨X, _, hXot, hXh, hXe⟩ := ih
      have hXsh := isOT_sh hV hs'ot hVs hXot
      have hX' : head (sh V (add V ω) X) ≤ ω := by
        rw [head_sh]
        exact le_of_le_of_eq (sh_le_sh hV hs'ot (le_of_lt hVs) (isOT_headT hXot) hωot hXh) hshω
      have happ : add ω (sh V (add V ω) X) = app ω (sh V (add V ω) X) :=
        add_eq_app_of_last hωot (by rw [hωlast]; exact hX')
      have hhd : head (app ω (sh V (add V ω) X)) = ω := by rw [hωf]; rfl
      refine ⟨app ω (sh V (add V ω) X), by rw [hωf]; simp [app], by rw [← happ]; exact isOT_add hωot hXsh,
        by rw [hhd], ?_⟩
      show add (add V ω) (sh V (add V ω) (sub (tqN V (add V ω) t1 (k + 1)) V)) = _
      rw [hXe, ← add_eq_app_of_last hs'ot (by rw [hlast]; exact hXh),
        sub_add_dist X hV hs'ot (le_of_lt hVs), hsubV, add_eq_app_of_last hωot (by rw [hωlast]; exact hXh),
        sh_app, hshω]
      exact add_eq_app_of_last hs'ot (by rw [hlast, hhd])
  obtain ⟨X, hX0, _, _, hXe⟩ := key k
  exact ⟨X, hX0, hXe⟩

end G

end Ytosk
