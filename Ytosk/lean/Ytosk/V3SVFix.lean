/-
**t = 2・sv の種の残り `T2SeedSVFix` の証明（closure、2026-10-12）。**

場面: x = r + L、P_0(x) = P_2(x) = r、x − 1 が x へ上げる（sv）。T = M.take x、τ は T の評価、
V = τ(v r)、V′ = V + 1、σ = σ_{V,V′}、f = shf V V′。e = x − 1 は T では上げないので v_T(e) = V′、o_T(e) = Ω_{V′}。

主張（T の見える列 c、順位の帰納法 `sv_main`）:
- σ(o c) = o c か、c は M と M.take x で変わる列（ChgX M x true c）で o c ∈ cutsHG V′ (σ (o c))、
- V < v c なら f(v c) = v c か、ChgX M x false c で v c = V′ か（V < lev (v c) で）v c ∈ cutsHG V′ (σ (v c))。
位置は ChgX の補題から: 変わる数える子は最後の数える子（chg_last）、行 2 ≠ 0 の列の下の変化は最後の子の下だけ
（chg_only_last）、v が変わる列は子を数えず P_1 の子を持たない（chg_struct の TopC）。
項の部分は V3CutOps（add_cut・step_cut・omega_cut）。
-/
import Ytosk.V3CutOps
import Ytosk.V3QNFC

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- An ancestor in `M` below `k` is an ancestor in `M.take k`. -/
theorem anc0_to_take {M : Mat} {k a b : Nat} (h : Anc0 M a b) (hb : b < k) : Anc0 (M.take k) a b := by
  induction h with
  | refl => exact Anc0.refl _
  | @step b c hp hab ih =>
    have hbc := par_lt M 0 c b hp
    have hp' : par (M.take k) 0 c = some b := by rw [par_take M 0 c hb]; exact hp
    exact Anc0.step hp' (ih (by omega))

/-! ## `P_1(c)` が r より上（x は r の子孫） -/

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x : Nat} (hA : Anc0 M r x)
  (hxM : x < M.length) (he2r : entry M 2 r = 0)
include hX hJ hC hG hR hA hxM he2r

/-- **`P_1(c)` above `r`, `c` visible**: `v(c) ≤ v(r)` (`x` a descendant of `r`). -/
theorem t_aboveA : ∀ c, r < c → c < x → (∀ p, r < p → Anc0 M p c → p ≠ c → ρ.v r < ρ.v p) →
    entry M 1 c ≠ 0 → ∀ m, par M 1 c = some m → m < r → ¬ ρ.v r < ρ.v c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro h1 h2 hvis he1 m hm hmr
  by_cases he2 : entry M 2 c = 0
  · exact t_above0A hX hJ hC hG hR hA hxM he2r h1 h2 he1 he2 hm hmr
  exfalso
  have he2c : entry M 2 c = 1 := by have := hX.z2 c; omega
  have hAr : Anc0 M r c := anc_between hA c (le_of_lt h1) (le_of_lt h2)
  obtain ⟨hmc, _, _, hbet⟩ := par1_facts hm
  have hAmr : Anc0 M m r := by
    rcases anc0_total hmc hAr with h | h
    · exact h
    · have := h.le; omega
  have hre1 : entry M 1 c ≤ entry M 1 r := hbet r hAmr hAr (by omega) (by omega)
  obtain ⟨p0, hp0⟩ := par0_some_of (M := M) h1 (anc0_e0_lt hAr (by omega))
  have hAp0 : Anc0 M r p0 := anc0_par hAr (by omega) hp0
  have hp0c : p0 < c := par_lt M 0 c p0 hp0
  have hJ0 : entry M 1 p0 ≤ entry M 1 c := hJ c p0 (by omega) hp0
  have hp0r : p0 ≠ r := by
    intro h; subst h
    have hcb : col M c = bump M p0 := by
      show (entry M 0 c, entry M 1 c, entry M 2 c) = (entry M 0 p0 + 1, entry M 1 p0, 1)
      rw [hX.r0p c p0 hp0, he2c]; congr 2; omega
    have := hX.loc.2.2.1 p0 c (mem_children_iff.mpr ⟨by omega, hp0⟩) hcb
    omega
  have hrp0 : r < p0 := by have := hAp0.le; omega
  have hAp0c : Anc0 M p0 c := anc0_of_par M 0 p0 c hp0
  have he1p0 : entry M 1 p0 = entry M 1 c := by
    have := hbet p0 (Anc0.trans hAmr hAp0) hAp0c (by omega) (by omega); omega
  have hm0 : par M 1 p0 = some m := by
    have hp := hm
    rw [par1_find, ancL_eq hp0, List.find?_cons, decide_eq_false (by omega)] at hp
    rw [par1_find, he1p0]; exact hp
  exact ih p0 hp0c hrp0 (by omega) (fun p hp hA' hne => hvis p hp (Anc0.trans hA' hAp0c) (by have := hA'.le; omega))
    (by omega) m hm0 hmr (hvis p0 hrp0 hAp0c (by omega))

end

/-! ## 補助 -/

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

theorem sh_of_shf_fix {u : T} (hu : isOT u = true) (h : shf V V' u = u) : sh V V' u = u := by
  by_cases hl : V < lev u
  · rw [← shf_eq_sh hV hV' hVV hl]; exact h
  · exact sh_fix hu hl

end

theorem add_absorb {V a b : T} (hV : isOT V = true) (hVa : V < a) : add V (psi a b z) = psi a b z := by
  cases V with
  | z => rfl
  | psi c d e =>
    apply add_eq_right_of_head_lt
    show psi c d z < psi a b z
    have h1 : lev (psi c d z) < psi c d e := lev_lt_of_summand hV (by simp [summands])
    exact psi_lt_psi_z_iff.mpr (Or.inl (lt_trans h1 hVa))

theorem lev_add_gt {V A a b : T} (hVa : V < a) : V < lev (add A (psi a b z)) := by
  cases A with
  | z => simpa using hVa
  | psi a1 b1 c1 =>
    show V < lev (if lt (psi a1 b1 z) (psi a b z) then psi a b z else psi a1 b1 (add c1 (psi a b z)))
    split
    · simpa using hVa
    · rename_i h
      have h1 : psi a b z ≤ psi a1 b1 z := not_lt.mp h
      have := lev_le_of_le h1
      simp only [lev_psi] at this ⊢
      exact lt_of_lt_of_le hVa this

theorem sumN_snoc_add {l : List T} {t : T} (hl : ∀ u ∈ l, isOT u = true) (ht : isOT t = true) :
    sumN (l ++ [t]) = add (sumN l) t := by
  show (l ++ [t]).foldl (fun a b => sf (add a b)) z = _
  rw [List.foldl_append]
  show sf (add (sumN l) t) = _
  exact sf_ot (isOT_add (isOT_sumN l hl) ht)

/-! ## 本体 -/

section
open Classical
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M) (I : Inv3 M ρ rk)
  {r x : Nat} (hx : x + 1 = M.length) (hr : par M 2 x = some r) (hq : par M 0 x = some r)
  (hux : upg M (x - 1) = some x)
  {τ : Valn} {rkT : Bool → Nat → Nat} (hXT : SInvX (M.take x)) (hJT : RowJ (M.take x))
  (hC : Cons (M.take x) τ) (hG : Good3 (M.take x) τ) (hR : Rk (M.take x) rkT)
include hX hJ I hx hr hq hux hXT hJT hC hG hR

/-- **The main induction** (sv): a visible column of `M.take x` is fixed by σ or a cut of its image, and the
non-fixed ones change between `M` and `M.take x`. -/
theorem sv_main : ∀ n c, TVis (M.take x) τ r x c →
    (rkT true c ≤ n → (sh (τ.v r) (succ (τ.v r)) (τ.o c) = τ.o c ∨
      (ChgX M x true c ∧ τ.o c ∈ cutsHG (succ (τ.v r)) (sh (τ.v r) (succ (τ.v r)) (τ.o c))))) ∧
    (rkT false c ≤ n → τ.v r < τ.v c → (shf (τ.v r) (succ (τ.v r)) (τ.v c) = τ.v c ∨
      (ChgX M x false c ∧ (τ.v c = succ (τ.v r) ∨
        (τ.v r < lev (τ.v c) ∧ τ.v c ∈ cutsHG (succ (τ.v r)) (sh (τ.v r) (succ (τ.v r)) (τ.v c))))))) := by
  have hTlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hrx : r < x := par_lt M 0 x r hq
  have hrT : r < (M.take x).length := by omega
  set V := τ.v r with hVdef
  have hVo : isOT V = true := hG.ot_v r hrT
  have hV'o : isOT (succ V) = true := isOT_succ hVo
  have hVV : V < succ V := lt_succ_self V
  have hcnt : ∀ i c, i < x → c ∈ children (M.take x) i → Counted (M.take x) i c → Counted M i c := by
    have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    rwa [show M.length - 1 = x by omega] at this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hVc
  obtain ⟨h1, h2, hvis⟩ := hVc
  have hcT : c < (M.take x).length := by omega
  have hRc := hR c hcT
  constructor
  · -- the `o` equation
    intro hn
    by_cases hlt : V < τ.v c
    · have hv := (ih (rkT false c) (by have := hRc.1; omega) c ⟨h1, h2, hvis⟩).2 le_rfl hlt
      have hvo := hG.ot_v c hcT
      have hkid : ∀ d ∈ CL (M.take x) c, (sh V (succ V) (τ.o d) = τ.o d ∨
          (ChgX M x true d ∧ τ.o d ∈ cutsHG (succ V) (sh V (succ V) (τ.o d)))) := by
        intro d hd
        have hdc := cl_mem_children hd
        have hpd : par (M.take x) 0 d = some c := (mem_children_iff.mp hdc).2
        have hcd := par_lt _ 0 d c hpd
        have hdT := (mem_children hdc).2
        have hcnt' : Counted (M.take x) c d := of_decide_eq_true (List.mem_filter.mp hd).2
        have hT : TVis (M.take x) τ r x d := by
          refine ⟨by omega, by omega, fun p hp hpd' hne => ?_⟩
          have hpc0 : Anc0 (M.take x) p c := anc0_par hpd' hne hpd
          by_cases hpe : p = c
          · rw [hpe]; exact hlt
          · exact hvis p hp hpc0 hpe
        exact (ih (rkT true d) (by have := hRc.2.1 d hdc hcnt'.1 hcnt'.2; omega) d hT).1 le_rfl
      have hoc := o_cl_eq hC hG hcT
      obtain ⟨hsing, hdec⟩ := cl_vals hC hG hcT
      rcases hv with hfix | ⟨hchg, hcut⟩
      · -- `v(c)` fixed: the argument
        have hfixo : ∀ Y, sh V (succ V) (psi (τ.v c) Y z) = psi (τ.v c) (sh V (succ V) Y) z := by
          intro Y; rw [sh_psi_gt hlt, hfix, sh_z]
        rcases (CL (M.take x) c).eq_nil_or_concat with hnil | ⟨L', d0, hLd⟩
        · left
          rw [hoc, hnil, hfixo]
          show psi (τ.v c) (sh V (succ V) z) z = psi (τ.v c) z z
          rw [sh_z]
        rw [List.concat_eq_append] at hLd
        have hd0m : d0 ∈ CL (M.take x) c := by rw [hLd]; simp
        have hfixL : ∀ d ∈ L', sh V (succ V) (τ.o d) = τ.o d := by
          intro d hd
          rcases hkid d (by rw [hLd]; simp [hd]) with h | ⟨hch, _⟩
          · exact h
          · exfalso
            have hsorted : (CL (M.take x) c).Pairwise (· < ·) :=
              List.Pairwise.filter _ (children_sorted _ c)
            rw [hLd] at hsorted
            have hdd0 : d < d0 := (List.pairwise_append.mp hsorted).2.2 d hd d0 (by simp)
            have hd0c := cl_mem_children hd0m
            have hdcT : d ∈ children (M.take x) c := cl_mem_children (by rw [hLd]; simp [hd])
            exact chg_last hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hdcT hch d0 hd0c hdd0
              (of_decide_eq_true (List.mem_filter.mp hd0m).2)
        have hLo : ∀ u ∈ L'.map τ.o, isOT u = true := by
          intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
          exact hG.ot_o d (mem_children (cl_mem_children (by rw [hLd]; simp [hd]))).2
        have hd0T := (mem_children (cl_mem_children hd0m)).2
        have hd0o := hG.ot_o d0 hd0T
        have hS : sumN ((CL (M.take x) c).map τ.o) = app (sumN (L'.map τ.o)) (τ.o d0) := by
          rw [hLd, List.map_append, List.map_singleton]
          rw [hLd, List.map_append, List.map_singleton] at hsing hdec
          rw [sumN_append_dec hsing hdec, sumN_singleton (hsing _ (by simp))]
        have hPfix : sh V (succ V) (sumN (L'.map τ.o)) = sumN (L'.map τ.o) := by
          rw [sh_sumN hVo hV'o hVV hLo, List.map_map]
          congr 1
          apply List.map_congr_left
          intro d hd; exact hfixL d hd
        have hPo := isOT_sumN _ hLo
        have hBf : sh V (succ V) (spArg (τ.v c) z (sumN (L'.map τ.o))) = spArg (τ.v c) z (sumN (L'.map τ.o)) := by
          have := sh_spArg hVo hV'o hVV hvo (le_of_lt hlt) (b := z) (S := sumN (L'.map τ.o)) rfl hPo (Or.inl hlt)
          rw [hfix, sh_z, hPfix] at this
          exact this.symm
        have hBo : isOT (spArg (τ.v c) z (sumN (L'.map τ.o))) = true := isOT_spArg _ _ _ rfl hPo
        obtain ⟨u, y, hu⟩ := o_psi_form hC hd0T
        obtain ⟨u', y', hu'⟩ := sh_single (V := V) (V' := succ V) u y
        have hY : spArg (τ.v c) z (app (sumN (L'.map τ.o)) (psi u y z)) =
            step (τ.v c) (spArg (τ.v c) z (sumN (L'.map τ.o))) u y z := by
          rw [spArg_app, spArg_cons]; rfl
        have hY' : spArg (τ.v c) z (app (sumN (L'.map τ.o)) (psi u' y' z)) =
            step (τ.v c) (spArg (τ.v c) z (sumN (L'.map τ.o))) u' y' z := by
          rw [spArg_app, spArg_cons]; rfl
        have hSo : isOT (app (sumN (L'.map τ.o)) (psi u y z)) = true := by
          rw [← hu, ← hS]; exact isOT_sumN _ (fun t ht => (hsing t ht).1)
        have hσY : sh V (succ V) (spArg (τ.v c) z (app (sumN (L'.map τ.o)) (psi u y z))) =
            spArg (τ.v c) z (app (sumN (L'.map τ.o)) (psi u' y' z)) := by
          have := sh_spArg hVo hV'o hVV hvo (le_of_lt hlt) (b := z) rfl hSo (Or.inl hlt)
          rw [hfix, sh_z, sh_app, hPfix, hu'] at this
          exact this.symm
        rcases hkid d0 hd0m with hf0 | ⟨hch0, hcut0⟩
        · left
          rw [hoc, hS, hfixo, hu, hσY]
          rw [hu] at hf0; rw [hu'] at hf0; rw [hf0]
        · right
          refine ⟨ChgX.ochild (mem_children_iff.mpr ⟨by omega, by
              have := (mem_children_iff.mp (cl_mem_children hd0m)).2
              rwa [par_take M 0 d0 (by omega)] at this⟩)
            (hcnt c d0 h2 (cl_mem_children hd0m) (of_decide_eq_true (List.mem_filter.mp hd0m).2)).1
            (hcnt c d0 h2 (cl_mem_children hd0m) (of_decide_eq_true (List.mem_filter.mp hd0m).2)).2 hch0, ?_⟩
          rw [hoc, hS, hfixo, hu, hσY, hY, hY']
          have hst := G.step_cut hVo hV'o hVV (a := τ.v c) (a' := τ.v c) (u := u) (y := y) (u' := u') (y' := y') hBo hBf (by rw [← hu]; exact hd0o) hu'
            (by rw [hu] at hcut0; rw [hu'] at hcut0; exact hcut0) (by
              have hfa : sh V (succ V) (psi (τ.v c) z z) = psi (τ.v c) z z := by rw [hfixo, sh_z]
              have hle := G.le_fix_iff hVo hV'o hVV (t := psi u y z) (isOT_psi_zz hvo) hfa (by rw [← hu]; exact hd0o)
              rw [hu'] at hle
              constructor
              · intro h; by_contra hn; exact (not_lt.mpr (hle.mpr (not_lt.mp hn))) h
              · intro h; by_contra hn; exact (not_lt.mpr (hle.mp (not_lt.mp hn))) h)
          exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨G.le_true_of_le (succ_le_of_lt hlt), _, hst, rfl⟩)))
      · -- `v(c)` changes: no counted child
        right
        refine ⟨ChgX.ov hchg, ?_⟩
        have hTop := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchg).1 rfl h2
        have hnil : CL (M.take x) c = [] := by
          unfold CL; rw [List.filter_eq_nil_iff]
          intro d hd hdc; exact hTop.2.1 d hd (of_decide_eq_true hdc)
        rw [hoc, hnil]
        show psi (τ.v c) z z ∈ cutsHG (succ V) (sh V (succ V) (psi (τ.v c) z z))
        rw [sh_psi_gt hlt, sh_z]
        rcases hcut with heq | ⟨hlev, hcv⟩
        · rw [heq, shf_succ hVo hV'o hVV hVo (le_refl V), shf_self]
          exact mem_cutsHG_psi.mpr (Or.inl ⟨G.le_true_of_le (le_of_lt (lt_succ_self _)), rfl⟩)
        · rw [shf_eq_sh hVo hV'o hVV hlev]
          exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨τ.v c, hcv, rfl⟩))
    · left
      obtain ⟨y, hy⟩ := o_psi_sub hC hcT
      rw [hy, sf_ot (hG.ot_v c hcT), sh_psi_le hlt, sh_z]
  · -- the `v` equation
    intro hn hlt
    have hcx : c < x := h2
    have he1 : entry (M.take x) 1 c ≠ 0 := by
      intro h0
      rw [(hC c hcT).2] at hlt; unfold vRhs at hlt; rw [if_pos h0] at hlt; exact T.not_lt_z _ hlt
    have he1M : entry M 1 c ≠ 0 := by rwa [entry_take M 1 hcx] at he1
    obtain ⟨m, hm⟩ : ∃ m, par (M.take x) 1 c = some m := par1_exists hXT.e00 hXT.r01 (by omega)
    have hmM : par M 1 c = some m := by rwa [par_take M 1 c hcx] at hm
    have hRc1 := hRc.2.2 he1
    obtain ⟨hmc, hmlt, _, _⟩ := par1_facts hm
    have hmT : m < (M.take x).length := by omega
    have hvmot := hG.ot_v m hmT
    obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
    have he2rT : entry (M.take x) 2 r = 0 := by rw [entry_take M 2 hrx]; exact he2r
    -- `P_1(x − 1) = r`
    have hr1x : par M 1 x = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
    have hP1e : par M 1 (x - 1) = some r := by
      obtain ⟨m', hm1, hm2, _⟩ := upg_spec hux
      rw [hr1x] at hm2; cases hm2; exact hm1
    have hAx : Anc0 M r x := anc0_of_par M 0 r x hq
    have hAe : Anc0 (M.take x) r (x - 1) := anc0_to_take (anc_between hAx (x - 1) (by omega) (by omega)) (by omega)
    -- the bump terms
    have hWot : isOT (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c j
    have hW : entry (M.take x) 2 c ≠ 0 → V ≤ τ.v m →
        sh V (succ V) (omega (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)))) =
          omega (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c))) ∨
        (ChgX M x false c ∧ omega (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c))) ∈
          cutsHG (succ V) (sh V (succ V) (omega (sumN (one :: (children (M.take x) c).map
            (bumpTerm (M.take x) τ c)))))) := by
      intro he2 hVm
      have he2M : entry M 2 c ≠ 0 := by rwa [entry_take M 2 hcx] at he2
      -- the kids of the bump children
      have hbk : ∀ j ∈ children (M.take x) c, col (M.take x) j = bump (M.take x) c → ∀ k ∈ children (M.take x) j,
          (sh V (succ V) (τ.o k) = τ.o k ∨ (ChgX M x true k ∧ τ.o k ∈ cutsHG (succ V) (sh V (succ V) (τ.o k)))) := by
        intro j hj hb k hk
        have hpj : par (M.take x) 0 j = some c := (mem_children_iff.mp hj).2
        have hpk : par (M.take x) 0 k = some j := (mem_children_iff.mp hk).2
        have hcj := par_lt _ 0 j c hpj
        have hjk := par_lt _ 0 k j hpk
        have hkT := (mem_children hk).2
        have hjT := (mem_children hj).2
        have hj1 : entry (M.take x) 1 j ≠ 0 := by
          have : entry (M.take x) 1 j = (col (M.take x) j).2.1 := rfl; rw [this, hb]; exact he1
        have hpj1 := t_bump_par1 hj hb hm
        have hvj : V < τ.v j :=
          lt_of_le_of_lt hVm (v_par1_lt hC hG hR (rkT false j) j m le_rfl hjT hj1 hpj1)
        have hT : TVis (M.take x) τ r x k := by
          refine ⟨by omega, by omega, fun p hp hpk' hne => ?_⟩
          have hpj' : Anc0 (M.take x) p j := anc0_par hpk' hne hpk
          by_cases hpe : p = j
          · rw [hpe]; exact hvj
          · have hpc : Anc0 (M.take x) p c := anc0_par hpj' hpe hpj
            by_cases hpe' : p = c
            · rw [hpe']; exact hlt
            · exact hvis p hp hpc hpe'
        exact (ih (rkT true k) (by have := hRc1.2.2 he2 j hj hb k hk; omega) k hT).1 le_rfl
      have hbot : ∀ j, isOT (bumpTerm (M.take x) τ c j) = true := fun j => isOT_bumpTerm hG c j
      have hl : ∀ t ∈ one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c), isOT t = true := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact hbot j
      by_cases hallfix : ∀ j ∈ children (M.take x) c,
          sh V (succ V) (bumpTerm (M.take x) τ c j) = bumpTerm (M.take x) τ c j
      · left
        rw [sh_omega hVo hV'o hVV hWot, sh_sumN hVo hV'o hVV hl, List.map_cons, sh_one, List.map_map]
        congr 3
        apply List.map_congr_left
        intro j hj; exact hallfix j hj
      push_neg at hallfix
      obtain ⟨j0, hj0, hj0nf⟩ := hallfix
      -- `j0` is a bump child with a changing kid `k0`
      have hb0 : col (M.take x) j0 = bump (M.take x) c := by
        by_contra hnb
        apply hj0nf; unfold bumpTerm; rw [if_neg hnb, sh_z]
      have hbt0 : bumpTerm (M.take x) τ c j0 = omega (sumN ((children (M.take x) j0).map τ.o)) := by
        unfold bumpTerm; rw [if_pos hb0]
      have hkot : ∀ k ∈ children (M.take x) j0, isOT (τ.o k) = true :=
        fun k hk => hG.ot_o k (mem_children hk).2
      have hlk : ∀ t ∈ (children (M.take x) j0).map τ.o, isOT t = true := by
        intro t ht; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hkot k hk
      have hj0M : j0 ∈ children M c := by
        have := (mem_children_take hj0).2; exact this
      have hj0x : j0 < x := (mem_children_take hj0).1
      have hb0M : col M j0 = bump M c := by
        rwa [col_take M hj0x, bump_take M hcx] at hb0
      have he2j0 : entry M 2 j0 ≠ 0 := by
        have : entry M 2 j0 = (col M j0).2.2 := rfl; rw [this, hb0M]; simp [bump]
      -- the changing kids are the last child of `j0`, and `j0` is the last child of `c`
      have hlastk : ∀ k ∈ children (M.take x) j0, ChgX M x true k → ∀ k' ∈ children (M.take x) j0, k < k' → False := by
        intro k hk hch k' hk' hkk'
        exact chg_only_last hx I.r0p I.z2 I.sd I.z1 I.uat I.uab he2j0 (mem_children_take hk).2 hk' hkk' hch (Anc0.refl k)
      have hlastj : ∀ k ∈ children (M.take x) j0, ChgX M x true k → ∀ j' ∈ children (M.take x) c, j0 < j' → False := by
        intro k hk hch j' hj' hjj'
        exact chg_only_last hx I.r0p I.z2 I.sd I.z1 I.uat I.uab he2M hj0M hj' hjj' hch
          (anc0_of_par M 0 j0 k (by
            have := (mem_children_iff.mp (mem_children_take hk).2).2; exact this))
      -- a non-fixed bump term comes from a changing kid
      have hnfkid : ∀ j ∈ children (M.take x) c, sh V (succ V) (bumpTerm (M.take x) τ c j) ≠ bumpTerm (M.take x) τ c j →
          col (M.take x) j = bump (M.take x) c ∧ ∃ k ∈ children (M.take x) j, ChgX M x true k := by
        intro j hj hnf
        have hb : col (M.take x) j = bump (M.take x) c := by
          by_contra hnb; apply hnf; unfold bumpTerm; rw [if_neg hnb, sh_z]
        refine ⟨hb, ?_⟩
        by_contra hno
        push_neg at hno
        apply hnf
        have hl' : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
          intro t ht; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2
        unfold bumpTerm; rw [if_pos hb, sh_omega hVo hV'o hVV (isOT_sumN _ hl'), sh_sumN hVo hV'o hVV hl', List.map_map]
        congr 2
        apply List.map_congr_left
        intro k hk
        rcases hbk j hj hb k hk with h | ⟨h, _⟩
        · exact h
        · exact absurd h (hno k hk)
      obtain ⟨_, k0, hk0, hch0⟩ := hnfkid j0 hj0 hj0nf
      have hk0M : k0 ∈ children M j0 := (mem_children_take hk0).2
      -- the kids of `j0`: all fixed but the last, which is `k0`
      rcases (children (M.take x) j0).eq_nil_or_concat with hnil | ⟨Lk, kl, hkl⟩
      · rw [hnil] at hk0; simp at hk0
      rw [List.concat_eq_append] at hkl
      have hsk : (children (M.take x) j0).Pairwise (· < ·) := children_sorted _ j0
      rw [hkl] at hsk
      have hk0l : k0 = kl := by
        have hk0' := hk0; rw [hkl] at hk0'
        rcases List.mem_append.mp hk0' with h | h
        · exfalso
          have := (List.pairwise_append.mp hsk).2.2 k0 h kl (by simp)
          exact hlastk k0 hk0 hch0 kl (by rw [hkl]; simp) this
        · simpa using h
      subst hk0l
      have hLkfix : ∀ k ∈ Lk, sh V (succ V) (τ.o k) = τ.o k := by
        intro k hk
        have hkc : k ∈ children (M.take x) j0 := by rw [hkl]; simp [hk]
        rcases hbk j0 hj0 hb0 k hkc with h | ⟨hch, _⟩
        · exact h
        · exfalso
          have := (List.pairwise_append.mp hsk).2.2 k hk k0 (by simp)
          exact hlastk k hkc hch k0 hk0 this
      have hcut0 : τ.o k0 ∈ cutsHG (succ V) (sh V (succ V) (τ.o k0)) := by
        rcases hbk j0 hj0 hb0 k0 hk0 with h | ⟨_, h⟩
        · exfalso
          apply hj0nf
          rw [hbt0, sh_omega hVo hV'o hVV (isOT_sumN _ hlk), sh_sumN hVo hV'o hVV hlk, List.map_map]
          congr 2
          rw [hkl, List.map_append, List.map_append]
          congr 1
          · apply List.map_congr_left; intro k hk; exact hLkfix k hk
          · simp [h]
        · exact h
      have hLko : ∀ u ∈ Lk.map τ.o, isOT u = true := by
        intro u hu; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu; exact hkot k (by rw [hkl]; simp [hk])
      have hk0o := hkot k0 hk0
      have hX0 : sumN ((children (M.take x) j0).map τ.o) = add (sumN (Lk.map τ.o)) (τ.o k0) := by
        rw [hkl, List.map_append, List.map_singleton, sumN_snoc_add hLko hk0o]
      have hB0 : sh V (succ V) (sumN (Lk.map τ.o)) = sumN (Lk.map τ.o) := by
        rw [sh_sumN hVo hV'o hVV hLko, List.map_map]
        congr 1; apply List.map_congr_left; intro k hk; exact hLkfix k hk
      have hX0cut : sumN ((children (M.take x) j0).map τ.o) ∈
          cutsHG (succ V) (sh V (succ V) (sumN ((children (M.take x) j0).map τ.o))) := by
        rw [hX0, sh_add hVo hV'o hVV (isOT_sumN _ hLko) hk0o, hB0]
        obtain ⟨u, y, hu⟩ := o_psi_form hC (mem_children hk0).2
        exact G.add_cut hVo hV'o hVV (isOT_sumN _ hLko) hB0 hk0o ⟨u, y, hu⟩ hcut0
      have hbt0cut : bumpTerm (M.take x) τ c j0 ∈ cutsHG (succ V) (sh V (succ V) (bumpTerm (M.take x) τ c j0)) := by
        rw [hbt0]
        rcases G.omega_cut hVo hV'o hVV (isOT_sumN _ hlk) hX0cut with h | h
        · exact absurd (by rw [hbt0]; exact h) hj0nf
        · exact h
      -- the children of `c`: all bump terms fixed but the last, which is `j0`
      rcases (children (M.take x) c).eq_nil_or_concat with hnil | ⟨Lc, jl, hcl⟩
      · rw [hnil] at hj0; simp at hj0
      rw [List.concat_eq_append] at hcl
      have hsc : (children (M.take x) c).Pairwise (· < ·) := children_sorted _ c
      rw [hcl] at hsc
      have hj0l : j0 = jl := by
        have hj0' := hj0; rw [hcl] at hj0'
        rcases List.mem_append.mp hj0' with h | h
        · exfalso
          have := (List.pairwise_append.mp hsc).2.2 j0 h jl (by simp)
          exact hlastj k0 hk0 hch0 jl (by rw [hcl]; simp) this
        · simpa using h
      subst hj0l
      have hLcfix : ∀ j ∈ Lc, sh V (succ V) (bumpTerm (M.take x) τ c j) = bumpTerm (M.take x) τ c j := by
        intro j hj
        have hjc : j ∈ children (M.take x) c := by rw [hcl]; simp [hj]
        by_contra hnf
        obtain ⟨hbj, k, hk, hch⟩ := hnfkid j hjc hnf
        have hjj0 := (List.pairwise_append.mp hsc).2.2 j hj j0 (by simp)
        exact chg_only_last hx I.r0p I.z2 I.sd I.z1 I.uat I.uab he2M (mem_children_take hjc).2 hj0 hjj0 hch
          (anc0_of_par M 0 j k (by have := (mem_children_iff.mp (mem_children_take hk).2).2; exact this))
      have hLco : ∀ u ∈ one :: Lc.map (bumpTerm (M.take x) τ c), isOT u = true := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · rfl
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu; exact hbot j
      have hW0 : sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)) =
          add (sumN (one :: Lc.map (bumpTerm (M.take x) τ c))) (bumpTerm (M.take x) τ c j0) := by
        rw [hcl, List.map_append, List.map_singleton, ← List.cons_append, sumN_snoc_add hLco (hbot j0)]
      have hBW : sh V (succ V) (sumN (one :: Lc.map (bumpTerm (M.take x) τ c))) =
          sumN (one :: Lc.map (bumpTerm (M.take x) τ c)) := by
        rw [sh_sumN hVo hV'o hVV hLco, List.map_cons, sh_one, List.map_map]
        congr 2; apply List.map_congr_left; intro j hj; exact hLcfix j hj
      have hWcut : sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)) ∈
          cutsHG (succ V) (sh V (succ V) (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)))) := by
        rw [hW0, sh_add hVo hV'o hVV (isOT_sumN _ hLco) (hbot j0), hBW]
        exact G.add_cut hVo hV'o hVV (isOT_sumN _ hLco) hBW (hbot j0) (by rw [hbt0]; exact omega_psi_form _) hbt0cut
      rcases G.omega_cut hVo hV'o hVV hWot hWcut with h | h
      · exact Or.inl h
      · exact Or.inr ⟨ChgX.vbump he1M he2M hj0M hb0M hk0M hch0, h⟩
    rcases lt_trichotomy m r with hmr | hmr | hrm
    · -- `P_1(c)` above `r`
      exfalso
      have hce : c ≠ x - 1 := by
        intro h; rw [h] at hmM; rw [hP1e] at hmM; cases hmM; omega
      exact t_aboveA hXT hJT hC hG hR hAe (by omega) he2rT c h1 (by omega)
        (fun p hp hA' hne => hvis p hp hA' hne) he1 m hm hmr hlt
    · -- `P_1(c) = r`
      have hrm' : r = m := hmr.symm
      subst hrm'
      by_cases he2 : entry (M.take x) 2 c = 0
      · have he2M : entry M 2 c = 0 := by rwa [entry_take M 2 hcx] at he2
        by_cases hce : c = x - 1
        · -- the leaf `x − 1`
          right
          have hvc : τ.v c = succ V := by
            rw [(hC c hcT).2]; unfold vRhs
            rw [if_neg he1, if_pos he2, hm, hce, upg_take_last M (by omega) (by omega)]
            show sf (add (τ.v r) one) = _
            rw [sf_ot (isOT_add hVo isOT_one), add_one_eq_succ hVo]
          refine ⟨by rw [hce]; exact ChgX.supg (by rw [hux]; simp), Or.inl hvc⟩
        · have hc1 : c + 1 < x := by omega
          obtain ⟨k, hu⟩ := Option.ne_none_iff_exists'.mp
            (t_upg_ne hX hq (by omega) (by
                obtain ⟨_, _, _, he2', _⟩ := (par2_iff M (show x < M.length by omega)).mp hr
                have h' : entry M 2 r < entry M 2 x := he2'
                have := hX.z2 x; omega)
              h1lt he2r h1 hcx he1M he2M hmM)
          have huT : upg (M.take x) c = some k := by rw [upg_take M hc1]; exact hu
          have hvck := v_upg_eq hC hcT he1 he2 huT (vOpt_ot hG hcT)
            (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
          rw [hmM] at hm'; cases hm'
          have hkx : k < x := by
            have := upg_le hu
            rcases hcase with h | ⟨_, h⟩ <;> omega
          have hpkT : par (M.take x) 0 k = some r := by rw [par_take M 0 k hkx]; exact hpk
          have hT : TVis (M.take x) τ r x k := by
            refine ⟨par_lt M 0 k r hpk, hkx, fun p hp hpk' hne => ?_⟩
            have := (anc0_par hpk' hne hpkT).le; omega
          rw [hvck] at hlt ⊢
          rcases (ih (rkT false k) (by have := hRc1.2.1 he2 k huT; omega) k hT).2 le_rfl hlt with h | ⟨hchk, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨ChgX.vupg he1M he2M hu hchk, h⟩
      · have hvc : τ.v c = add V (omega (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)))) := by
          rw [(hC c hcT).2]; unfold vRhs; rw [if_neg he1, if_neg he2, hm]
          exact sf_ot (isOT_add hVo (isOT_omega hWot))
        rcases hW he2 (le_refl _) with hWf | ⟨hchg, hWc⟩
        · left
          rw [hvc, shf_add hVo hV'o hVV hVo (isOT_omega hWot) (le_refl _), shf_self, hWf]
          exact t_add_succ hVo (omega_psi_form _) (bumpOmega_ne_one hC hG c)
        · right
          obtain ⟨a, b, hab⟩ := omega_psi_form (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)))
          have hsa : succ V ≤ a := by have := cutsHG_lev_cut hWc; rwa [hab] at this
          rw [hab] at hWc hvc
          rw [add_absorb hVo (lt_of_lt_of_le hVV hsa)] at hvc
          rw [hvc]
          exact ⟨hchg, Or.inr ⟨lt_of_lt_of_le hVV hsa, hWc⟩⟩
    · -- `P_1(c)` strictly between `r` and `c`
      have hTm : TVis (M.take x) τ r x m :=
        ⟨hrm, by omega, fun p hp hpm hne => hvis p hp (Anc0.trans hpm hmc) (by have := hpm.le; omega)⟩
      have hvm : V < τ.v m := hvis m hrm hmc (by omega)
      have hfm : shf V (succ V) (τ.v m) = τ.v m := by
        rcases (ih (rkT false m) (by have := hRc1.1 m hm; omega) m hTm).2 le_rfl hvm with h | ⟨hchm, _⟩
        · exact h
        · exfalso
          exact (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchm).1 rfl (by omega) |>.2.2 c hcx hmM
      have hσm : sh V (succ V) (τ.v m) = τ.v m := sh_of_shf_fix hVo hV'o hVV hvmot hfm
      by_cases he2 : entry (M.take x) 2 c = 0
      · have he2M : entry M 2 c = 0 := by rwa [entry_take M 2 hcx] at he2
        cases hu : upg (M.take x) c with
        | none =>
          left
          have hvc : τ.v c = add (τ.v m) one := by
            rw [(hC c hcT).2]; unfold vRhs; rw [if_neg he1, if_pos he2, hm, hu]
            exact sf_ot (isOT_add hvmot isOT_one)
          rw [hvc, shf_add hVo hV'o hVV hvmot isOT_one (le_of_lt hvm), hfm, sh_one]
        | some k =>
          have hvck := v_upg_eq hC hcT he1 he2 hu (vOpt_ot hG hcT)
            (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          obtain ⟨_, huM⟩ := upg_of_take hu
          obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts huM
          rw [hmM] at hm'; cases hm'
          have hkx : k < x := by
            have := upg_le huM
            rcases hcase with h | ⟨_, h⟩ <;> omega
          have hpkT : par (M.take x) 0 k = some m := by rw [par_take M 0 k hkx]; exact hpk
          have hT : TVis (M.take x) τ r x k := by
            refine ⟨by have := par_lt M 0 k m hpk; omega, hkx, fun p hp hpk' hne => ?_⟩
            have hpm : Anc0 (M.take x) p m := anc0_par hpk' hne hpkT
            by_cases hpe : p = m
            · rw [hpe]; exact hvm
            · exact hvis p hp (Anc0.trans hpm hmc) (by have := hpm.le; omega)
          rw [hvck] at hlt ⊢
          rcases (ih (rkT false k) (by have := hRc1.2.1 he2 k hu; omega) k hT).2 le_rfl hlt with h | ⟨hchk, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨ChgX.vupg he1M he2M huM hchk, h⟩
      · have hvc : τ.v c = add (τ.v m) (omega (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)))) := by
          rw [(hC c hcT).2]; unfold vRhs; rw [if_neg he1, if_neg he2, hm]
          exact sf_ot (isOT_add hvmot (isOT_omega hWot))
        rcases hW he2 (le_of_lt hvm) with hWf | ⟨hchg, hWc⟩
        · left
          rw [hvc, shf_add hVo hV'o hVV hvmot (isOT_omega hWot) (le_of_lt hvm), hfm,
            sh_omega hVo hV'o hVV hWot]
          rw [sh_omega hVo hV'o hVV hWot] at hWf
          rw [hWf]
        · right
          obtain ⟨a, b, hab⟩ := omega_psi_form (sumN (one :: (children (M.take x) c).map (bumpTerm (M.take x) τ c)))
          have hsa : succ V ≤ a := by have := cutsHG_lev_cut hWc; rwa [hab] at this
          rw [hab] at hWc hvc
          have hao : isOT (psi a b z) = true := by rw [← hab]; exact isOT_omega hWot
          refine ⟨hchg, Or.inr ⟨by rw [hvc]; exact lev_add_gt (lt_of_lt_of_le hVV hsa), ?_⟩⟩
          rw [hvc, sh_add hVo hV'o hVV hvmot hao, hσm]
          exact G.add_cut hVo hV'o hVV hvmot hσm hao ⟨a, b, rfl⟩ hWc

end

/-! ## T2SeedSVFix -/

namespace G

theorem hg_to_nsg {s : T} : ∀ {h t : T}, t ∈ cutsHG s h → AllGeT (psi (succ s) z z) t → t ∈ cutsNSG s h
  | z, _, ht, _ => by simp [cutsHG] at ht
  | psi a x c, t, ht, hall => by
    rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨_, u, hu, rfl⟩ | ⟨_, u, hu, rfl⟩
    · exfalso
      exact hall (psi s z z) (by simp [summands]) (psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s)))
    · exact mem_cutsNSG_psi.mpr (Or.inl ⟨u, hu, rfl⟩)
    · exact mem_cutsNSG_psi.mpr (Or.inr (Or.inl ⟨u, hu, rfl⟩))
    · exact mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨u, hg_to_nsg hu (fun q hq => hall q (by simp [summands, hq])), rfl⟩))

open Classical in
/-- **`T2SeedSVFix` holds** (sv, from `Inv3`・`Res3A` of `M`). -/
theorem t2SeedSVFix_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L)) : T2SeedSVFix M ρ r L := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 0 _ _ hq
  -- the drop and `M.take x`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hG1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  obtain ⟨hXT, hJT⟩ := sInvXJ_std (std_take hM (r + L) (by omega)) hTS
  have core : ∀ τ, Cons (M.take (r + L)) τ →
      (sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) = t2X1 M r L τ ∨
        t2X1 M r L τ ∈ cutsNSG (succ (ρ.v r)) (sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ))) ∧
      AllGeT (psi (succ (succ (ρ.v r))) z z) (t2X1 M r L τ) := by
    intro τ hτ
    have hG : Good3 (M.take (r + L)) τ := good3_congr hG1 (agree_of_cons hC1 hτ hRk1)
    have hvr : τ.v r = ρ.v r := v_take_of_untopped I hlen hrx (topP_sv hlen I.z2 I.z1 hr hq hux) hτ
    rw [← hvr]
    unfold t2X1
    have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
    have hrT : r < (M.take (r + L)).length := by omega
    set V := τ.v r with hVdef
    have hVo : isOT V = true := hG.ot_v r hrT
    have hV'o : isOT (succ V) = true := isOT_succ hVo
    have hVV : V < succ V := lt_succ_self V
    obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
    have he2x : entry M 2 (r + L) = 1 := by
      obtain ⟨_, _, _, he2', _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
      have h' : entry M 2 r < entry M 2 (r + L) := he2'
      have := hX.z2 (r + L); omega
    -- the children of `r`
    have hkid : ∀ d ∈ CL (M.take (r + L)) r, succ V < τ.v d ∧ (sh V (succ V) (τ.o d) = τ.o d ∨
        (ChgX M (r + L) true d ∧ τ.o d ∈ cutsHG (succ V) (sh V (succ V) (τ.o d)))) := by
      intro d hd
      have hdc := cl_mem_children hd
      have hdT := (mem_children hdc).2
      have hdx : d < r + L := by omega
      have hpdT : par (M.take (r + L)) 0 d = some r := (mem_children_iff.mp hdc).2
      have hpd : par M 0 d = some r := by rwa [par_take M 0 d hdx] at hpdT
      have hrd := par_lt M 0 d r hpd
      refine ⟨?_, ?_⟩
      · have hcol := t_child_col hX hq (by omega) he2x h1lt (mem_children_iff.mpr ⟨by omega, hpd⟩) (le_of_lt hdx)
        have hcx := t_col_x hX hq (by omega) he2x h1lt
        have he1 : entry (M.take (r + L)) 1 d = entry M 1 r + 1 := by
          rw [entry_take M 1 hdx]; have : entry M 1 d = (col M d).2.1 := rfl; rw [this, hcol, hcx]
        have he2 : entry (M.take (r + L)) 2 d = 1 := by
          rw [entry_take M 2 hdx]; have : entry M 2 d = (col M d).2.2 := rfl; rw [this, hcol, hcx]
        have hm : par (M.take (r + L)) 1 d = some r := by
          rw [par_take M 1 d hdx]; apply par1_of_child hpd
          rw [entry_take M 1 hdx] at he1; omega
        have hWot : isOT (sumN (one :: (children (M.take (r + L)) d).map (bumpTerm (M.take (r + L)) τ d))) = true := by
          apply isOT_sumN
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · rfl
          · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG d j
        have hvd : τ.v d = add V (omega (sumN (one :: (children (M.take (r + L)) d).map
            (bumpTerm (M.take (r + L)) τ d)))) := by
          rw [(hτ d hdT).2]; unfold vRhs; rw [if_neg (by omega), if_neg (by omega), hm]
          exact sf_ot (isOT_add hVo (isOT_omega hWot))
        obtain ⟨s', y', hsy⟩ := omega_psi_form (sumN (one :: (children (M.take (r + L)) d).map
          (bumpTerm (M.take (r + L)) τ d)))
        rw [hvd, ← t_add_succ hVo (omega_psi_form _) (bumpOmega_ne_one hτ hG d), hsy]
        exact lt_add_principal s' y' _
      · have hT : TVis (M.take (r + L)) τ r (r + L) d := ⟨hrd, hdx, fun p hp hpd' hne => by
          have := (anc0_par hpd' hne hpdT).le; omega⟩
        exact (sv_main hX hJ I hlen hr hq hux hXT hJT hτ hG hRk1 (rkT := rk) (rk true d) d hT).1 le_rfl
    obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
    have hlevS : ∀ q ∈ summands (sumN ((CL (M.take (r + L)) r).map τ.o)), succ V < lev q := by
      intro q hq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
      have hdT := (mem_children (cl_mem_children hd)).2
      obtain ⟨y, hy⟩ := o_psi_sub hτ hdT
      rw [hy, lev_psi, sf_ot (hG.ot_v d hdT)]; exact (hkid d hd).1
    have hSo := isOT_sumN _ (fun t ht => (hsing t ht).1)
    have hall : AllGeT (psi (succ (succ V)) z z) (spArg V z (sumN ((CL (M.take (r + L)) r).map τ.o))) := by
      intro q hq hlt
      have hge := spArg_summands_ge (a := V) (c := psi (succ (succ V)) z z) ⟨_, _, rfl⟩
        (sumN ((CL (M.take (r + L)) r).map τ.o)) z hSo (fun q hq => by
          obtain ⟨a, b, rfl⟩ := mem_summands_form hq
          have := hlevS _ hq; simp only [lev_psi] at this
          exact psi_le_psi_z (succ_le_of_lt this)) (by simp [summands]) q hq
      exact absurd hlt (not_lt.mpr hge)
    refine ⟨?_, hall⟩
    rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨L', d0, hLd⟩
    · left; rw [hnil]; show sh V (succ V) z = z; exact sh_z
    rw [List.concat_eq_append] at hLd
    have hd0m : d0 ∈ CL (M.take (r + L)) r := by rw [hLd]; simp
    have hfixL : ∀ d ∈ L', sh V (succ V) (τ.o d) = τ.o d := by
      intro d hd
      rcases (hkid d (by rw [hLd]; simp [hd])).2 with h | ⟨hch, _⟩
      · exact h
      · exfalso
        have hsorted : (CL (M.take (r + L)) r).Pairwise (· < ·) :=
          List.Pairwise.filter _ (children_sorted _ r)
        rw [hLd] at hsorted
        have hdd0 : d < d0 := (List.pairwise_append.mp hsorted).2.2 d hd d0 (by simp)
        have hdcT : d ∈ children (M.take (r + L)) r := cl_mem_children (by rw [hLd]; simp [hd])
        exact chg_last hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hdcT hch d0 (cl_mem_children hd0m) hdd0
          (of_decide_eq_true (List.mem_filter.mp hd0m).2)
    have hLo : ∀ u ∈ L'.map τ.o, isOT u = true := by
      intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
      exact hG.ot_o d (mem_children (cl_mem_children (by rw [hLd]; simp [hd]))).2
    have hd0T := (mem_children (cl_mem_children hd0m)).2
    have hd0o := hG.ot_o d0 hd0T
    have hS : sumN ((CL (M.take (r + L)) r).map τ.o) = app (sumN (L'.map τ.o)) (τ.o d0) := by
      rw [hLd, List.map_append, List.map_singleton]
      rw [hLd, List.map_append, List.map_singleton] at hsing hdec
      rw [sumN_append_dec hsing hdec, sumN_singleton (hsing _ (by simp))]
    have hPfix : sh V (succ V) (sumN (L'.map τ.o)) = sumN (L'.map τ.o) := by
      rw [sh_sumN hVo hV'o hVV hLo, List.map_map]
      congr 1
      apply List.map_congr_left
      intro d hd; exact hfixL d hd
    have hPo := isOT_sumN _ hLo
    have hlevP : ∀ q ∈ summands (sumN (L'.map τ.o)), succ V < lev q := by
      intro q hq; apply hlevS; rw [hS, summands_app]; exact List.mem_append_left _ hq
    have hB : spArg (succ V) z (sumN (L'.map τ.o)) = spArg V z (sumN (L'.map τ.o)) :=
      spArg_level (fun q hq => ⟨hlevP q hq, lt_trans hVV (hlevP q hq)⟩)
    have hBf : sh V (succ V) (spArg V z (sumN (L'.map τ.o))) = spArg V z (sumN (L'.map τ.o)) := by
      have := sh_spArg hVo hV'o hVV hVo (le_refl V) (b := z) rfl hPo
        (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlevP q hq))))
      rw [shf_self, sh_z, hPfix, hB] at this
      exact this.symm
    have hBo : isOT (spArg V z (sumN (L'.map τ.o))) = true := isOT_spArg _ _ _ rfl hPo
    obtain ⟨u, y, hu⟩ := o_psi_form hτ hd0T
    obtain ⟨u', y', hu'⟩ := sh_single (V := V) (V' := succ V) u y
    have hSo' : isOT (app (sumN (L'.map τ.o)) (psi u y z)) = true := by rw [← hu, ← hS]; exact hSo
    have hlevS' : ∀ q ∈ summands (app (sumN (L'.map τ.o)) (psi u y z)), succ V < lev q := by
      rw [← hu, ← hS]; exact hlevS
    have hσX : sh V (succ V) (spArg V z (app (sumN (L'.map τ.o)) (psi u y z))) =
        spArg (succ V) z (app (sumN (L'.map τ.o)) (psi u' y' z)) := by
      have := sh_spArg hVo hV'o hVV hVo (le_refl V) (b := z) rfl hSo'
        (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlevS' q hq))))
      rw [shf_self, sh_z, sh_app, hPfix, hu'] at this
      exact this.symm
    have hY : spArg V z (app (sumN (L'.map τ.o)) (psi u y z)) =
        step V (spArg V z (sumN (L'.map τ.o))) u y z := by
      rw [spArg_app, spArg_cons]; rfl
    have hY' : spArg (succ V) z (app (sumN (L'.map τ.o)) (psi u' y' z)) =
        step (succ V) (spArg V z (sumN (L'.map τ.o))) u' y' z := by
      rw [spArg_app, hB, spArg_cons]; rfl
    rw [hS, hu]
    rw [hS, hu] at hall
    rcases (hkid d0 hd0m).2 with hf0 | ⟨_, hcut0⟩
    · left
      rw [hσX]
      rw [hu, hu'] at hf0
      rw [hf0]
      exact spArg_level (fun q hq => ⟨hlevS' q hq, lt_trans hVV (hlevS' q hq)⟩)
    · right
      rw [hσX]
      apply hg_to_nsg _ hall
      rw [hY, hY']
      have hu0 : succ V < u := by
        have := (hkid d0 hd0m).1
        obtain ⟨yy, hyy⟩ := o_psi_sub hτ hd0T
        rw [hyy, sf_ot (hG.ot_v d0 hd0T)] at hu
        simp only [psi.injEq] at hu
        rw [← hu.1]; exact this
      have hVu : V < u := lt_trans hVV hu0
      have huo : isOT u = true := by rw [hu] at hd0o; exact isOT_sub hd0o
      have hu'u : u ≤ u' := by
        rw [sh_psi_gt hVu, sh_z] at hu'
        simp only [psi.injEq] at hu'
        rw [← hu'.1]; exact le_shf_self hVo hV'o (le_of_lt hVV) huo (le_of_lt hVu)
      exact G.step_cut hVo hV'o hVV (a := V) (a' := succ V) (u := u) (y := y) (u' := u') (y' := y') hBo hBf
        (by rw [← hu]; exact hd0o) hu' (by rw [hu, hu'] at hcut0; exact hcut0)
        ⟨fun _ => psi_lt_psi_z_iff.mpr (Or.inl (lt_of_lt_of_le hu0 hu'u)),
          fun _ => psi_lt_psi_z_iff.mpr (Or.inl hVu)⟩
  exact ⟨fun τ hτ => (core τ hτ).1, fun τ hτ => (core τ hτ).2⟩

end G

end Ytosk
