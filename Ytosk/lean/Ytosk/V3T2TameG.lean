/-
**種の状態は σ_{V, V′} で動かない（一般の V′、2026-10-17、t2）。**

closure の V3Tame（σ_{V, V+1}）を、V′ が「V + ω^W の形の値を吸収する」一般の V′ に広げた。t2 の
`T2SeedQNRes.σB`（q ≠ r、σ_{V, s′}、s′ = V + ω^{S}）に使う。

V3Tame との違い:
- V3Tame は見えるすべての列 c で f(v c) = v c を示す。V′ = V + 1 では、P_1(c) = r・行 2 = 1 の列の
  v(c) = V + ω^W がいつも V + 1 を吸収するから。一般の V′ では、r の下の bump 子（P_1 = r・行 2 = 1 で
  r の子でない列）は v が小さく、吸収しない（実測でも f(v c) ≠ v c）。
- そこで主張を bump 子でない列（`TNB`）に制限する。帰納法で読む列はどれも bump 子でない:
  数える子（Counted の定義）、bump 子の子（BumpLeaf で行 2 = 0）、上げの的（行 1 が P_1 より大きい）、
  P_1 の親（Z1C により行 2 = 1 の列は P_1 にならない）。
- P_1(c) = r・行 2 = 1・bump 子でない列は r の子（RowJ と P_1 の性質で、親が r でなければ c は親の bump 子）。
  r の x より前の子 d では V′ < v(d)（仮定 `hdir`）なので、吸収の仮定 `habs` で f(v d) = v d。
-/
import Ytosk.V3Tame

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- A column that is not a bump child. -/
def TNB (M : Mat) (c : Nat) : Prop := ∀ p, par M 0 c = some p → col M c ≠ bump M p

section
open Classical
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x : Nat} (hrx : par M 0 x = some r)
  (hxM : x < M.length) (he2x : entry M 2 x = 1) (he1x : entry M 1 r < entry M 1 x)
  (he2r : entry M 2 r = 0) {V' : T} (hV' : isOT V' = true) (hVV : ρ.v r < V')
  (habs : ∀ W, isOT W = true → V' < add (ρ.v r) (omega W) → add V' (omega W) = add (ρ.v r) (omega W))
  (hdir : ∀ d ∈ children M r, d < x → entry M 2 d ≠ 0 → V' < ρ.v d)
  (hux : ∀ i, upg M i = some x → ρ.v r < ρ.v x → shf (ρ.v r) V' (ρ.v x) = ρ.v x)
include hX hJ hC hG hR hrx hxM he2x he1x he2r hV' hVV habs hdir hux

/-- **The main induction** (general `V′`): for a visible column `c` that is not a bump child, `σ(o c) = o c`,
and `f(v c) = v c` when `V < v c`. -/
theorem tg_main : ∀ n c, TVis M ρ r x c → TNB M c →
    (rk true c ≤ n → sh (ρ.v r) V' (ρ.o c) = ρ.o c) ∧
    (rk false c ≤ n → ρ.v r < ρ.v c → shf (ρ.v r) V' (ρ.v c) = ρ.v c) := by
  have hrM : r < M.length := by have := t_rx hX hrx; omega
  have hV : isOT (ρ.v r) = true := hG.ot_v r hrM
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hVc hNB
  obtain ⟨h1, h2, hvis⟩ := hVc
  have hcM : c < M.length := by omega
  have hRc := hR c hcM
  constructor
  · -- the `o` equation
    intro hn
    by_cases hlt : ρ.v r < ρ.v c
    · have hf := (ih (rk false c) (by have := hRc.1; omega) c ⟨h1, h2, hvis⟩ hNB).2 le_rfl hlt
      have hvo := hG.ot_v c hcM
      have hl : ∀ t ∈ (children M c).map (cnt M ρ c), isOT t = true := by
        intro t ht
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp ht
        unfold cnt; split_ifs
        · rfl
        · rfl
        · exact hG.ot_o c' (mem_children hc').2
      have hS := isOT_sumN _ hl
      have hmap : (children M c).map (sh (ρ.v r) V' ∘ cnt M ρ c) =
          (children M c).map (cnt M ρ c) := by
        apply List.map_congr_left
        intro c' hc'
        simp only [Function.comp]
        rw [cnt_eq_ite]
        split_ifs with hcnt
        · have hpc' := t_par_of_child hc'
          have hcc' : c < c' := par_lt M 0 c' c hpc'
          have hA : Anc0 M c c' := anc0_of_par M 0 c c' hpc'
          have hT : TVis M ρ r x c' := by
            refine ⟨by omega, t_desc_lt hX hrx h1 h2 hA, fun p hp hpc hne => ?_⟩
            have hpc0 : Anc0 M p c := anc0_par hpc hne hpc'
            by_cases hpe : p = c
            · rw [hpe]; exact hlt
            · exact hvis p hp hpc0 hpe
          have hNB' : TNB M c' := by
            intro p hp; rw [hpc'] at hp; cases hp; exact hcnt.1
          exact (ih (rk true c') (by have := hRc.2.1 c' hc' hcnt.1 hcnt.2; omega) c' hT hNB').1 le_rfl
        · exact sh_z
      rw [(hC c hcM).1]; unfold oRhs
      rw [← sf_psi_sh_gt hV hV' hVV hvo hS hlt, hf, sh_sumN hV hV' hVV hl, List.map_map, hmap]
    · obtain ⟨y, hy⟩ := o_psi_sub hC hcM
      rw [hy, sf_ot (hG.ot_v c hcM), sh_psi_le hlt, sh_z]
  · -- the `v` equation
    intro hn hlt
    have he1 : entry M 1 c ≠ 0 := by
      intro h0
      rw [(hC c hcM).2] at hlt; unfold vRhs at hlt; rw [if_pos h0] at hlt; exact T.not_lt_z _ hlt
    obtain ⟨m, hm⟩ : ∃ m, par M 1 c = some m := by
      obtain ⟨Rt, hRt, he0, _⟩ := root_exists hX.e00 c
      have hRe1 : entry M 1 Rt = 0 := hX.r01 Rt he0
      have hRtc : Rt ≠ c := by
        intro h; subst h; have := t_e0_mid hX hrx h1 h2; omega
      obtain ⟨m, hm, _, _⟩ := par1_near hRt hRtc (by omega)
      exact ⟨m, hm⟩
    have hRc1 := hRc.2.2 he1
    obtain ⟨hmc, hmlt, he1m, hbet⟩ := par1_facts hm
    have hmM : m < M.length := by omega
    -- the bump terms are fixed when `V ≤ v(P_1 c)`
    have hW : entry M 2 c ≠ 0 → ρ.v r ≤ ρ.v m →
        sh (ρ.v r) V' (sumN (one :: (children M c).map (bumpTerm M ρ c))) =
          sumN (one :: (children M c).map (bumpTerm M ρ c)) := by
      intro he2 hVm
      have hl : ∀ t ∈ one :: (children M c).map (bumpTerm M ρ c), isOT t = true := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c j
      rw [sh_sumN hV hV' hVV hl, List.map_cons, sh_one, List.map_map]
      congr 2
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp]
      unfold bumpTerm
      split_ifs with hb
      · have hpj := t_par_of_child hj
        have hcj : c < j := par_lt M 0 j c hpj
        have hjM : j < M.length := (mem_children hj).2
        have hj1 : entry M 1 j ≠ 0 := by
          have : entry M 1 j = (col M j).2.1 := rfl; rw [this, hb]; exact he1
        have hpj1 := t_bump_par1 hj hb hm
        have hvj : ρ.v r < ρ.v j :=
          lt_of_le_of_lt hVm (v_par1_lt hC hG hR (rk false j) j m le_rfl hjM hj1 hpj1)
        have hlk : ∀ t ∈ (children M j).map ρ.o, isOT t = true := by
          intro t ht
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
          exact hG.ot_o k (mem_children hk).2
        have hmapk : (children M j).map (sh (ρ.v r) V' ∘ ρ.o) = (children M j).map ρ.o := by
          apply List.map_congr_left
          intro k hk
          simp only [Function.comp]
          have hpk := t_par_of_child hk
          have hjk : j < k := par_lt M 0 k j hpk
          have hAck : Anc0 M c k := Anc0.trans (anc0_of_par M 0 c j hpj) (anc0_of_par M 0 j k hpk)
          have hT : TVis M ρ r x k := by
            refine ⟨by omega, t_desc_lt hX hrx h1 h2 hAck, fun p hp hpk' hne => ?_⟩
            have hpj' : Anc0 M p j := anc0_par hpk' hne hpk
            by_cases hpe : p = j
            · rw [hpe]; exact hvj
            · have hpc : Anc0 M p c := anc0_par hpj' hpe hpj
              by_cases hpe' : p = c
              · rw [hpe']; exact hlt
              · exact hvis p hp hpc hpe'
          -- a child of a bump child is not a bump child (BumpLeaf)
          have hNBk : TNB M k := by
            intro p hp hkb
            rw [hpk] at hp; cases hp
            have he1kj : entry M 1 k = entry M 1 j := by
              have : entry M 1 k = (col M k).2.1 := rfl; rw [this, hkb]; rfl
            have he1jc : entry M 1 j = entry M 1 c := by
              have : entry M 1 j = (col M j).2.1 := rfl; rw [this, hb]; rfl
            have hBL := hX.loc.2.2.2 c j k hj hb hk (by omega)
            have : entry M 2 k = 1 := by
              have : entry M 2 k = (col M k).2.2 := rfl; rw [this, hkb]; rfl
            omega
          exact (ih (rk true k) (by have := hRc1.2.2 he2 j hj hb k hk; omega) k hT hNBk).1 le_rfl
        rw [sh_omega hV hV' hVV (isOT_sumN _ hlk), sh_sumN hV hV' hVV hlk, List.map_map, hmapk]
      · exact sh_z
    have hWot : isOT (sumN (one :: (children M c).map (bumpTerm M ρ c))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c j
    have hvmot := hG.ot_v m hmM
    -- an upgrade target is not a bump child (its row 1 is above that of `P_1`)
    have hNBup : ∀ k, upg M c = some k → TNB M k := by
      intro k hu p hp hkb
      obtain ⟨m', hm', hpk, he1k, _⟩ := upg_facts hu
      rw [hm] at hm'; cases hm'
      rw [hpk] at hp; cases hp
      have : entry M 1 k = entry M 1 m := by
        have : entry M 1 k = (col M k).2.1 := rfl; rw [this, hkb]; rfl
      omega
    rcases lt_trichotomy m r with hmr | hmr | hrm
    · exact absurd hlt (t_above hX hJ hC hG hR hrx hxM he2r c ⟨h1, h2, hvis⟩ he1 m hm hmr)
    · -- `P_1(c) = r`
      have hrm' : r = m := hmr.symm
      subst hrm'
      by_cases he2 : entry M 2 c = 0
      · obtain ⟨k, hu⟩ := Option.ne_none_iff_exists'.mp
          (t_upg_ne hX hrx hxM he2x he1x he2r h1 h2 he1 he2 hm)
        have hvck := v_upg_eq hC hcM he1 he2 hu (vOpt_ot hG hcM)
          (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
        obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
        rw [hm] at hm'; cases hm'
        rw [hvck] at hlt ⊢
        by_cases hkx : k = x
        · subst hkx; exact hux c hu hlt
        have hkx' : k < x := by
          rcases hcase with h | ⟨_, h⟩ <;> omega
        have hT : TVis M ρ r x k := by
          refine ⟨par_lt M 0 k r hpk, hkx', fun p hp hpk' hne => ?_⟩
          have := (anc0_par hpk' hne hpk).le; omega
        exact (ih (rk false k) (by have := hRc1.2.1 he2 k hu; omega) k hT (hNBup k hu)).2 le_rfl hlt
      · -- `c` is a child of `r`: otherwise it is a bump child of its parent
        obtain ⟨p, hp⟩ := par0_some_of (M := M) h1 (by have := t_e0_mid hX hrx h1 h2; omega)
        have hpr : p = r := by
          by_contra hpr
          have hpc : Anc0 M p c := anc0_of_par M 0 p c hp
          have hp_lt : p < c := par_lt M 0 c p hp
          have hAr := t_anc_r hX hrx (le_of_lt h1) (le_of_lt h2)
          have hAp : Anc0 M r p := anc0_par hAr (by omega) hp
          have hle1 : entry M 1 c ≤ entry M 1 p := hbet p hAp hpc hpr (by omega)
          have hle2 : entry M 1 p ≤ entry M 1 c := hJ c p he2 hp
          have he2c : entry M 2 c = 1 := by have := hX.z2 c; omega
          apply hNB p hp
          show (entry M 0 c, entry M 1 c, entry M 2 c) = (entry M 0 p + 1, entry M 1 p, 1)
          rw [hX.r0p c p hp, he2c]; congr 2; omega
        rw [hpr] at hp
        have hcr : c ∈ children M r := t_mem_children hX hp hp hcM
        have hvc : ρ.v c = add (ρ.v r) (omega (sumN (one :: (children M c).map (bumpTerm M ρ c)))) := by
          rw [(hC c hcM).2]; unfold vRhs; rw [if_neg he1, if_neg he2, hm]
          exact sf_ot (isOT_add hvmot (isOT_omega hWot))
        have hlt' : V' < add (ρ.v r) (omega (sumN (one :: (children M c).map (bumpTerm M ρ c)))) := by
          rw [← hvc]; exact hdir c hcr h2 he2
        rw [hvc, shf_add hV hV' hVV hV (isOT_omega hWot) (le_refl _), shf_self,
          sh_omega hV hV' hVV hWot, hW he2 (le_refl _)]
        exact habs _ hWot hlt'
    · -- `P_1(c)` strictly between `r` and `c`; `m` has row 2 zero (Z1C), so it is not a bump child
      have hTm : TVis M ρ r x m :=
        ⟨hrm, by omega, fun p hp hpm hne => hvis p hp (Anc0.trans hpm hmc) (by have := hpm.le; omega)⟩
      have hNBm : TNB M m := by
        intro p hp hmb
        have he2m : entry M 2 m = 1 := by
          have : entry M 2 m = (col M m).2.2 := rfl; rw [this, hmb]; rfl
        exact no_par1_of_e2 hX.loc.2.1 hcM he2m hm
      have hvm : ρ.v r < ρ.v m := hvis m hrm hmc (by omega)
      have hfm := (ih (rk false m) (by have := hRc1.1 m hm; omega) m hTm hNBm).2 le_rfl hvm
      by_cases he2 : entry M 2 c = 0
      · cases hu : upg M c with
        | none =>
          have hvc : ρ.v c = add (ρ.v m) one := by
            rw [(hC c hcM).2]; unfold vRhs; rw [if_neg he1, if_pos he2, hm, hu]
            exact sf_ot (isOT_add hvmot isOT_one)
          rw [hvc, shf_add hV hV' hVV hvmot isOT_one (le_of_lt hvm), hfm, sh_one]
        | some k =>
          have hvck := v_upg_eq hC hcM he1 he2 hu (vOpt_ot hG hcM)
            (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
          rw [hm] at hm'; cases hm'
          rw [hvck] at hlt ⊢
          have hkx : k ≠ x := by
            intro h; subst h; rw [hrx] at hpk; cases hpk; omega
          have hkx' : k < x := by
            rcases hcase with h | ⟨_, h⟩ <;> omega
          have hT : TVis M ρ r x k := by
            refine ⟨by have := par_lt M 0 k m hpk; omega, hkx', fun p hp hpk' hne => ?_⟩
            have hpm : Anc0 M p m := anc0_par hpk' hne hpk
            by_cases hpe : p = m
            · rw [hpe]; exact hvm
            · exact hvis p hp (Anc0.trans hpm hmc) (by have := hpm.le; omega)
          exact (ih (rk false k) (by have := hRc1.2.1 he2 k hu; omega) k hT (hNBup k hu)).2 le_rfl hlt
      · have hvc : ρ.v c = add (ρ.v m) (omega (sumN (one :: (children M c).map (bumpTerm M ρ c)))) := by
          rw [(hC c hcM).2]; unfold vRhs; rw [if_neg he1, if_neg he2, hm]
          exact sf_ot (isOT_add hvmot (isOT_omega hWot))
        rw [hvc, shf_add hV hV' hVV hvmot (isOT_omega hWot) (le_of_lt hvm), hfm,
          sh_omega hV hV' hVV hWot, hW he2 (le_of_lt hvm)]

/-- **Children of `r` before `x` are fixed by σ** (general `V′`). -/
theorem tg_child_fix {d : Nat} (hd : d ∈ children M r) (hdx : d < x) :
    sh (ρ.v r) V' (ρ.o d) = ρ.o d := by
  have hpd := t_par_of_child hd
  have hT : TVis M ρ r x d := ⟨par_lt M 0 d r hpd, hdx, fun p hp hpd' hne => by
    have := (anc0_par hpd' hne hpd).le; omega⟩
  have hNB : TNB M d := by
    intro p hp hb
    rw [hpd] at hp; cases hp
    have := hX.loc.2.2.1 r d hd hb
    omega
  exact (tg_main hX hJ hC hG hR hrx hxM he2x he1x he2r hV' hVV habs hdir hux (rk true d) d hT hNB).1 le_rfl

/-- **The seed state is fixed by σ** (general `V′`): `CL M r = Lc ++ [x]` and `B = spArg V 0 (Σ o(Lc))`
satisfies `σ_{V, V′}(B) = B`. -/
theorem tg_sigmaB {Lc : List Nat} (hCL : CL M r = Lc ++ [x]) :
    sh (ρ.v r) V' (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) = spArg (ρ.v r) z (sumN (Lc.map ρ.o)) := by
  have hrM : r < M.length := by have := t_rx hX hrx; omega
  have hV : isOT (ρ.v r) = true := hG.ot_v r hrM
  have hmemL : ∀ d ∈ Lc, d ∈ children M r ∧ d < x := by
    intro d hdL
    have hdCL : d ∈ CL M r := by rw [hCL]; exact List.mem_append_left _ hdL
    have hdc : d ∈ children M r := (List.mem_filter.mp hdCL).1
    have hsort : (CL M r).Pairwise (· < ·) := (children_sorted M r).filter _
    rw [hCL, List.pairwise_append] at hsort
    exact ⟨hdc, hsort.2.2 d hdL x (by simp)⟩
  have hl : ∀ t ∈ Lc.map ρ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o d (mem_children (hmemL d hd).1).2
  have hS := isOT_sumN _ hl
  have hfix : sh (ρ.v r) V' (sumN (Lc.map ρ.o)) = sumN (Lc.map ρ.o) := by
    rw [sh_sumN hV hV' hVV hl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro d hd
    exact tg_child_fix hX hJ hC hG hR hrx hxM he2x he1x he2r hV' hVV habs hdir hux (hmemL d hd).1 (hmemL d hd).2
  have hlev : ∀ q ∈ summands (sumN (Lc.map ρ.o)), V' < lev q := by
    intro q hq
    have hsing : ∀ t ∈ Lc.map ρ.o, Single t := by
      intro t ht
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
      exact single_o hC hG (mem_children (hmemL d hd).1).2
    obtain ⟨d, hdL, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
    obtain ⟨hdc, hdx⟩ := hmemL d hdL
    obtain ⟨y, hy⟩ := o_psi_sub hC (mem_children hdc).2
    rw [hy, lev_psi, sf_ot (hG.ot_v d (mem_children hdc).2)]
    have hcol := t_child_col hX hrx hxM he2x he1x hdc (le_of_lt hdx)
    have he2d : entry M 2 d = 1 := by
      have : entry M 2 d = (col M d).2.2 := rfl; rw [this, hcol, t_col_x hX hrx hxM he2x he1x]
    exact hdir d hdc hdx (by omega)
  have h1 := sh_spArg hV hV' hVV hV (le_refl _) (b := z) rfl hS
    (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlev q hq))))
  rw [shf_self, sh_z, hfix] at h1
  rw [← h1]
  exact spArg_level (fun q hq => ⟨hlev q hq, lt_trans hVV (hlev q hq)⟩)

end

/-- **Absorption**: `V + ω^S + ω^W = V + ω^W` when `V + ω^S < V + ω^W`. -/
theorem add_omega_absorb {V S W : T} (h : add V (omega S) < add V (omega W)) :
    add (add V (omega S)) (omega W) = add V (omega W) := by
  have hSW : omega S < omega W := by
    by_contra hn
    exact lt_irrefl' _ (lt_of_lt_of_le h (add_le_add_left V (le_of_not_gt hn)))
  rw [add_assoc']
  congr 1
  obtain ⟨d, e, hde⟩ := omega_psi_form W
  obtain ⟨d', e', hde'⟩ := omega_psi_form S
  rw [hde]
  apply add_eq_right_of_head_lt
  rw [hde'] at hSW ⊢
  rw [hde] at hSW
  simpa [head] using hSW

end Ytosk
