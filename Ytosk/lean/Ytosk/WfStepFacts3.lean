/-
HUAC from two danger-free chain facts, without the "no w-step below a B-step" fact.

`WfStepFacts2.StepFacts2` part (B) is FALSE (standard 34-column matrix in the B-step
family `bfam`, a danger frame; see `tmp/wf/WfStep/notes.md`), and so is (i) of the old
reduction (`stepDom_of_noBump`): a danger frame can have a B-step in `(a, m]`.

Here only absorbed summands are certified (`dom_add_of_absorbed`).  Along the row-1
chain from `a` to `m` every summand of `v(x)` is
  `≥ W` (a B-step increment, by (A), or a summand kept above it),
  a summand of `v(a)`, `1`, or `ω` from a w-step (`chain_summands`).
Absorbed summands of `v(a)` pass to `W` through the deep return
(`v(c) = v(a)`, `o(c)` in `G_j`, the bump term of `j` in `P`, `P` in `W`);
`ω` needs a level-0 component `≥ 1`, from (II).

Residual `StepFacts3` (no Danger): at the last bump child `j` of `k` having a child, its
first child `c`, and `a` the row-1 ancestor of `m` at the level of `c`, when `lev W ≠ 0`:
  (A)  every B-step increment in `(a, m]` is `≥ W`;
  (II) a w-step in `(a, m]` gives `v(a)` a level-0 component `≥ 1`.
-/
import Ytosk.WfStepFacts2

namespace Ytosk.WfStepFacts3
open T
open WfHUACDeep
open WfStepFacts
open WfStepFacts2

/-- The chain facts (A) and (II) at a witness `a`. -/
def ChainFacts3 (N : Mat) (σ : Valn) (k m a : Nat) : Prop :=
  (∀ y t, Up1 N a y → Up1 N y m → y ≠ a → upg N y = some t → HasBump N t →
    bumpW N σ k ≤ last (σ.v t)) ∧
  ((∃ y t, Up1 N a y ∧ Up1 N y m ∧ y ≠ a ∧ upg N y = some t ∧ ¬ HasBump N t) →
    ∃ g ∈ comps z (σ.v a), one ≤ g)

/-- **Residual (danger-free).** -/
def StepFacts3 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      lev (bumpW N σ k) ≠ z →
      ∀ L j R c C, children N k = L ++ j :: R → col N j = bump N k →
        (∀ d ∈ R, col N d = bump N k → children N d = []) → children N j = c :: C →
        ∀ a, Up1 N a m → entry N 1 a = entry N 1 c → ChainFacts3 N σ k m a

/-- `ω = ψ_0(1)`. -/
abbrev om1 : T := psi z one z

/-- **The summands along the chain.** -/
theorem chain_summands {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {W : T} {a x : Nat} (hA : Up1 M a x) (hxN : x < M.length) (hx2 : entry M 2 x = 0)
    (hAst : ∀ y t, Up1 M a y → Up1 M y x → y ≠ a → upg M y = some t → HasBump M t →
      W ≤ last (ρ.v t)) :
    ∀ q ∈ summands (ρ.v x), ¬ q < W ∨ q ∈ summands (ρ.v a) ∨ q = one ∨
      (q = om1 ∧ ∃ y t, Up1 M a y ∧ Up1 M y x ∧ y ≠ a ∧ upg M y = some t ∧ ¬ HasBump M t) := by
  induction hA with
  | refl => intro q hq; exact Or.inr (Or.inl hq)
  | @step x y hp hA ih =>
    have hyx := par_lt M 1 x y hp
    have hy2 : entry M 2 y = 0 := by
      have := par1_e2_ne_one S.z1c hp
      have := S.z2 y
      omega
    have hay := up1_le hA
    have hxa : x ≠ a := by omega
    have h1 : entry M 1 x ≠ 0 := by have := par1_entry_lt hp; omega
    have hpOT := vOpt_ot hG hxN
    rw [hp] at hpOT
    simp only [vOpt] at hpOT
    have ihy := ih (by omega) hy2
      (fun y' t h1 h2 hne hu hb => hAst y' t h1 (Up1.step hp h2) hne hu hb)
    -- lift the w-step witness from `y` to `x`
    have lift : ∀ q, (q = om1 ∧ ∃ y' t, Up1 M a y' ∧ Up1 M y' y ∧ y' ≠ a ∧ upg M y' = some t ∧
        ¬ HasBump M t) →
        (q = om1 ∧ ∃ y' t, Up1 M a y' ∧ Up1 M y' x ∧ y' ≠ a ∧ upg M y' = some t ∧
        ¬ HasBump M t) := by
      rintro q ⟨hq, y', t, h1, h2, hne, hu, hb⟩
      exact ⟨hq, y', t, h1, Up1.step hp h2, hne, hu, hb⟩
    have fromy : ∀ q ∈ summands (ρ.v y), ¬ q < W ∨ q ∈ summands (ρ.v a) ∨ q = one ∨
        (q = om1 ∧ ∃ y' t, Up1 M a y' ∧ Up1 M y' x ∧ y' ≠ a ∧ upg M y' = some t ∧
          ¬ HasBump M t) := by
      intro q hq
      rcases ihy q hq with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (lift q h)))
    rw [(hC x hxN).2]
    unfold vRhs
    rw [if_neg h1, if_pos hx2, hp]
    simp only [vOpt]
    cases hu : upg M x with
    | none =>
      rw [sf_ot (isOT_add hpOT isOT_one)]
      intro q hq
      rcases summands_add_gen _ _ q hq with hq | ⟨hq, _⟩
      · have : q = one := by simpa [one, summands] using hq
        exact Or.inr (Or.inr (Or.inl this))
      · exact fromy q hq
    | some t =>
      rw [sf_ot (isOT_add hpOT (isOT_last (hG.ot_v t (upg_lt hxN hu))))]
      intro q hq
      rcases summands_add_gen _ _ q hq with hq | ⟨hq, _⟩
      · by_cases hbt : HasBump M t
        · have hWL : W ≤ last (ρ.v t) := hAst x t (Up1.step hp hA) (Up1.refl x) hxa hu hbt
          left
          rw [summands_last hq]
          exact not_lt.mpr hWL
        · have hnb : ∀ d ∈ children M t, col M d ≠ bump M t := by
            intro d hd hdb; exact hbt ⟨d, hd, hdb⟩
          rw [last_v_noBump S hC hG hxN hu hnb] at hq
          have : q = om1 := by simpa [summands] using hq
          exact Or.inr (Or.inr (Or.inr ⟨this, x, t, Up1.step hp hA, Up1.refl x, hxa, hu, hbt⟩))
      · exact fromy q hq

/-- The deep return passes the components of `v(c)` to `W`. -/
theorem dom_vc_W {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {k j c : Nat}
    (hjb : col M j = bump M k)
    (hB_P : ∀ u, Dom (comps u (bumpTerm M ρ k j))
      (comps u (sumN (one :: (children M k).map (bumpTerm M ρ k))) ++ [z]))
    (hc : c ∈ children M j) (hoG : ρ.o c ∈ summands (sumN ((children M j).map ρ.o))) :
    ∀ u, Dom (comps u (ρ.v c)) (comps u (bumpW M ρ k) ++ [z]) := by
  have hcN := (mem_children hc).2
  obtain ⟨y, hy⟩ := o_psi_sub hC hcN
  rw [sf_ot (hG.ot_v c hcN)] at hy
  have hV_o : ∀ u, Dom (comps u (ρ.v c)) (comps u (ρ.o c) ++ [z]) := by
    rw [hy]
    exact HUACPath.index_comp_dom (hG.ot_v c hcN)
  have ho_G : ∀ u, Dom (comps u (ρ.o c))
      (comps u (sumN ((children M j).map ρ.o)) ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hoG g hg), le_refl _⟩
  have hGot : isOT (sumN ((children M j).map ρ.o)) = true :=
    isOT_sumN _ (by intro q hq; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq; exact hG.ot_o d (mem_children hd).2)
  have hG_B : ∀ u, Dom (comps u (sumN ((children M j).map ρ.o)))
      (comps u (bumpTerm M ρ k j) ++ [z]) := by
    unfold bumpTerm
    rw [if_pos hjb]
    exact OmegaComps.dom_comps_omega hGot
  have hP_W : ∀ u, Dom (comps u (sumN (one :: (children M k).map (bumpTerm M ρ k))))
      (comps u (bumpW M ρ k) ++ [z]) :=
    OmegaComps.dom_comps_omega (isOT_bumpP hG k)
  exact HUACPath.comp_dom_trans hV_o (HUACPath.comp_dom_trans ho_G
    (HUACPath.comp_dom_trans hG_B (HUACPath.comp_dom_trans hB_P hP_W)))

theorem comps_om1 {u g : T} (h : g ∈ comps u om1) : u = z ∧ (g = one ∨ g = z) := by
  by_cases hu : u = z
  · subst hu
    have : comps z om1 = [one, z] := by decide
    rw [this] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨rfl, h⟩
  · exfalso
    have hzu : lt z u = true := by
      cases u with
      | z => exact absurd rfl hu
      | psi => rfl
    simp [om1, comps, hzu] at h

/-- **HUAC at a frame** from the chain facts at the witness. -/
theorem dom_of_facts3 {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {n k m : Nat} (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m) {L R : List Nat} {j c a : Nat}
    (hL : children M k = L ++ j :: R) (hjb : col M j = bump M k)
    (hR : ∀ d ∈ R, col M d = bump M k → children M d = [])
    (hc : c ∈ children M j) (hoG : ρ.o c ∈ summands (sumN ((children M j).map ρ.o)))
    (hcn : c < n) (hA : Up1 M a m) (h1 : entry M 1 c = entry M 1 a) (hc2 : entry M 2 c = 0)
    (hF : ChainFacts3 M ρ k m a) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  obtain ⟨hAst, hII⟩ := hF
  have hj : j ∈ children M k := by rw [hL]; simp
  have hcN := (mem_children hc).2
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  have hmN : m < M.length := by
    have := par_lt M 0 k m hkm
    have := upg_lt hn hu
    omega
  have hm2 : entry M 2 m = 0 := by
    obtain ⟨m'', hm'', _, hcol, _⟩ := upg_spec hu
    rw [hm'] at hm''; cases hm''
    have := e2_of_col hcol; have := S.z2 k; omega
  have ha2 := up1_e2 S hA hm2
  have haN : a < M.length := by have := up1_le hA; omega
  obtain ⟨hp, hup⟩ := deep_return S hn hu hkn hkm hj hjb hc hcn hA h1 hc2 ha2
  have hv := value_eq_of_same_rhs hC hcN haN h1 hc2 ha2 hp hup
  have hvaW : ∀ u, Dom (comps u (ρ.v a)) (comps u (bumpW M ρ k) ++ [z]) := by
    rw [← hv]; exact dom_vc_W hC hG hjb (bp_dom_of_lastKid hG hL hR) hc hoG
  have hsum := chain_summands S hC hG hA hmN hm2 hAst
  rw [HUACSupport.value_at_target S hC hG hn hu, hm']
  simp only [vOpt]
  apply HUACSupport.dom_add_of_absorbed (hG.ot_v m hmN)
  intro q hq hqW u g hg
  rcases hsum q hq with h | h | h | ⟨rfl, hw⟩
  · exact absurd hqW h
  · exact hvaW u g (comps_summand_subH u h g hg)
  · subst h
    exact ⟨z, List.mem_append_right _ (by simp), by simp [comps_one_eq hg]⟩
  · obtain ⟨rfl, hg'⟩ := comps_om1 hg
    rcases hg' with rfl | rfl
    · obtain ⟨g0, hg0, hle⟩ := hII hw
      obtain ⟨e, he, hge⟩ := hvaW z g0 hg0
      exact ⟨e, he, le_trans hle hge⟩
    · exact ⟨z, List.mem_append_right _ (by simp), le_refl _⟩

/-- **Bridge**: `StepFacts3 → HUAC`. -/
theorem hUAC_of_facts3 (hF : StepFacts3) : HUAC := by
  intro N σ rk hN hNe hC hR hG n k hu hkn
  have S := sInv_std hN hNe
  have hn : n < N.length := by have := upg_succ_lt hu; omega
  obtain ⟨m, _, hkm⟩ := upg_target_par0 S.r0p hu
  by_cases hlev : lev (bumpW N σ k) = z
  · exact HUACZero.dom_of_zero S hC hG hn hu hlev
  · obtain ⟨L, j, R, hL, ⟨hjb, hjc⟩, hR'⟩ :=
      split_last (p := fun d => col N d = bump N k ∧ children N d ≠ []) (children N k)
        (exists_kid_of_lev hlev)
    have hRl : ∀ d ∈ R, col N d = bump N k → children N d = [] := by
      intro d hd hb
      by_contra hc
      exact hR' d hd ⟨hb, hc⟩
    obtain ⟨c, C, hCc⟩ : ∃ c C, children N j = c :: C := by
      cases h : children N j with
      | nil => exact absurd h hjc
      | cons c C => exact ⟨c, C, rfl⟩
    have hj : j ∈ children N k := by rw [hL]; simp
    obtain ⟨hcn, hc2, a, ha, hae⟩ := WfHUAC2Canon.canon_struct hN hNe hu hkn hkm hL hjb hCc
    have hF' := hF N σ rk hN hNe hC hR hG n k m hu hkn hkm hlev L j R c C hL hjb hRl hCc a ha hae
    exact dom_of_facts3 S hC hG hn hu hkn hkm hL hjb hRl (by rw [hCc]; simp)
      (WfHUAC2Canon.first_kid_survives hN hNe hC hG hj hjb hCc) hcn ha hae.symm hc2 hF'

end Ytosk.WfStepFacts3
