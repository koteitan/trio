/-
HUAC from danger-free chain facts, with the witness `j` = the last bump child of `k`
that HAS a child.

`WfStepFacts.StepFacts` asked the last bump child to have a child when `lev W ≠ 0`; that
is false (a standard 34-column matrix, `N` frame).  Here:
- `lev W ≠ 0` gives a bump child with a child (`exists_kid_of_lev`: otherwise every bump
  term is `0` or `1` and `W = ω^P` with a finite `P`);
- the term of the last bump child with a child keeps its components in `P`
  (`bp_dom_of_lastKid`: later bump children are leaves, their terms are `1`, and adding
  `1` never absorbs);
- the canonical structure (`canon_struct`), survival of `o(c)` and the deep return are
  the old lemmas, which never used that `j` is the last bump child.
What is left is `StepFacts2`: the chain facts (A), (B), (II) at this witness.
-/
import Ytosk.WfStepFacts

namespace Ytosk.WfStepFacts2
open T
open WfHUACDeep
open WfStepFacts

theorem not_lt_one (a b : T) : ¬ (psi a b z < psi z z z) := by
  intro h
  change lt (psi a b z) (psi z z z) = true at h
  cases a <;> cases b <;> simp [lt] at h

theorem add_one_eq_app : ∀ X : T, add X one = app X one
  | z => rfl
  | psi a b c => by
    show add (psi a b c) (psi z z z) = psi a b (app c one)
    rw [add_psi_psi, if_neg (not_lt_one a b)]
    exact congrArg (psi a b) (add_one_eq_app c)

theorem omega_z : omega z = one := by decide

/-- Trailing `0`/`1` inputs keep every component of a standard sum. -/
theorem mem_comps_trailing {u g : T} : ∀ (r : List T), (∀ q ∈ r, q = z ∨ q = one) →
    ∀ a, isOT a = true → g ∈ comps u a → g ∈ comps u (r.foldl (fun a b => sf (add a b)) a)
  | [], _, _, _, hg => hg
  | q :: r, hr, a, ha, hg => by
    rw [List.foldl_cons]
    have hr' : ∀ q ∈ r, q = z ∨ q = one := fun q hq => hr q (by simp [hq])
    rcases hr q (by simp) with rfl | rfl
    · rw [add_z_right, sf_ot ha]
      exact mem_comps_trailing r hr' a ha hg
    · have hOT : isOT (add a one) = true := isOT_add ha isOT_one
      rw [sf_ot hOT]
      apply mem_comps_trailing r hr' _ hOT
      rw [add_one_eq_app, comps_app]
      exact List.mem_append_left _ hg

theorem mem_sumN_trailing {l r : List T} {t u g : T}
    (hl : ∀ q ∈ l, isOT q = true) (ht : isOT t = true)
    (hr : ∀ q ∈ r, q = z ∨ q = one) (hg : g ∈ comps u t) :
    g ∈ comps u (sumN (l ++ t :: r)) := by
  have hs : ∀ q ∈ l ++ [t], isOT q = true := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hl q hq
    · simp only [List.mem_singleton] at hq
      subst q
      exact ht
  have he : sumN (l ++ t :: r) = r.foldl (fun a b => sf (add a b)) (sumN (l ++ [t])) := by
    simp [sumN, List.foldl_append]
  rw [he]
  exact mem_comps_trailing r hr _ (isOT_sumN _ hs) (SumComps.mem_sumN_snoc hl ht hg)

/-- A bump term is `0` or `1` unless the child is a bump child with a child. -/
theorem bumpTerm_small {M : Mat} {ρ : Valn} {k d : Nat}
    (h : col M d = bump M k → children M d = []) :
    bumpTerm M ρ k d = z ∨ bumpTerm M ρ k d = one := by
  unfold bumpTerm
  split
  · rename_i hb
    rw [h hb]
    right
    exact omega_z
  · left; rfl

/-- The last bump child with a child passes its components to `P`. -/
theorem bp_dom_of_lastKid {M : Mat} {ρ : Valn} (hG : Good3 M ρ) {k j : Nat} {L R : List Nat}
    (hL : children M k = L ++ j :: R) (hR : ∀ d ∈ R, col M d = bump M k → children M d = []) :
    ∀ u, Dom (comps u (bumpTerm M ρ k j))
      (comps u (sumN (one :: (children M k).map (bumpTerm M ρ k))) ++ [z]) := by
  intro u a ha
  refine ⟨a, List.mem_append_left _ ?_, le_refl _⟩
  rw [hL, List.map_append, List.map_cons]
  change a ∈ comps u (sumN ((one :: L.map (bumpTerm M ρ k)) ++
    bumpTerm M ρ k j :: R.map (bumpTerm M ρ k)))
  apply mem_sumN_trailing ?_ (isOT_bumpTerm hG k j) ?_ ha
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
      exact isOT_bumpTerm hG k d
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact bumpTerm_small (hR d hd)

/-- Sums of `0`s and `1`s are `0` or start with `1`. -/
theorem foldl_small : ∀ (l : List T), (∀ q ∈ l, q = z ∨ q = one) →
    ∀ a, isOT a = true → (a = z ∨ ∃ c, a = psi z z c) →
    isOT (l.foldl (fun a b => sf (add a b)) a) = true ∧
      (l.foldl (fun a b => sf (add a b)) a = z ∨
        ∃ c, l.foldl (fun a b => sf (add a b)) a = psi z z c)
  | [], _, _, ha, hf => ⟨ha, hf⟩
  | q :: r, hr, a, ha, hf => by
    rw [List.foldl_cons]
    have hr' : ∀ q ∈ r, q = z ∨ q = one := fun q hq => hr q (by simp [hq])
    rcases hr q (by simp) with rfl | rfl
    · rw [add_z_right, sf_ot ha]
      exact foldl_small r hr' a ha hf
    · have hOT : isOT (add a one) = true := isOT_add ha isOT_one
      rw [sf_ot hOT]
      apply foldl_small r hr' _ hOT
      right
      rw [add_one_eq_app]
      rcases hf with rfl | ⟨c, rfl⟩
      · exact ⟨z, rfl⟩
      · exact ⟨app c one, rfl⟩

/-- If every bump child of `k` is a leaf, `W = ω^P` has level `0`. -/
theorem lev_bumpW_of_leaves {M : Mat} {ρ : Valn} {k : Nat}
    (h : ∀ d ∈ children M k, col M d = bump M k → children M d = []) :
    lev (bumpW M ρ k) = z := by
  have hs : ∀ q ∈ one :: (children M k).map (bumpTerm M ρ k), q = z ∨ q = one := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · right; rfl
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      exact bumpTerm_small (h d hd)
  obtain ⟨_, hf⟩ := foldl_small _ hs z rfl (Or.inl rfl)
  have hlt : lt (sumN (one :: (children M k).map (bumpTerm M ρ k)))
      (psi z (psi one z z) z) = true := by
    unfold sumN
    rcases hf with h0 | ⟨c, hc⟩
    · rw [h0]; rfl
    · rw [hc]; simp [lt]
  unfold bumpW omega
  rw [if_pos hlt]
  rfl

/-- `lev W ≠ 0` gives a bump child with a child. -/
theorem exists_kid_of_lev {M : Mat} {ρ : Valn} {k : Nat} (h : lev (bumpW M ρ k) ≠ z) :
    ∃ d ∈ children M k, col M d = bump M k ∧ children M d ≠ [] := by
  by_contra hn
  apply h
  apply lev_bumpW_of_leaves
  intro d hd hb
  by_contra hc
  exact hn ⟨d, hd, hb, hc⟩

/-- The last element of a list satisfying a predicate. -/
theorem split_last {p : Nat → Prop} : ∀ l : List Nat, (∃ x ∈ l, p x) →
    ∃ L x R, l = L ++ x :: R ∧ p x ∧ ∀ d ∈ R, ¬ p d
  | [], ⟨_, hx, _⟩ => by simp at hx
  | y :: l, h => by
    by_cases hl : ∃ x ∈ l, p x
    · obtain ⟨L, x, R, he, hp, hR⟩ := split_last l hl
      exact ⟨y :: L, x, R, by simp [he], hp, hR⟩
    · obtain ⟨x, hx, hp⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨[], x, l, rfl, hp, fun d hd hpd => hl ⟨d, hd, hpd⟩⟩
      · exact absurd ⟨x, hx, hp⟩ hl

/-- The chain facts at a witness `a`. -/
def ChainFacts (N : Mat) (σ : Valn) (k m a : Nat) : Prop :=
  (∀ y t, Up1 N a y → Up1 N y m → y ≠ a → upg N y = some t → HasBump N t →
    bumpW N σ k ≤ last (σ.v t)) ∧
  (∀ y1 y2 t1 t2, Up1 N a y1 → Up1 N y1 y2 → Up1 N y2 m → y1 ≠ a → y2 ≠ y1 →
    upg N y1 = some t1 → HasBump N t1 → upg N y2 = some t2 → ¬ HasBump N t2 → False) ∧
  ((∃ y t, Up1 N a y ∧ Up1 N y m ∧ y ≠ a ∧ upg N y = some t) →
    ∃ g ∈ comps z (σ.v a), one ≤ g)

/-- **Residual (danger-free).**  At the last bump child `j` of `k` having a child, with
first child `c`, and `a` the row-1 ancestor of `m` at the level of `c`: (A), (B), (II). -/
def StepFacts2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      lev (bumpW N σ k) ≠ z →
      ∀ L j R c C, children N k = L ++ j :: R → col N j = bump N k →
        (∀ d ∈ R, col N d = bump N k → children N d = []) → children N j = c :: C →
        ∀ a, Up1 N a m → entry N 1 a = entry N 1 c → ChainFacts N σ k m a

/-- Danger and the chain facts give `StepDom`. -/
theorem stepDom_of_chainFacts {N : Mat} {σ : Valn} (S : SInv N) (hC : Cons N σ)
    (hG : Good3 N σ) {n k m a : Nat} (hn : n < N.length) (hu : upg N n = some k)
    (hkm : par N 0 k = some m) (ha : Up1 N a m)
    (hdg : HUACShapes.Danger (vOpt σ (par N 1 n)) (bumpW N σ k))
    (hF : ChainFacts N σ k m a) : StepDom N σ a m := by
  obtain ⟨hAst, hBst, hII⟩ := hF
  obtain ⟨m', hm', _, hcol, _⟩ := upg_spec hu
  obtain ⟨m'', hm'', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  rw [hm'] at hm''; cases hm''
  have hmN : m < N.length := by
    have := par_lt N 0 k m hkm
    have := upg_lt hn hu
    omega
  have hm2 : entry N 2 m = 0 := by have := e2_of_col hcol; have := S.z2 k; omega
  have hnoB : ∀ y, Up1 N a y → Up1 N y m → y ≠ a → ∀ t, upg N y = some t →
      ∀ d ∈ children N t, col N d ≠ bump N t := by
    intro y h1 h2 hne t ht d hd hdb
    obtain ⟨q, hq, hqW, g, hg, hgz⟩ := hdg
    rw [hm'] at hq
    simp only [vOpt] at hq
    exact hgz (noDanger_of_B S hC hG ha hmN hm2 hAst hBst ⟨y, t, h1, h2, hne, ht, d, hd, hdb⟩
      q hq hqW g hg)
  by_cases hU : ∃ y t, Up1 N a y ∧ Up1 N y m ∧ y ≠ a ∧ upg N y = some t
  · exact stepDom_of_noBump S hC hG hmN hnoB (hII hU)
  · intro y h1 h2 hne t ht
    exact absurd ⟨y, t, h1, h2, hne, ht⟩ hU

/-- The deep return with the last bump child having a child. -/
theorem dom_of_deep2 {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k m : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m) {L R : List Nat} {j c a : Nat}
    (hL : children M k = L ++ j :: R) (hjb : col M j = bump M k)
    (hR : ∀ d ∈ R, col M d = bump M k → children M d = [])
    (hc : c ∈ children M j) (hoG : ρ.o c ∈ summands (sumN ((children M j).map ρ.o)))
    (hcn : c < n) (hA : Up1 M a m) (h1 : entry M 1 c = entry M 1 a) (hc2 : entry M 2 c = 0)
    (hst : StepDom M ρ a m) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  have hj : j ∈ children M k := by rw [hL]; simp
  have hcN := (mem_children hc).2
  have hmN : m < M.length := by
    have := par_lt M 0 k m hkm
    have := upg_lt hn hu
    omega
  have hm2 : entry M 2 m = 0 := by
    obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
    rw [hkm] at hk0; cases hk0
    obtain ⟨m'', hm'', _, hcol, _⟩ := upg_spec hu
    rw [hm'] at hm''; cases hm''
    have := e2_of_col hcol; have := S.z2 k; omega
  have ha2 := up1_e2 S hA hm2
  have haN : a < M.length := by have := up1_le hA; omega
  obtain ⟨hp, hup⟩ := deep_return S hn hu hkn hkm hj hjb hc hcn hA h1 hc2 ha2
  have hv := value_eq_of_same_rhs hC hcN haN h1 hc2 ha2 hp hup
  have hs := dom_up1 S hC hG hA hmN hm2 (fun y h1 h2 hne t ht => hst y h1 h2 hne t ht)
  exact dom_of_grandchild_dom S hC hG hn hu hkm hj hjb (bp_dom_of_lastKid hG hL hR) hc hoG
    (by rw [hv]; exact hs)

/-- **Bridge**: `StepFacts2 → HUAC`. -/
theorem hUAC_of_facts2 (hF : StepFacts2) : HUAC := by
  intro N σ rk hN hNe hC hR hG n k hu hkn
  have S := sInv_std hN hNe
  have hn : n < N.length := by have := upg_succ_lt hu; omega
  obtain ⟨m, _, hkm⟩ := upg_target_par0 S.r0p hu
  by_cases hd : HUACShapes.Danger (vOpt σ (par N 1 n)) (bumpW N σ k)
  · by_cases hlev : lev (bumpW N σ k) = z
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
      have hF' := hF N σ rk hN hNe hC hR hG n k m hu hkn hkm hlev L j R c C hL hjb hRl hCc a ha
        hae
      have hst := stepDom_of_chainFacts S hC hG hn hu hkm ha hd hF'
      exact dom_of_deep2 S hC hG hn hu hkn hkm hL hjb hRl (by rw [hCc]; simp)
        (WfHUAC2Canon.first_kid_survives hN hNe hC hG hj hjb hCc) hcn ha hae.symm hc2 hst
  · exact HUACShapes.dom_of_no_danger S hC hG hn hu hd

end Ytosk.WfStepFacts2
