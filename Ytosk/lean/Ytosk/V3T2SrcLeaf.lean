/-
The actual source leaf in T2AbsNSrcW(a), without a conjectural value bound.
The nonchild disjunction reduces to a row-0 nonchild, the old upgrade target
is an ancestor, and the old/new o-values are explicit psi terms.
-/
import Ytosk.V3T2SrcWindow
import Ytosk.V3HUAC
import Ytosk.V3T2UpgAbs
import Ytosk.V3T0SeedSum

namespace Ytosk.T2SrcLeaf
open T

/-- With a last leaf as the next upgrade target, strong absorption holds for
all right operands W (not just for the canonical bump term). -/
theorem absorption_of_last_target {M : Mat} {ρ : Valn} {x : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hpos : 0 < x) (hu : upg M (x - 1) = some x) : UpgAbsX M x ρ := by
  intro i k W hi hk hv hW
  have he : i = x - 1 := by omega
  subst i
  rw [hu] at hk
  cases hk
  exact T2UpgAbs.absorption_at_leaf hC hG (by omega) hu (children_last hx) hv

/-- At a t2 last column, if it is the row-0 child of an upgrading column,
it is also its row-1 child. -/
theorem par1_of_last_child {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) {x k : Nat} (hx : x + 1 = M.length)
    (h2 : entry M 2 x = 1) (hu : upg M (x - 1) = some k)
    (h0 : par M 0 x = some (x - 1)) : par M 1 x = some (x - 1) := by
  obtain ⟨SX, SJ⟩ := sInvXJ_std C.std C.ne
  have hle := SJ x (x - 1) (by omega) h0
  have hlt : entry M 1 (x - 1) < entry M 1 x := by
    by_contra h
    have he : entry M 1 x = entry M 1 (x - 1) := by omega
    have hb : col M x = bump M (x - 1) := by
      change (entry M 0 x, entry M 1 x, entry M 2 x) = _
      simp only [bump, C.S.r0p x (x - 1) h0, he, h2]
    have hp2 := C.S.bumpE2 (x - 1) x (mem_children_iff.mpr ⟨by omega, h0⟩) hb
    have hn2 := (upg_e12 hu).2
    omega
  exact par1_of_child h0 hlt

/-- **Structural and exact value reduction of (a).** All hypotheses are the
real matrix context. No HUAC or new global residual is used. -/
theorem source_leaf_shapes {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : Bad2 M) {x : Nat} (hx : x + 1 = M.length)
    (h2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    {τ : Valn} (hτ : Cons (M.take x) τ) :
    par M 0 x ≠ some (x - 1) ∧
    ∃ k p g, upg M (x - 1) = some k ∧ k < x - 1 ∧
      par M 0 (x - 1) = some p ∧ par M 0 p = some g ∧ col M p = bump M g ∧
      children M (x - 1) = [] ∧
      ρ.o (x - 1) = psi (ρ.v (x - 1)) z z ∧
      τ.o (x - 1) = psi (add (vOpt ρ (par M 1 (x - 1))) one) z z := by
  have hxm : M.length - 1 = x := by omega
  have hxm2 : M.length - 2 = x - 1 := by omega
  unfold Bad2 at hB
  rw [hxm, hxm2] at hB
  obtain ⟨⟨k, hu⟩, p, g, hp, hg, hpb, hb⟩ := hB
  have hpos : 0 < x := by
    obtain ⟨m, hm, _⟩ := upg_spec hu
    have := par_lt M 1 (x - 1) m hm
    omega
  have hn : x - 1 < M.length := by omega
  have hn1 : x - 1 + 1 = x := by omega
  have hno : par M 0 x ≠ some (x - 1) := by
    intro hc
    rcases ha with ha | ha
    · exact ha hc
    · exact ha (par1_of_last_child C hx h2 hu hc)
  have hwit : ∃ σ, Cons M σ ∧ ¬ UpgAbsX M x σ := by
    rcases hb with ⟨_, σ, hc, hbad⟩ | ⟨hc, _⟩
    · exact ⟨σ, hc, hbad⟩
    · exact False.elim (hno hc)
  have hkn : k < x - 1 := by
    obtain ⟨_, _, _, _, he | ⟨_, he⟩⟩ := upg_spec hu
    · have huLast : upg M (x - 1) = some x := by simpa only [he, hn1] using hu
      obtain ⟨σ, hσ, hbad⟩ := hwit
      have hGσ := good3_congr C.I.good (agree_of_cons C.I.cons hσ C.I.rank)
      exact False.elim (hbad (absorption_of_last_target hσ hGσ hx hpos huLast))
    · exact he
  have hleaf : children M (x - 1) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    have hd0 := (mem_children hd).1
    have hdN := (mem_children hd).2
    have hdEq : d = x := by omega
    have hpd := (mem_children_iff.mp hd).2
    rw [hdEq] at hpd
    exact hno hpd
  have ho := o_nochild C.I.cons hn hleaf (C.I.good.ot_v _ hn)
  have hcnt := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
  rw [hxm] at hcnt
  have hRT : Rk (M.take x) rk := rk_take (by omega) C.I.rank hcnt
  have hCT := cons_of_rk hRT
  have hag := agree_of_cons hCT hτ hRT
  have hoT : τ.o (x - 1) = psi (add (vOpt ρ (par M 1 (x - 1))) one) z z := by
    rw [← (hag _ (by simp only [List.length_take]; omega)).1]
    exact (lost_upg_take C.std C.ne C.I hx hn1 hu).2
  exact ⟨hno, k, p, g, hu, hkn, hp, hg, hpb, hleaf, ho, hoT⟩

/-- The old leaf's subscript is precisely V+W_k, while the prefix uses
V+one. W_k is the canonical bump term, not an arbitrary new guard. -/
theorem leaf_increment {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hl : children M n = []) :
    ρ.o n = psi (add (vOpt ρ (par M 1 n)) (bumpW M ρ k)) z z ∧
      Single (bumpW M ρ k) := by
  obtain ⟨h1, h2⟩ := upg_e12 hu
  have h20 : entry M 2 n = 0 := by have := S.z2 n; omega
  have hv := v_upg_eq hC hn h1 h20 hu (vOpt_ot hG hn)
    (fun j _ _ d hd => hG.ot_o d (mem_children hd).2)
  obtain ⟨_, _, _, _, hk, hW⟩ := upg_target_val hC hG hn hu
  refine ⟨?_, hW⟩
  rw [o_nochild hC hn hl (hG.ot_v n hn), hv, hk]

/-- The measured one-term replacement inside a bump child is structural:
the changing child is last, all earlier o-values agree, and both sums have
the same prefix. This does not assume any absorption comparison. -/
theorem changed_bump_child_last {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x i j c : Nat}
    (hx : x + 1 = M.length) (hb : col M j = bump M i)
    (hnx : x ∉ children M j) (hc : c ∈ children M j)
    (hne : τ.o c ≠ ρ.o c) (hT : Cons (M.take x) τ)
    (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ) :
    ∃ L, children M j = L ++ [c] ∧ children (M.take x) j = L ++ [c] ∧
      (∀ d ∈ L, τ.o d = ρ.o d) ∧
      sumN ((children M j).map ρ.o) = add (sumN (L.map ρ.o)) (ρ.o c) ∧
      sumN ((children (M.take x) j).map τ.o) = add (sumN (L.map ρ.o)) (τ.o c) := by
  classical
  have hch : children (M.take x) j = children M j := by
    rw [children_take, children_filter_x hx hnx]
  have hcT : c ∈ children (M.take x) j := by rwa [hch]
  have hj2 : entry M 2 j ≠ 0 := by
    change (col M j).2.2 ≠ 0
    rw [hb]
    simp [bump]
  have hmax : ∀ d ∈ children M j, d ≤ c := by
    intro d hd
    by_contra h
    have hcd : c < d := by omega
    exact hne (T0SeedSum.earlier_o_stable S hC hG hx hj2 hc
      (by rwa [hch]) hcd hT hRT)
  have hs := split_last_max _ c (children_sorted M j) hc hmax
  let L := (children M j).filter (fun d => decide (d < c))
  have he : children M j = L ++ [c] := hs
  have hfix : ∀ d ∈ L, τ.o d = ρ.o d := by
    intro d hd
    obtain ⟨hdM, hdc⟩ := List.mem_filter.mp hd
    exact T0SeedSum.earlier_o_stable S hC hG hx hj2 hdM hcT
      (of_decide_eq_true hdc) hT hRT
  have hLo : ∀ t ∈ L.map ρ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o d (mem_children (List.mem_filter.mp hd).1).2
  have hcOT := hG.ot_o c (mem_children hc).2
  have hTcOT := hGT.ot_o c (mem_children hcT).2
  refine ⟨L, he, hch.trans he, hfix, ?_, ?_⟩
  · rw [he, List.map_append, List.map_singleton, sumN_snoc_add hLo hcOT]
  · rw [hch, he, List.map_append, List.map_singleton,
      List.map_congr_left hfix, sumN_snoc_add hLo hTcOT]

/-- The changing branch is also last among the source prefix's children.
Earlier bump terms agree. The last column may still be an extra child of i
in M; that separate contribution is not silently assumed unchanged. -/
theorem changed_branch_last {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x i j c : Nat}
    (hx : x + 1 = M.length) (hi2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i)
    (hc : c ∈ children M j) (hcx : c < x) (hne : τ.o c ≠ ρ.o c)
    (hnx : ∀ d ∈ children M i, col M d = bump M i → x ∉ children M d)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) :
    ∃ L, children (M.take x) i = L ++ [j] ∧
      ∀ d ∈ L, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d := by
  classical
  have hjx : j < x := Nat.lt_trans (mem_children hc).1 hcx
  have hix : i < x := Nat.lt_trans (mem_children hj).1 hjx
  have hjT : j ∈ children (M.take x) i := by
    rw [children_take, List.mem_filter]
    exact ⟨hj, by simpa using hjx⟩
  have hchg : ChgX M x true c := by
    by_contra h
    exact hne ((chg_off hx hC hG hT hRT c hcx).1 h)
  have hAc : Anc0 M j c := anc0_of_par M 0 j c (mem_children_iff.mp hc).2
  have hmax : ∀ d ∈ children (M.take x) i, d ≤ j := by
    intro d hd
    by_contra h
    exact chg_only_last hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hi2 hj hd
      (by omega) hchg hAc
  let L := (children (M.take x) i).filter (fun d => decide (d < j))
  have he : children (M.take x) i = L ++ [j] :=
    split_last_max _ j (children_sorted (M.take x) i) hjT hmax
  refine ⟨L, he, ?_⟩
  intro d hd
  obtain ⟨hdT, hdj⟩ := List.mem_filter.mp hd
  have hdj' : d < j := of_decide_eq_true hdj
  obtain ⟨hdx, hdM⟩ := mem_children_take hdT
  unfold bumpTerm
  rw [col_take M hdx, bump_take M hix]
  by_cases hbd : col M d = bump M i
  · rw [if_pos hbd, if_pos hbd]
    have hchd : children (M.take x) d = children M d := by
      rw [children_take, children_filter_x hx (hnx d hdM hbd)]
    rw [hchd]
    congr 2
    apply List.map_congr_left
    intro e heM
    have hex : e < x := by
      have := (mem_children heM).2
      have hen : e ≠ x := fun h => hnx d hdM hbd (h ▸ heM)
      omega
    apply (chg_off hx hC hG hT hRT e hex).1
    intro hche
    exact chg_only_last hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hi2 hdM hjT hdj' hche
      (anc0_of_par M 0 d e (mem_children_iff.mp heM).2)
  · rw [if_neg hbd, if_neg hbd]

/-- The exclusion used above is already supplied by the real t2 context;
it is not an extra matrix residual. -/
theorem last_not_child_of_bump {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) {r L i j : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hj : j ∈ children M i) (hb : col M j = bump M i) :
    r + L ∉ children M j := by
  intro hxj
  have hA := anc0_of_par M 2 r (r + L) hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (Nat.ne_of_lt (par_lt M 2 _ _ hr))
  have hnb := t2_xparNB C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq
  have he := (mem_children_iff.mp hxj).2
  rw [hq] at he
  cases he
  exact hnb i (mem_children_iff.mp hj).2 hb

/-- Normalized omega exponentiation never decreases its OT input. -/
theorem self_le_omega {X : T} (hX : isOT X = true) : X ≤ omega X := by
  by_cases hE : X < E0
  · rw [omega_small hE]
    exact le_of_lt (lt_psi0_self hX hE)
  · cases X with
    | z => exact z_le _
    | psi s b c => exact le_omega_big hX hE

/-- Every term in a list is below its normalized ordinal sum. -/
theorem mem_le_sumN {l : List T} (hl : ∀ t ∈ l, isOT t = true)
    {t : T} (ht : t ∈ l) : t ≤ sumN l := by
  have hex : ∃ a b, l = a ++ t :: b := by
    induction l with
    | nil => simp at ht
    | cons d ds ih =>
      rcases List.mem_cons.mp ht with he | he
      · subst d; exact ⟨[], ds, rfl⟩
      · obtain ⟨a, b, hab⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu)) he
        exact ⟨d :: a, b, by simp only [List.cons_append, hab]⟩
  obtain ⟨a, b, rfl⟩ := hex
  have ha : ∀ u ∈ a, isOT u = true := fun u hu => hl u (by simp [hu])
  have hb : ∀ u ∈ b, isOT u = true := fun u hu => hl u (by simp [hu])
  have hot : isOT t = true := hl t (by simp)
  have hat : ∀ u ∈ a ++ [t], isOT u = true := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact ha u hu
    · have he : u = t := by simpa using hu
      simpa only [he] using hot
  have hsum := le_sumN_appendO (a ++ [t]) b hat hb
  rw [sumN_snoc_add ha hot] at hsum
  rw [List.append_assoc] at hsum
  exact le_trans (le_add_left_self hot _) hsum

/-- The new child sum used in the measured comparison is genuinely below
the new bump term. No source absorption bound is assumed. -/
theorem child_sum_le_bumpW {M : Mat} {τ : Valn} (hG : Good3 M τ)
    {i j : Nat} (hj : j ∈ children M i) (hb : col M j = bump M i) :
    sumN ((children M j).map τ.o) ≤ bumpW M τ i := by
  have hGo : ∀ t ∈ (children M j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o c (mem_children hc).2
  have hGOT := isOT_sumN _ hGo
  have hterms : ∀ t ∈ one :: (children M i).map (bumpTerm M τ i), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm hG i d
  have hmem : bumpTerm M τ i j ∈ one :: (children M i).map (bumpTerm M τ i) :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
  have hle := mem_le_sumN hterms hmem
  have hbt : bumpTerm M τ i j = omega (sumN ((children M j).map τ.o)) := by
    simp only [bumpTerm, if_pos hb]
  rw [hbt] at hle
  exact le_trans (self_le_omega hGOT)
    (le_trans hle (self_le_omega (isOT_sumN _ hterms)))

/-- Exact outer sums after isolating the final changing branch. The old
sum retains the contribution of x when x is itself a child of i. -/
theorem bump_sums_of_last_branch {M : Mat} {ρ τ : Valn} {x i j : Nat}
    (hG : Good3 M ρ) (hGT : Good3 (M.take x) τ)
    (hx : x + 1 = M.length) {L : List Nat}
    (hch : children (M.take x) i = L ++ [j])
    (hfix : ∀ d ∈ L, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d) :
    let Q := sumN (one :: L.map (bumpTerm M ρ i))
    sumN (one :: (children (M.take x) i).map (bumpTerm (M.take x) τ i)) =
        add Q (bumpTerm (M.take x) τ i j) ∧
    sumN (one :: (children M i).map (bumpTerm M ρ i)) =
        if x ∈ children M i then add (add Q (bumpTerm M ρ i j)) (bumpTerm M ρ i x)
        else add Q (bumpTerm M ρ i j) := by
  classical
  dsimp only
  have hOT : ∀ t ∈ one :: L.map (bumpTerm M ρ i), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm hG i d
  have he : sumN (one :: (L ++ [j]).map (bumpTerm M ρ i)) =
      add (sumN (one :: L.map (bumpTerm M ρ i))) (bumpTerm M ρ i j) := by
    rw [List.map_append, List.map_singleton, ← List.cons_append,
      sumN_snoc_add hOT (isOT_bumpTerm hG i j)]
  constructor
  · rw [hch, List.map_append, List.map_singleton, ← List.cons_append,
      List.map_congr_left hfix, sumN_snoc_add hOT (isOT_bumpTerm hGT i j)]
  · by_cases hxi : x ∈ children M i
    · rw [if_pos hxi, children_split_x hx hxi,
        ← children_take M x i, hch]
      rw [List.map_append, List.map_singleton, ← List.cons_append,
        sumN_snoc_add (by
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact isOT_one
          · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
            exact isOT_bumpTerm hG i d) (isOT_bumpTerm hG i x), he]
    · rw [if_neg hxi]
      have heq : children M i = L ++ [j] := by
        rw [children_take, children_filter_x hx hxi] at hch
        exact hch
      rw [heq, he]

/-- The extra last-column contribution in the old outer sum is exactly
one when it is a bump child, and zero otherwise. -/
theorem bumpTerm_last {M : Mat} {ρ : Valn} {x i : Nat}
    (hx : x + 1 = M.length) :
    bumpTerm M ρ i x = if col M x = bump M i then one else z := by
  unfold bumpTerm
  rw [children_last hx]
  simp only [List.map_nil, sumN, List.foldl_nil]
  split <;> rfl

end Ytosk.T2SrcLeaf
