/-
Gamma.lean: γ 装置のステップ合成。

`Lift1 ((0,v,z)::graft M y) t` の展開を、graft 三分法（Xbar）と
リフト同変性（Lcone / `liftInner_holds`）で義務レベルに落とす:

  inner   : (Lift1 N t)⟦n⟧ = Lift1 ((0,v,z)::graft M (y⟦n⟧)) t
  blocked : (Lift1 N t)⟦n⟧ = Lift1 ((0,v,z)::graft (M.take (p+1)) Y') t
            （文脈が厳密に短くなる）

N = (0,v,z)::graft M y。どちらも既証明補題の合成。
-/
import Lcone
import Xbar

namespace TRIO

open Wset

/-- **The (a)-branch step**: an inner parent lets the lifted obligation recurse
into the argument's expansion. -/
theorem lift_graft_inner_step {M y : TrioSeq} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ []) (hyL : y.length - 1 ≠ 0)
    (hG : argOK (graft M y))
    (hp : hasParent y (srow y (y.length - 1)) (y.length - 1)) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M (y⟦n⟧)) t := by
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  have hpG := hasParent_graft_inner hM hy hp
  rw [liftInner_holds v z t n (graft M y) hG hGne hpG,
    oper_cons_nat hG hGne hpG, oper_graft_inner n hM hy hyL hp]

/-- **The γ-branch step**: a blocked parent lets the lifted obligation recurse
onto a strictly shorter context. -/
theorem lift_graft_blocked_step {M y : TrioSeq} {p : ℕ} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ [])
    (hG : argOK (graft M y))
    (hL : (graft M y).length - 1 ≠ 0)
    (hpG : hasParent (graft M y)
      (srow (graft M y) ((graft M y).length - 1)) ((graft M y).length - 1))
    (hpar : parent (graft M y) (srow (graft M y) ((graft M y).length - 1))
      ((graft M y).length - 1) = p)
    (hplt : p < M.length - 1) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ)
          :: graft (M.take (p + 1))
            (shiftl0 (entry M 0 p)
              (gcopies (graft M y) p ((graft M y).length - 1 - p)
                (if 0 < srow (graft M y) ((graft M y).length - 1)
                  then entry (graft M y) 0 ((graft M y).length - 1)
                    - entry (graft M y) 0 p else 0)
                (if 1 < srow (graft M y) ((graft M y).length - 1)
                  then entry (graft M y) 1 ((graft M y).length - 1)
                    - entry (graft M y) 1 p else 0) n))) t := by
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  rw [liftInner_holds v z t n (graft M y) hG hGne hpG,
    oper_cons_nat hG hGne hpG,
    oper_graft_blocked n hM hy hL hpG hpar hplt]


/-- **The peel step**: a dead trailing column (no parent even with the root)
peels, and the lift passes through. -/
theorem lift_graft_dead_step {M y : TrioSeq} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ [])
    (hlen2 : 1 < (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y).length)
    (hnp : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M y).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M y).length - 1)) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y.dropLast) t := by
  classical
  set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: graft M y with hN
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  have hLN : (Lift1 N t).length - 1 ≠ 0 := by
    rw [Lift1_length, hN]
    simp only [List.length_cons]
    have : 0 < (graft M y).length := List.length_pos_iff.mpr hGne
    omega
  have hnpL : ¬ hasParent (Lift1 N t)
      (srow (Lift1 N t) ((Lift1 N t).length - 1)) ((Lift1 N t).length - 1) := by
    rw [Lift1_length, srow_Lift1 (by
      rw [hN]
      simp only [List.length_cons]
      have : 0 < (graft M y).length := List.length_pos_iff.mpr hGne
      omega), hasParent_Lift1]
    exact hnp
  have hpred : (Lift1 N t)⟦n⟧ = Pred (Lift1 N t) := by
    by_cases hz : entry (Lift1 N t) 0 ((Lift1 N t).length - 1) = 0 ∧
        entry (Lift1 N t) 1 ((Lift1 N t).length - 1) = 0 ∧
        entry (Lift1 N t) 2 ((Lift1 N t).length - 1) = 0
    · exact oper_eq_pred_of_zero n hLN hz
    · exact oper_eq_pred_of_noParent n hLN hz hnpL
  rw [hpred]
  unfold Pred
  rw [if_neg (by rw [Lift1_length]; omega), Lift1_dropLast, hN,
    dropLast_cons hGne, graft_dropLast hy]


/-! ## GX 機械の補助 -/

theorem based_oper {B : TrioSeq} {n : ℕ} (hn : 1 ≤ n) (h : based B) :
    based (B⟦n⟧) := by
  unfold based at h ⊢
  rw [oper_head_eq hn, h]

theorem based_dropLast {B : TrioSeq} (h : based B) : based B.dropLast := by
  rcases B with _ | ⟨b0, B'⟩
  · simp
  · rcases B' with _ | ⟨b1, B''⟩
    · simp [based, entry]
    · unfold based at h ⊢
      simpa [entry] using h

/-- Rows 1 and 2 of the graft block's trailing column are the argument's. -/
theorem lev_graft_last {M y : TrioSeq} (hy : y ≠ []) :
    lev (graft M y) ((graft M y).length - 1) = lev y (y.length - 1) := by
  classical
  have hylen : 0 < y.length := List.length_pos_iff.mpr hy
  unfold lev
  rw [graft_eq_shift]
  have hlen : (M.dropLast ++ shiftr01 (entry M 0 (M.length - 1)) 0 y).length - 1
      = M.dropLast.length + (y.length - 1) := by
    rw [List.length_append, shiftr01_length]
    omega
  rw [hlen, entry_append_right, entry_append_right, entry1_shiftr01,
    entry2_shiftr01]


/-! ## GX 機械

`CtxOK M` = 全接頭辞パッケージ（MASTER の長さ帰納が供給）。
`GX` = 装備付き文脈すべてに対する graft-義務の集合。 -/

def CtxOK (M : TrioSeq) : Prop :=
  ∀ k, k ≤ M.length → ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.take k) t ∈ W a

theorem ctxOK_take {M : TrioSeq} (h : CtxOK M) (j : ℕ) : CtxOK (M.take j) := by
  intro k hk v z a t hz1 hva
  rw [List.take_take]
  have hk' : min k j ≤ M.length := by
    rw [List.length_take] at hk
    omega
  exact h (min k j) hk' v z a t hz1 hva

def GX : Set TrioSeq :=
  {y | based y → ∀ M : TrioSeq, argOK M → 2 ≤ M.length → CtxOK M →
    ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t ∈ W a}

/-- **Core γ' (blocked)**: the descended obligations. -/
def CoreBlocked : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length → CtxOK M →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    ∀ v z a t n : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a → 1 ≤ n →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ)
        :: graft (M.take (p + 1))
          (shiftl0 (entry M 0 p)
            (gcopies (graft M Y) p ((graft M Y).length - 1 - p)
              (if 0 < srow (graft M Y) ((graft M Y).length - 1)
                then entry (graft M Y) 0 ((graft M Y).length - 1)
                  - entry (graft M Y) 0 p else 0)
              (if 1 < srow (graft M Y) ((graft M Y).length - 1)
                then entry (graft M Y) 1 ((graft M Y).length - 1)
                  - entry (graft M Y) 1 p else 0) n))) t ∈ W a

/-- **Core α (row-1 tower under lift)**. -/
def CoreT1L : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length → CtxOK M →
    srow (graft M Y) ((graft M Y).length - 1) = 1 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a

/-- **Core β (row-2 tower over clause-2 data)**. -/
def CoreT2E : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    (∀ n, 1 ≤ n → Y⟦n⟧ ∈ GX) → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length → CtxOK M →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a


theorem based_graft_arg {Y w : TrioSeq} (hy : Y ≠ []) (hbY : based Y)
    (hbw : based w) : based (graft Y w) := by
  classical
  rcases Y with _ | ⟨c, Y'⟩
  · exact absurd rfl hy
  · rcases Y' with _ | ⟨c1, Y''⟩
    · have hc : c = ((0, c.2.1, c.2.2) : ℕ × ℕ × ℕ) := by
        unfold based entry at hbY
        simp at hbY
        exact Prod.ext hbY rfl
      rw [hc, graft_Om]
      exact hbw
    · unfold based
      rw [graft_head_eq (by simp) hbw
        (graft_ne_nil (by simp))]
      exact hbY

open Classical in
/-- **The GX machine closes** modulo the three cores. -/
theorem GX_closed (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GX Y → Y ∈ GX := by
  intro u Y AY
  intro hbased M hMarg hM2 hctx v z a t hz1 hva
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  by_cases hy : Y = []
  · subst hy
    rw [graft_nil, List.dropLast_eq_take]
    exact hctx (M.length - 1) (by omega) v z a t hz1 hva
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hG : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hGne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by rw [graft_length]; omega)
  have hGlen : 2 ≤ (graft M Y).length := by rw [graft_length]; omega
  have hGL : (graft M Y).length - 1 ≠ 0 := by omega
  by_cases hpY : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1)
  · -- (a) inner
    have hyL : Y.length - 1 ≠ 0 := by
      have := nextR_index_lt (parent_nextR hpY)
      omega
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_inner_step v z t n hMne hy hyL hG hpY]
    rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, hd, -⟩
    · omega
    · exact hop n hn (based_oper hn hbased) M hMarg hM2 hctx v z a t hz1 hva
    · exact absurd hpY hd.2
  by_cases hpG : hasParent (graft M Y)
      (srow (graft M Y) ((graft M Y).length - 1)) ((graft M Y).length - 1)
  · -- (γ) blocked
    have hplt := blocked_parent_lt hMne hy hpY hpG
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_blocked_step v z t n hMne hy hG hGL hpG rfl hplt]
    exact hb u Y M _ AY hbased hy hMarg hM2 hctx hpY hpG rfl hplt
      v z a t n hz1 hva hn
  -- trailing dead within the graft block
  have hdrop : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y.dropLast) t ∈ W a := by
    by_cases hY2 : 2 ≤ Y.length
    · have hYd : Y.dropLast ∈ GX := by
        rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, -, hgr⟩
        · omega
        · have hYL : Y.length - 1 ≠ 0 := by omega
          have hpred : Y⟦1⟧ = Y.dropLast := by
            have he : Y⟦1⟧ = Pred Y := by
              by_cases hz0 : entry Y 0 (Y.length - 1) = 0 ∧
                  entry Y 1 (Y.length - 1) = 0 ∧ entry Y 2 (Y.length - 1) = 0
              · exact oper_eq_pred_of_zero 1 hYL hz0
              · exact oper_eq_pred_of_noParent 1 hYL hz0 hpY
            rw [he]
            unfold Pred
            rw [if_neg (by omega)]
          have h := hop 1 le_rfl
          rwa [hpred] at h
        · have h := hgr [] (W_nil m) based_nil
          rwa [graft_nil] at h
      exact hYd (based_dropLast hbased) M hMarg hM2 hctx v z a t hz1 hva
    · have hYd : Y.dropLast = [] := by
        rw [List.dropLast_eq_take, show Y.length - 1 = 0 from by omega]
        rfl
      rw [hYd, graft_nil, List.dropLast_eq_take]
      exact hctx (M.length - 1) (by omega) v z a t hz1 hva
  by_cases hw0 : lev (graft M Y) ((graft M Y).length - 1) = 0
  · -- (b) succ: the lifted block sheds unshifted copies
    have hsr0 : srow (graft M Y) ((graft M Y).length - 1) = 0 := by
      unfold srow
      unfold lev at hw0
      rw [if_neg (by omega), if_neg (by omega)]
    set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y with hN
    set Rt : TrioSeq := Wset.ltail v z (graft M Y) t with hRt
    have hRtlen : Rt.length = (graft M Y).length := Wset.ltail_length
    have hRtne : Rt ≠ [] := Wset.ltail_ne hGne
    have hRtOK : argOK Rt := Wset.argOK_ltail hG
    have hwt : lev Rt (Rt.length - 1) = 0 := by
      rw [hRtlen, hRt]
      exact Wset.lev_ltail_of_zero hw0
    have hnpt : ¬ hasParent Rt 0 (Rt.length - 1) := by
      rw [hRtlen, hRt, Wset.hasParent_ltail]
      rw [← hsr0]
      exact hpG
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [Wset.lift_cons, ← hRt, oper_cons_succ hRtOK hRtne hwt hnpt]
    refine W_flatMap_copies ?_ (rsum_self_cons (v + t) z _) n
    have hkey : ((0, v + t, z) : ℕ × ℕ × ℕ) :: Rt.dropLast
        = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y.dropLast) t := by
      rw [hRt, Wset.ltail_dropLast, graft_dropLast hy]
    rw [hkey]
    exact hdrop
  · -- towers or dead
    by_cases hpN : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length
    · -- revived by the root
      have hdG : domT (graft M Y) (lev (graft M Y) ((graft M Y).length - 1) - 1) :=
        ⟨by omega, hpG⟩
      have hsplit : srow (graft M Y) ((graft M Y).length - 1) = 1 ∨
          srow (graft M Y) ((graft M Y).length - 1) = 2 := by
        unfold srow
        unfold lev at hw0
        by_cases h2' : 0 < entry (graft M Y) 2 ((graft M Y).length - 1)
        · rw [if_pos h2']; exact Or.inr rfl
        · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
      rcases hsplit with hs1 | hs2
      · exact h1 u Y M AY hbased hy hMarg hM2 hctx hs1 ⟨_, hdG⟩
          v z a t hz1 hva (by rw [hs1] at hpN ⊢; exact hpN)
      · rcases AY with ⟨hl, hw⟩ | hop | ⟨m, -, hd, hgr⟩
        · exfalso
          have hY1 : Y.length = 1 := by omega
          have := lev_graft_last (M := M) hy
          rw [hY1] at this
          simp at this
          rw [this, hw] at hw0
          exact hw0 rfl
        · exact h2 u Y M hop hbased hy hMarg hM2 hctx hs2 ⟨_, hdG⟩
            v z a t hz1 hva (by rw [hs2] at hpN ⊢; exact hpN)
        · -- (d) the proven row-2 graft tower
          have hlev : lev (graft M Y) ((graft M Y).length - 1) = m + 1 := by
            rw [lev_graft_last hy]
            exact hd.1
          have hdGm : domT (graft M Y) m := ⟨hlev, hpG⟩
          refine towerGraft2_lift_mem hG hGne hz1 hva hdGm hs2 ?_
            (by rw [hs2] at hpN ⊢; exact hpN)
          intro w hw hbw
          rw [graft_assoc hy]
          have hYw : graft Y w ∈ GX := hgr w hw hbw
          exact fun hargOK v' z' a' t' hz' ha' =>
            hYw (based_graft_arg hy hbased hbw) M hMarg hM2 hctx v' z' a' t' hz' ha'
    · -- (c) still dead: peel
      refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
      have hnp' : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
          (srow (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
            ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y).length - 1))
          ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y).length - 1) := by
        rw [cons_length, srow_cons_last hGne]
        exact hpN
      rw [lift_graft_dead_step v z t n hMne hy
        (by simp only [List.length_cons]; omega) hnp']
      exact hdrop


/-- **A2 corollary**: every `W`-element is in the machine's set. -/
theorem W_le_GX (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) (u : ℕ) :
    W u ⊆ GX :=
  A2' (fun Y hY => GX_closed hb h1 h2 u Y hY)

/-- **GraftAll for equipped contexts**, modulo the three cores: the missing
graft closure at every stage, for every context whose prefix packages are
supplied (by the master length induction). -/
theorem graftAll_of_GX (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ S : TrioSeq, argOK S → 2 ≤ S.length → CtxOK S →
      ∀ (u : ℕ) (y : TrioSeq), y ∈ W u → based y → graft S y ∈ Wstar2 := by
  intro S hS hS2 hctx u y hy hby
  have hyGX : y ∈ GX := W_le_GX hb h1 h2 u hy
  exact fun hargOK v z a t hz1 hva =>
    hyGX hby S hS hS2 hctx v z a t hz1 hva

end TRIO
