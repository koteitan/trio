/-
GxB.lean: 段ごとの族 `ZF`（持ち上げを族の等式で扱う W*）。

列ではなく族 `F : ℕ → TrioSeq`（`F v` は根 `(0,v,0)` の上の中身）について、段 `v ≥ w` ごとに
`Aopg` の分岐を取る最小不動点 `ZF`。z の孤児（行 2 の親が根）の分岐は、展開の等式

    ((0,v,0) :: F v)⟦n+2⟧ = (0,v,0) :: graft (F v) (((0,v+1,0) :: F (v+1))⟦n+1⟧)

（族の一様性はこの等式だけで表す）と、荷 `B ∈ Wg (2v+2)` の graft の族を前提にする。

主定理 `ZF_mem`: `(w, F) ∈ ZF → v ≥ w → (0,v,0) :: F v ∈ Wg (2v)`。
展開の帰納 `C(n) := ∀ v ≥ w, ((0,v,0) :: F v)⟦n+1⟧ ∈ Wg 2v` を n で回す。
z の孤児の段 v の `C(n+1)` は段 v+1 の `C(n)` を荷にし、塔の段 v の `C(n+1)` は段 v の `C(n)` を荷にする。
-/
import GxA

namespace TRIO
namespace GxB

open Wset
open Gw

abbrev Fam := ℕ → TrioSeq

/-! ## 族の集合の最小不動点 -/

def lfpF (f : Set (ℕ × Fam) → Set (ℕ × Fam)) : Set (ℕ × Fam) := ⋂₀ {Y | f Y ⊆ Y}

theorem lfpF_lowerbound {f : Set (ℕ × Fam) → Set (ℕ × Fam)} {Y : Set (ℕ × Fam)}
    (h : f Y ⊆ Y) : lfpF f ⊆ Y := fun _ hx => hx Y h

theorem lfpF_unfold_le {f : Set (ℕ × Fam) → Set (ℕ × Fam)} (hm : Monotone f) :
    f (lfpF f) ⊆ lfpF f := by
  intro x hx Y hY
  exact hY (hm (lfpF_lowerbound hY) hx)

/-! ## 分岐 -/

/-- 段 `v` での分岐。前提の族は段 `v` から先で使う。 -/
def ZBr (X : Set (ℕ × Fam)) (v : ℕ) (F : Fam) : Prop :=
  F v = [] ∨
  (F v ≠ [] ∧ hasParent (F v) (srow (F v) ((F v).length - 1)) ((F v).length - 1) ∧
    ∀ n, 1 ≤ n → (v, fun u => (F u)⟦n⟧) ∈ X) ∨
  (F v ≠ [] ∧ lev (F v) ((F v).length - 1) = 0 ∧ ¬ hasParent (F v) 0 ((F v).length - 1) ∧
    (v, fun u => (F u).dropLast) ∈ X) ∨
  (∃ m, m < 2 * v + 2 ∧ domT (F v) m ∧ entry (F v) 2 ((F v).length - 1) = 0 ∧
    ∀ y ∈ Wg m, based y → (v, fun u => graft (F u) y) ∈ X) ∨
  (F v ≠ [] ∧ 0 < entry (F v) 2 ((F v).length - 1) ∧
    hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) 2 (F v).length ∧
    (∀ n, (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)⟦n + 1 + 1⟧ =
      ((0, v, 0) : ℕ × ℕ × ℕ) :: graft (F v) ((((0, v + 1, 0) : ℕ × ℕ × ℕ) :: F (v + 1))⟦n + 1⟧)) ∧
    ∀ B ∈ Wg (2 * v + 2), based B → (v, fun u => graft (F u) B) ∈ X)

def ZOp (X : Set (ℕ × Fam)) : Set (ℕ × Fam) :=
  {p | ∀ v, p.1 ≤ v → argOK (p.2 v) ∧ ZBr X v p.2}

theorem ZOp_mono : Monotone ZOp := by
  intro X Y hXY p hp v hv
  obtain ⟨hA, hB⟩ := hp v hv
  refine ⟨hA, ?_⟩
  rcases hB with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨m, hm, hd, h2, hg⟩ |
      ⟨h1, h2, h3, h4, hg⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2, fun n hn => hXY (h3 n hn)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, hXY h4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, hd, h2, fun y hy hb => hXY (hg y hy hb)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, fun B hB hb => hXY (hg B hB hb)⟩)))

/-- 段ごとの族の良い集合。 -/
def ZF : Set (ℕ × Fam) := lfpF ZOp

theorem ZF_intro {p : ℕ × Fam} (h : p ∈ ZOp ZF) : p ∈ ZF := lfpF_unfold_le ZOp_mono h

/-! ## 主定理 -/

def ZY : Set (ℕ × Fam) :=
  {p | ∀ v, p.1 ≤ v → ∀ a, 2 * v ≤ a → (((0, v, 0) : ℕ × ℕ × ℕ) :: p.2 v) ∈ Wg a}

theorem Om_oper (v n : ℕ) : [((0, v, 0) : ℕ × ℕ × ℕ)]⟦n⟧ = [((0, v, 0) : ℕ × ℕ × ℕ)] :=
  oper_eq_self_of_short n (by simp)

theorem len_cons_gt {v : ℕ} {R : TrioSeq} (hRne : R ≠ []) :
    1 < (((0, v, 0) : ℕ × ℕ × ℕ) :: R).length := by
  have := List.length_pos_iff.mpr hRne
  simp only [List.length_cons]; omega

set_option maxHeartbeats 1000000 in
theorem ZOp_ZY : ZOp ZY ⊆ ZY := by
  intro p hp
  obtain ⟨w, F⟩ := p
  have hp' : ∀ v, w ≤ v → argOK (F v) ∧ ZBr ZY v F := hp
  -- 展開の帰納
  have C : ∀ n v, w ≤ v → ∀ a, 2 * v ≤ a →
      (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)⟦n + 1⟧ ∈ Wg a := by
    intro n
    induction n with
    | zero =>
        intro v hv a ha
        obtain ⟨hR, hB⟩ := hp' v hv
        by_cases hRnil : F v = []
        · rw [hRnil, Om_oper]
          exact Wg_mono ha (Om_mem_Wg v)
        · rw [oper_one_eq_dropLast (len_cons_gt hRnil), List.dropLast_cons_of_ne_nil hRnil]
          rcases hB with h | ⟨_, hp, h3⟩ | ⟨_, _, _, h4⟩ | ⟨m, _, _, _, hg⟩ | ⟨_, _, _, _, hg⟩
          · exact absurd h hRnil
          · have h1 : (((0, v, 0) : ℕ × ℕ × ℕ) :: (F v)⟦1⟧) ∈ Wg a := h3 1 le_rfl v le_rfl a ha
            by_cases hL2 : 1 < (F v).length
            · rw [oper_one_eq_dropLast hL2] at h1
              exact h1
            · exfalso
              obtain ⟨j0, hj0, -⟩ := hp
              have := nextR_index_lt hj0
              omega
          · exact h4 v le_rfl a ha
          · have h1 : (((0, v, 0) : ℕ × ℕ × ℕ) :: graft (F v) []) ∈ Wg a :=
              hg [] (Wg_nil m) (by simp [based, entry]) v le_rfl a ha
            simpa [graft_nil] using h1
          · have h1 : (((0, v, 0) : ℕ × ℕ × ℕ) :: graft (F v) []) ∈ Wg a :=
              hg [] (Wg_nil (2 * v + 2)) (by simp [based, entry]) v le_rfl a ha
            simpa [graft_nil] using h1
    | succ n ih =>
        intro v hv a ha
        obtain ⟨hR, hB⟩ := hp' v hv
        rcases hB with h | ⟨hRne, hp, h3⟩ | ⟨hRne, hw, hnp, h4⟩ | ⟨m, hm, hd, h2, hg⟩ |
            ⟨hRne, h2pos, hpar, hid, hg⟩
        · rw [h, Om_oper]
          exact Wg_mono ha (Om_mem_Wg v)
        · rw [oper_cons_nat hR hRne hp]
          exact h3 (n + 2) (by omega) v le_rfl a ha
        · rw [oper_cons_succ hR hRne hw hnp]
          have hQ : (((0, v, 0) : ℕ × ℕ × ℕ) :: (F v).dropLast) ∈ Wg a := h4 v le_rfl a ha
          exact Wg_flatMap_copies hQ (rsum_self_cons v 0 _) (n + 2)
        · have hRne : F v ≠ [] := by rintro h0; rw [h0] at hd; exact not_domT_nil m hd
          have hlevpos : 0 < lev (F v) ((F v).length - 1) := by rw [hd.1]; omega
          have hi1 : srow (F v) ((F v).length - 1) = 1 := by
            unfold srow
            unfold lev at hlevpos
            rw [if_neg (by omega), if_pos (by omega)]
          by_cases hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)
              (srow (F v) ((F v).length - 1)) (F v).length
          · rw [oper_cons_tower1 hR hRne hd hi1 hpM]
            have hvm : 2 * v + 0 ≤ m := tower1_le hRne (by omega) hd hi1 hpM
            have htow : tow v 0 (F v) (n + 1) ∈ Wg m := by
              rw [← oper_cons_tower1 hR hRne hd hi1 hpM]
              exact ih v hv m (by omega)
            have h1 : (((0, v, 0) : ℕ × ℕ × ℕ) :: graft (F v) (tow v 0 (F v) (n + 1))) ∈ Wg a :=
              hg _ htow (based_tow v 0 (F v) (n + 1)) v le_rfl a ha
            exact h1
          · have hdM : domT (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) m := domT_cons_of_dead hRne hd hpM
            rw [oper_eq_graft_nil_of_domT (len_cons_gt hRne) hdM, graft_nil,
              List.dropLast_cons_of_ne_nil hRne]
            have h1 : (((0, v, 0) : ℕ × ℕ × ℕ) :: graft (F v) []) ∈ Wg a :=
              hg [] (Wg_nil m) (by simp [based, entry]) v le_rfl a ha
            simpa [graft_nil] using h1
        · rw [hid n]
          have hB : (((0, v + 1, 0) : ℕ × ℕ × ℕ) :: F (v + 1))⟦n + 1⟧ ∈ Wg (2 * v + 2) :=
            ih (v + 1) (by omega) (2 * v + 2) (by omega)
          have hbB : based ((((0, v + 1, 0) : ℕ × ℕ × ℕ) :: F (v + 1))⟦n + 1⟧) := by
            unfold based
            rw [oper_head_eq (B := ((0, v + 1, 0) : ℕ × ℕ × ℕ) :: F (v + 1)) (n := n + 1)
              (by omega)]
            simp [entry]
          exact hg _ hB hbB v le_rfl a ha
  -- 所属
  show ∀ v, w ≤ v → ∀ a, 2 * v ≤ a → (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) ∈ Wg a
  intro v hv a ha
  obtain ⟨hR, hB⟩ := hp' v hv
  have hexp : ∀ n, 1 ≤ n → (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)⟦n⟧ ∈ Wg a := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact C k v hv a ha
  have hMlen : ((((0, v, 0) : ℕ × ℕ × ℕ) :: F v)).length - 1 = (F v).length := by simp
  rcases hB with h | ⟨hRne, hp, _⟩ | ⟨hRne, hw, _, _⟩ | ⟨m, hm, hd, h2, hg⟩ |
      ⟨hRne, h2pos, hpar, _, _⟩
  · rw [h]
    exact Wg_mono ha (Om_mem_Wg v)
  · have hi1M : srow (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)
        ((((0, v, 0) : ℕ × ℕ × ℕ) :: F v).length - 1) = srow (F v) ((F v).length - 1) := by
      rw [hMlen]; exact srow_cons_last hRne
    refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inr ?_), hexp⟩))
    rw [hi1M, hMlen]
    exact hasParent_cons_of hR hRne hp
  · have hlevM : lev (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)
        ((((0, v, 0) : ℕ × ℕ × ℕ) :: F v).length - 1) = lev (F v) ((F v).length - 1) := by
      unfold lev
      rw [hMlen, entry_cons_last hRne 1, entry_cons_last hRne 2]
    exact A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inl (by rw [hlevM]; exact hw)), hexp⟩))
  · have hRne : F v ≠ [] := by rintro h0; rw [h0] at hd; exact not_domT_nil m hd
    have hi1M : srow (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)
        ((((0, v, 0) : ℕ × ℕ × ℕ) :: F v).length - 1) = srow (F v) ((F v).length - 1) := by
      rw [hMlen]; exact srow_cons_last hRne
    have hlevpos : 0 < lev (F v) ((F v).length - 1) := by rw [hd.1]; omega
    have hi1 : srow (F v) ((F v).length - 1) = 1 := by
      unfold srow
      unfold lev at hlevpos
      rw [if_neg (by omega), if_pos (by omega)]
    by_cases hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) (srow (F v) ((F v).length - 1))
        (F v).length
    · refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inr ?_), hexp⟩))
      rw [hi1M, hMlen]; exact hpM
    · have hdM : domT (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) m := domT_cons_of_dead hRne hd hpM
      have hdead1 : ¬ hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) 1 (F v).length := by
        rw [← hi1]; exact hpM
      have hle : entry (F v) 1 ((F v).length - 1) ≤ v := entry1_le_of_dead_one hR hRne hdead1
      have hma : m < a := by
        have h1 := hd.1
        unfold lev at h1
        omega
      have h2M : entry (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) 2
          ((((0, v, 0) : ℕ × ℕ × ℕ) :: F v).length - 1) = 0 := by
        rw [hMlen, entry_cons_last hRne 2]; exact h2
      refine A1g_intro (Or.inr (Or.inr ⟨m, hma, hdM, h2M, fun y hy hby => ?_⟩))
      rw [graft_cons hRne]
      exact hg y hy hby v le_rfl a ha
  · have hi2M : srow (((0, v, 0) : ℕ × ℕ × ℕ) :: F v)
        ((((0, v, 0) : ℕ × ℕ × ℕ) :: F v).length - 1) = 2 := by
      rw [hMlen, srow_cons_last hRne]
      unfold srow
      rw [if_pos h2pos]
    refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inr ?_), hexp⟩))
    rw [hi2M, hMlen]; exact hpar

theorem ZF_sub_ZY : ZF ⊆ ZY := lfpF_lowerbound ZOp_ZY

/-- ★ 主定理: 良い族の段 `v` の根の列は `Wg (2v)` 以上に入る。 -/
theorem ZF_mem {w : ℕ} {F : Fam} (h : (w, F) ∈ ZF) {v : ℕ} (hv : w ≤ v) {a : ℕ}
    (ha : 2 * v ≤ a) : (((0, v, 0) : ℕ × ℕ × ℕ) :: F v) ∈ Wg a :=
  ZF_sub_ZY h v hv a ha

/-- `Wg 0 ⊆ W 0`（段 0 では graft の分岐が無く、ガードを外すだけ）。 -/
theorem Wg0_sub_W0 : Wg 0 ⊆ W 0 := by
  refine A2g' ?_
  intro M hM
  refine A1_intro ?_
  rcases hM with h | ⟨_, h⟩ | ⟨m, hm, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd hm (Nat.not_lt_zero m)

#print axioms ZF_mem
#print axioms Wg0_sub_W0

end GxB
end TRIO
