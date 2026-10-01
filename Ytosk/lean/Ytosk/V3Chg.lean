/-
**落とす補題: M.take x で値が変わりうる呼び出しの集合 `ChgX`。**

始点は 4 つ: x の o（`leaf`）、x − 1 の上げの消失（`supg`）、数える子かどうかが変わる子を持つ列の o（`scnt`）、
x がのりしろの子である列の v（`snb`）。依存の辺（DepX と同じ）で閉じる。
`chg_off`: この集合の外では、M.take x の値は M の値と同じ（`agree_off_at` による順位の帰納法）。
実測（L8 網羅、全型）: この集合は実際に値が変わる呼び出しの集合と一致する。
-/
import Ytosk.V3Agree
import Ytosk.V3Good

namespace Ytosk

open T

/-- The calls of `M.take x` whose value may differ from that in `M`. -/
inductive ChgX (M : Mat) (x : Nat) : Bool → Nat → Prop
  | leaf : ChgX M x true x
  | supg : upg M (x - 1) ≠ none → ChgX M x false (x - 1)
  | scnt {i c : Nat} : c ∈ children M i → c < x → ¬ (Counted (M.take x) i c ↔ Counted M i c) →
      ChgX M x true i
  | snb {i : Nat} : x ∈ children M i → col M x = bump M i → ChgX M x false i
  | ochild {i c : Nat} : c ∈ children M i → col M c ≠ bump M i →
      ¬ (isUpg M c = true ∧ topped M c = true) → ChgX M x true c → ChgX M x true i
  | ov {i : Nat} : ChgX M x false i → ChgX M x true i
  | vpar {i m : Nat} : entry M 1 i ≠ 0 → par M 1 i = some m → ChgX M x false m → ChgX M x false i
  | vupg {i k : Nat} : entry M 1 i ≠ 0 → entry M 2 i = 0 → upg M i = some k → ChgX M x false k →
      ChgX M x false i
  | vbump {i j k : Nat} : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → ChgX M x true k → ChgX M x false i

/-! ## 和の末尾の 0 -/

theorem foldl_sf_ot : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, isOT t = true) →
    isOT (l.foldl (fun a b => sf (add a b)) acc) = true
  | [], _, h, _ => h
  | t :: l, acc, h, hl => by
    have ht : isOT (add acc t) = true := isOT_add h (hl t (by simp))
    exact foldl_sf_ot l _ (by show isOT (sf (add acc t)) = true; rw [sf_ot ht]; exact ht)
      (fun t' h' => hl t' (by simp [h']))

theorem isOT_sumN (l : List T) (h : ∀ t ∈ l, isOT t = true) : isOT (sumN l) = true :=
  foldl_sf_ot l z rfl h

theorem sumN_snoc_z {l : List T} (h : ∀ t ∈ l, isOT t = true) : sumN (l ++ [z]) = sumN l := by
  rw [sumN_snoc, add_z_right, sf_ot (isOT_sumN l h)]

/-! ## 一致の定理（M の割り当てでの右辺の一致だけを仮定する版） -/

/-- **Agreement outside a set of calls**, with the right sides compared at `ρ` only. -/
theorem agree_off_at {M M' : Mat} {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (E : Bool → Nat → Prop)
    (hC : Cons M ρ) (hC' : Cons M' ρ') (hR' : Rk M' rk') (hlen : M'.length ≤ M.length)
    (ho : ∀ i, i < M'.length → ¬ E true i → oRhs M' ρ i = oRhs M ρ i)
    (hv : ∀ i, i < M'.length → ¬ E false i → vRhs M' ρ i = vRhs M ρ i)
    (hdo : ∀ i, i < M'.length → ¬ E true i →
      ¬ E false i ∧ ∀ c ∈ children M' i, Counted M' i c → ¬ E true c)
    (hdv : ∀ i, i < M'.length → ¬ E false i → entry M' 1 i ≠ 0 →
      (∀ m, par M' 1 i = some m → ¬ E false m) ∧
      (entry M' 2 i = 0 → ∀ k, upg M' i = some k → ¬ E false k) ∧
      (entry M' 2 i ≠ 0 → ∀ j ∈ children M' i, col M' j = bump M' i → ∀ k ∈ children M' j,
        ¬ E true k)) :
    ∀ i, i < M'.length → (¬ E true i → ρ'.o i = ρ.o i) ∧ (¬ E false i → ρ'.v i = ρ.v i) := by
  have key : ∀ N, ∀ i, i < M'.length → (rk' true i ≤ N → ¬ E true i → ρ'.o i = ρ.o i) ∧
      (rk' false i ≤ N → ¬ E false i → ρ'.v i = ρ.v i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hvv : ∀ i, i < M'.length → rk' false i ≤ N → ¬ E false i → ρ'.v i = ρ.v i := by
        intro i hi hN hE
        obtain ⟨_, _, hR⟩ := hR' i hi
        rw [(hC' i hi).2, (hC i (by omega)).2, ← hv i hi hE]
        apply vRhs_congr
        · intro m h1 hm
          have hlt := (hR h1).1 m hm
          exact (ih _ (by omega) m (by have := par_lt M' 1 i m hm; omega)).2 (Nat.le_refl _)
            ((hdv i hi hE h1).1 m hm)
        · intro k h1 h2 hk
          have hlt := (hR h1).2.1 h2 k hk
          exact (ih _ (by omega) k (upg_lt hi hk)).2 (Nat.le_refl _) ((hdv i hi hE h1).2.1 h2 k hk)
        · intro j hj h1 h2 hb k hk
          have hlt := (hR h1).2.2 h2 j hj hb k hk
          exact (ih _ (by omega) k (mem_children hk).2).1 (Nat.le_refl _)
            ((hdv i hi hE h1).2.2 h2 j hj hb k hk)
      refine fun i hi => ⟨fun hN hE => ?_, hvv i hi⟩
      obtain ⟨hvo, hc, _⟩ := hR' i hi
      obtain ⟨hEv, hEc⟩ := hdo i hi hE
      rw [(hC' i hi).1, (hC i (by omega)).1, ← ho i hi hE]
      apply oRhs_congr
      · exact hvv i hi (by omega) hEv
      · intro c hcm hbc huc
        have hlt := hc c hcm hbc huc
        exact (ih _ (by omega) c (mem_children hcm).2).1 (Nat.le_refl _) (hEc c hcm ⟨hbc, huc⟩)
  intro i hi
  exact ⟨fun hE => (key _ i hi).1 (Nat.le_refl _) hE, fun hE => (key _ i hi).2 (Nat.le_refl _) hE⟩

/-! ## C の外で値は同じ -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
include hx

theorem children_split_x {i : Nat} (h : x ∈ children M i) :
    children M i = (children M i).filter (fun d => decide (d < x)) ++ [x] :=
  split_last_max _ _ (children_sorted M i) h (fun d hd => by have := (mem_children hd).2; omega)

theorem children_filter_x {i : Nat} (h : x ∉ children M i) :
    (children M i).filter (fun d => decide (d < x)) = children M i := by
  rw [List.filter_eq_self]
  intro d hd
  have := (mem_children hd).2
  have hdx : d ≠ x := fun e => h (e ▸ hd)
  simp only [decide_eq_true_eq]; omega

omit hx in
theorem cnt_take_eq {ρ : Valn} {i c : Nat}
    (hiff : Counted (M.take x) i c ↔ Counted M i c) : cnt (M.take x) ρ i c = cnt M ρ i c := by
  classical
  rw [cnt_eq_ite, cnt_eq_ite]
  by_cases h : Counted M i c
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem oRhs_take_off {ρ : Valn} (hot : ∀ c, c < M.length → isOT (ρ.o c) = true) {i : Nat}
    (hE : ¬ ChgX M x true i) : oRhs (M.take x) ρ i = oRhs M ρ i := by
  classical
  unfold oRhs
  have hcnt : ∀ c ∈ (children M i).filter (fun d => decide (d < x)),
      cnt (M.take x) ρ i c = cnt M ρ i c := by
    intro c hc
    rw [List.mem_filter] at hc
    have hcx : c < x := by simpa using hc.2
    apply cnt_take_eq
    by_contra hne
    exact hE (ChgX.scnt hc.1 hcx hne)
  rw [children_take, List.map_congr_left hcnt]
  by_cases hxi : x ∈ children M i
  · -- `x` is not counted, so it adds a zero at the end
    have hxn : ¬ Counted M i x := fun h => hE (ChgX.ochild hxi h.1 h.2 ChgX.leaf)
    have hz : cnt M ρ i x = z := by rw [cnt_eq_ite, if_neg hxn]
    conv_rhs => rw [children_split_x hx hxi, List.map_append, List.map_singleton, hz]
    rw [sumN_snoc_z]
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [cnt_eq_ite]
    split
    · exact hot c (by rw [List.mem_filter] at hc; exact (mem_children hc.1).2)
    · rfl
  · rw [children_filter_x hx hxi]

theorem vRhs_take_off {ρ : Valn} (hot : ∀ c, c < M.length → isOT (ρ.o c) = true) {i : Nat}
    (hi : i < x) (hE : ¬ ChgX M x false i) : vRhs (M.take x) ρ i = vRhs M ρ i := by
  unfold vRhs
  rw [entry_take M 1 hi, entry_take M 2 hi, par_take M 1 i hi]
  have hupg : upg (M.take x) i = upg M i := by
    by_cases hi1 : i + 1 < x
    · exact upg_take M hi1
    · have hix : i = x - 1 := by omega
      rw [hix, upg_take_last M (by omega) (by omega)]
      by_contra hne
      apply hE; rw [hix]; exact ChgX.supg (fun h => hne h.symm)
  rw [hupg]
  by_cases h1 : entry M 1 i = 0
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : entry M 2 i = 0
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  -- the bump terms
  have hbt : ∀ j ∈ (children M i).filter (fun d => decide (d < x)),
      bumpTerm (M.take x) ρ i j = bumpTerm M ρ i j := by
    intro j hj
    rw [List.mem_filter] at hj
    have hjx : j < x := by simpa using hj.2
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hi]
    split
    · rename_i hb
      rw [children_take, children_filter_x hx (fun hxj => hE (ChgX.vbump h1 h2 hj.1 hb hxj ChgX.leaf))]
    · rfl
  rw [children_take, List.map_congr_left hbt]
  by_cases hxi : x ∈ children M i
  · have hxb : col M x ≠ bump M i := fun hb => hE (ChgX.snb hxi hb)
    have hz : bumpTerm M ρ i x = z := by unfold bumpTerm; rw [if_neg hxb]
    conv_rhs => rw [children_split_x hx hxi, List.map_append, List.map_singleton, hz,
      ← List.cons_append]
    rw [sumN_snoc_z]
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      split
      · apply isOT_omega
        apply isOT_sumN
        intro t' ht'
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht'
        exact hot k (mem_children hk).2
      · rfl
  · rw [children_filter_x hx hxi]

/-- **Outside `ChgX` the values of `M.take x` are those of `M`.** -/
theorem chg_off {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') :
    ∀ i, i < x → (¬ ChgX M x true i → ρ'.o i = ρ.o i) ∧ (¬ ChgX M x false i → ρ'.v i = ρ.v i) := by
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  intro i hi
  apply agree_off_at (ChgX M x) hC hC' hR' (by rw [hlen]; omega) _ _ _ _ i (by rw [hlen]; exact hi)
  · intro i hi hE
    rw [hlen] at hi
    exact oRhs_take_off hx hG.ot_o hE
  · intro i hi hE
    rw [hlen] at hi
    exact vRhs_take_off hx hG.ot_o hi hE
  · intro i hi hE
    rw [hlen] at hi
    refine ⟨fun h => hE (ChgX.ov h), fun c hc hcnt hEc => ?_⟩
    rw [children_take, List.mem_filter] at hc
    have hcx : c < x := by simpa using hc.2
    have hcM : Counted M i c := by
      by_contra hn
      exact hE (ChgX.scnt hc.1 hcx (fun hiff => hn (hiff.mp hcnt)))
    exact hE (ChgX.ochild hc.1 hcM.1 hcM.2 hEc)
  · intro i hi hE he1
    rw [hlen] at hi
    rw [entry_take M 1 hi] at he1
    refine ⟨fun m hm => fun hEm => ?_, fun he2 k hk => fun hEk => ?_, fun he2 j hj hjb k hk => fun hEk => ?_⟩
    · rw [par_take M 1 i hi] at hm
      exact hE (ChgX.vpar he1 hm hEm)
    · rw [entry_take M 2 hi] at he2
      have hi1 : i + 1 < x := by
        by_contra hn
        have hix : i = x - 1 := by omega
        rw [hix, upg_take_last M (by omega) (by omega)] at hk; cases hk
      rw [upg_take M hi1] at hk
      exact hE (ChgX.vupg he1 he2 hk hEk)
    · rw [entry_take M 2 hi] at he2
      rw [children_take, List.mem_filter] at hj hk
      have hjx : j < x := by simpa using hj.2
      rw [col_take M hjx, bump_take M hi] at hjb
      exact hE (ChgX.vbump he1 he2 hj.1 hjb hk.1 hEk)

end

end Ytosk
