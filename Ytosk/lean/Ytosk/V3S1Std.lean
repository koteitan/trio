/-
**S1 はすべての標準形で成り立つ（2026-10-17、t0）。**

trio の結果から出す: Ytosk の標準形は trio の `ST_TS` に入り（`std_stts`、V3Order）、
`ST_TS` の translate は CNF（`cnf_ST_TS`: 木の兄弟は `<o` で増えない）で、深さ d のブロックの上で
translate は列の辞書式順序 `seqlex` と `<o` の順序同型（`olt_iff_seqlex`）。
隣り合う兄弟 a < b の部分木はどちらも深さ e0 a のブロックで、その translate は CNF の兄弟の比較に現れる。
-/
import Ytosk.V3Order
import Ytosk.V3S1T0
import Goper

namespace Ytosk

open TRIO TRIO.Three

set_option linter.unusedSectionVars false

/-! ## seqLtB と seqlex -/

theorem seqLtB_iff_seqlex : ∀ A B : Mat, seqLtB A B = true ↔ TRIO.seqlex A B
  | [], [] => by simp [seqLtB, TRIO.seqlex]
  | [], _ :: _ => by simp [seqLtB, TRIO.seqlex]
  | _ :: _, [] => by simp [seqLtB, TRIO.seqlex]
  | p :: A, q :: B => by
    simp only [seqLtB, TRIO.seqlex, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      seqLtB_iff_seqlex A B]
    unfold colLtB TRIO.collt
    simp

/-! ## CNF は兄弟の鎖に降りる -/

theorem translate_cons (p : Nat × Nat × Nat) (rest : TrioSeq) :
    translate (p :: rest) = P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
      (translate (rest.dropWhile fun q => p.1 < q.1)) := by
  rw [translate]

theorem takeWhile_takeWhile_lt_le (d : Nat) (l : TrioSeq) :
    (l.takeWhile fun q => decide (d ≤ q.1)).takeWhile (fun q => decide (d < q.1)) =
      l.takeWhile fun q => decide (d < q.1) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h1 : d < a.1
    · have h2 : d ≤ a.1 := le_of_lt h1
      rw [List.takeWhile_cons_of_pos (by simpa using h2), List.takeWhile_cons_of_pos (by simpa using h1),
        List.takeWhile_cons_of_pos (by simpa using h1), ih]
    · by_cases h2 : d ≤ a.1
      · rw [List.takeWhile_cons_of_pos (by simpa using h2), List.takeWhile_cons_of_neg (by simpa using h1),
          List.takeWhile_cons_of_neg (by simpa using h1)]
      · rw [List.takeWhile_cons_of_neg (by simpa using h2), List.takeWhile_cons_of_neg (by simpa using h1)]
        rfl

theorem dropWhile_takeWhile_lt_le (d : Nat) (l : TrioSeq) :
    (l.takeWhile fun q => decide (d ≤ q.1)).dropWhile (fun q => decide (d < q.1)) =
      (l.dropWhile fun q => decide (d < q.1)).takeWhile fun q => decide (d ≤ q.1) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h1 : d < a.1
    · have h2 : d ≤ a.1 := le_of_lt h1
      rw [List.takeWhile_cons_of_pos (by simpa using h2), List.dropWhile_cons_of_pos (by simpa using h1),
        List.dropWhile_cons_of_pos (by simpa using h1), ih]
    · by_cases h2 : d ≤ a.1
      · rw [List.takeWhile_cons_of_pos (by simpa using h2), List.dropWhile_cons_of_neg (by simpa using h1),
          List.dropWhile_cons_of_neg (by simpa using h1), List.takeWhile_cons_of_pos (by simpa using h2)]
      · rw [List.takeWhile_cons_of_neg (by simpa using h2), List.dropWhile_cons_of_neg (by simpa using h1),
          List.takeWhile_cons_of_neg (by simpa using h2)]
        rfl

/-- The sibling chain from a column on: its subtree and the later siblings (up to the parent's end). -/
def sibChain (p : Nat × Nat × Nat) (post : TrioSeq) : TrioSeq :=
  p :: post.takeWhile fun q => decide (p.1 ≤ q.1)

theorem translate_sibChain (p : Nat × Nat × Nat) (post : TrioSeq) :
    translate (sibChain p post) = P p.2.1 p.2.2 (translate (post.takeWhile fun q => decide (p.1 < q.1)))
      (translate ((post.dropWhile fun q => decide (p.1 < q.1)).takeWhile fun q => decide (p.1 ≤ q.1))) := by
  unfold sibChain
  rw [translate_cons]
  simp only [takeWhile_takeWhile_lt_le, dropWhile_takeWhile_lt_le]

theorem dropWhile_head_false {α : Type} (p : α → Bool) : ∀ (l : List α) (y : α) (r : List α),
    l.dropWhile p = y :: r → p y = false
  | [], _, _, h => by simp at h
  | a :: l, y, r, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact dropWhile_head_false p l y r h
    · rename_i hpa; simp only [List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simpa using hpa

theorem takeWhile_append_stop {α : Type} (p : α → Bool) : ∀ (l m : List α),
    (∀ y r, m = y :: r → p y = false) → (l ++ m).takeWhile p = l.takeWhile p
  | [], [], _ => rfl
  | [], y :: r, h => by simp [List.takeWhile_cons, h y r rfl]
  | a :: l, m, h => by
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · rw [takeWhile_append_stop p l m h]
    · rfl

/-- **CNF descends to every sibling chain.** -/
theorem cnf_sibChain : ∀ (n : Nat) (S : TrioSeq), S.length ≤ n → cnf (translate S) →
    ∀ pre p post, S = pre ++ p :: post → cnf (translate (sibChain p post))
  | 0, S, hl, _, pre, p, post, e => by subst e; simp at hl
  | n + 1, S, hl, hc, pre, p, post, e => by
    cases S with
    | nil => cases pre <;> simp at e
    | cons s rest =>
      have hlt0 := (List.takeWhile_sublist (fun q => decide (s.1 < q.1)) (l := rest)).length_le
      have hld0 := List.length_dropWhile_le (fun q => decide (s.1 < q.1)) rest
      have hsplit : rest = rest.takeWhile (fun q => decide (s.1 < q.1)) ++
          rest.dropWhile (fun q => decide (s.1 < q.1)) := (List.takeWhile_append_dropWhile).symm
      have hdwh : ∀ y r, rest.dropWhile (fun q => decide (s.1 < q.1)) = y :: r → decide (s.1 < y.1) = false :=
        fun y r h => dropWhile_head_false _ rest y r h
      generalize htw : rest.takeWhile (fun q => decide (s.1 < q.1)) = tw at hlt0 hsplit
      generalize hdw : rest.dropWhile (fun q => decide (s.1 < q.1)) = dw at hld0 hsplit hdwh
      rw [translate_cons, htw, hdw] at hc
      have hcb : cnf (translate tw) := by
        cases hd : translate dw with
        | Z => rw [hd] at hc; exact hc
        | P _ _ _ _ => rw [hd] at hc; exact hc.1
      have hcc : cnf (translate dw) := by
        cases hd : translate dw with
        | Z => trivial
        | P _ _ _ _ => rw [hd] at hc; exact hc.2.2
      have hlt : tw.length ≤ n := by simp at hl; omega
      have hld : dw.length ≤ n := by simp at hl; omega
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [translate_sibChain, htw, hdw]
        cases hq : dw with
        | nil => rw [hq] at hc; simpa [translate] using hcb
        | cons q dwr =>
          have hqs := hdwh q dwr hq
          simp only [decide_eq_false_iff_not, not_lt] at hqs
          by_cases hqe : s.1 ≤ q.1
          · have hqp : q.1 = s.1 := by omega
            have hch := cnf_sibChain n dw hld hcc [] q dwr (by rw [hq]; rfl)
            have e1 : (q :: dwr).takeWhile (fun r => decide (s.1 ≤ r.1)) = sibChain q dwr := by
              unfold sibChain; rw [List.takeWhile_cons, if_pos (by simp [hqe]), hqp]
            rw [e1, translate_sibChain]
            rw [translate_sibChain] at hch
            rw [hq, translate_cons] at hc
            simp only [cnf_P_P]
            exact ⟨hcb, hc.2.1, hch⟩
          · have e1 : (q :: dwr).takeWhile (fun r => decide (s.1 ≤ r.1)) = [] := by
              rw [List.takeWhile_cons, if_neg (by simp [hqe])]
            rw [e1]; simpa [translate] using hcb
      | cons s' pre' =>
        simp only [List.cons_append, List.cons.injEq] at e
        obtain ⟨rfl, e⟩ := e
        rw [hsplit] at e
        rcases List.append_eq_append_iff.mp e with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
        · exact cnf_sibChain n dw hld hcc a' p post h2
        · cases c' with
          | nil =>
            simp only [List.nil_append] at h2
            exact cnf_sibChain n dw hld hcc [] p post h2.symm
          | cons c0 c'' =>
            simp only [List.cons_append, List.cons.injEq] at h2
            obtain ⟨rfl, rfl⟩ := h2
            have hpmem : p ∈ tw := by rw [h1]; simp
            have hps : s.1 < p.1 := by
              rw [← htw] at hpmem
              have := List.mem_takeWhile_imp hpmem; simpa using this
            have hch := cnf_sibChain n tw hlt hcb pre' p c'' h1
            have e2 : sibChain p (c'' ++ dw) = sibChain p c'' := by
              unfold sibChain
              rw [takeWhile_append_stop _ _ _ (fun y r h => by
                have := hdwh y r h
                simp only [decide_eq_false_iff_not, not_lt] at this ⊢; omega)]
            rw [e2]; exact hch

/-! ## ブロックの補題 -/

theorem steps1_drop : ∀ (l : TrioSeq) (k : Nat), steps1 l → steps1 (l.drop k)
  | [], _, _ => by simp
  | _ :: _, 0, h => by simpa using h
  | p :: r, k + 1, h => by simpa using steps1_drop r k (steps1_tail h)

theorem steps1_prefix : ∀ {l l' : TrioSeq}, steps1 l → l' <+: l → steps1 l'
  | _, [], _, _ => trivial
  | _, [_], _, _ => trivial
  | l, p :: q :: r, h, hp => by
    obtain ⟨t, rfl⟩ := hp
    simp only [List.cons_append, steps1_cons_cons] at h ⊢
    exact ⟨h.1, steps1_prefix h.2 ⟨t, by simp⟩⟩

theorem takeWhile_all_self {α : Type} (p : α → Bool) : ∀ l : List α, (∀ y ∈ l, p y = true) →
    l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.takeWhile_cons_of_pos (h a (by simp)), takeWhile_all_self p l (fun y hy => h y (by simp [hy]))]

theorem dropWhile_all_nil {α : Type} (p : α → Bool) : ∀ l : List α, (∀ y ∈ l, p y = true) →
    l.dropWhile p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.dropWhile_cons_of_pos (h a (by simp)), dropWhile_all_nil p l (fun y hy => h y (by simp [hy]))]

/-- The translate of a subtree is a single tree. -/
theorem translate_subT (M : Mat) (a : Nat) :
    translate (subT M a) = P (col M a).2.1 (col M a).2.2
      (translate ((M.drop (a + 1)).takeWhile fun q => decide ((col M a).1 < q.1))) Z := by
  unfold subT
  rw [translate_cons, entry0_col]
  have hall : ∀ y ∈ (M.drop (a + 1)).takeWhile (fun q => decide ((col M a).1 < q.1)),
      decide ((col M a).1 < y.1) = true := fun y hy =>
    List.mem_takeWhile_imp (p := fun q : Nat × Nat × Nat => decide ((col M a).1 < q.1)) hy
  rw [takeWhile_all_self _ _ hall, dropWhile_all_nil _ _ hall, show translate [] = Z by rw [translate]]

theorem blockok_subT {M : Mat} (hs : steps1 M) (a : Nat) :
    blockok (col M a).1 (subT M a) := by
  refine ⟨fun _ => rfl, fun p hp => ?_, ?_⟩
  · unfold subT at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_refl _
    · have := List.mem_takeWhile_imp hp
      simp only [decide_eq_true_eq] at this
      rw [← entry0_col]; omega
  · by_cases ha : a < M.length
    · apply steps1_prefix (steps1_drop M a hs)
      unfold subT
      rw [List.drop_eq_getElem_cons ha, ← col_getElem ha]
      exact List.prefix_cons_inj _ |>.mpr (List.takeWhile_prefix _)
    · unfold subT
      rw [List.drop_eq_nil_of_le (by omega)]
      simp

/-! ## S1 from CNF -/

/-- **S1 (sequence form) from the CNF of the translate** and the block condition. -/
theorem S1s_of_cnf {M : Mat} (hc : cnf (translate M)) (hs : steps1 M) : S1s M := by
  intro a b hab hbM he _ hbet
  have haM : a < M.length := by omega
  have hcol : ∀ j, j < M.length → (col M j).1 = entry M 0 j := fun j _ => (entry0_col M j).symm
  -- the segment `(a, b)` and the drop
  have hseg : M.drop (a + 1) = (M.drop (a + 1)).take (b - (a + 1)) ++ M.drop b := by
    conv_lhs => rw [← List.take_append_drop (b - (a + 1)) (M.drop (a + 1))]
    rw [List.drop_drop, show a + 1 + (b - (a + 1)) = b by omega]
  have hsegall : ∀ y ∈ (M.drop (a + 1)).take (b - (a + 1)), decide ((col M a).1 < y.1) = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
    simp only [List.length_take, List.length_drop] at hk
    simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
    rw [← col_getElem (by omega), hcol a haM, hcol _ (by omega)]
    exact hbet _ (by omega) (by omega)
  have hbcons : M.drop b = col M b :: M.drop (b + 1) := by
    rw [List.drop_eq_getElem_cons hbM, ← col_getElem hbM]
  have hbfail : decide ((col M a).1 < (col M b).1) = false := by
    rw [hcol a haM, hcol b hbM, he]; simp
  have htw : (M.drop (a + 1)).takeWhile (fun q => decide ((col M a).1 < q.1)) =
      (M.drop (a + 1)).take (b - (a + 1)) := by
    conv_lhs => rw [hseg, takeWhile_append_all _ _ _ hsegall, hbcons,
      List.takeWhile_cons_of_neg (by simp [hbfail]), List.append_nil]
  have hdw : (M.drop (a + 1)).dropWhile (fun q => decide ((col M a).1 < q.1)) = M.drop b := by
    rw [hseg]
    rw [List.dropWhile_append_of_pos hsegall]
    rw [hbcons, List.dropWhile_cons_of_neg (by simp [hbfail])]
  -- the CNF at the chain of `a`
  have hch := cnf_sibChain M.length M (le_refl _) hc (M.take a) (col M a) (M.drop (a + 1)) (by
    rw [col_getElem haM, ← List.drop_eq_getElem_cons haM, List.take_append_drop])
  rw [translate_sibChain, hdw, hbcons, List.takeWhile_cons_of_pos (by
    rw [hcol a haM, hcol b hbM, he]; simp)] at hch
  have hb1 : (col M b).1 = (col M a).1 := by rw [hcol a haM, hcol b hbM, he]
  have e3 : (col M b :: (M.drop (b + 1)).takeWhile fun q => decide ((col M a).1 ≤ q.1)) =
      sibChain (col M b) (M.drop (b + 1)) := by unfold sibChain; rw [hb1]
  rw [e3, translate_sibChain] at hch
  simp only [cnf_P_P] at hch
  have hno : ¬ (translate (subT M a) <o translate (subT M b)) := by
    rw [translate_subT, translate_subT]
    exact hch.2.1
  -- back to the sequences
  by_cases hAB : subT M a = subT M b
  · rw [hAB]; exact seqLtB_self _
  · have hbA := blockok_subT hs a
    have hbB := blockok_subT hs b
    rw [hb1] at hbB
    have hiff := olt_iff_seqlex hbA hbB hAB
    cases hq : seqLtB (subT M a) (subT M b)
    · rfl
    · exact absurd (hiff.mpr ((seqLtB_iff_seqlex _ _).mp hq)) hno

/-- **S1 holds for every standard form.** -/
theorem S1_std {M : Mat} (hM : Std M) : S1 M := by
  rcases std_stts hM with rfl | hst
  · intro p l₁ l₂ a b h
    have : children ([] : Mat) p = [] := by unfold children; simp
    rw [this] at h; simp at h
  · have hR0 : R0P M := by
      by_cases hS : M = SRO
      · rw [hS]; exact sro_cols.1
      · exact (sInv_std hM hS).r0p
    exact S1_of_S1s hR0 (S1s_of_cnf (cnf_ST_TS hst) (blockok_ST_TS hst).2.2)

end Ytosk
