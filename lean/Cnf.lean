/-
**Cantor 標準形条件**（トリオ数列）。

述語 `cnf`: 主要項の和が lead 対（添字対）で広義単調減少していること。
対角列の cnf、末尾除去・前部分列への閉包、同一ブロックの反復の cnf。

2 行の Cnf.lean と同じ骨格。比較 `P a b Z <o P e f Z` が
`P a1 a2 b Z <o P e1 e2 f Z` の対比較になる。
-/
import Decrease
import Seqlex

namespace TRIO

open Three
open Classical

/-! ## 対角列の構造 -/

theorem fst_in_diagSeqT {q : ℕ × ℕ × ℕ} {a b : ℕ} (h : q ∈ diagSeqT a b) :
    a ≤ q.1 := by
  unfold diagSeqT at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  obtain ⟨i, _, rfl⟩ := List.mem_range'.1 hj
  simp

theorem translate_diagSeqT {u v : ℕ} (h : u ≤ v) :
    translate (diagSeqT u v)
      = P u (min u 1) (translate (diagSeqT (u + 1) v)) Z := by
  rw [diagSeqT_cons h]
  exact translate_single_tree fun q hq => by
    have := fst_in_diagSeqT hq
    simp only []
    omega

/-! ## The Cantor normal form condition -/

/-- `cnf`: the sum of principal terms is weakly decreasing in the lead pair
(the trailing sums cut to `Z` for the comparison), recursively at every
position. -/
def cnf : Three → Prop
  | Z => True
  | P _ _ b Z => cnf b
  | P a1 a2 b (P e1 e2 f g) =>
      cnf b ∧ ¬ (P a1 a2 b Z <o P e1 e2 f Z) ∧ cnf (P e1 e2 f g)

@[simp] theorem cnf_Z : cnf Z := trivial

@[simp] theorem cnf_P_Z {a1 a2 : ℕ} {b : Three} : cnf (P a1 a2 b Z) ↔ cnf b :=
  Iff.rfl

@[simp] theorem cnf_P_P {a1 a2 e1 e2 : ℕ} {b f g : Three} :
    cnf (P a1 a2 b (P e1 e2 f g)) ↔
      cnf b ∧ ¬ (P a1 a2 b Z <o P e1 e2 f Z) ∧ cnf (P e1 e2 f g) := Iff.rfl

theorem cnf_translate_diagSeqT_aux (n u : ℕ) :
    cnf (translate (diagSeqT u (u + n))) := by
  induction n generalizing u with
  | zero =>
    rw [translate_diagSeqT (by omega)]
    have e : diagSeqT (u + 1) (u + 0) = [] := by
      unfold diagSeqT
      rw [show u + 0 + 1 - (u + 1) = 0 by omega]
      rfl
    rw [e]
    show cnf (P u (min u 1) (translate []) Z)
    rw [cnf_P_Z]
    show cnf (translate [])
    simp [translate]
  | succ n ih =>
    rw [translate_diagSeqT (by omega)]
    rw [cnf_P_Z]
    have := ih (u + 1)
    rwa [show u + 1 + n = u + (n + 1) by omega] at this

theorem cnf_diag (v : ℕ) : cnf (translate (diagSeqT 0 v)) := by
  have := cnf_translate_diagSeqT_aux v 0
  rwa [Nat.zero_add] at this

/-! ## Appending can only grow a leading block -/

/-- Appending a column can only *increase* (weakly) the translation of a
leading same-level block. -/
theorem translate_takeWhile_snoc_le (a : ℕ) (C : TrioSeq) (m : ℕ × ℕ × ℕ) :
    translate (C.takeWhile fun x => a < x.1)
      ≤o translate ((C ++ [m]).takeWhile fun x => a < x.1) := by
  by_cases hall : ∀ x ∈ C, a < x.1
  · have hall' : ∀ x ∈ C, (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) x = true := by
      intro x hx; simpa using hall x hx
    have twC : C.takeWhile (fun x => a < x.1) = C := List.takeWhile_eq_self_iff.2 hall'
    by_cases hm : a < m.1
    · have e : (C ++ [m]).takeWhile (fun x => a < x.1) = C ++ [m] := by
        apply List.takeWhile_eq_self_iff.2
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hall' x hx
        · simp at hx
          simpa [hx] using hm
      rw [twC, e]
      exact Or.inl (translate_snoc_increase _ _)
    · have e : (C ++ [m]).takeWhile (fun x => a < x.1) = C := by
        rw [takeWhile_append_all hall']
        simp [hm]
      rw [twC, e]
      exact Or.inr rfl
  · push Not at hall
    obtain ⟨x, hx, hnx⟩ := hall
    have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) x = true := by
      simpa using hnx
    rw [takeWhile_append_not hx hnx']
    exact Or.inr rfl

/-! ## Closure under dropping the last column and taking prefixes -/

/-- `cnf` is preserved by dropping the last column. -/
theorem cnf_snoc {D : TrioSeq} {m : ℕ × ℕ × ℕ}
    (h : cnf (translate (D ++ [m]))) : cnf (translate D) := by
  induction D using translate.induct with
  | case1 => simp [translate]
  | case2 p rest ih1 ih2 =>
    by_cases allp : ∀ x ∈ rest, p.1 < x.1
    · have allp' : ∀ x ∈ rest, (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        intro x hx; simpa using allp x hx
      have tw : rest.takeWhile (fun q => p.1 < q.1) = rest :=
        List.takeWhile_eq_self_iff.2 allp'
      have dw : rest.dropWhile (fun q => p.1 < q.1) = [] :=
        List.dropWhile_eq_nil_iff.2 allp'
      have eq0 : translate (p :: rest) = P p.2.1 p.2.2 (translate rest) Z := by
        rw [translate, tw, dw, translate]
      by_cases hm : p.1 < m.1
      · have all' : ∀ x ∈ rest ++ [m],
            (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact allp' x hx
          · simp at hx
            simpa [hx] using hm
        have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest ++ [m] :=
          List.takeWhile_eq_self_iff.2 all'
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [] :=
          List.dropWhile_eq_nil_iff.2 all'
        have hsnoc : cnf (translate (rest ++ [m])) := by
          have e : translate ((p :: rest) ++ [m])
              = P p.2.1 p.2.2 (translate (rest ++ [m])) Z := by
            rw [List.cons_append, translate, tw', dw', translate]
          rw [e] at h
          exact (cnf_P_Z).1 h
        have : cnf (translate rest) := by
          have := ih1 (by rw [tw]; exact hsnoc)
          rwa [tw] at this
        rw [eq0]
        exact (cnf_P_Z).2 this
      · have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest := by
          rw [takeWhile_append_all allp']
          simp [hm]
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [m] := by
          rw [dropWhile_append_all allp']
          simp [hm]
        have e : translate ((p :: rest) ++ [m])
            = P p.2.1 p.2.2 (translate rest) (translate [m]) := by
          rw [List.cons_append, translate, tw', dw']
        have e2 : translate ([m] : TrioSeq) = P m.2.1 m.2.2 Z Z := by
          rw [translate]
          simp [translate]
        rw [e, e2] at h
        rw [eq0]
        exact (cnf_P_Z).2 h.1
    · push Not at allp
      obtain ⟨x, hx, hnx⟩ := allp
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        simpa using hnx
      have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1)
          = rest.takeWhile (fun q => p.1 < q.1) := takeWhile_append_not hx hnx'
      have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1)
          = rest.dropWhile (fun q => p.1 < q.1) ++ [m] := dropWhile_append_not hx hnx'
      have dwne : rest.dropWhile (fun q => p.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨q, rest2, dwq⟩ : ∃ q rest2,
          rest.dropWhile (fun q => p.1 < q.1) = q :: rest2 := by
        rcases hdw : rest.dropWhile (fun q => p.1 < q.1) with - | ⟨q, rest2⟩
        · exact absurd hdw dwne
        · exact ⟨q, rest2, hdw⟩
      have td : translate (rest.dropWhile fun q => p.1 < q.1)
          = P q.2.1 q.2.2 (translate (rest2.takeWhile fun y => q.1 < y.1))
              (translate (rest2.dropWhile fun y => q.1 < y.1)) := by
        rw [dwq, translate]
      have td' : translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])
          = P q.2.1 q.2.2 (translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1))
              (translate ((rest2 ++ [m]).dropWhile fun y => q.1 < y.1)) := by
        rw [dwq, List.cons_append, translate]
      have fle : translate (rest2.takeWhile fun y => q.1 < y.1)
          ≤o translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1) :=
        translate_takeWhile_snoc_le q.1 rest2 m
      have e : translate ((p :: rest) ++ [m])
          = P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])) := by
        rw [List.cons_append, translate, tw', dw']
      rw [e, td'] at h
      obtain ⟨cb, sib', cnf'⟩ := cnf_P_P.1 h
      have cdw : cnf (translate (rest.dropWhile fun q => p.1 < q.1)) := by
        apply ih2
        rw [td']
        exact cnf'
      have leP : P q.2.1 q.2.2 (translate (rest2.takeWhile fun y => q.1 < y.1)) Z
          ≤o P q.2.1 q.2.2
              (translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1)) Z := by
        rcases fle with hlt | heq
        · exact Or.inl (olt_P_b _ _ _ _ hlt)
        · rw [heq]
          exact Or.inr rfl
      have sib : ¬ (P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1)) Z
          <o P q.2.1 q.2.2 (translate (rest2.takeWhile fun y => q.1 < y.1)) Z) := by
        intro hlt
        exact sib' (olt_ole_trans hlt leP)
      rw [translate, td]
      exact cnf_P_P.2 ⟨cb, sib, td ▸ cdw⟩

theorem cnf_dropLast {C : TrioSeq} (ne : C ≠ []) (h : cnf (translate C)) :
    cnf (translate C.dropLast) := by
  apply cnf_snoc (m := C.getLast ne)
  rwa [List.dropLast_append_getLast ne]

/-- `cnf` is preserved by any prefix `take k`. -/
theorem cnf_take {M : TrioSeq} (h : cnf (translate M)) (k : ℕ) :
    cnf (translate (M.take k)) := by
  suffices H : ∀ d k, M.length - k = d → cnf (translate (M.take k)) from H _ k rfl
  intro d
  induction d with
  | zero =>
    intro k hk
    rw [List.take_of_length_le (by omega)]
    exact h
  | succ d ih =>
    intro k hk
    have klt : k < M.length := by omega
    have ihk : cnf (translate (M.take (k + 1))) := ih (k + 1) (by omega)
    have ne : M.take (k + 1) ≠ [] := by
      have hlen : (M.take (k + 1)).length = k + 1 := by
        rw [List.length_take]
        omega
      intro he
      rw [he] at hlen
      simp at hlen
    have e : (M.take (k + 1)).dropLast = M.take k := by
      rw [List.dropLast_eq_take, List.take_take]
      congr 1
      simp
      omega
    rw [← e]
    exact cnf_dropLast ne ihk

/-- `n` identical copies of a block `(v0, w1, w2) :: R` translate to a CNF
term. -/
theorem cnf_replicate_block {v0 w1 w2 : ℕ} {R : TrioSeq}
    (hR : ∀ x ∈ R, v0 < x.1) (cR : cnf (translate R)) (n : ℕ) :
    cnf (translate (List.replicate n ((v0, w1, w2) :: R)).flatten) := by
  induction n with
  | zero => simp [translate]
  | succ m ih =>
    have hd : (List.replicate (m + 1) ((v0, w1, w2) :: R)).flatten
        = ((v0, w1, w2) :: R) ++ (List.replicate m ((v0, w1, w2) :: R)).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    have Tcond : (List.replicate m ((v0, w1, w2) :: R)).flatten = []
        ∨ ¬ v0 < (((List.replicate m ((v0, w1, w2) :: R)).flatten).headI).1 := by
      cases m with
      | zero => left; rfl
      | succ m' =>
        right
        rw [List.replicate_succ, List.flatten_cons]
        simp
    have tb : translate (((v0, w1, w2) :: R)
          ++ (List.replicate m ((v0, w1, w2) :: R)).flatten)
        = P w1 w2 (translate R)
            (translate (List.replicate m ((v0, w1, w2) :: R)).flatten) :=
      translate_block_append hR Tcond
    cases m with
    | zero =>
      rw [hd, tb,
        show translate (List.replicate 0 ((v0, w1, w2) :: R)).flatten = Z from by
          simp [translate]]
      exact cnf_P_Z.2 cR
    | succ m' =>
      have e : (List.replicate (m' + 1) ((v0, w1, w2) :: R)).flatten
          = ((v0, w1, w2) :: R) ++ (List.replicate m' ((v0, w1, w2) :: R)).flatten := by
        rw [List.replicate_succ, List.flatten_cons]
      have c : (List.replicate m' ((v0, w1, w2) :: R)).flatten = []
          ∨ ¬ v0 < (((List.replicate m' ((v0, w1, w2) :: R)).flatten).headI).1 := by
        cases m' with
        | zero => left; rfl
        | succ m'' =>
          right
          rw [List.replicate_succ, List.flatten_cons]
          simp
      have tT : translate (List.replicate (m' + 1) ((v0, w1, w2) :: R)).flatten
          = P w1 w2 (translate R)
              (translate (List.replicate m' ((v0, w1, w2) :: R)).flatten) := by
        rw [e]
        exact translate_block_append hR c
      rw [hd, tb, tT]
      refine cnf_P_P.2 ⟨cR, fun hlt => olt_irrefl _ hlt, ?_⟩
      rw [← tT]
      exact ih

end TRIO
