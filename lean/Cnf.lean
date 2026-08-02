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

/-! ## CNF context congruence -/

/-- **CNF context congruence.**  If `Z1 = z1 :: T1`, `Z2 = z2 :: T2` share
their leading row-0 (`z1.1 = z2.1`), `translate Z1 <o translate Z2`, and
`translate Z1` is CNF, then a common good part `G` preserves CNF. -/
theorem cnf_ctx_cong {z1 z2 : ℕ × ℕ × ℕ} {T1 T2 : TrioSeq}
    (cZ1 : cnf (translate (z1 :: T1)))
    (decr : translate (z1 :: T1) <o translate (z2 :: T2))
    (root : z1.1 = z2.1)
    (leadle : ∃ p1 p2 b1 c1 q1 q2 b2 c2, translate (z1 :: T1) = P p1 p2 b1 c1
        ∧ translate (z2 :: T2) = P q1 q2 b2 c2 ∧ P p1 p2 b1 Z ≤o P q1 q2 b2 Z)
    (r1 : ∀ x ∈ T1, z1.1 ≤ x.1) (r2 : ∀ x ∈ T2, z2.1 ≤ x.1)
    (G : TrioSeq) (hG2 : cnf (translate (G ++ z2 :: T2))) :
    cnf (translate (G ++ z1 :: T1)) := by
  obtain ⟨p1, p2, b1, c1, q1, q2, b2, c2, lZ1, lZ2, lle⟩ := leadle
  match G with
  | [] => simpa using cZ1
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        intro x hx; simpa using allG x hx
      by_cases hPg : g.1 < z1.1
      · -- the whole tail nests under `g`; pass to `G'`
        have aZ1 : ∀ x ∈ z1 :: T1, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (r1 _ hx)
        have aZ2 : ∀ x ∈ z2 :: T2, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact root ▸ hPg
          · exact lt_of_lt_of_le (root ▸ hPg) (r2 _ hx)
        have all1 : ∀ x ∈ G' ++ z1 :: T1, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ1 x h]
        have all2 : ∀ x ∈ G' ++ z2 :: T2, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ2 x h]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2.1 g.2.2 (translate (G' ++ z1 :: T1)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all1),
            List.dropWhile_eq_nil_iff.2 (by simpa using all1), translate]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2.1 g.2.2 (translate (G' ++ z2 :: T2)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all2),
            List.dropWhile_eq_nil_iff.2 (by simpa using all2), translate]
        rw [List.cons_append] at hG2 ⊢
        rw [e2] at hG2
        rw [e1]
        exact cnf_P_Z.2 (cnf_ctx_cong cZ1 decr root
          ⟨p1, p2, b1, c1, q1, q2, b2, c2, lZ1, lZ2, lle⟩ r1 r2 G' (cnf_P_Z.1 hG2))
      · -- the tail is a sibling after `g`'s subtree
        have hPg2 : ¬ g.1 < z2.1 := root ▸ hPg
        have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1) = z1 :: T1 := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg2]
        have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1) = z2 :: T2 := by
          rw [dropWhile_append_all allG']
          simp [hPg2]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2.1 g.2.2 (translate G') (P p1 p2 b1 c1) := by
          rw [translate, tw1, dw1, lZ1]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2.1 g.2.2 (translate G') (P q1 q2 b2 c2) := by
          rw [translate, tw2, dw2, lZ2]
        rw [List.cons_append] at hG2 ⊢
        rw [e2] at hG2
        obtain ⟨ctg, bnd2, -⟩ := cnf_P_P.1 hG2
        have bnd1 : ¬ (P g.2.1 g.2.2 (translate G') Z <o P p1 p2 b1 Z) := by
          intro hlt
          exact bnd2 (olt_ole_trans hlt lle)
        rw [e1]
        exact cnf_P_P.2 ⟨ctg, bnd1, lZ1 ▸ cZ1⟩
    · -- `G'` already drops to/below `g`; recurse on the shorter tail
      push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        simpa using hnx
      have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z1 :: T1 := dropWhile_append_not hx hnx'
      have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z2 :: T2 := dropWhile_append_not hx hnx'
      have Dne : G'.dropWhile (fun q => g.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨d, D', hD⟩ : ∃ d D', G'.dropWhile (fun q => g.1 < q.1) = d :: D' := by
        rcases hD : G'.dropWhile (fun q => g.1 < q.1) with - | ⟨d, D'⟩
        · exact absurd hD Dne
        · exact ⟨d, D', hD⟩
      have e1 : translate (g :: (G' ++ z1 :: T1))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ z1 :: T1)) := by
        rw [translate, tw1, dw1, hD]
      have e2 : translate (g :: (G' ++ z2 :: T2))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ z2 :: T2)) := by
        rw [translate, tw2, dw2, hD]
      have p1' : translate ((d :: D') ++ z1 :: T1)
          = P d.2.1 d.2.2 (translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ z1 :: T1).dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      have p2' : translate ((d :: D') ++ z2 :: T2)
          = P d.2.1 d.2.2 (translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ z2 :: T2).dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      have decrD : translate ((d :: D') ++ z1 :: T1)
          <o translate ((d :: D') ++ z2 :: T2) :=
        translate_ctx_cong decr root r1 r2 (d :: D')
      have argle : translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)
            <o translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1)
          ∨ translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)
            = translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1) := by
        rw [p1', p2', olt_P_P] at decrD
        rcases decrD with h | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h, -⟩
        · omega
        · omega
        · exact Or.inl h
        · exact Or.inr h
      rw [List.cons_append] at hG2 ⊢
      rw [e2, p2'] at hG2
      obtain ⟨ctw, bnd2, cD2⟩ := cnf_P_P.1 hG2
      have cD2' : cnf (translate ((d :: D') ++ z2 :: T2)) := by
        rw [p2']
        exact cD2
      have cD1 : cnf (translate ((d :: D') ++ z1 :: T1)) :=
        cnf_ctx_cong cZ1 decr root
          ⟨p1, p2, b1, c1, q1, q2, b2, c2, lZ1, lZ2, lle⟩ r1 r2 (d :: D') cD2'
      -- the boundary transfers from the appended argument
      have bnd1 : ¬ (P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1)) Z
          <o P d.2.1 d.2.2
              (translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)) Z) := by
        intro hlt
        rw [olt_P_P] at hlt
        rcases hlt with h | ⟨heq, h⟩ | ⟨heq1, heq2, h⟩ | ⟨-, -, -, h⟩
        · exact bnd2 (olt_P_P.2 (Or.inl h))
        · exact bnd2 (olt_P_P.2 (Or.inr (Or.inl ⟨heq, h⟩)))
        · rcases argle with ha | ha
          · exact bnd2 (olt_P_P.2 (Or.inr (Or.inr (Or.inl ⟨heq1, heq2, olt_trans h ha⟩))))
          · exact bnd2 (olt_P_P.2 (Or.inr (Or.inr (Or.inl ⟨heq1, heq2, ha ▸ h⟩))))
        · exact not_olt_Z Z h
      rw [e1, p1']
      refine cnf_P_P.2 ⟨ctw, bnd1, ?_⟩
      rw [← p1']
      exact cD1
  termination_by G.length
  decreasing_by
  · simp only [List.length_cons]
    omega
  · have hle : (d :: D').length ≤ G'.length := by
      rw [← hD]
      exact List.length_dropWhile_le _ G'
    simp only [List.length_cons] at hle ⊢
    omega

/-- CNF is inherited by a re-opening tail. -/
theorem cnf_tail {t : ℕ × ℕ × ℕ} {T' : TrioSeq}
    (rT : ∀ x ∈ T', t.1 ≤ x.1)
    (G : TrioSeq) (hGT : cnf (translate (G ++ t :: T'))) :
    cnf (translate (t :: T')) := by
  match G with
  | [] => simpa using hGT
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        intro x hx; simpa using allG x hx
      by_cases hPg : g.1 < t.1
      · have aT : ∀ x ∈ t :: T', g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (rT _ hx)
        have all : ∀ x ∈ G' ++ t :: T', g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aT x h]
        have e : translate (g :: (G' ++ t :: T'))
            = P g.2.1 g.2.2 (translate (G' ++ t :: T')) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all),
            List.dropWhile_eq_nil_iff.2 (by simpa using all), translate]
        rw [List.cons_append] at hGT
        rw [e] at hGT
        exact cnf_tail rT G' (cnf_P_Z.1 hGT)
      · have tw : (G' ++ t :: T').takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw : (G' ++ t :: T').dropWhile (fun q => g.1 < q.1) = t :: T' := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have e : translate (g :: (G' ++ t :: T'))
            = P g.2.1 g.2.2 (translate G') (translate (t :: T')) := by
          rw [translate, tw, dw]
        rw [List.cons_append] at hGT
        rw [e, translate] at hGT
        rw [translate]
        exact (cnf_P_P.1 hGT).2.2
    · push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        simpa using hnx
      have tw : (G' ++ t :: T').takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw : (G' ++ t :: T').dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ t :: T' := dropWhile_append_not hx hnx'
      have Dne : G'.dropWhile (fun q => g.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨d, D', hD⟩ : ∃ d D', G'.dropWhile (fun q => g.1 < q.1) = d :: D' := by
        rcases hD : G'.dropWhile (fun q => g.1 < q.1) with - | ⟨d, D'⟩
        · exact absurd hD Dne
        · exact ⟨d, D', hD⟩
      have e : translate (g :: (G' ++ t :: T'))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ t :: T')) := by
        rw [translate, tw, dw, hD]
      have p : translate ((d :: D') ++ t :: T')
          = P d.2.1 d.2.2 (translate ((D' ++ t :: T').takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ t :: T').dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      rw [List.cons_append] at hGT
      rw [e, p] at hGT
      have hD1 : cnf (translate ((d :: D') ++ t :: T')) := by
        rw [p]
        exact (cnf_P_P.1 hGT).2.2
      exact cnf_tail rT (d :: D') hD1
  termination_by G.length
  decreasing_by
  · simp only [List.length_cons]
    omega
  · have hle : (d :: D').length ≤ G'.length := by
      rw [← hD]
      exact List.length_dropWhile_le _ G'
    simp only [List.length_cons] at hle ⊢
    omega

end TRIO
