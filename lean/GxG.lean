/-
GxG.lean: 先頭にタイの中身の字 `(1,b+1,1)(2,b+1,0)` が m 個ある語の頭の潰れ。

    pre b m = [[(1,b+1,0)]]^m
    ((0,b,0) :: rword 0 b (pre b m ++ l) ++ (1,b+1,1))⟦n⟧ = Dzf (fun a b => rword a b (pre b m ++ l)) 0 b n

先頭の字の列は全部根の錐（行 1 = b+1）なので持ち上がり、`l` の中身（`RiseOkv v0`, `v0 ≤ b`）は持ち上がらない。
GwZ の `oper_z1wWv` の一般化（`hb1 : 1 ≤ b` は要らない）。
-/
import GxF

namespace TRIO
namespace GxG

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ

def pre (b m : ℕ) : List TrioSeq := List.replicate m [((1, b + 1, 0) : ℕ × ℕ × ℕ)]

open Classical in
/-- `rise_rwordWv` の、中身の条件を `l2` だけに弱めた版。 -/
theorem rise_rwordWp (Y0 : TrioSeq) {v0 : ℕ} (a b k : ℕ) (hb : v0 ≤ b) {l : List TrioSeq} :
    ∀ (l2 l1 l3 : List TrioSeq), (∀ T ∈ l2, RawWv v0 T) → l = l1 ++ l2 ++ l3 →
      (List.range (rword a b l2).length).map (fun i =>
        ((entry (rword a b l2) 0 i + k, entry (rword a b l2) 1 i +
          (if le1 (MzR Y0 a b l) Y0.length (Y0.length + 1 + (rword a b l1).length + i)
            then k else 0), entry (rword a b l2) 2 i) : ℕ × ℕ × ℕ))
      = rword (a + k) (b + k) l2
  | [], _, _, _, _ => by simp [rword]
  | (T :: l2), l1, l3, hw, hl => by
      have hl' : l = (l1 ++ [T]) ++ l2 ++ l3 := by rw [hl]; simp
      have hl'' : l = l1 ++ T :: (l2 ++ l3) := by rw [hl]; simp
      have hT : RawWv v0 T := hw T (by simp)
      have ih := rise_rwordWp Y0 a b k hb l2 (l1 ++ [T]) l3
        (fun U hU => hw U (List.mem_cons_of_mem _ hU)) hl'
      rw [rword_cons, rword_cons, List.length_append, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · rw [← rise_rcol a b k T (fun t => le1 (MzR Y0 a b l) Y0.length
            (Y0.length + 1 + (rword a b l1).length + t))
            (by rw [hl'']; simpa using le1_zposR Y0 a b l1 (l2 ++ l3) T)
            (by intro t ht1 ht
                obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
                rw [hl'']
                refine not_le1_treeWv Y0 a b hb l1 (l2 ++ l3) hT.2 u ?_
                rw [rcol_length] at ht; omega)]
        apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        rw [Small.entry_append_left ht, Small.entry_append_left ht,
          Small.entry_append_left ht]
      · rw [← ih]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        rw [entry_append_right, entry_append_right, entry_append_right, rword_append,
          rword_singleton, List.length_append,
          show Y0.length + 1 + (rword a b l1).length + ((rcol a b T).length + i)
            = Y0.length + 1 + ((rword a b l1).length + (rcol a b T).length) + i from by omega]

open Classical in
theorem map_all_lift (X : TrioSeq) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i, i < X.length → P i) (k : ℕ) :
    (List.range X.length).map (fun i =>
      ((entry X 0 i + k, entry X 1 i + (if P i then k else 0), entry X 2 i) : ℕ × ℕ × ℕ))
      = X.map (fun p => ((p.1 + k, p.2.1 + k, p.2.2) : ℕ × ℕ × ℕ)) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < X.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [if_pos (hP i hi)]
  have eg : X.getD i (0, 0, 0) = X[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  show ((X.getD i (0, 0, 0)).1 + k, (X.getD i (0, 0, 0)).2.1 + k, (X.getD i (0, 0, 0)).2.2) = _
  rw [eg]

theorem rword_pre (a b m : ℕ) :
    rword a b (pre b m) = (List.range m).flatMap
      (fun _ => [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ), ((a + 2, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
  rw [pre, rword_replicate]
  apply List.flatMap_congr
  intro k _
  simp only [rcol, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> (first | rfl | omega | (dsimp only; omega) | simp)

theorem pre_lift (b k m : ℕ) :
    (rword 0 b (pre b m)).map (fun p => ((p.1 + k, p.2.1 + k, p.2.2) : ℕ × ℕ × ℕ))
      = rword k (b + k) (pre (b + k) m) := by
  rw [rword_pre, rword_pre, List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨Prod.ext ?_ (Prod.ext ?_ rfl), Prod.ext ?_ (Prod.ext ?_ rfl)⟩ <;>
    (first | rfl | omega | (dsimp only; omega) | simp)

theorem pre_row1 (b m : ℕ) : ∀ x ∈ rword 0 b (pre b m), x.2.1 = b + 1 := by
  intro x hx
  rw [rword_pre] at hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  obtain ⟨-, -, hx⟩ := hx
  rcases hx with rfl | rfl <;> rfl

open Classical in
theorem oper_z1p {v0 : ℕ} (b : ℕ) (hb : v0 ≤ b) (m : ℕ) {l : List TrioSeq}
    (hw : WOkWv v0 l) (n : ℕ) :
    ((((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l)) ++ [((1, b + 1, 1) : ℕ × ℕ × ℕ)])⟦n⟧
      = Dzf (fun a b => rword a b (pre b m ++ l)) 0 b n := by
  have h := oper_z1_mask [] 0 b (rword 0 b (pre b m ++ l)) (rword_ge 0 b _) n
  have eM : (((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l)) ++
      [((1, b + 1, 1) : ℕ × ℕ × ℕ)]
      = [] ++ (((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l) ++
        [((0 + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) := rfl
  rw [eM, h, List.nil_append]
  unfold Dzf
  apply List.flatMap_congr
  intro k _
  congr 1
  set M : TrioSeq := MzR [] 0 b (pre b m ++ l) with hM
  have hMeq : [] ++ (((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l) ++
      [((0 + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) = M := rfl
  rw [hMeq]
  -- 先頭の字は錐
  have hent1 : ∀ r j, j < (rword 0 b (pre b m ++ l)).length →
      entry M r (j + 1) = entry (rword 0 b (pre b m ++ l)) r j := by
    intro r j hj
    have h1 := entry_MzR_word [] 0 b (pre b m ++ l) r j hj
    rw [show j + 1 = ([] : TrioSeq).length + 1 + j by simp only [List.length_nil]; omega]
    exact h1
  have hMlen : M.length = (rword 0 b (pre b m ++ l)).length + 2 := by
    rw [hM, MzR_length]; simp only [List.length_nil]; omega
  have hr : ∀ q, 0 < q → q < M.length → entry M 0 0 < entry M 0 q := by
    intro q hq0 hq
    have h00 : entry M 0 0 = 0 := by
      have := entry_MzR_p [] 0 b (pre b m ++ l) 0
      simpa [entry] using this
    rw [h00]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rcases Nat.lt_or_ge q' (rword 0 b (pre b m ++ l)).length with hq' | hq'
    · rw [hent1 0 q' hq']
      have hmem : (rword 0 b (pre b m ++ l)).getD q' (0, 0, 0) ∈ rword 0 b (pre b m ++ l) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']
        exact List.getElem_mem _
      have := rword_ge 0 b _ _ hmem
      show 0 < ((rword 0 b (pre b m ++ l)).getD q' (0, 0, 0)).1
      omega
    · have hqe : q' = (rword 0 b (pre b m ++ l)).length := by omega
      rw [hqe, hM, MzR]
      have e : ([] : TrioSeq) ++ (((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l) ++
          [((0 + 1, b + 1, 1) : ℕ × ℕ × ℕ)])
          = (((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l)) ++
            [((0 + 1, b + 1, 1) : ℕ × ℕ × ℕ)] := rfl
      rw [e, show (rword 0 b (pre b m ++ l)).length + 1
        = (((0, b, 0) : ℕ × ℕ × ℕ) :: rword 0 b (pre b m ++ l)).length + 0 by simp,
        entry_append_right]
      simp [entry]
  have hlepre : ∀ i, i < (rword 0 b (pre b m)).length → le1 M 0 (0 + 1 + i) := by
    intro i hi
    rw [le1_zero_iff hr (by rw [hMlen, rword_append, List.length_append]; omega)]
    intro y hy hy0
    have hyle := rtg0_le hy
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have hy' : y' < (rword 0 b (pre b m)).length := by omega
    have h10 : entry M 1 0 = b := by
      have := entry_MzR_p [] 0 b (pre b m ++ l) 1
      simpa [entry] using this
    rw [h10, hent1 1 y' (by rw [rword_append, List.length_append]; omega), rword_append,
      Small.entry_append_left hy']
    have hmem : (rword 0 b (pre b m)).getD y' (0, 0, 0) ∈ rword 0 b (pre b m) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy']
      exact List.getElem_mem _
    have := pre_row1 b m _ hmem
    show b < ((rword 0 b (pre b m)).getD y' (0, 0, 0)).2.1
    omega
  show _ = rword (0 + k) (b + k) (pre (b + k) m ++ l)
  rw [rword_append 0 b (pre b m) l, rword_append (0 + k) (b + k) (pre (b + k) m) l,
    List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · have e1 : (List.range (rword 0 b (pre b m)).length).map (fun i =>
        ((entry (rword 0 b (pre b m) ++ rword 0 b l) 0 i + k,
          entry (rword 0 b (pre b m) ++ rword 0 b l) 1 i +
            (if le1 M ([] : TrioSeq).length (([] : TrioSeq).length + 1 + i) then k else 0),
          entry (rword 0 b (pre b m) ++ rword 0 b l) 2 i) : ℕ × ℕ × ℕ))
        = (List.range (rword 0 b (pre b m)).length).map (fun i =>
          ((entry (rword 0 b (pre b m)) 0 i + k,
            entry (rword 0 b (pre b m)) 1 i +
              (if le1 M 0 (0 + 1 + i) then k else 0),
            entry (rword 0 b (pre b m)) 2 i) : ℕ × ℕ × ℕ)) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [Small.entry_append_left hi, Small.entry_append_left hi, Small.entry_append_left hi]
      rfl
    rw [e1, map_all_lift (rword 0 b (pre b m)) (fun i => le1 M 0 (0 + 1 + i)) hlepre k,
      pre_lift]
    simp
  · have h2 := rise_rwordWp [] 0 b k hb (l := pre b m ++ l) l (pre b m) []
      (fun T hT => hw T hT) (by simp)
    rw [← hM] at h2
    rw [← h2]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    rw [entry_append_right, entry_append_right, entry_append_right,
      show ([] : TrioSeq).length + 1 + ((rword 0 b (pre b m)).length + i)
        = ([] : TrioSeq).length + 1 + (rword 0 b (pre b m)).length + i by omega]

#print axioms oper_z1p


/-! ## 先頭つきの語の閉包（GwZ の Bwv / GOKWv の写し。段 0 も含む） -/

def BwP (v0 m : ℕ) (l : List TrioSeq) : Prop :=
  ∀ v : ℕ, v0 ≤ v → rword 0 v (pre v m ++ l) ∈ Wstarv v

def GOKWP (v0 m : ℕ) (T : TrioSeq) : Prop :=
  ∀ l : List TrioSeq, WOkWv v0 l → BwP v0 m l → BwP v0 m (l ++ [T])

theorem DzfP_cons (m : ℕ) (l : List TrioSeq) (a b : ℕ) : ∀ n : ℕ,
    Dzf (fun a b => rword a b (pre b m ++ l)) a b (n + 1)
      = ((a, b, 0) : ℕ × ℕ × ℕ) ::
        (rword a b (pre b m ++ l) ++ Dzf (fun a b => rword a b (pre b m ++ l)) (a + 1) (b + 1) n)
  | 0 => by simp [Dzf]
  | (n + 1) => by
      rw [Dzf_succ, DzfP_cons m l a b n, Dzf_succ]
      have e1 : a + (n + 1) = a + 1 + n := by omega
      have e2 : b + (n + 1) = b + 1 + n := by omega
      rw [e1, e2]
      simp only [List.cons_append, List.append_assoc]

theorem DzfP_ge (m : ℕ) (l : List TrioSeq) (a b n : ℕ) :
    ∀ x ∈ Dzf (fun a b => rword a b (pre b m ++ l)) a b n, a ≤ x.1 := by
  intro x hx
  simp only [Dzf, List.mem_flatMap, List.mem_range, List.mem_cons] at hx
  obtain ⟨k, -, hx⟩ := hx
  rcases hx with rfl | hx
  · show a ≤ a + k; omega
  · have := rword_ge (a + k) (b + k) _ x hx
    omega

theorem DzfP_shift (m : ℕ) (l : List TrioSeq) (a b s n : ℕ) :
    shiftr01 s 0 (Dzf (fun a b => rword a b (pre b m ++ l)) a b n)
      = Dzf (fun a b => rword a b (pre b m ++ l)) (a + s) b n := by
  induction n with
  | zero => simp [Dzf, shiftr01]
  | succ n ih =>
      rw [Dzf_succ, Dzf_succ, shiftr01_append0, ih]
      congr 1
      rw [show ((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: rword (a + n) (b + n) (pre (b + n) m ++ l)
          = [((a + n, b + n, 0) : ℕ × ℕ × ℕ)] ++ rword (a + n) (b + n) (pre (b + n) m ++ l)
          from rfl, shiftr01_append0, shift_col, rword_shift]
      have e : a + n + s = a + s + n := by omega
      rw [e]
      rfl

theorem Dzf_memP {v0 m : ℕ} {l : List TrioSeq} (hB : BwP v0 m l) :
    ∀ n v, v0 ≤ v → ∀ a, 2 * v ≤ a →
      Dzf (fun a b => rword a b (pre b m ++ l)) 0 v n ∈ Wg a := by
  intro n
  induction n with
  | zero => intro v _ a _; exact Wg_nil a
  | succ n ih =>
      intro v hv a ha
      rw [DzfP_cons m l 0 v n]
      have hR : Dzf (fun a b => rword a b (pre b m ++ l)) (0 + 1) (v + 1) n
          ∈ Wg (2 * (v + 1)) := by
        have h := Wg_shift (ih (v + 1) (by omega) (2 * (v + 1)) le_rfl) 1
        rwa [DzfP_shift] at h
      have hge : ∀ p ∈ rword 0 v (pre v m ++ l) ++
          Dzf (fun a b => rword a b (pre b m ++ l)) (0 + 1) (v + 1) n, 1 ≤ p.1 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have := rword_ge 0 v _ p hp; omega
        · have := DzfP_ge m l (0 + 1) (v + 1) n p hp; omega
      have hhd : entry (Dzf (fun a b => rword a b (pre b m ++ l)) (0 + 1) (v + 1) n) 0 0 ≤ 1 := by
        cases n with
        | zero => simp [Dzf, entry]
        | succ k => rw [DzfP_cons]; simp [entry]
      have hrs : rsum (rword 0 v (pre v m ++ l))
          (Dzf (fun a b => rword a b (pre b m ++ l)) (0 + 1) (v + 1) n) := by
        intro p hp
        have := hge p hp
        omega
      exact hang_Wg (hB v hv) hR hrs (fun p hp => by have := hge p hp; omega) a ha

theorem Bw_snoczP {v0 m : ℕ} {l : List TrioSeq} (hw : WOkWv v0 l) (hB : BwP v0 m l) :
    BwP v0 m (l ++ [[]]) := by
  intro v hv _ a ha
  have e : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ (l ++ [[]])))
      = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ++
        [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
    rw [← List.append_assoc, rword_append, rword_singleton, rcol_nil]; rfl
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_zroot v (fun x hx => by
    have := rword_ge 0 v _ x hx; omega), fun n _ => ?_⟩))
  rw [oper_z1p v hv m hw n]
  exact Dzf_memP hB n v hv a ha

theorem Bw_repP {v0 m : ℕ} {T : TrioSeq} (hT : RawWv v0 T) (hG : GOKWP v0 m T)
    {l : List TrioSeq} (hw : WOkWv v0 l) (hB : BwP v0 m l) :
    ∀ n, BwP v0 m (l ++ List.replicate n T)
  | 0 => by simpa using hB
  | (n + 1) => by
      have hwn : WOkWv v0 (l ++ List.replicate n T) := by
        refine WOkWv_append hw ?_
        intro U hU
        rw [List.eq_of_mem_replicate hU]; exact hT
      have h := hG (l ++ List.replicate n T) hwn (Bw_repP hT hG hw hB n)
      have e : l ++ List.replicate n T ++ [T] = l ++ List.replicate (n + 1) T := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

theorem Bw_snoc_operP {v0 m : ℕ} {l : List TrioSeq} {T : TrioSeq}
    (hlen : 2 ≤ T.length) (hp : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hIH : ∀ n, 1 ≤ n → BwP v0 m (l ++ [T⟦n⟧])) : BwP v0 m (l ++ [T]) := by
  intro v hv _ a ha
  rw [← List.append_assoc, rword0_snoc]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_append_shift _ T 1
    (by rintro rfl; simp at hlen) hp, fun n hn => ?_⟩))
  rw [oper_shift _ T 1 n hlen hp, ← rword0_snoc, List.append_assoc]
  exact hIH n hn v hv (argOK_rword v _) a ha

theorem Bw_snoc_flatP {v0 m : ℕ} {l : List TrioSeq} {T : TrioSeq} {x : ℕ} (hx : 1 ≤ x)
    (hTx : ∀ y ∈ T, x ≤ y.1) (hIH : ∀ n, 1 ≤ n → BwP v0 m (l ++ List.replicate n T)) :
    BwP v0 m (l ++ [T ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]]) := by
  intro v hv _ a ha
  have hhead : entry (rcol 0 v T) 0 0 < 0 + 1 + x := by
    show 0 + 1 < 0 + 1 + x; omega
  have htail : ∀ r, 1 ≤ r → r < (rcol 0 v T).length → 0 + 1 + x ≤ entry (rcol 0 v T) 0 r := by
    intro r hr1 hrl
    obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    have hu : u < T.length := by rw [rcol_length] at hrl; omega
    rw [entry_rcol_succ, entry0_shiftr01 hu]
    have hmem : T.getD u (0, 0, 0) ∈ T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
      exact List.getElem_mem hu
    have := hTx _ hmem
    show 0 + 1 + x ≤ (T.getD u (0, 0, 0)).1 + (0 + 1)
    omega
  have e : (((0, v, 0) : ℕ × ℕ × ℕ) ::
      rword 0 v (pre v m ++ (l ++ [T ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]])))
      = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ++ rcol 0 v T
        ++ [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)] := by
    have e1 : shiftr01 (0 + 1) 0 [((x, 0, 0) : ℕ × ℕ × ℕ)]
        = [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl)
        (Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) rfl)
    rw [← List.append_assoc, rword_append, rword_singleton, rcol, rcol, shiftr01_append0, e1]
    simp [List.append_assoc]
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inl ?_), fun n hn => ?_⟩))
  · unfold lev
    rw [show ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ++ rcol 0 v T
        ++ [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
        = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ++ rcol 0 v T).length + 0
        from by simp; omega,
      entry_append_right, entry_append_right]
    simp [entry]
  · rw [oper_snoc00'' _ (rcol_ne 0 v T) hhead htail n]
    have e2 : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ++
        (List.range n).flatMap (fun _ => rcol 0 v T)
        = ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ (l ++ List.replicate n T)) := by
      rw [← List.append_assoc, rword_append 0 v (pre v m ++ l) (List.replicate n T),
        rword_replicate]; simp
    rw [e2]
    exact hIH n hn v hv (argOK_rword v _) a ha

theorem Bw_snoc_orphP {v0 m : ℕ} {l : List TrioSeq} {T0 : TrioSeq} {h j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ v0)
    (hnp : ¬ hasParent (T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hprev : ∀ z ∈ Wg (2 * j - 1), based z → BwP v0 m (l ++ [T0 ++ shiftr01 h 0 z])) :
    BwP v0 m (l ++ [T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]]) := by
  intro v hv _ a ha
  rw [← List.append_assoc, rword0_snoc]
  obtain ⟨P, hP⟩ : ∃ P : TrioSeq,
      P = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ++
        [((1, v + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨hPlen, hP0, hPL1, hPL0, hPmid⟩ := P_facts v (pre v m ++ l)
  rw [← hP] at hPlen hP0 hPL1 hPL0 hPmid ⊢
  have hnp' := noParent_letter (P := P) (T := T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) (v := v) (j := j)
    (by omega) hPlen hP0 hPL1 hPL0 hPmid (by simp)
    (by
      rw [show (T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1 = T0.length + 0 by simp,
        entry_append_right]
      rfl) hnp
  have eS : shiftr01 1 0 (T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
      = shiftr01 1 0 T0 ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [shiftr01_append0, shift_col]
  have hidx : P.length + ((T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1)
      = (P ++ shiftr01 1 0 T0).length := by simp [shiftr01]
  rw [eS, hidx, ← List.append_assoc] at hnp'
  rw [eS, ← List.append_assoc]
  have hL : ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]).length - 1
      = (P ++ shiftr01 1 0 T0).length := by simp
  have eL : ∀ r, entry ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) r
      (P ++ shiftr01 1 0 T0).length = entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    simpa using entry_append_right (P ++ shiftr01 1 0 T0) [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0
  have e1 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 1 0 = j := rfl
  have e2 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 2 0 = 0 := rfl
  have e0 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 0 0 = h + 1 := rfl
  have hsr : srow ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)])
      (P ++ shiftr01 1 0 T0).length = 1 := by
    unfold srow; rw [eL, eL, e2, e1]; simp; omega
  have hdom : domT ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) (2 * j - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [hL, eL, eL, e1, e2]; omega
    · rw [hL, hsr]; exact hnp'
  refine A1g_intro (Or.inr (Or.inr ⟨2 * j - 1, by omega, hdom, by rw [hL, eL, e2],
    fun z hz hbz => ?_⟩))
  have hg : graft ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) z
      = P ++ shiftr01 1 0 (T0 ++ shiftr01 h 0 z) := by
    rw [graft_eq_shift, List.dropLast_concat, hL, eL, e0, shiftr01_append0, shiftr01_add0,
      List.append_assoc]
  rw [hg, hP, ← rword0_snoc, List.append_assoc]
  exact hprev z hz hbz v hv (argOK_rword v _) a ha

theorem GOKWP_of_Wg {v0 : ℕ} (m : ℕ) :
    ∀ T ∈ Wg (2 * v0), (∀ x ∈ T, 1 ≤ x.1) → GOKWP v0 m T := by
  have key : Wg (2 * v0) ⊆ {T : TrioSeq | T ∈ Wg (2 * v0) ∧
      ((∀ x ∈ T, 1 ≤ x.1) → GOKWP v0 m T)} := by
    refine A2g' ?_
    intro T hA
    have hTW : T ∈ Wg (2 * v0) := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hTW, ?_⟩
    intro hge l hw hB
    by_cases hTnil : T = []
    · subst hTnil; exact Bw_snoczP hw hB
    have hTlen : 0 < T.length := List.length_pos_iff.mpr hTnil
    have hdlW : T.dropLast ∈ Wg (2 * v0) := Wg_dropLast hTW
    have hdlRaw : RawWv v0 T.dropLast := ⟨fun x hx => hge x (List.dropLast_subset _ hx),
      Wg_RiseOkv hdlW⟩
    set c := T.getLast hTnil with hc
    have hsplit : T = T.dropLast ++ [c] := (List.dropLast_append_getLast hTnil).symm
    have hclast : ∀ r, entry T r (T.length - 1) = entry [c] r 0 := by
      intro r
      have h := entry_append_right T.dropLast [c] r 0
      rw [← hsplit] at h
      rw [show T.length - 1 = T.dropLast.length + 0 by simp]
      exact h
    have eT : ∀ r i, i < T.dropLast.length → entry T r i = entry T.dropLast r i := by
      intro r i hi
      have h := Small.entry_append_left (P := T.dropLast) (B := [c]) (i := r) hi
      rw [← hsplit] at h
      exact h
    have hcmem : c ∈ T := List.getLast_mem hTnil
    have hc1 : 1 ≤ c.1 := hge c hcmem
    have hflat : c.2.1 = 0 → c.2.2 = 0 → (∀ y ∈ T.dropLast, c.1 ≤ y.1) →
        GOKWP v0 m T.dropLast → BwP v0 m (l ++ [T]) := by
      intro hc10 hc20 hTx hGdl
      have hceq : c = ((c.1, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc10 hc20)
      rw [hsplit, hceq]
      exact Bw_snoc_flatP hc1 hTx (fun n _ => Bw_repP hdlRaw hGdl hw hB n)
    have hflat1 : T.length = 1 → c.2.1 = 0 → c.2.2 = 0 → BwP v0 m (l ++ [T]) := by
      intro hT1 hc10 hc20
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine hflat hc10 hc20 (by rw [hdl]; simp) ?_
      rw [hdl]; exact fun l' hw' hB' => Bw_snoczP hw' hB'
    have hlev0 : lev T (T.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
    · have hT1 : T.length = 1 := by omega
      have hz : lev T (T.length - 1) = 0 := by rw [hT1]; exact hw0
      exact hflat1 hT1 (hlev0 hz).1 (hlev0 hz).2
    · by_cases hlen2 : 2 ≤ T.length
      · by_cases hp : hasParent T (srow T (T.length - 1)) (T.length - 1)
        · exact Bw_snoc_operP hlen2 hp (fun n hn =>
            (hop n hn).2 (fun x hx => oper_mem_ge (c := 1) hge x hx) l hw hB)
        · have hz : lev T (T.length - 1) = 0 := by
            rcases natDom_iff.mp hnat with h | h
            · exact h
            · exact absurd h hp
          have hsr : srow T (T.length - 1) = 0 := by
            have := hz
            unfold srow
            unfold lev at this
            rw [if_neg (by omega), if_neg (by omega)]
          rw [hsr] at hp
          have hTx : ∀ y ∈ T.dropLast, c.1 ≤ y.1 := by
            intro y hy
            by_contra hlt
            push Not at hlt
            obtain ⟨k, hk, hky⟩ := List.getElem_of_mem hy
            apply hp
            refine (Wset.hasParent_zero_iff (by omega)).mpr ⟨k, by simp at hk; omega, ?_⟩
            have e1 : entry T 0 k = y.1 := by
              rw [eT 0 k hk]
              show (T.dropLast.getD k (0, 0, 0)).1 = y.1
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hky]
            rw [e1, hclast 0]
            exact hlt
          have hGdl : GOKWP v0 m T.dropLast := by
            have h1 := (hop 1 le_rfl).2 (fun x hx => oper_mem_ge (c := 1) hge x hx)
            rwa [oper_one_eq_dropLast (by omega)] at h1
          exact hflat (hlev0 hz).1 (hlev0 hz).2 hTx hGdl
      · have hT1 : T.length = 1 := by omega
        have hz : lev T (T.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exfalso
            rw [hT1] at h
            obtain ⟨j0, hj0, -⟩ := h
            exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        exact hflat1 hT1 (hlev0 hz).1 (hlev0 hz).2
    · have hlev := hd.1
      unfold lev at hlev
      have h20' : entry T 2 (T.length - 1) = 0 := h20
      have hj1 : 1 ≤ entry T 1 (T.length - 1) := by omega
      have hjv : entry T 1 (T.length - 1) ≤ v0 := by omega
      have hm' : m' = 2 * entry T 1 (T.length - 1) - 1 := by omega
      subst hm'
      have hsr : srow T (T.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent T 1 (T.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc1' : c.2.1 = entry T 1 (T.length - 1) := by
        have := hclast 1; exact this.symm
      have hc20 : c.2.2 = 0 := by
        have := hclast 2; rw [h20'] at this; exact this.symm
      have hTeq : T = T.dropLast ++ [((c.1, entry T 1 (T.length - 1), 0) : ℕ × ℕ × ℕ)] := by
        have hceq : c = ((c.1, entry T 1 (T.length - 1), 0) : ℕ × ℕ × ℕ) :=
          Prod.ext rfl (Prod.ext hc1' hc20)
        rw [← hceq]; exact hsplit
      have hgr' := hgr
      have hnp' := hnp
      generalize hjdef : entry T 1 (T.length - 1) = j at hj1 hjv hTeq hgr' hnp'
      rw [hTeq] at hnp'
      rw [hTeq]
      refine Bw_snoc_orphP hj1 hjv (by simpa using hnp') ?_
      intro z hz hbz
      have h1 := (hgr' z hz hbz).2
      have e : graft T z = T.dropLast ++ shiftr01 c.1 0 z := by
        rw [graft_eq_shift, hclast 0]
        rfl
      rw [e] at h1
      refine h1 ?_ l hw hB
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hge x (List.dropLast_subset _ hx)
      · simp only [shiftr01, List.mem_map] at hx
        obtain ⟨p, -, rfl⟩ := hx
        dsimp only; omega
  intro T hT hge
  exact (key hT).2 hge

#print axioms GOKWP_of_Wg

end GxG
end TRIO
