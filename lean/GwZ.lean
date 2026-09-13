/-
GwZ.lean: `GwU` の `GOKW` を段 `v0` に一般化する（字の中身が根とタイの行 1 を持ってよい）。

中身の条件 `RiseOkv v0 T`: 行 1 > v0 の列は、中身の中に行 1 ≤ v0 の行 0 祖先を持つ。
頭の行 1 が `b ≥ v0` なら、中身の列は頭の行 1 の子孫にならない（頭の潰れで持ち上がらない）。
第 1 部: `Wg (2 v0)` の元は `RiseOkv v0`、頭の潰れの展開 `oper_z1wWv`。
-/
import GwY

namespace TRIO
namespace GwZ

open Wset
open Small
open GwS
open Gw
open GwU

/-! ## 段 v0 の中身の条件 -/

def RiseOkv (v0 : ℕ) (T : TrioSeq) : Prop :=
  ∀ u, u < T.length → v0 + 1 ≤ entry T 1 u →
    ∃ k, k < u ∧ Relation.ReflTransGen (nextrel0 T) k u ∧ entry T 1 k ≤ v0

def RawWv (v0 : ℕ) (T : TrioSeq) : Prop := (∀ x ∈ T, 1 ≤ x.1) ∧ RiseOkv v0 T

def WOkWv (v0 : ℕ) (l : List TrioSeq) : Prop := ∀ T ∈ l, RawWv v0 T

theorem WOkWv_append {v0 : ℕ} {l1 l2 : List TrioSeq} (h1 : WOkWv v0 l1) (h2 : WOkWv v0 l2) :
    WOkWv v0 (l1 ++ l2) := by
  intro T hT
  rcases List.mem_append.mp hT with h | h
  · exact h1 T h
  · exact h2 T h

theorem WOkWv_singleton {v0 : ℕ} {T : TrioSeq} (hT : RawWv v0 T) : WOkWv v0 [T] := by
  intro U hU
  rw [List.mem_singleton.mp hU]; exact hT

theorem RawWv_nil (v0 : ℕ) : RawWv v0 [] := ⟨by simp, fun u hu => by simp at hu⟩

/-- `Wg (2 v0)` の木では、行 1 > v0 の列は必ず行 1 ≤ v0 の行 0 祖先を持つ。 -/
theorem Wg_RiseOkv {v0 : ℕ} {T : TrioSeq} (h : T ∈ Wg (2 * v0)) : RiseOkv v0 T := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu h2
    set S := T.take (u + 1) with hS
    have hSW : S ∈ Wg (2 * v0) := Wg_take T.length T le_rfl h (u + 1)
    have hSlen : S.length = u + 1 := by simp [hS]; omega
    have eT : T = S ++ T.drop (u + 1) := (List.take_append_drop (u + 1) T).symm
    have hSe : ∀ r j, j < u + 1 → entry S r j = entry T r j := by
      intro r j hj
      conv_rhs => rw [eT]
      rw [Small.entry_append_left (by rw [hSlen]; exact hj)]
    have hA : Aopg Wg (2 * v0) (Wg (2 * v0)) S := by
      have h' := hSW
      rw [← A1g (2 * v0)] at h'
      exact h'
    have hlast : S.length - 1 = u := by omega
    have hS1 : v0 + 1 ≤ entry S 1 u := by rw [hSe 1 u (by omega)]; exact h2
    have hanc : ∃ e, e < u ∧ Relation.ReflTransGen (nextrel0 S) e u ∧
        entry S 1 e < entry S 1 u := by
      rcases hA with ⟨hl, hw⟩ | ⟨hn, -⟩ | ⟨m, hm, hd, -, -⟩
      · exfalso
        have hu0 : u = 0 := by omega
        subst hu0
        unfold lev at hw
        omega
      · rcases natDom_iff.mp hn with hz | hp
        · exfalso; rw [hlast] at hz; unfold lev at hz; omega
        · rw [hlast] at hp
          by_cases h2pos : 0 < entry S 2 u
          · have hsr : srow S u = 2 := by unfold srow; rw [if_pos h2pos]
            rw [hsr] at hp
            have hn2 := parent_nextR hp
            unfold nextR at hn2
            rw [if_neg (by omega), if_neg (by omega)] at hn2
            obtain ⟨-, -, hpu, -, hle1, -⟩ := hn2
            obtain ⟨-, -, hch⟩ := hle1
            rcases Relation.ReflTransGen.cases_tail hch with heq | ⟨e, -, hen⟩
            · omega
            · exact ⟨e, hen.2.2.1, hen.2.2.2.2.1.2.2, hen.2.2.2.1⟩
          · have hsr : srow S u = 1 := by
              unfold srow; rw [if_neg h2pos, if_pos (by omega)]
            rw [hsr] at hp
            have hn1 := parent_nextR hp
            unfold nextR at hn1
            rw [if_neg (by omega), if_pos rfl] at hn1
            exact ⟨_, hn1.2.2.1, hn1.2.2.2.2.1.2.2, hn1.2.2.2.1⟩
      · exfalso
        have := hd.1
        rw [hlast] at this
        unfold lev at this
        omega
    obtain ⟨e, heu, hch, he1⟩ := hanc
    have hchT : Relation.ReflTransGen (nextrel0 T) e u := by
      rw [eT]
      exact rtg0_append_left hch (by omega)
    rw [hSe 1 e (by omega), hSe 1 u (by omega)] at he1
    by_cases he2 : entry T 1 e ≤ v0
    · exact ⟨e, heu, hchT, he2⟩
    · obtain ⟨k, hke, hkch, hk1⟩ := ih e heu (by omega) (by omega)
      exact ⟨k, by omega, hkch.trans hchT, hk1⟩

/-! ## 頭の潰れ（中身は持ち上がらない） -/

theorem not_le1_treeWv (Y0 : TrioSeq) {v0 : ℕ} (a b : ℕ) (hb : v0 ≤ b) (l1 l3 : List TrioSeq)
    {T : TrioSeq} (hT : RiseOkv v0 T) (u : ℕ) (hu : u < T.length) :
    ¬ le1 (MzR Y0 a b (l1 ++ T :: l3)) Y0.length
      (Y0.length + 1 + (rword a b l1).length + (u + 1)) := by
  set M := MzR Y0 a b (l1 ++ T :: l3) with hM
  have hlenw : (rword a b (l1 ++ T :: l3)).length
      = (rword a b l1).length + (rcol a b T).length + (rword a b l3).length := by
    rw [rword_append, rword_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (rword a b (l1 ++ T :: l3)).length + 1 := by
    rw [hM, MzR_length]
  have hcl := rcol_length a b T
  have hent : ∀ (r t : ℕ), t < T.length →
      entry M r (Y0.length + 1 + (rword a b l1).length + 1 + t)
        = entry (shiftr01 (a + 1) 0 T) r t := by
    intro r t ht
    have h := entry_rword_pos Y0 a b l1 l3 T r (t + 1) (by omega)
    rw [rcol, entry_cons_succ] at h
    rw [hM, show Y0.length + 1 + (rword a b l1).length + 1 + t
      = Y0.length + 1 + (rword a b l1).length + (t + 1) from by omega]
    exact h
  have hp1 : entry M 1 Y0.length = b := by rw [hM, entry_MzR_p]; simp [entry]
  intro hle
  have hlt := le1_row1_lt hle (by omega)
  rw [show Y0.length + 1 + (rword a b l1).length + (u + 1)
      = Y0.length + 1 + (rword a b l1).length + 1 + u from by omega] at hle hlt
  rw [hent 1 u hu, entry1_shiftr01, hp1] at hlt
  obtain ⟨k, hku, hch, hk1⟩ := hT u hu (by omega)
  have hkc : le0 M (Y0.length + 1 + (rword a b l1).length + 1 + k)
      (Y0.length + 1 + (rword a b l1).length + 1 + u) := by
    refine ⟨by omega, by omega, GwS.rtg0_block (d := a + 1) (by omega) (fun t ht => ?_) hch hu⟩
    rw [hent 0 t ht, entry0_shiftr01 ht]
  refine not_le1_blocked hle _ (by omega) hkc ?_
  rw [hent 1 k (by omega), entry1_shiftr01, hp1]; omega

open Classical in
theorem rise_rwordWv (Y0 : TrioSeq) {v0 : ℕ} (a b k : ℕ) (hb : v0 ≤ b) (hb1 : 1 ≤ b)
    {l : List TrioSeq} (hw : WOkWv v0 l) :
    ∀ (l2 l1 l3 : List TrioSeq), l = l1 ++ l2 ++ l3 →
      (List.range (rword a b l2).length).map (fun i =>
        ((entry (rword a b l2) 0 i + k, entry (rword a b l2) 1 i +
          (if le1 (MzR Y0 a b l) Y0.length (Y0.length + 1 + (rword a b l1).length + i)
            then k else 0), entry (rword a b l2) 2 i) : ℕ × ℕ × ℕ))
      = rword (a + k) (b + k) l2
  | [], _, _, _ => by simp [rword]
  | (T :: l2), l1, l3, hl => by
      have hl' : l = (l1 ++ [T]) ++ l2 ++ l3 := by rw [hl]; simp
      have hl'' : l = l1 ++ T :: (l2 ++ l3) := by rw [hl]; simp
      have hT : RawWv v0 T := hw T (by rw [hl]; simp)
      have ih := rise_rwordWv Y0 a b k hb hb1 hw l2 (l1 ++ [T]) l3 hl'
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
theorem oper_z1wWv (Y0 : TrioSeq) {v0 : ℕ} (a b : ℕ) (hb : v0 ≤ b) (hb1 : 1 ≤ b)
    {l : List TrioSeq} (hw : WOkWv v0 l) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf (fun a b => rword a b l) a b n := by
  rw [oper_z1_mask Y0 a b (rword a b l) (rword_ge a b l) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have := rise_rwordWv Y0 a b k hb hb1 hw l [] [] (by simp)
  simpa [rword, MzR] using this

#print axioms oper_z1wWv

/-! ## 段 v0 の `Bw` -/

def Bwv (v0 : ℕ) (l : List TrioSeq) : Prop := ∀ v : ℕ, v0 ≤ v → rword 0 v l ∈ Wstarv v

def GOKWv (v0 : ℕ) (T : TrioSeq) : Prop :=
  ∀ l : List TrioSeq, WOkWv v0 l → Bwv v0 l → Bwv v0 (l ++ [T])

theorem Bwv_nil (v0 : ℕ) : Bwv v0 [] := by
  intro v _ _ a ha
  show (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v ([] : List TrioSeq)) ∈ Wg a
  rw [rword_nil]
  exact Wg_mono ha (Om_mem_Wg v)

theorem Dzf_memv {v0 : ℕ} {l : List TrioSeq} (hB : Bwv v0 l) :
    ∀ n v, v0 ≤ v → ∀ a, 2 * v ≤ a → Dzf (fun a b => rword a b l) 0 v n ∈ Wg a := by
  intro n
  induction n with
  | zero => intro v _ a _; exact Wg_nil a
  | succ n ih =>
      intro v hv a ha
      rw [Dzf_cons l 0 v n]
      have hR : Dzf (fun a b => rword a b l) (0 + 1) (v + 1) n ∈ Wg (2 * (v + 1)) := by
        have h := Wg_shift (ih (v + 1) (by omega) (2 * (v + 1)) le_rfl) 1
        rwa [Dzf_shift] at h
      have hge : ∀ p ∈ rword 0 v l ++ Dzf (fun a b => rword a b l) (0 + 1) (v + 1) n,
          1 ≤ p.1 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have := rword_ge 0 v l p hp; omega
        · have := Dzf_ge l (0 + 1) (v + 1) n p hp; omega
      have hhd : entry (Dzf (fun a b => rword a b l) (0 + 1) (v + 1) n) 0 0 ≤ 1 := by
        cases n with
        | zero => simp [Dzf, entry]
        | succ k => rw [Dzf_cons]; simp [entry]
      have hrs : rsum (rword 0 v l) (Dzf (fun a b => rword a b l) (0 + 1) (v + 1) n) := by
        intro p hp
        have := hge p hp
        omega
      exact hang_Wg (hB v hv) hR hrs (fun p hp => by have := hge p hp; omega) a ha

theorem Bw_snoczv {v0 : ℕ} (hv0 : 1 ≤ v0) {l : List TrioSeq} (hw : WOkWv v0 l)
    (hB : Bwv v0 l) : Bwv v0 (l ++ [[]]) := by
  intro v hv _ a ha
  have e : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [[]]))
      = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
    rw [rword_append, rword_singleton, rcol_nil]; rfl
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_zroot v (fun x hx => by
    have := rword_ge 0 v l x hx; omega), fun n _ => ?_⟩))
  have h := oper_z1wWv [] 0 v hv (by omega) hw n
  simp only [List.nil_append] at h
  rw [show ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])
      = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l ++ [((0 + 1, v + 1, 1) : ℕ × ℕ × ℕ)]) from rfl, h]
  exact Dzf_memv hB n v hv a ha

theorem Bw_repv {v0 : ℕ} {T : TrioSeq} (hT : RawWv v0 T) (hG : GOKWv v0 T) {l : List TrioSeq}
    (hw : WOkWv v0 l) (hB : Bwv v0 l) : ∀ n, Bwv v0 (l ++ List.replicate n T)
  | 0 => by simpa using hB
  | (n + 1) => by
      have hwn : WOkWv v0 (l ++ List.replicate n T) := by
        refine WOkWv_append hw ?_
        intro U hU
        rw [List.eq_of_mem_replicate hU]; exact hT
      have h := hG (l ++ List.replicate n T) hwn (Bw_repv hT hG hw hB n)
      have e : l ++ List.replicate n T ++ [T] = l ++ List.replicate (n + 1) T := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

theorem Bw_snoc_operv {v0 : ℕ} {l : List TrioSeq} {T : TrioSeq}
    (hlen : 2 ≤ T.length) (hp : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hIH : ∀ n, 1 ≤ n → Bwv v0 (l ++ [T⟦n⟧])) : Bwv v0 (l ++ [T]) := by
  intro v hv _ a ha
  rw [rword0_snoc]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_append_shift _ T 1
    (by rintro rfl; simp at hlen) hp, fun n hn => ?_⟩))
  rw [oper_shift _ T 1 n hlen hp, ← rword0_snoc]
  exact hIH n hn v hv (argOK_rword v _) a ha

theorem Bw_snoc_flatv {v0 : ℕ} {l : List TrioSeq} {T : TrioSeq} {x : ℕ} (hx : 1 ≤ x)
    (hTx : ∀ y ∈ T, x ≤ y.1) (hIH : ∀ n, 1 ≤ n → Bwv v0 (l ++ List.replicate n T)) :
    Bwv v0 (l ++ [T ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]]) := by
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
  have e : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [T ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]]))
      = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ rcol 0 v T
        ++ [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)] := by
    have e1 : shiftr01 (0 + 1) 0 [((x, 0, 0) : ℕ × ℕ × ℕ)]
        = [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl)
        (Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) rfl)
    rw [rword_append, rword_singleton, rcol, rcol, shiftr01_append0, e1]
    simp [List.append_assoc]
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inl ?_), fun n hn => ?_⟩))
  · unfold lev
    rw [show ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ rcol 0 v T
        ++ [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
        = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ rcol 0 v T).length + 0 from by simp; omega,
      entry_append_right, entry_append_right]
    simp [entry]
  · rw [oper_snoc00'' _ (rcol_ne 0 v T) hhead htail n]
    have e2 : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++
        (List.range n).flatMap (fun _ => rcol 0 v T)
        = ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ List.replicate n T) := by
      rw [rword_append, rword_replicate]; simp
    rw [e2]
    exact hIH n hn v hv (argOK_rword v _) a ha

/-! ## 段 v0 の孤児 `(h, j, 0)`（j ≤ v0）: 根でも字の頭でも生き返らない -/

/-- 台座 `P`（根の行 1 は `v`、最後は字の頭 `(1,v+1,1)`、間は高さ ≥ 1）の後ろの中身 `T` の
末尾が `T` の中で行 1 の親を持たず、行 1 が `j ≤ v` なら、全体でも親を持たない。 -/
theorem noParent_letter {P T : TrioSeq} {v j : ℕ} (hj : j ≤ v) (hPlen : 1 ≤ P.length)
    (hP0 : entry P 1 0 = v) (hPL1 : entry P 1 (P.length - 1) = v + 1)
    (hPL0 : entry P 0 (P.length - 1) = 1)
    (hPmid : ∀ k, 0 < k → k < P.length - 1 → 1 ≤ entry P 0 k)
    (hTne : T ≠ []) (hlast : entry T 1 (T.length - 1) = j)
    (hnp : ¬ hasParent T 1 (T.length - 1)) :
    ¬ hasParent (P ++ shiftr01 1 0 T) 1 (P.length + (T.length - 1)) := by
  have hTl : 0 < T.length := List.length_pos_iff.mpr hTne
  rintro ⟨k, hk, -⟩
  by_cases hkP : P.length ≤ k
  · obtain ⟨q, rfl⟩ : ∃ q, k = P.length + q := ⟨k - P.length, by omega⟩
    have h1 := (nextR_append_right P (shiftr01 1 0 T) 1 q (T.length - 1)).1 hk
    have h2 := nextR_shiftr01.mp h1
    have h3 : nextrel1 T q (T.length - 1) := by
      unfold nextR at h2; rwa [if_neg (by omega), if_pos rfl] at h2
    exact hnp (H12Export.hasParent1_of_le0_witness (by omega) h3.2.2.2.2.1.2.2 h3.2.2.2.1)
  · have hk' : nextrel1 (P ++ shiftr01 1 0 T) k (P.length + (T.length - 1)) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, hk1, hle0, -⟩ := hk'
    have hkP' : k < P.length := by omega
    have eL1 : entry (P ++ shiftr01 1 0 T) 1 (P.length + (T.length - 1)) = j := by
      rw [entry_append_right, entry1_shiftr01, hlast]
    rw [Small.entry_append_left hkP', eL1] at hk1
    by_cases hk0 : k = 0
    · subst hk0; omega
    · by_cases hkL : k = P.length - 1
      · rw [hkL, hPL1] at hk1; omega
      · have hrec := rtg0_rec hle0.2.2 (P.length - 1) (by omega) (by omega)
        rw [Small.entry_append_left hkP', Small.entry_append_left (by omega), hPL0] at hrec
        have := hPmid k (by omega) (by omega)
        omega

theorem P_facts (v : ℕ) (l : List TrioSeq) :
    let P := (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]
    1 ≤ P.length ∧ entry P 1 0 = v ∧ entry P 1 (P.length - 1) = v + 1 ∧
      entry P 0 (P.length - 1) = 1 ∧ (∀ k, 0 < k → k < P.length - 1 → 1 ≤ entry P 0 k) := by
  intro P
  have hlen : P.length = (rword 0 v l).length + 2 := by simp [P]
  have eL : ∀ r, entry P r (P.length - 1) = entry [((1, v + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    have h := entry_append_right (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l)
      [((1, v + 1, 1) : ℕ × ℕ × ℕ)] r 0
    rw [show P.length - 1 = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l)).length + 0 from by
      simp [P]]
    exact h
  refine ⟨by omega, ?_, by rw [eL]; rfl, by rw [eL]; rfl, ?_⟩
  · show entry ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 1 0 = v
    rw [Small.entry_append_left (by simp)]
    rfl
  · intro k hk0 hk
    obtain ⟨u, rfl⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
    have hu : u < (rword 0 v l).length := by omega
    show 1 ≤ entry ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 0
      (u + 1)
    rw [Small.entry_append_left (by simp; omega), entry_cons_succ]
    have hmem : (rword 0 v l).getD u (0, 0, 0) ∈ rword 0 v l := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
      exact List.getElem_mem _
    have := rword_ge 0 v l _ hmem
    exact this

theorem Bw_snoc_orphv {v0 : ℕ} {l : List TrioSeq} {T0 : TrioSeq} {h j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ v0)
    (hnp : ¬ hasParent (T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hprev : ∀ z ∈ Wg (2 * j - 1), based z → Bwv v0 (l ++ [T0 ++ shiftr01 h 0 z])) :
    Bwv v0 (l ++ [T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]]) := by
  intro v hv _ a ha
  rw [rword0_snoc]
  obtain ⟨P, hP⟩ : ∃ P : TrioSeq,
      P = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨hPlen, hP0, hPL1, hPL0, hPmid⟩ := P_facts v l
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
    intro r; simpa using entry_append_right (P ++ shiftr01 1 0 T0) [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0
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
  rw [hg, hP, ← rword0_snoc]
  exact hprev z hz hbz v hv (argOK_rword v _) a ha

/-! ## ★★★★★ 本体: `Wg (2 v0)` の中身は根の語の最後に継げる -/

theorem GOKWv_of_Wg {v0 : ℕ} (hv0 : 1 ≤ v0) :
    ∀ T ∈ Wg (2 * v0), (∀ x ∈ T, 1 ≤ x.1) → GOKWv v0 T := by
  have key : Wg (2 * v0) ⊆ {T : TrioSeq | T ∈ Wg (2 * v0) ∧
      ((∀ x ∈ T, 1 ≤ x.1) → GOKWv v0 T)} := by
    refine A2g' ?_
    intro T hA
    have hTW : T ∈ Wg (2 * v0) := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hTW, ?_⟩
    intro hge l hw hB
    by_cases hTnil : T = []
    · subst hTnil; exact Bw_snoczv hv0 hw hB
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
        GOKWv v0 T.dropLast → Bwv v0 (l ++ [T]) := by
      intro hc10 hc20 hTx hGdl
      have hceq : c = ((c.1, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc10 hc20)
      rw [hsplit, hceq]
      exact Bw_snoc_flatv hc1 hTx (fun n _ => Bw_repv hdlRaw hGdl hw hB n)
    have hflat1 : T.length = 1 → c.2.1 = 0 → c.2.2 = 0 → Bwv v0 (l ++ [T]) := by
      intro hT1 hc10 hc20
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine hflat hc10 hc20 (by rw [hdl]; simp) ?_
      rw [hdl]; exact fun l' hw' hB' => Bw_snoczv hv0 hw' hB'
    have hlev0 : lev T (T.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, h20, hgr⟩
    · have hT1 : T.length = 1 := by omega
      have hz : lev T (T.length - 1) = 0 := by rw [hT1]; exact hw0
      exact hflat1 hT1 (hlev0 hz).1 (hlev0 hz).2
    · by_cases hlen2 : 2 ≤ T.length
      · by_cases hp : hasParent T (srow T (T.length - 1)) (T.length - 1)
        · exact Bw_snoc_operv hlen2 hp (fun n hn =>
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
          have hGdl : GOKWv v0 T.dropLast := by
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
      have hm' : m = 2 * entry T 1 (T.length - 1) - 1 := by omega
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
      refine Bw_snoc_orphv hj1 hjv (by simpa using hnp') ?_
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

#print axioms GOKWv_of_Wg

/-! ## 段 v の語 `(0,v,0)(1,v+1,1)(2,v+1,0) ∈ Wg 2v` -/

def R12v (v : ℕ) : TrioSeq := [((1, v + 1, 1) : ℕ × ℕ × ℕ), ((2, v + 1, 0) : ℕ × ℕ × ℕ)]

theorem argOK_R12v (v : ℕ) : argOK (R12v v) := by
  intro p hp
  simp only [R12v, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> (dsimp only; omega)

theorem srow_R12v (v : ℕ) : srow (R12v v) ((R12v v).length - 1) = 1 := by
  simp [srow, R12v, entry]

theorem domT_R12v (v : ℕ) : domT (R12v v) (2 * v + 1) := by
  refine ⟨by simp [lev, R12v, entry] <;> omega, ?_⟩
  rw [srow_R12v]
  rintro ⟨k, hk, -⟩
  have hk' : nextrel1 (R12v v) k ((R12v v).length - 1) := by
    unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
  obtain ⟨-, -, hkl, hk1, -⟩ := hk'
  have hk0 : k = 0 := by simp [R12v] at hkl; omega
  subst hk0
  simp [R12v, entry] at hk1

theorem hasParent_G2cv (v : ℕ) :
    hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) (srow (R12v v) ((R12v v).length - 1))
      (R12v v).length := by
  rw [srow_R12v]
  show hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) 1 2
  have h01 : nextrel0 (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) 0 1 :=
    ⟨by simp [R12v], by simp [R12v], by omega, by simp [R12v, entry], fun j hj => by omega⟩
  have h12 : nextrel0 (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) 1 2 :=
    ⟨by simp [R12v], by simp [R12v], by omega, by simp [R12v, entry], fun j hj => by omega⟩
  have hle : le0 (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) 0 2 :=
    ⟨by simp [R12v], by simp [R12v],
      Relation.ReflTransGen.tail (Relation.ReflTransGen.single h01) h12⟩
  exact hasParent_one_of (by simp [R12v]) (by omega) hle (by simp [R12v, entry])

theorem natDom_G2cv (v : ℕ) : natDom (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) := by
  refine natDom_iff.mpr (Or.inr ?_)
  have hl : ((((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v).length - 1) = (R12v v).length := by
    simp [R12v]
  have hs : srow (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v)
      ((((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v).length - 1) = srow (R12v v) ((R12v v).length - 1) := by
    simp [srow, R12v, entry]
  rw [hs, hl]
  exact hasParent_G2cv v

theorem tow_R12v_succ (v k : ℕ) :
    tow v 0 (R12v v) (k + 1)
      = ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v [shiftr01 1 0 (tow v 0 (R12v v) k)] := by
  rw [tow, graft_eq_shift, rword_singleton, rcol, shiftr01_add0]
  rfl

theorem tow_R12v_Wg (v : ℕ) (hv : 1 ≤ v) : ∀ k, tow v 0 (R12v v) k ∈ Wg (2 * v)
  | 0 => by simpa [tow] using Wg_nil (2 * v)
  | (k + 1) => by
      rw [tow_R12v_succ]
      have hT : shiftr01 1 0 (tow v 0 (R12v v) k) ∈ Wg (2 * v) :=
        Wg_shift (tow_R12v_Wg v hv k) 1
      have hge : ∀ x ∈ shiftr01 1 0 (tow v 0 (R12v v) k), 1 ≤ x.1 := by
        intro x hx
        simp only [shiftr01, List.mem_map] at hx
        obtain ⟨p, -, rfl⟩ := hx
        dsimp only; omega
      have hB : Bwv v [shiftr01 1 0 (tow v 0 (R12v v) k)] := by
        have h := GOKWv_of_Wg hv _ hT hge [] (by intro U hU; simp at hU) (Bwv_nil v)
        simpa using h
      exact hB v le_rfl (argOK_rword v _) (2 * v) le_rfl

/-- ★ 段 v の語。 -/
theorem G2cv_Wg (v : ℕ) (hv : 1 ≤ v) : (((0, v, 0) : ℕ × ℕ × ℕ) :: R12v v) ∈ Wg (2 * v) := by
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_G2cv v, fun n _ => ?_⟩))
  rw [oper_cons_tower1 (argOK_R12v v) (by simp [R12v]) (domT_R12v v) (srow_R12v v)
    (hasParent_G2cv v)]
  exact tow_R12v_Wg v hv n

#print axioms G2cv_Wg

/-! ## 塊の鎖と目標 -/

def S : ℕ → ℕ → TrioSeq
  | _, 0 => []
  | v, (k + 1) => ((0, v, 0) : ℕ × ℕ × ℕ) :: (R12v v ++ shiftr01 1 0 (S (v + 1) k))

theorem S_Wg : ∀ k v, 1 ≤ v → S v k ∈ Wg (2 * v)
  | 0, v, _ => Wg_nil (2 * v)
  | (k + 1), v, hv => by
      show (((0, v, 0) : ℕ × ℕ × ℕ) :: (R12v v ++ shiftr01 1 0 (S (v + 1) k))) ∈ Wg (2 * v)
      have hA : R12v v ∈ Wstarv v := fun _ a ha => Wg_mono ha (G2cv_Wg v hv)
      have hR : shiftr01 1 0 (S (v + 1) k) ∈ Wg (2 * (v + 1)) :=
        Wg_shift (S_Wg k (v + 1) (by omega)) 1
      have hge : ∀ p ∈ R12v v ++ shiftr01 1 0 (S (v + 1) k), 1 ≤ p.1 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · simp only [R12v, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;> (dsimp only; omega)
        · simp only [shiftr01, List.mem_map] at hp
          obtain ⟨q, -, rfl⟩ := hp
          dsimp only; omega
      have hhd : entry (shiftr01 1 0 (S (v + 1) k)) 0 0 ≤ 1 := by
        cases k with
        | zero => simp [S, shiftr01, entry]
        | succ k' => simp [S, shiftr01, entry]
      have hrs : rsum (R12v v) (shiftr01 1 0 (S (v + 1) k)) := by
        intro p hp
        have := hge p hp
        omega
      exact hang_Wg hA hR hrs (fun p hp => by have := hge p hp; omega) (2 * v) le_rfl

/-- 塊 `(j, v+j, 0)(j+1, v+j+1, 1)(j+2, v+j+1, 0)`。 -/
def Blk (v j : ℕ) : TrioSeq :=
  [((j, v + j, 0) : ℕ × ℕ × ℕ), ((j + 1, v + j + 1, 1) : ℕ × ℕ × ℕ),
    ((j + 2, v + j + 1, 0) : ℕ × ℕ × ℕ)]

theorem shift_Blk (v j : ℕ) : shiftr01 1 0 (Blk (v + 1) j) = Blk v (j + 1) := by
  simp only [Blk, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨Prod.ext ?_ (Prod.ext ?_ rfl), Prod.ext ?_ (Prod.ext ?_ rfl),
    Prod.ext ?_ (Prod.ext ?_ rfl)⟩ <;>
    (first | (dsimp only; omega) | dsimp only | omega | rfl)

theorem S_flat : ∀ k v, S v k = (List.range k).flatMap (fun j => Blk v j)
  | 0, _ => rfl
  | (k + 1), v => by
      show ((0, v, 0) : ℕ × ℕ × ℕ) :: (R12v v ++ shiftr01 1 0 (S (v + 1) k)) = _
      rw [S_flat k (v + 1), GwV.shiftr01_flatMap, List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_map]
      have e : (List.range k).flatMap (fun j => shiftr01 1 0 (Blk (v + 1) j))
          = (List.range k).flatMap ((fun j => Blk v j) ∘ Nat.succ) := by
        apply List.flatMap_congr
        intro j _
        rw [shift_Blk]
        rfl
      rw [e]
      rfl

def TG (n : ℕ) : TrioSeq := shiftr01 1 0 (S 1 n)

theorem TG_Wg (n : ℕ) : TG n ∈ Wg 2 := Wg_shift (S_Wg n 1 le_rfl) 1

theorem TG_ge (n : ℕ) : ∀ x ∈ TG n, 1 ≤ x.1 := by
  intro x hx
  simp only [TG, shiftr01, List.mem_map] at hx
  obtain ⟨p, -, rfl⟩ := hx
  dsimp only; omega

theorem TG_mono (n : ℕ) : Mono (TG n) := by
  intro x hx
  simp only [TG, shiftr01, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [S_flat] at hp
  simp only [List.mem_flatMap, List.mem_range, Blk, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, -, hp⟩ := hp
  rcases hp with rfl | rfl | rfl <;> (dsimp only; omega)

theorem TG_head (n : ℕ) : entry (TG n) 0 0 ≤ 1 := by
  cases n with
  | zero => simp [TG, S, shiftr01, entry]
  | succ k => simp [TG, S, shiftr01, entry]

/-- ★★ 目標の展開の各項 `R338 ++ TG n ∈ W 0`（BH）。 -/
theorem Gn_mem (n : ℕ) : R338 ++ TG n ∈ W 0 :=
  GwY.base_hang (TG n) (TG_Wg n) (TG_ge n) (TG_mono n) (TG_head n) R338 Aok_R338

theorem flat_Blk (m : ℕ) :
    (List.range (m + 1)).flatMap (fun k => Blk 0 k) = R338 ++ TG m := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  have e : TG m = (List.range m).flatMap ((fun k => Blk 0 k) ∘ Nat.succ) := by
    rw [TG, S_flat, GwV.shiftr01_flatMap]
    apply List.flatMap_congr
    intro j _
    exact shift_Blk 0 j
  rw [e]
  rfl

#print axioms Gn_mem

/-! ## ★★★★★★★★★★ 最終目標 `(0,0,0)(1,1,1)(2,1,0)(1,1,1) ∈ W 0` -/

def Gm : TrioSeq := [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
  ((1, 1, 1) : ℕ × ℕ × ℕ)]

theorem Gm_n01 : nextrel0 Gm 0 1 :=
  ⟨by simp [Gm], by simp [Gm], by omega, by simp [Gm, entry], fun j hj => by omega⟩

theorem Gm_n12 : nextrel0 Gm 1 2 :=
  ⟨by simp [Gm], by simp [Gm], by omega, by simp [Gm, entry], fun j hj => by omega⟩

theorem Gm_le1_1 : le1 Gm 0 1 := by
  refine ⟨by simp [Gm], by simp [Gm], Relation.ReflTransGen.single
    ⟨by simp [Gm], by simp [Gm], by omega, by simp [Gm, entry],
      ⟨by simp [Gm], by simp [Gm], Relation.ReflTransGen.single Gm_n01⟩, fun j hj => ?_⟩⟩
  have h1 := rtg0_le hj.2.2.2
  have : j = 1 := by omega
  subst this
  exact le_rfl

theorem Gm_le1_2 : le1 Gm 0 2 := by
  refine ⟨by simp [Gm], by simp [Gm], Relation.ReflTransGen.single
    ⟨by simp [Gm], by simp [Gm], by omega, by simp [Gm, entry],
      ⟨by simp [Gm], by simp [Gm],
        Relation.ReflTransGen.tail (Relation.ReflTransGen.single Gm_n01) Gm_n12⟩,
      fun j hj => ?_⟩⟩
  have h1 := rtg0_le hj.2.2.2
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> simp [Gm, entry]

open Classical in
theorem oper_Gm (n : ℕ) : Gm⟦n⟧ = (List.range n).flatMap (fun k => Blk 0 k) := by
  have h := oper_z1_mask [] 0 0 [((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)]
    (by decide) n
  have eG : Gm = [] ++ (((0, 0, 0) : ℕ × ℕ × ℕ) :: [((1, 1, 1) : ℕ × ℕ × ℕ),
      ((2, 1, 0) : ℕ × ℕ × ℕ)] ++ [((0 + 1, 0 + 1, 1) : ℕ × ℕ × ℕ)]) := rfl
  rw [eG, h, List.nil_append]
  apply List.flatMap_congr
  intro k _
  have hle1 : le1 [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
      ((1, 1, 1) : ℕ × ℕ × ℕ)] 0 1 := Gm_le1_1
  have hle2 : le1 [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
      ((1, 1, 1) : ℕ × ℕ × ℕ)] 0 2 := Gm_le1_2
  simp [List.range_succ, hle1, hle2, entry, Blk, Nat.add_comm]

/-- ★★★★★★★★★★ 最終目標 `(0,0,0)(1,1,1)(2,1,0)(1,1,1) ∈ W 0`（仮定なし）。 -/
theorem goal_mem : Gm ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [oper_Gm, flat_Blk]
  exact Gn_mem m

#print axioms goal_mem

end GwZ
end TRIO
