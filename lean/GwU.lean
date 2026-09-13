/-
GwU.lean: 根の行 1 を固定した `W*`（`Wstarv v`）と、根の語の後ろに `Wg` の元を吊るす補題。

`Gw.Wstarg_closed` の証明は根の行 1 の値 `v` を最後まで変えない。そこで `v` を固定した
族 `Wstarv v` も同じ証明で閉じる。根の直後に字の語 `A = rword 0 v l` を置くと、`A` は
`Wstarg`（全ての `v`）には入らないが `Wstarv v` には入りうる。`Gw.XAg_closed` を
`X = Wstarv v` に使うと、`A ∈ Wstarv v` のもとで `Wg` の任意の元を語の後ろに継げる。
-/
import GwT

namespace TRIO
namespace GwU

open Wset
open Small
open GwS
open Gw

/-! ## 根の行 1 を固定した `W*` -/

def Wstarv (v : ℕ) : Set TrioSeq :=
  {R | argOK R → ∀ a : ℕ, 2 * v ≤ a → (((0, v, 0) : ℕ × ℕ × ℕ) :: R) ∈ Wg a}

theorem tower1_mem_v {v m a : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hva : 2 * v ≤ a) (hd : domT R m) (hi1 : srow R (R.length - 1) = 1)
    (hgr : ∀ y ∈ Wg m, based y → graft R y ∈ Wstarv v)
    (hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ k, tow v 0 R k ∈ Wg a := by
  have hvm : 2 * v + 0 ≤ m := tower1_le hRne (by omega) hd hi1 hpM
  have key : ∀ k, ∀ a', 2 * v ≤ a' → tow v 0 R k ∈ Wg a' := by
    intro k
    induction k with
    | zero => intro a' _; simpa [tow] using Wg_nil a'
    | succ k ih =>
        intro a' ha'
        have hk : tow v 0 R k ∈ Wg m := ih m (by omega)
        have hgk := hgr (tow v 0 R k) hk (based_tow v 0 R k)
        exact hgk (argOK_graft hRne hR _) a' ha'
  exact fun k => key k a hva

/-- ★ `A_u(W*_v) ⊆ W*_v`（`Wstarg_closed` の `v` 固定版）。 -/
theorem Wstarv_closed (v : ℕ) :
    ∀ (u0 : ℕ) (R : TrioSeq), Aopg Wg u0 (Wstarv v) R → R ∈ Wstarv v := by
  intro u0 R AR hR a hva
  by_cases hRnil : R = []
  · subst hRnil
    exact Wg_mono hva (Om_mem_Wg v)
  · set p0 : ℕ × ℕ × ℕ := (0, v, 0) with hp0
    have hRlen : 0 < R.length := List.length_pos_iff.mpr hRnil
    have hMlen : (p0 :: R).length - 1 = R.length := by simp
    have hi1M : srow (p0 :: R) ((p0 :: R).length - 1) = srow R (R.length - 1) := by
      rw [hMlen]; exact srow_cons_last hRnil
    have hlevM : lev (p0 :: R) ((p0 :: R).length - 1) = lev R (R.length - 1) := by
      unfold lev
      rw [hMlen, entry_cons_last hRnil 1, entry_cons_last hRnil 2]
    have hdlmem : R.dropLast ∈ Wstarv v → (p0 :: R.dropLast) ∈ Wg a := by
      intro h
      exact h (argOK_dropLast hR) a hva
    have hnatP : hasParent (p0 :: R) (srow R (R.length - 1)) R.length →
        natDom (p0 :: R) := by
      intro hp
      refine natDom_iff.mpr (Or.inr ?_)
      rw [hi1M, hMlen]; exact hp
    have hnatZ : lev R (R.length - 1) = 0 → natDom (p0 :: R) := by
      intro hz
      exact natDom_iff.mpr (Or.inl (by rw [hlevM]; exact hz))
    rcases AR with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, h2, hgr⟩
    · have hR1 : R.length = 1 := by omega
      have hw' : lev R (R.length - 1) = 0 := by rw [hR1]; exact hw
      have hnp : ¬ hasParent R 0 (R.length - 1) := by
        rw [hR1]
        rintro ⟨j0, hj0, -⟩
        exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
      have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine A1g_intro (Or.inr (Or.inl ⟨hnatZ hw', fun n hn => ?_⟩))
      rw [oper_cons_succ hR hRnil hw' hnp, hdl]
      exact Wg_flatMap_copies (Wg_mono hva (Om_mem_Wg v)) (rsum_self_cons v 0 []) n
    · have hpredmem : ¬ hasParent R (srow R (R.length - 1)) (R.length - 1) →
          (p0 :: R.dropLast) ∈ Wg a := by
        intro hp
        by_cases hR2 : 2 ≤ R.length
        · have hop1 := hop 1 le_rfl
          have hpred : R⟦1⟧ = R.dropLast := by
            have hL : R.length - 1 ≠ 0 := by omega
            have he : R⟦1⟧ = Pred R := by
              by_cases hz0 : entry R 0 (R.length - 1) = 0 ∧
                  entry R 1 (R.length - 1) = 0 ∧ entry R 2 (R.length - 1) = 0
              · exact oper_eq_pred_of_zero 1 hL hz0
              · exact oper_eq_pred_of_noParent 1 hL hz0 hp
            rw [he]
            unfold Pred
            rw [if_neg (by omega)]
          rw [hpred] at hop1
          exact hdlmem hop1
        · have hdl : R.dropLast = [] :=
            List.eq_nil_of_length_eq_zero (by simp; omega)
          rw [hdl]
          exact Wg_mono hva (Om_mem_Wg v)
      by_cases hp : hasParent R (srow R (R.length - 1)) (R.length - 1)
      · refine A1g_intro (Or.inr (Or.inl
          ⟨hnatP (hasParent_cons_of hR hRnil hp), fun n hn => ?_⟩))
        rw [oper_cons_nat hR hRnil hp]
        exact hop n hn (argOK_oper hR n) a hva
      · have hw0 : lev R (R.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exact absurd h hp
        have hsr : srow R (R.length - 1) = 0 := by
          unfold srow
          unfold lev at hw0
          rw [if_neg (by omega), if_neg (by omega)]
        have hnp : ¬ hasParent R 0 (R.length - 1) := by rw [← hsr]; exact hp
        refine A1g_intro (Or.inr (Or.inl ⟨hnatZ hw0, fun n hn => ?_⟩))
        rw [oper_cons_succ hR hRnil hw0 hnp]
        exact Wg_flatMap_copies (hpredmem hp) (rsum_self_cons v 0 _) n
    · have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
      have hi1 : srow R (R.length - 1) = 1 := by
        unfold srow
        unfold lev at hlevpos
        rw [if_neg (by omega), if_pos (by omega)]
      by_cases hpM : hasParent (p0 :: R) (srow R (R.length - 1)) R.length
      · refine A1g_intro (Or.inr (Or.inl ⟨hnatP hpM, fun n hn => ?_⟩))
        rw [oper_cons_tower1 hR hRnil hd hi1 hpM]
        exact tower1_mem_v hR hRnil hva hd hi1 hgr hpM n
      · have hdM : domT (p0 :: R) m := domT_cons_of_dead hRnil hd hpM
        have hdead1 : ¬ hasParent (p0 :: R) 1 R.length := by rw [← hi1]; exact hpM
        have hle : entry R 1 (R.length - 1) ≤ v := entry1_le_of_dead_one hR hRnil hdead1
        have hma : m < a := by
          have h1 := hd.1
          unfold lev at h1
          omega
        have h2M : entry (p0 :: R) 2 ((p0 :: R).length - 1) = 0 := by
          rw [hMlen, entry_cons_last hRnil 2]; exact h2
        refine A1g_intro (Or.inr (Or.inr ⟨m, hma, hdM, h2M, fun y hy hby => ?_⟩))
        rw [graft_cons hRnil]
        exact hgr y hy hby (argOK_graft hRnil hR y) a hva

/-- ★ 吊るしの補題: `A ∈ W*_v` なら、`Wg` の元 `R`（`rsum A R`）を `A` の後ろに継げる。 -/
theorem hang_Wg {v : ℕ} {A : TrioSeq} (hA : A ∈ Wstarv v) {u : ℕ} {R : TrioSeq}
    (hR : R ∈ Wg u) (hrs : rsum A R) : A ++ R ∈ Wstarv v :=
  A2g' (XAg_closed (u := u) (X := Wstarv v) (fun M hM => Wstarv_closed v u M hM) hA) hR hrs

#print axioms hang_Wg

/-! ## 対角の塔の頭をはがす -/

theorem Dzf_cons (l : List TrioSeq) (a b : ℕ) : ∀ n : ℕ,
    Dzf (fun a b => rword a b l) a b (n + 1)
      = ((a, b, 0) : ℕ × ℕ × ℕ) ::
        (rword a b l ++ Dzf (fun a b => rword a b l) (a + 1) (b + 1) n)
  | 0 => by simp [Dzf]
  | (n + 1) => by
      rw [Dzf_succ, Dzf_cons l a b n, Dzf_succ]
      have e1 : a + (n + 1) = a + 1 + n := by omega
      have e2 : b + (n + 1) = b + 1 + n := by omega
      rw [e1, e2]
      simp only [List.cons_append, List.append_assoc]

theorem Dzf_ge (l : List TrioSeq) (a b n : ℕ) :
    ∀ x ∈ Dzf (fun a b => rword a b l) a b n, a ≤ x.1 := by
  intro x hx
  simp only [Dzf, List.mem_flatMap, List.mem_range, List.mem_cons] at hx
  obtain ⟨k, -, hx⟩ := hx
  rcases hx with rfl | hx
  · show a ≤ a + k; omega
  · have := rword_ge (a + k) (b + k) l x hx
    omega

theorem Dzf_shift (l : List TrioSeq) (a b s n : ℕ) :
    shiftr01 s 0 (Dzf (fun a b => rword a b l) a b n)
      = Dzf (fun a b => rword a b l) (a + s) b n := by
  induction n with
  | zero => simp [Dzf, shiftr01]
  | succ n ih =>
      rw [Dzf_succ, Dzf_succ, shiftr01_append0, ih]
      congr 1
      rw [show ((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: rword (a + n) (b + n) l
          = [((a + n, b + n, 0) : ℕ × ℕ × ℕ)] ++ rword (a + n) (b + n) l from rfl,
        shiftr01_append0, shift_col, rword_shift]
      have e : a + n + s = a + s + n := by omega
      rw [e]
      rfl

/-! ## Mono を外した字の中身（`Wg` の graft は Mono でない森も受け取る） -/

def RawW (T : TrioSeq) : Prop := (∀ x ∈ T, 1 ≤ x.1) ∧ RiseOk T

def WOkW (l : List TrioSeq) : Prop := ∀ T ∈ l, RawW T

theorem WOkW_append {l1 l2 : List TrioSeq} (h1 : WOkW l1) (h2 : WOkW l2) :
    WOkW (l1 ++ l2) := by
  intro T hT
  rcases List.mem_append.mp hT with h | h
  · exact h1 T h
  · exact h2 T h

theorem WOkW_singleton {T : TrioSeq} (hT : RawW T) : WOkW [T] := by
  intro U hU
  rw [List.mem_singleton.mp hU]; exact hT

theorem RawW_nil : RawW [] := ⟨by simp, fun u hu => by simp at hu⟩

theorem not_le1_treeW (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) (l1 l3 : List TrioSeq)
    {T : TrioSeq} (hT : RiseOk T) (u : ℕ) (hu : u < T.length) :
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
theorem rise_rwordW (Y0 : TrioSeq) (a b k : ℕ) (hb : 1 ≤ b) {l : List TrioSeq} (hw : WOkW l) :
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
      have hT : RawW T := hw T (by rw [hl]; simp)
      have ih := rise_rwordW Y0 a b k hb hw l2 (l1 ++ [T]) l3 hl'
      rw [rword_cons, rword_cons, List.length_append, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · rw [← rise_rcol a b k T (fun t => le1 (MzR Y0 a b l) Y0.length
            (Y0.length + 1 + (rword a b l1).length + t))
            (by rw [hl'']; simpa using le1_zposR Y0 a b l1 (l2 ++ l3) T)
            (by intro t ht1 ht
                obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
                rw [hl'']
                refine not_le1_treeW Y0 a b hb l1 (l2 ++ l3) hT.2 u ?_
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
theorem oper_z1wW (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) {l : List TrioSeq}
    (hw : WOkW l) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf (fun a b => rword a b l) a b n := by
  rw [oper_z1_mask Y0 a b (rword a b l) (rword_ge a b l) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have := rise_rwordW Y0 a b k hb hw l [] [] (by simp)
  simpa [rword, MzR] using this

/-! ## 根の語の `Wg` 所属 `Bw` -/

theorem argOK_rword (v : ℕ) (l : List TrioSeq) : argOK (rword 0 v l) := by
  intro p hp
  have := rword_ge 0 v l p hp
  omega

/-- 根 `(0,v,0)` の直後の字の頭 `(1,v+1,1)` は、行 2 の親（根）を持つ。 -/
theorem natDom_zroot (v : ℕ) {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) :
    natDom ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
  have hlen : ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]).length
      = X.length + 2 := by simp
  have e0 : ∀ r, entry ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) r 0
      = entry [((0, v, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    rw [Small.entry_append_left (by simp)]
    simp [entry]
  have eL : ∀ r, entry ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) r
      (X.length + 1) = entry [((1, v + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    have h := entry_append_right (((0, v, 0) : ℕ × ℕ × ℕ) :: X)
      [((1, v + 1, 1) : ℕ × ℕ × ℕ)] r 0
    simpa using h
  have emid : ∀ j, 0 < j → j < X.length + 1 →
      1 ≤ entry ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 0 j := by
    intro j hj0 hjl
    obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    rw [Small.entry_append_left (by simp; omega), entry_cons_succ]
    have hmem : X.getD u (0, 0, 0) ∈ X := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    exact hX _ hmem
  have hL1 : entry [((1, v + 1, 1) : ℕ × ℕ × ℕ)] 0 0 = 1 := rfl
  have hle0 : le0 ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 0
      (X.length + 1) := by
    refine ⟨by omega, by omega, Relation.ReflTransGen.single
      ⟨by omega, by omega, by omega, ?_, fun j hj => ?_⟩⟩
    · rw [e0, eL]; simp [entry]
    · rw [eL, hL1]; exact emid j hj.1 hj.2
  have hle1 : le1 ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 0
      (X.length + 1) := by
    refine ⟨by omega, by omega, Relation.ReflTransGen.single
      ⟨by omega, by omega, by omega, ?_, hle0, fun j hj => ?_⟩⟩
    · rw [e0, eL]; simp [entry]
    · have hjle : j ≤ X.length + 1 := rtg0_le hj.2.2.2
      rcases Nat.eq_or_lt_of_le hjle with h | h
      · rw [h]
      · exfalso
        have h1 := rtg0_rec hj.2.2.2 (X.length + 1) h le_rfl
        rw [eL, hL1] at h1
        have h2 := emid j hj.1 h
        omega
  refine natDom_iff.mpr (Or.inr ?_)
  have hb : ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]).length - 1
      = X.length + 1 := by omega
  have hsr : srow ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])
      (X.length + 1) = 2 := by
    unfold srow; rw [eL]; simp [entry]
  rw [hb, hsr]
  exact hasParent_two_of (by omega) (by omega) hle1 (by rw [e0, eL]; simp [entry])

/-- 根 `(0,v,0)` と語 `rword 0 v l` が、どの `v ≥ 1` でも `W*_v`。 -/
def Bw (l : List TrioSeq) : Prop := ∀ v : ℕ, 1 ≤ v → rword 0 v l ∈ Wstarv v

/-- 字の中身 `T` を語の最後に継いでも `Bw` が保たれる。 -/
def GOKW (T : TrioSeq) : Prop := ∀ l : List TrioSeq, WOkW l → Bw l → Bw (l ++ [T])

theorem Bw_nil : Bw [] := by
  intro v _ _ a ha
  show (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v ([] : List TrioSeq)) ∈ Wg a
  rw [rword_nil]
  exact Wg_mono ha (Om_mem_Wg v)

theorem Dzf_mem {l : List TrioSeq} (hB : Bw l) :
    ∀ n v, 1 ≤ v → ∀ a, 2 * v ≤ a → Dzf (fun a b => rword a b l) 0 v n ∈ Wg a := by
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

/-- (G4) 語の最後に空の字（頭の潰れ）。 -/
theorem Bw_snocz {l : List TrioSeq} (hw : WOkW l) (hB : Bw l) : Bw (l ++ [[]]) := by
  intro v hv _ a ha
  have e : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [[]]))
      = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
    rw [rword_append, rword_singleton, rcol_nil]; rfl
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_zroot v (fun x hx => by
    have := rword_ge 0 v l x hx; omega), fun n _ => ?_⟩))
  have h := oper_z1wW [] 0 v hv hw n
  simp only [List.nil_append] at h
  rw [show ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])
      = (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l ++ [((0 + 1, v + 1, 1) : ℕ × ℕ × ℕ)]) from rfl, h]
  exact Dzf_mem hB n v hv a ha

theorem Bw_rep {T : TrioSeq} (hT : RawW T) (hG : GOKW T) {l : List TrioSeq} (hw : WOkW l)
    (hB : Bw l) : ∀ n, Bw (l ++ List.replicate n T)
  | 0 => by simpa using hB
  | (n + 1) => by
      have hwn : WOkW (l ++ List.replicate n T) := by
        refine WOkW_append hw ?_
        intro U hU
        rw [List.eq_of_mem_replicate hU]; exact hT
      have h := hG (l ++ List.replicate n T) hwn (Bw_rep hT hG hw hB n)
      have e : l ++ List.replicate n T ++ [T] = l ++ List.replicate (n + 1) T := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

theorem rword0_snoc (v : ℕ) (l : List TrioSeq) (T : TrioSeq) :
    (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [T]))
      = ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v l) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])
        ++ shiftr01 1 0 T := by
  rw [rword_append, rword_singleton, rcol]
  simp [List.append_assoc]

theorem natDom_append_shift (P T : TrioSeq) (d : ℕ) (hT : T ≠ [])
    (hp : hasParent T (srow T (T.length - 1)) (T.length - 1)) :
    natDom (P ++ shiftr01 d 0 T) := by
  have hTl : 0 < T.length := List.length_pos_iff.mpr hT
  refine natDom_iff.mpr (Or.inr ?_)
  have hl : (P ++ shiftr01 d 0 T).length - 1 = P.length + (T.length - 1) := by
    simp [shiftr01]; omega
  have hsr : srow (P ++ shiftr01 d 0 T) (P.length + (T.length - 1))
      = srow T (T.length - 1) := by
    unfold srow
    rw [entry_append_right, entry_append_right, entry2_shiftr01, entry1_shiftr01]
  rw [hl, hsr]
  exact hasParent_append_right_of P _ (hasParent_shiftr01.mpr hp)

/-- (G1) 字の中身の末尾の親が中身の中にある。 -/
theorem Bw_snoc_oper {l : List TrioSeq} {T : TrioSeq}
    (hlen : 2 ≤ T.length) (hp : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hIH : ∀ n, 1 ≤ n → Bw (l ++ [T⟦n⟧])) : Bw (l ++ [T]) := by
  intro v hv _ a ha
  rw [rword0_snoc]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_append_shift _ T 1
    (by rintro rfl; simp at hlen) hp, fun n hn => ?_⟩))
  rw [oper_shift _ T 1 n hlen hp, ← rword0_snoc]
  exact hIH n hn v hv (argOK_rword v _) a ha

/-- (G3) 字の中身の最後が最上位の平らな列: 字が複製される。 -/
theorem Bw_snoc_flat {l : List TrioSeq} {T : TrioSeq} {x : ℕ} (hx : 1 ≤ x)
    (hTx : ∀ y ∈ T, x ≤ y.1) (hIH : ∀ n, 1 ≤ n → Bw (l ++ List.replicate n T)) :
    Bw (l ++ [T ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]]) := by
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

/-- 見える列が全部行 1 ≥ 1 で先頭も行 1 ≥ 1 なら、後ろの `(d,1,0)` は行 1 の親を持たない。 -/
theorem noParent1_snoc {Y : TrioSeq} {d : ℕ} (hY : Ancd d Y) (hY0 : 1 ≤ entry Y 1 0) :
    ¬ hasParent (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)]) 1 Y.length := by
  rintro ⟨k, hk, -⟩
  have hk' : nextrel1 (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)]) k Y.length := by
    unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
  obtain ⟨-, -, hkj, hk1, hle0, -⟩ := hk'
  have eL : ∀ r, entry (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)]) r Y.length
      = entry [((d, 1, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; simpa using entry_append_right Y [((d, 1, 0) : ℕ × ℕ × ℕ)] r 0
  have eK : ∀ r i, i < Y.length → entry (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)]) r i = entry Y r i :=
    fun r i hi => Small.entry_append_left hi
  have e1 : entry [((d, 1, 0) : ℕ × ℕ × ℕ)] 1 0 = 1 := rfl
  have e0 : entry [((d, 1, 0) : ℕ × ℕ × ℕ)] 0 0 = d := rfl
  rw [eL, eK 1 k hkj, e1] at hk1
  have hrec := rtg0_rec hle0.2.2
  by_cases hk0 : k = 0
  · subst hk0; omega
  · have hlt : entry Y 0 k < d := by
      have := hrec Y.length hkj le_rfl
      rwa [eL, eK 0 k hkj, e0] at this
    have hvis : ∀ i, k < i → i < Y.length → entry Y 0 k < entry Y 0 i := by
      intro i hi hil
      have := hrec i hi (by omega)
      rwa [eK 0 k hkj, eK 0 i hil] at this
    have := hY k (Nat.pos_of_ne_zero hk0) hkj hlt hvis
    omega

/-- (G2) 字の中身の最後が 1 の列の孤児 `(h,1,0)`: 根の行 1 が ≥ 1 なので死んだまま、graft の分岐。 -/
theorem Bw_snoc_orph {l : List TrioSeq} (hw : WOkW l) {T0 : TrioSeq} {h : ℕ}
    (hsp : ∀ j, j < T0.length → entry T0 0 j < h →
      (∀ i, j < i → i < T0.length → entry T0 0 j < entry T0 0 i) → 1 ≤ entry T0 1 j)
    (hprev : ∀ z ∈ Wg 1, based z → Bw (l ++ [T0 ++ shiftr01 h 0 z])) :
    Bw (l ++ [T0 ++ [((h, 1, 0) : ℕ × ℕ × ℕ)]]) := by
  intro v hv _ a ha
  obtain ⟨Y, hYdef⟩ : ∃ Y : TrioSeq, Y = ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [T0]) :=
    ⟨_, rfl⟩
  have e : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [T0 ++ [((h, 1, 0) : ℕ × ℕ × ℕ)]]))
      = Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [rword_snoc_orph, hYdef]; rfl
  have hanc : Ancd (0 + 1 + h) Y := by
    have eY : Y = [] ++ (((0, v, 0) : ℕ × ℕ × ℕ) :: (rword 0 v l ++ rcol 0 v T0)) := by
      rw [hYdef, rword_append, rword_singleton]; rfl
    rw [eY]
    exact Ancd_recrword (a := 0) (b := v) (h := h) hv (Z0 := []) (by intro j _ hjl; simp at hjl)
      l (fun T hT x hx => (hw T hT).1 x hx) T0 hsp
  have hY0 : 1 ≤ entry Y 1 0 := by rw [hYdef]; simp [entry]; omega
  have hL : (Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]).length - 1 = Y.length := by simp
  have eL : ∀ r, entry (Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]) r Y.length
      = entry [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; simpa using entry_append_right Y [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)] r 0
  have hsr : srow (Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]) Y.length = 1 := by
    unfold srow; rw [eL, eL]; simp [entry]
  have hdom : domT (Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]) 1 := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [hL, eL, eL]; simp [entry]
    · rw [hL, hsr]; exact noParent1_snoc hanc hY0
  have h2 : entry (Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]) 2
      ((Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 := by
    rw [hL, eL]; simp [entry]
  rw [e]
  refine A1g_intro (Or.inr (Or.inr ⟨1, by omega, hdom, h2, fun z hz hbz => ?_⟩))
  have hg : graft (Y ++ [((0 + 1 + h, 1, 0) : ℕ × ℕ × ℕ)]) z
      = Y ++ shiftr01 (0 + 1 + h) 0 z := by
    rw [graft_eq_shift, List.dropLast_concat, hL, eL]
    rfl
  have e2 : Y ++ shiftr01 (0 + 1 + h) 0 z
      = ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (l ++ [T0 ++ shiftr01 h 0 z]) := by
    rw [rword_snoc_load, hYdef]; rfl
  rw [hg, e2]
  exact hprev z hz hbz v hv (argOK_rword v _) a ha

/-! ## ★★★★★ 本体: `Wg 2` の中身は根の語の最後に継げる -/

theorem GOKW_of_Wg2 : ∀ T ∈ Wg 2, (∀ x ∈ T, 1 ≤ x.1) → GOKW T := by
  have key : Wg 2 ⊆ {T : TrioSeq | T ∈ Wg 2 ∧ ((∀ x ∈ T, 1 ≤ x.1) → GOKW T)} := by
    refine A2g' ?_
    intro T hA
    have hTW : T ∈ Wg 2 := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hTW, ?_⟩
    intro hge l hw hB
    by_cases hTnil : T = []
    · subst hTnil; exact Bw_snocz hw hB
    have hTlen : 0 < T.length := List.length_pos_iff.mpr hTnil
    have hdlW : T.dropLast ∈ Wg 2 := Wg_dropLast hTW
    have hdlRaw : RawW T.dropLast := ⟨fun x hx => hge x (List.dropLast_subset _ hx),
      Wg2_RiseOk hdlW⟩
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
        GOKW T.dropLast → Bw (l ++ [T]) := by
      intro hc10 hc20 hTx hGdl
      have hceq : c = ((c.1, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc10 hc20)
      rw [hsplit, hceq]
      exact Bw_snoc_flat hc1 hTx (fun n _ => Bw_rep hdlRaw hGdl hw hB n)
    have hflat1 : T.length = 1 → c.2.1 = 0 → c.2.2 = 0 → Bw (l ++ [T]) := by
      intro hT1 hc10 hc20
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine hflat hc10 hc20 (by rw [hdl]; simp) ?_
      rw [hdl]; exact fun l' hw' hB' => Bw_snocz hw' hB'
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
        · exact Bw_snoc_oper hlen2 hp (fun n hn =>
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
          have hGdl : GOKW T.dropLast := by
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
      have hw1 : entry T 1 (T.length - 1) = 1 := by omega
      have hm1 : m = 1 := by omega
      subst hm1
      have hsr : srow T (T.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent T 1 (T.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc11 : c.2.1 = 1 := by
        have := hclast 1; rw [hw1] at this; exact this.symm
      have hc20 : c.2.2 = 0 := by
        have := hclast 2; rw [h20'] at this; exact this.symm
      have hceq : c = ((c.1, 1, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc11 hc20)
      have hTeq : T = T.dropLast ++ [((c.1, 1, 0) : ℕ × ℕ × ℕ)] := by
        rw [← hceq]; exact hsplit
      have hsp : ∀ j, j < T.dropLast.length → entry T.dropLast 0 j < c.1 →
          (∀ i, j < i → i < T.dropLast.length → entry T.dropLast 0 j < entry T.dropLast 0 i) →
          1 ≤ entry T.dropLast 1 j := by
        intro j hj hjh hvis
        by_contra h0
        push Not at h0
        apply hnp
        have hjT : j < T.length - 1 := by simpa using hj
        have hle : le0 T j (T.length - 1) := by
          refine le0_of_between (a := entry T 0 j) rfl (T.length - 1) (by omega) (by omega) ?_
          intro j' h1 h2
          rcases Nat.lt_or_ge j' (T.length - 1) with h3 | h3
          · have hj' : j' < T.dropLast.length := by simpa using h3
            rw [eT 0 j hj, eT 0 j' hj']
            have := hvis j' h1 hj'
            omega
          · have : j' = T.length - 1 := by omega
            subst this
            rw [hclast 0, eT 0 j hj]
            show entry T.dropLast 0 j + 1 ≤ c.1
            omega
        refine H12Export.hasParent1_of_le0_witness (by omega) hle.2.2 ?_
        rw [eT 1 j hj, hw1]; omega
      rw [hTeq]
      refine Bw_snoc_orph hw hsp ?_
      intro z hz hbz
      have h1 := (hgr z hz hbz).2
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

#print axioms GOKW_of_Wg2

/-! ## 入れ子の中身と行 378 -/

/-- 中身 `(1,1,0) :: rword 1 1 l` は `Bw l` から `Wg 2`。 -/
theorem content_mem {l : List TrioSeq} (hB : Bw l) :
    (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 l) ∈ Wg 2 := by
  have h := hB 1 le_rfl (argOK_rword 1 l) 2 le_rfl
  have h2 := Wg_shift h 1
  rw [show (((0, 1, 0) : ℕ × ℕ × ℕ) :: rword 0 1 l) = [((0, 1, 0) : ℕ × ℕ × ℕ)] ++ rword 0 1 l
      from rfl, shiftr01_append0, shift_col, rword_shift] at h2
  simpa using h2

theorem Bw_snoc_mem {l : List TrioSeq} (hw : WOkW l) (hB : Bw l) {T : TrioSeq}
    (hT : T ∈ Wg 2) (hge : ∀ x ∈ T, 1 ≤ x.1) : Bw (l ++ [T]) :=
  GOKW_of_Wg2 T hT hge l hw hB

theorem Bw_nil_nil : Bw [[], []] := by
  have h1 : Bw ([] ++ [[]]) := Bw_snocz (by intro T hT; simp at hT) Bw_nil
  have h2 := Bw_snocz (l := [] ++ [[]])
    (by intro T hT; simp at hT; subst hT; exact RawW_nil) h1
  simpa using h2

def T378 : TrioSeq := ((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [[], []]

theorem T378_eq : T378 = [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ)] := rfl

/-- ★ シート行 378 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(4,2,1) ∈ W 0`（仮定なし）。 -/
theorem R378_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hT : T378 ∈ Wg 2 := content_mem Bw_nil_nil
  have hge : ∀ x ∈ T378, 1 ≤ x.1 := by rw [T378_eq]; decide
  have hmo : Mono T378 := by rw [T378_eq]; unfold Mono; decide
  have hG := GOKR_of_Wg2 T378 hT hge hmo [] (by intro T hT; simp at hT) GoodFb_rword_nil
  have h := row_mem_of_GoodFb Aok_R338 hG
  have e : R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 ([] ++ [T378]))
      = R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
        ((4, 2, 1) : ℕ × ℕ × ℕ)] := rfl
  rw [← e]; exact h

#print axioms R378_mem

end GwU
end TRIO
