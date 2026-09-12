/-
Gw.lean: ガードつきの W 階層（lean-yapss の `W*` の議論の移植）。

`Wset.Aop` との違いは 2 点だけ:
- 分岐 2 に `natDom` ガード（末尾が正レベルの孤児なら展開では入れない）。
- 分岐 3 は行 2 が 0 の孤児に限る（srow = 1 の孤児だけが graft で入る）。

ガードがあると、孤児の末尾は分岐 3 でしか入らないので graft の情報が必ず残る
（`Wset` の `TowerExp` が空になる）。分岐 3 を srow = 1 に絞ると、根が復活させる
孤児は srow = 1 だけになる（`TowerGraft2` も空）。そのため `W*` の閉包
`Wstarg_closed` は無条件に通る。trio 全体でガードが反証された例 `[(1,0,1)]`
（srow = 2 の死んだ孤児）は、この族ではどの分岐でも入らない。
-/
import Wset

namespace TRIO
namespace Gw

open Wset

/-! ## 演算子と族 -/

/-- ガードつきの演算子 `A_u`。 -/
def Aopg (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) (M : TrioSeq) : Prop :=
  (M.length ≤ 1 ∧ lev M 0 = 0) ∨
  (natDom M ∧ ∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m : ℕ, m < u ∧ domT M m ∧ entry M 2 (M.length - 1) = 0 ∧
    ∀ z ∈ Wfam m, based z → graft M z ∈ X)

def Asetg (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) :
    Set TrioSeq :=
  {M | Aopg Wfam u X M}

theorem Aopg_mono_X {Wfam : ℕ → Set TrioSeq} {u : ℕ}
    {X Y : Set TrioSeq} {M : TrioSeq} (h : Aopg Wfam u X M) (hXY : X ⊆ Y) :
    Aopg Wfam u Y M := by
  rcases h with h | ⟨hn, h⟩ | ⟨m, hm, hd, h2, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hn, fun n hn' => hXY (h n hn')⟩)
  · exact Or.inr (Or.inr ⟨m, hm, hd, h2, fun z hz hb => hXY (hop z hz hb)⟩)

theorem Asetg_mono (Wfam : ℕ → Set TrioSeq) (u : ℕ) :
    Monotone (Asetg Wfam u) := by
  intro X Y hXY M hM
  exact Aopg_mono_X (Wfam := Wfam) (u := u) hM hXY

theorem Aopg_mono_level {Wfam : ℕ → Set TrioSeq} {u v : ℕ}
    {X : Set TrioSeq} {M : TrioSeq} (le : u ≤ v) (h : Aopg Wfam u X M) :
    Aopg Wfam v X M := by
  rcases h with h | h | ⟨m, hm, hd, h2, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, lt_of_lt_of_le hm le, hd, h2, hop⟩)

theorem Aopg_cong {Wfam Wgam : ℕ → Set TrioSeq} {u : ℕ}
    {X : Set TrioSeq} {M : TrioSeq} (e : ∀ m : ℕ, m < u → Wfam m = Wgam m) :
    Aopg Wfam u X M ↔ Aopg Wgam u X M := by
  constructor
  · rintro (h | h | ⟨m, hm, hd, h2, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, h2, fun z hz => hop z ((e m hm) ▸ hz)⟩)
  · rintro (h | h | ⟨m, hm, hd, h2, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, h2, fun z hz => hop z ((e m hm).symm ▸ hz)⟩)

/-- 段の族: `Wfg n m` は `m < n` で `Wg m`。 -/
def Wfg : ℕ → ℕ → Set TrioSeq
  | 0 => fun _ => ∅
  | v + 1 => fun m => if m = v then lfpS (Asetg (Wfg v) v) else Wfg v m

/-- ガードつきの `W_u`。 -/
def Wg (u : ℕ) : Set TrioSeq := Wfg (u + 1) u

theorem Wfg_coh {m n : ℕ} (h : m < n) :
    Wfg n m = Wfg (m + 1) m := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ v ih =>
      by_cases hmv : m = v
      · subst hmv; rfl
      · have mlv : m < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hmv
        show (if m = v then _ else Wfg v m) = _
        rw [if_neg hmv]
        exact ih mlv

theorem Wfg_eq_Wg {m n : ℕ} (h : m < n) : Wfg n m = Wg m :=
  Wfg_coh h

theorem Wg_unfold (u : ℕ) : Wg u = lfpS (Asetg (Wg) u) := by
  have stage : Wg u = lfpS (Asetg (Wfg u) u) := by
    show Wfg (u + 1) u = _
    show (if u = u then _ else Wfg u u) = _
    rw [if_pos rfl]
  have cong : ∀ m : ℕ, m < u → Wfg u m = Wg m := fun m hm => Wfg_eq_Wg hm
  have ptw : ∀ X : Set TrioSeq, Asetg (Wfg u) u X = Asetg (Wg) u X := by
    intro X; ext M
    exact Aopg_cong (Wfam := Wfg u) (Wgam := Wg) (u := u) (X := X) cong
  rw [stage, funext ptw]

theorem A1g (u : ℕ) : Asetg (Wg) u (Wg u) = Wg u := by
  rw [Wg_unfold u]
  exact lfpS_unfold (Asetg_mono (Wg) u)

theorem A2g {u : ℕ} {Y : Set TrioSeq}
    (h : Asetg (Wg) u Y ⊆ Y) : Wg u ⊆ Y := by
  rw [Wg_unfold u]
  exact lfpS_lowerbound h

theorem A2g' {u : ℕ} {Y : Set TrioSeq}
    (hY : ∀ M : TrioSeq, Aopg (Wg) u Y M → M ∈ Y) : Wg u ⊆ Y :=
  A2g (fun M hM => hY M hM)

theorem A1g_intro {u : ℕ} {M : TrioSeq}
    (h : Aopg (Wg) u (Wg u) M) : M ∈ Wg u := by
  have : M ∈ Asetg (Wg) u (Wg u) := h
  rwa [A1g u] at this

theorem Wg_nil (u : ℕ) : ([] : TrioSeq) ∈ Wg u :=
  A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)

theorem Wg_mono {u v : ℕ} (h : u ≤ v) : Wg u ⊆ Wg v :=
  A2g' (fun _ A => A1g_intro (Aopg_mono_level h A))

/-! ## ずらし・連結・根 1 列 -/

theorem Wg_shift {u : ℕ} {M : TrioSeq} (h : M ∈ Wg u) (d : ℕ) :
    shiftr01 d 0 M ∈ Wg u := by
  have hsub : Wg u ⊆ {N : TrioSeq | shiftr01 d 0 N ∈ Wg u} := by
    refine A2g' ?_
    intro N A
    refine A1g_intro ?_
    rcases A with ⟨hl, hw⟩ | ⟨hn, hop⟩ | ⟨m, hm, hd, h2, hgr⟩
    · refine Or.inl ⟨by rw [shiftr01_length]; exact hl, ?_⟩
      rw [lev_shiftr01]
      exact hw
    · exact Or.inr (Or.inl ⟨natDom_shiftr01.mpr hn, fun n hn' => by
        rw [oper_shiftr01]
        exact hop n hn'⟩)
    · refine Or.inr (Or.inr ⟨m, hm, domT_shiftr01.mpr hd,
        by rw [shiftr01_length, entry2_shiftr01]; exact h2, fun z hz hb => ?_⟩)
      have hne : N ≠ [] := by rintro rfl; exact not_domT_nil m hd
      rw [graft_shiftr01 hne]
      exact hgr z hz hb
  exact hsub h

set_option maxHeartbeats 1000000 in
/-- `A_u(X) ⊆ X` かつ `A ∈ X` なら `A_u(X⁽ᴬ⁾) ⊆ X⁽ᴬ⁾`（ガードつき）。 -/
theorem XAg_closed {u : ℕ} {X : Set TrioSeq}
    (hX : ∀ M : TrioSeq, Aopg (Wg) u X M → M ∈ X) {A : TrioSeq} (hA : A ∈ X) :
    ∀ M : TrioSeq, Aopg (Wg) u (XA A X) M → M ∈ XA A X := by
  intro B AB hrs
  by_cases hBnil : B = []
  · subst hBnil; simpa using hA
  · have hBlen : 0 < B.length := List.length_pos_iff.mpr hBnil
    have hBge : ∀ p ∈ B, entry B 0 0 ≤ p.1 :=
      fun p hp => hrs p (List.mem_append_right _ hp)
    have hAge : ∀ p ∈ A, entry B 0 0 ≤ p.1 :=
      fun p hp => hrs p (List.mem_append_left _ hp)
    rcases AB with ⟨hl, hw⟩ | ⟨hn, hop⟩ | ⟨m, hm, hd, h2, hgr⟩
    · have hB1 : B.length = 1 := by omega
      by_cases hAnil : A = []
      · subst hAnil; simpa using hX B (Or.inl ⟨hl, hw⟩)
      · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
        have hlast : (A ++ B).length - 1 = A.length + 0 := by
          rw [List.length_append]; omega
        have hnp : ∀ i, ¬ hasParent (A ++ B) i ((A ++ B).length - 1) := by
          intro i hh
          rw [hlast] at hh
          have := (hasParent_append_gen (i := i) (j := 0) (by omega) hrs).mp hh
          obtain ⟨j0, hj0, -⟩ := this
          exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        have hzz0 : lev B (B.length - 1) = 0 := by
          have : B.length - 1 = 0 := by omega
          rw [this]; exact hw
        refine hX _ (Or.inr (Or.inl ⟨(natDom_append hBnil hrs).mpr
          (natDom_iff.mpr (Or.inl hzz0)), fun n hn => ?_⟩))
        have hpred : (A ++ B)⟦n⟧ = Pred (A ++ B) := by
          by_cases hzz : entry (A ++ B) 0 ((A ++ B).length - 1) = 0 ∧
              entry (A ++ B) 1 ((A ++ B).length - 1) = 0 ∧
              entry (A ++ B) 2 ((A ++ B).length - 1) = 0
          · exact oper_eq_pred_of_zero n (by rw [List.length_append]; omega) hzz
          · exact oper_eq_pred_of_noParent n (by rw [List.length_append]; omega)
              hzz (hnp _)
        rw [hpred]
        unfold Pred
        rw [if_neg (by rw [List.length_append]; omega),
          List.dropLast_append_of_ne_nil hBnil]
        have hdl : B.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
        rw [hdl]
        simpa using hA
    · by_cases hB2 : 2 ≤ B.length
      · refine hX _ (Or.inr (Or.inl ⟨(natDom_append hBnil hrs).mpr hn, fun n hn' => ?_⟩))
        rw [oper_append_gen n hB2 hrs]
        refine hop n hn' (fun p hp => ?_)
        rw [oper_head_eq hn']
        rcases List.mem_append.mp hp with hp | hp
        · exact hAge p hp
        · exact oper_mem_ge hBge p hp
      · have hB1 : B⟦1⟧ = B := oper_eq_self_of_short 1 (by omega)
        have h1 := hop 1 le_rfl
        rw [hB1] at h1
        exact h1 hrs
    · have h2' : entry (A ++ B) 2 ((A ++ B).length - 1) = 0 := by
        rw [show (A ++ B).length - 1 = A.length + (B.length - 1) by
          rw [List.length_append]; omega, entry_append_right]
        exact h2
      refine hX _ (Or.inr (Or.inr ⟨m, hm, (domT_append hBnil hrs).mpr hd, h2',
        fun z hz hbz => ?_⟩))
      rw [graft_append hBnil]
      refine hgr z hz hbz ?_
      by_cases hgz' : graft B z = []
      · rw [hgz']
        intro p hp
        simp [entry]
      · intro p hp
        rw [graft_head_eq hBnil hbz hgz']
        rcases List.mem_append.mp hp with hp | hp
        · exact hAge p hp
        · exact graft_mem_ge hBnil hBge p hp

/-- `Wg` は最上位の連結で閉じる。 -/
theorem Wg_add {u : ℕ} {A B : TrioSeq} (hA : A ∈ Wg u)
    (hB : B ∈ Wg u) (h : rsum A B) : A ++ B ∈ Wg u :=
  A2g' (XAg_closed (u := u) (X := Wg u) (fun _ hM => A1g_intro hM) hA) hB h

theorem Om_mem_Wg (v : ℕ) : [((0, v, 0) : ℕ × ℕ × ℕ)] ∈ Wg (2 * v) := by
  rcases Nat.eq_zero_or_pos v with h0 | hpos
  · subst h0
    exact A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)
  · have hd : domT [((0, v, 0) : ℕ × ℕ × ℕ)] (2 * v - 1) := by
      have := domT_Om (v := v) (z := 0) (by omega)
      simpa using this
    refine A1g_intro (Or.inr (Or.inr ⟨2 * v - 1, by omega, hd, by simp [entry], ?_⟩))
    intro y hy _
    rw [graft_Om]
    exact Wg_mono (by omega) hy

/-- 1 本の木の `n` 個の複製は `Wg` に残る。 -/
theorem Wg_flatMap_copies {u : ℕ} {Q : TrioSeq} (hQ : Q ∈ Wg u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) :
    ∀ n : ℕ, ((List.range n).flatMap fun _ => Q) ∈ Wg u := by
  intro n
  induction n with
  | zero => simpa using Wg_nil u
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      have hQ1 : ((List.flatMap fun _ => Q) [n]) = Q := by simp
      rw [hQ1]
      refine Wg_add ih hQ ?_
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rw [List.mem_flatMap] at hp
        obtain ⟨-, -, hp⟩ := hp
        exact hQr p hp
      · exact hQr p hp

#print axioms Wg_add
#print axioms Om_mem_Wg

/-! ## `W*`（ガードつき）: 根で潰した列が入る

`Wset.Wstar_closed` の写し。分岐 3 は srow = 1 なので塔は `oper_cons_tower1`、
死んだ孤児は `entry1_le_of_dead_one` で段の下にある。 -/

def Wstarg : Set TrioSeq :=
  {R | argOK R → ∀ v a : ℕ, 2 * v ≤ a → (((0, v, 0) : ℕ × ℕ × ℕ) :: R) ∈ Wg a}

theorem tower1_mem_g {v m a : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hva : 2 * v ≤ a) (hd : domT R m) (hi1 : srow R (R.length - 1) = 1)
    (hgr : ∀ y ∈ Wg m, based y → graft R y ∈ Wstarg)
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
        exact hgk (argOK_graft hRne hR _) v a' ha'
  exact fun k => key k a hva

/-- ★ `A_u(W*) ⊆ W*`（ガードつき、無条件）。 -/
theorem Wstarg_closed : ∀ (u0 : ℕ) (R : TrioSeq), Aopg Wg u0 Wstarg R → R ∈ Wstarg := by
  intro u0 R AR hR v a hva
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
    have hdlmem : R.dropLast ∈ Wstarg → (p0 :: R.dropLast) ∈ Wg a := by
      intro h
      exact h (argOK_dropLast hR) v a hva
    have hnatP : hasParent (p0 :: R) (srow R (R.length - 1)) R.length →
        natDom (p0 :: R) := by
      intro hp
      refine natDom_iff.mpr (Or.inr ?_)
      rw [hi1M, hMlen]; exact hp
    have hnatZ : lev R (R.length - 1) = 0 → natDom (p0 :: R) := by
      intro hz
      exact natDom_iff.mpr (Or.inl (by rw [hlevM]; exact hz))
    rcases AR with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, h2, hgr⟩
    · -- 分岐 1: `R = [(x,0,0)]`
      have hR1 : R.length = 1 := by omega
      have hw' : lev R (R.length - 1) = 0 := by rw [hR1]; exact hw
      have hnp : ¬ hasParent R 0 (R.length - 1) := by
        rw [hR1]
        rintro ⟨j0, hj0, -⟩
        exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
      have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine A1g_intro (Or.inr (Or.inl ⟨hnatZ hw', fun n hn => ?_⟩))
      rw [oper_cons_succ hR hRnil hw' hnp, hdl]
      exact Wg_flatMap_copies (Wg_mono hva (Om_mem_Wg v)) (rsum_self_cons v 0 []) n
    · -- 分岐 2: `natDom R` と展開
      have hpredmem : ¬ hasParent R (srow R (R.length - 1)) (R.length - 1) →
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
        exact hop n hn (argOK_oper hR n) v a hva
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
    · -- 分岐 3: srow = 1 の孤児と graft の閉包
      have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
      have hi1 : srow R (R.length - 1) = 1 := by
        unfold srow
        unfold lev at hlevpos
        rw [if_neg (by omega), if_pos (by omega)]
      by_cases hpM : hasParent (p0 :: R) (srow R (R.length - 1)) R.length
      · -- 根が復活させる: 塔
        refine A1g_intro (Or.inr (Or.inl ⟨hnatP hpM, fun n hn => ?_⟩))
        rw [oper_cons_tower1 hR hRnil hd hi1 hpM]
        exact tower1_mem_g hR hRnil hva hd hi1 hgr hpM n
      · -- 死んだまま: 段の下にあるので graft の節が根を越えて残る
        have hdM : domT (p0 :: R) m := domT_cons_of_dead hRnil hd hpM
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
        exact hgr y hy hby (argOK_graft hRnil hR y) v a hva

/-! ## 長さの帰納: 行 2 ≡ 0 の列は全部 `Wg` -/

def Z2s (M : TrioSeq) : Prop := ∀ p ∈ M, p.2.2 = 0

theorem mem_of_Aclosed_g_aux : ∀ (N : ℕ) (M : TrioSeq), M.length ≤ N → Z2s M →
    ∀ X : Set TrioSeq, (∀ (u : ℕ) (M' : TrioSeq), Aopg Wg u X M' → M' ∈ X) →
      M ∈ X := by
  intro N
  induction N with
  | zero =>
      intro M hM _ X hX
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact hX 0 [] (Or.inl ⟨by simp, by simp [lev, entry]⟩)
  | succ N ih =>
      intro M hM hzM X hX
      by_cases hMnil : M = []
      · subst hMnil; exact hX 0 [] (Or.inl ⟨by simp, by simp [lev, entry]⟩)
      · obtain ⟨A, P, hEq, hPne, hrs, htail⟩ := split_lastMin hMnil
        subst hEq
        have hPlen : 0 < P.length := List.length_pos_iff.mpr hPne
        have hMlen : A.length + P.length ≤ N + 1 := by
          rw [List.length_append] at hM; exact hM
        by_cases hAnil : A = []
        · subst hAnil
          obtain ⟨p0, R, rfl⟩ : ∃ p0 R, P = p0 :: R := by
            cases P with
            | nil => exact absurd rfl hPne
            | cons a b => exact ⟨a, b, rfl⟩
          have hRgt : ∀ q ∈ R, p0.1 < q.1 := by
            intro q hq
            have := htail q (by simpa using hq)
            simpa [entry] using this
          have hargOK : argOK (shiftl0 p0.1 R) := by
            intro q hq
            rw [mem_shiftl0] at hq
            obtain ⟨r, hr, rfl⟩ := hq
            have := hRgt r hr
            simp only []
            omega
          have hWs : shiftl0 p0.1 R ∈ Wstarg := by
            refine ih _ ?_ ?_ Wstarg Wstarg_closed
            · rw [shiftl0_length]
              simp only [List.length_cons] at hMlen
              omega
            · intro q hq
              rw [mem_shiftl0] at hq
              obtain ⟨r, hr, rfl⟩ := hq
              exact hzM r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
          have hz0 : p0.2.2 = 0 := hzM p0 (List.mem_append_right _ List.mem_cons_self)
          have hmem : (((0, p0.2.1, 0) : ℕ × ℕ × ℕ) :: shiftl0 p0.1 R)
              ∈ Wg (2 * p0.2.1) := hWs hargOK p0.2.1 (2 * p0.2.1) le_rfl
          have hQeq : (((0, p0.2.1, 0) : ℕ × ℕ × ℕ) :: shiftl0 p0.1 R)
              = shiftl0 p0.1 (p0 :: R) := by
            rw [shiftl0_cons]
            congr 1
            exact Prod.ext (by dsimp only; omega) (Prod.ext rfl hz0.symm)
          have hPsub : ∀ x ∈ (p0 :: R), p0.1 ≤ x.1 := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_rfl
            · exact le_of_lt (hRgt x hx)
          have hP : (p0 :: R) ∈ Wg (2 * p0.2.1) := by
            have h := Wg_shift (hQeq ▸ hmem) p0.1
            rwa [shiftr01_shiftl0 hPsub] at h
          simp only [List.nil_append]
          exact A2g' (fun M' h => hX (2 * p0.2.1) M' h) hP
        · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
          have hAX : A ∈ X := ih A (by omega)
            (fun q hq => hzM q (List.mem_append_left _ hq)) X hX
          have hPX : P ∈ XA A X := ih P (by omega)
            (fun q hq => hzM q (List.mem_append_right _ hq)) (XA A X)
            (fun u M' h => XAg_closed (fun M'' h'' => hX u M'' h'') hAX M' h)
          exact hPX hrs

theorem mem_Wstarg (R : TrioSeq) (hz : Z2s R) : R ∈ Wstarg :=
  mem_of_Aclosed_g_aux R.length R le_rfl hz Wstarg Wstarg_closed

/-- 1 本の木（根が一番浅い）は根のレベルの `Wg` に入る。 -/
theorem tree_mem_Wg {p0 : ℕ × ℕ × ℕ} {R : TrioSeq} (hz : Z2s (p0 :: R))
    (hRgt : ∀ q ∈ R, p0.1 < q.1) : (p0 :: R) ∈ Wg (2 * p0.2.1) := by
  have hargOK : argOK (shiftl0 p0.1 R) := by
    intro q hq
    rw [mem_shiftl0] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have := hRgt r hr
    simp only []
    omega
  have hWs : shiftl0 p0.1 R ∈ Wstarg := by
    refine mem_Wstarg _ ?_
    intro q hq
    rw [mem_shiftl0] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact hz r (List.mem_cons_of_mem _ hr)
  have hz0 : p0.2.2 = 0 := hz p0 List.mem_cons_self
  have hmem : (((0, p0.2.1, 0) : ℕ × ℕ × ℕ) :: shiftl0 p0.1 R) ∈ Wg (2 * p0.2.1) :=
    hWs hargOK p0.2.1 (2 * p0.2.1) le_rfl
  have hQeq : (((0, p0.2.1, 0) : ℕ × ℕ × ℕ) :: shiftl0 p0.1 R)
      = shiftl0 p0.1 (p0 :: R) := by
    rw [shiftl0_cons]
    congr 1
    exact Prod.ext (by dsimp only; omega) (Prod.ext rfl hz0.symm)
  have hPsub : ∀ x ∈ (p0 :: R), p0.1 ≤ x.1 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt (hRgt x hx)
  have h := Wg_shift (hQeq ▸ hmem) p0.1
  rwa [shiftr01_shiftl0 hPsub] at h

/-- ★★ 行 2 ≡ 0 の列は、行 1 の上限 `u/2` があれば `Wg u` に入る。 -/
theorem mem_Wg_of_bound : ∀ (N : ℕ) (M : TrioSeq), M.length ≤ N → Z2s M →
    ∀ u : ℕ, (∀ p ∈ M, 2 * p.2.1 ≤ u) → M ∈ Wg u := by
  intro N
  induction N with
  | zero =>
      intro M hM _ u _
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact Wg_nil u
  | succ N ih =>
      intro M hM hzM u hbd
      by_cases hMnil : M = []
      · subst hMnil; exact Wg_nil u
      · obtain ⟨A, P, hEq, hPne, hrs, htail⟩ := split_lastMin hMnil
        subst hEq
        have hMlen : A.length + P.length ≤ N + 1 := by
          rw [List.length_append] at hM; exact hM
        have hPlen : 0 < P.length := List.length_pos_iff.mpr hPne
        obtain ⟨p0, R, hPeq⟩ : ∃ p0 R, P = p0 :: R := by
          cases P with
          | nil => exact absurd rfl hPne
          | cons a b => exact ⟨a, b, rfl⟩
        subst hPeq
        have hRgt : ∀ q ∈ R, p0.1 < q.1 := by
          intro q hq
          have := htail q (by simpa using hq)
          simpa [entry] using this
        have hP : (p0 :: R) ∈ Wg (2 * p0.2.1) :=
          tree_mem_Wg (fun q hq => hzM q (List.mem_append_right _ hq)) hRgt
        have hPu : (p0 :: R) ∈ Wg u :=
          Wg_mono (hbd p0 (List.mem_append_right _ List.mem_cons_self)) hP
        by_cases hAnil : A = []
        · subst hAnil; simpa using hPu
        · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
          have hAu : A ∈ Wg u :=
            ih A (by simp only [List.length_cons] at hMlen; omega)
              (fun q hq => hzM q (List.mem_append_left _ hq)) u
              (fun p hp => hbd p (List.mem_append_left _ hp))
          exact Wg_add hAu hPu hrs

#print axioms Wstarg_closed
#print axioms mem_Wg_of_bound

end Gw
end TRIO
