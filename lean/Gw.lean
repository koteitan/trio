/-
Gw.lean: ガードつきの W 階層（lean-yapss の `W*` の議論の移植）。

`Wset.Aop` との違いは 2 点だけ:
- 分岐 2 に `natDom` ガード（末尾が正レベルの孤児なら展開では入れない）。
- 分岐 3 の graft は `Gd z` を満たす `z` に限る（`Gd` は引数）。

ガードがあると、孤児の末尾は分岐 3 でしか入らないので graft の情報が必ず残る
（`Wset` の `TowerExp` が空になる）。trio 全体ではガードは反証済み
（死んだ孤児 `(x,0,1)`）だが、Mono の世界では起きない。
-/
import Wset

namespace TRIO
namespace Gw

open Wset

/-! ## 演算子と族 -/

/-- ガードつきの演算子 `A_u`。 -/
def Aopg (Gd : TrioSeq → Prop) (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq)
    (M : TrioSeq) : Prop :=
  (M.length ≤ 1 ∧ lev M 0 = 0) ∨
  (natDom M ∧ ∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m : ℕ, m < u ∧ domT M m ∧
    ∀ z ∈ Wfam m, based z → Gd z → graft M z ∈ X)

def Asetg (Gd : TrioSeq → Prop) (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) :
    Set TrioSeq :=
  {M | Aopg Gd Wfam u X M}

theorem Aopg_mono_X {Gd : TrioSeq → Prop} {Wfam : ℕ → Set TrioSeq} {u : ℕ}
    {X Y : Set TrioSeq} {M : TrioSeq} (h : Aopg Gd Wfam u X M) (hXY : X ⊆ Y) :
    Aopg Gd Wfam u Y M := by
  rcases h with h | ⟨hn, h⟩ | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hn, fun n hn' => hXY (h n hn')⟩)
  · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb hg => hXY (hop z hz hb hg)⟩)

theorem Asetg_mono (Gd : TrioSeq → Prop) (Wfam : ℕ → Set TrioSeq) (u : ℕ) :
    Monotone (Asetg Gd Wfam u) := by
  intro X Y hXY M hM
  exact Aopg_mono_X (Wfam := Wfam) (u := u) hM hXY

theorem Aopg_mono_level {Gd : TrioSeq → Prop} {Wfam : ℕ → Set TrioSeq} {u v : ℕ}
    {X : Set TrioSeq} {M : TrioSeq} (le : u ≤ v) (h : Aopg Gd Wfam u X M) :
    Aopg Gd Wfam v X M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, lt_of_lt_of_le hm le, hd, hop⟩)

theorem Aopg_cong {Gd : TrioSeq → Prop} {Wfam Wgam : ℕ → Set TrioSeq} {u : ℕ}
    {X : Set TrioSeq} {M : TrioSeq} (e : ∀ m : ℕ, m < u → Wfam m = Wgam m) :
    Aopg Gd Wfam u X M ↔ Aopg Gd Wgam u X M := by
  constructor
  · rintro (h | h | ⟨m, hm, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz => hop z ((e m hm) ▸ hz)⟩)
  · rintro (h | h | ⟨m, hm, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz => hop z ((e m hm).symm ▸ hz)⟩)

/-- 段の族: `Wfg Gd n m` は `m < n` で `Wg Gd m`。 -/
def Wfg (Gd : TrioSeq → Prop) : ℕ → ℕ → Set TrioSeq
  | 0 => fun _ => ∅
  | v + 1 => fun m => if m = v then lfpS (Asetg Gd (Wfg Gd v) v) else Wfg Gd v m

/-- ガードつきの `W_u`。 -/
def Wg (Gd : TrioSeq → Prop) (u : ℕ) : Set TrioSeq := Wfg Gd (u + 1) u

theorem Wfg_coh (Gd : TrioSeq → Prop) {m n : ℕ} (h : m < n) :
    Wfg Gd n m = Wfg Gd (m + 1) m := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ v ih =>
      by_cases hmv : m = v
      · subst hmv; rfl
      · have mlv : m < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hmv
        show (if m = v then _ else Wfg Gd v m) = _
        rw [if_neg hmv]
        exact ih mlv

theorem Wfg_eq_Wg (Gd : TrioSeq → Prop) {m n : ℕ} (h : m < n) : Wfg Gd n m = Wg Gd m :=
  Wfg_coh Gd h

theorem Wg_unfold (Gd : TrioSeq → Prop) (u : ℕ) : Wg Gd u = lfpS (Asetg Gd (Wg Gd) u) := by
  have stage : Wg Gd u = lfpS (Asetg Gd (Wfg Gd u) u) := by
    show Wfg Gd (u + 1) u = _
    show (if u = u then _ else Wfg Gd u u) = _
    rw [if_pos rfl]
  have cong : ∀ m : ℕ, m < u → Wfg Gd u m = Wg Gd m := fun m hm => Wfg_eq_Wg Gd hm
  have ptw : ∀ X : Set TrioSeq, Asetg Gd (Wfg Gd u) u X = Asetg Gd (Wg Gd) u X := by
    intro X; ext M
    exact Aopg_cong (Wfam := Wfg Gd u) (Wgam := Wg Gd) (u := u) (X := X) cong
  rw [stage, funext ptw]

theorem A1g (Gd : TrioSeq → Prop) (u : ℕ) : Asetg Gd (Wg Gd) u (Wg Gd u) = Wg Gd u := by
  rw [Wg_unfold Gd u]
  exact lfpS_unfold (Asetg_mono Gd (Wg Gd) u)

theorem A2g {Gd : TrioSeq → Prop} {u : ℕ} {Y : Set TrioSeq}
    (h : Asetg Gd (Wg Gd) u Y ⊆ Y) : Wg Gd u ⊆ Y := by
  rw [Wg_unfold Gd u]
  exact lfpS_lowerbound h

theorem A2g' {Gd : TrioSeq → Prop} {u : ℕ} {Y : Set TrioSeq}
    (hY : ∀ M : TrioSeq, Aopg Gd (Wg Gd) u Y M → M ∈ Y) : Wg Gd u ⊆ Y :=
  A2g (fun M hM => hY M hM)

theorem A1g_intro {Gd : TrioSeq → Prop} {u : ℕ} {M : TrioSeq}
    (h : Aopg Gd (Wg Gd) u (Wg Gd u) M) : M ∈ Wg Gd u := by
  have : M ∈ Asetg Gd (Wg Gd) u (Wg Gd u) := h
  rwa [A1g Gd u] at this

theorem Wg_nil (Gd : TrioSeq → Prop) (u : ℕ) : ([] : TrioSeq) ∈ Wg Gd u :=
  A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)

theorem Wg_mono {Gd : TrioSeq → Prop} {u v : ℕ} (h : u ≤ v) : Wg Gd u ⊆ Wg Gd v :=
  A2g' (fun _ A => A1g_intro (Aopg_mono_level h A))

/-! ## ずらし・連結・根 1 列 -/

theorem Wg_shift {Gd : TrioSeq → Prop} {u : ℕ} {M : TrioSeq} (h : M ∈ Wg Gd u) (d : ℕ) :
    shiftr01 d 0 M ∈ Wg Gd u := by
  have hsub : Wg Gd u ⊆ {N : TrioSeq | shiftr01 d 0 N ∈ Wg Gd u} := by
    refine A2g' ?_
    intro N A
    refine A1g_intro ?_
    rcases A with ⟨hl, hw⟩ | ⟨hn, hop⟩ | ⟨m, hm, hd, hgr⟩
    · refine Or.inl ⟨by rw [shiftr01_length]; exact hl, ?_⟩
      rw [lev_shiftr01]
      exact hw
    · exact Or.inr (Or.inl ⟨natDom_shiftr01.mpr hn, fun n hn' => by
        rw [oper_shiftr01]
        exact hop n hn'⟩)
    · refine Or.inr (Or.inr ⟨m, hm, domT_shiftr01.mpr hd, fun z hz hb hg => ?_⟩)
      have hne : N ≠ [] := by rintro rfl; exact not_domT_nil m hd
      rw [graft_shiftr01 hne]
      exact hgr z hz hb hg
  exact hsub h

set_option maxHeartbeats 1000000 in
/-- `A_u(X) ⊆ X` かつ `A ∈ X` なら `A_u(X⁽ᴬ⁾) ⊆ X⁽ᴬ⁾`（ガードつき）。 -/
theorem XAg_closed {Gd : TrioSeq → Prop} {u : ℕ} {X : Set TrioSeq}
    (hX : ∀ M : TrioSeq, Aopg Gd (Wg Gd) u X M → M ∈ X) {A : TrioSeq} (hA : A ∈ X) :
    ∀ M : TrioSeq, Aopg Gd (Wg Gd) u (XA A X) M → M ∈ XA A X := by
  intro B AB hrs
  by_cases hBnil : B = []
  · subst hBnil; simpa using hA
  · have hBlen : 0 < B.length := List.length_pos_iff.mpr hBnil
    have hBge : ∀ p ∈ B, entry B 0 0 ≤ p.1 :=
      fun p hp => hrs p (List.mem_append_right _ hp)
    have hAge : ∀ p ∈ A, entry B 0 0 ≤ p.1 :=
      fun p hp => hrs p (List.mem_append_left _ hp)
    rcases AB with ⟨hl, hw⟩ | ⟨hn, hop⟩ | ⟨m, hm, hd, hgr⟩
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
    · refine hX _ (Or.inr (Or.inr ⟨m, hm, (domT_append hBnil hrs).mpr hd,
        fun z hz hbz hgz => ?_⟩))
      rw [graft_append hBnil]
      refine hgr z hz hbz hgz ?_
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
theorem Wg_add {Gd : TrioSeq → Prop} {u : ℕ} {A B : TrioSeq} (hA : A ∈ Wg Gd u)
    (hB : B ∈ Wg Gd u) (h : rsum A B) : A ++ B ∈ Wg Gd u :=
  A2g' (XAg_closed (u := u) (X := Wg Gd u) (fun _ hM => A1g_intro hM) hA) hB h

theorem Om_mem_Wg (Gd : TrioSeq → Prop) (v z : ℕ) :
    [((0, v, z) : ℕ × ℕ × ℕ)] ∈ Wg Gd (2 * v + z) := by
  rcases Nat.eq_zero_or_pos (2 * v + z) with h0 | hpos
  · rw [h0]
    exact A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]; omega⟩)
  · refine A1g_intro (Or.inr (Or.inr ⟨2 * v + z - 1, by omega, domT_Om hpos, ?_⟩))
    intro y hy _ _
    rw [graft_Om]
    exact Wg_mono (by omega) hy

/-- 1 本の木の `n` 個の複製は `Wg` に残る。 -/
theorem Wg_flatMap_copies {Gd : TrioSeq → Prop} {u : ℕ} {Q : TrioSeq} (hQ : Q ∈ Wg Gd u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) :
    ∀ n : ℕ, ((List.range n).flatMap fun _ => Q) ∈ Wg Gd u := by
  intro n
  induction n with
  | zero => simpa using Wg_nil Gd u
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

end Gw
end TRIO
