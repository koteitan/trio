/-
**新しい構造の不変条件 RowJ: 行 2 が正の列に入る辺で、行 1 は下がらない。**

RowJ M: e2 c ≠ 0 かつ P_0 c = q なら e1 q ≤ e1 c。
- 標準形の接頭辞閉包 C′（404051 個）で例外 0。SInvX からは出ない（ランダムな SInvX 行列の 0.6% で偽）。
- t = 2・q ≠ r の構造の事実（x は q ののりしろの子など）の根拠（V3InvT2）。
- 展開で保たれる（`rowJ_expand`）: 種 S を経由する。ブロックの中の辺はガードの比較で、コピーの根の辺は
  S の x の辺で示す。t = 2 では r の子はすべてガードされる（`e1_child_r`）。
-/
import Ytosk.V3InvExpand
import Ytosk.V3VLocT1

namespace Ytosk

open T Classical

/-- **Row 1 does not drop into a column with row 2 nonzero.** -/
def RowJ (M : Mat) : Prop :=
  ∀ c q, entry M 2 c ≠ 0 → par M 0 c = some q → entry M 1 q ≤ entry M 1 c

theorem rowJ_take {M : Mat} (h : RowJ M) (k : Nat) : RowJ (M.take k) := by
  intro c q h2 hp
  have hc : c < k := by
    by_contra hc
    exact h2 (entry_out (by simp [List.length_take]; omega) 2)
  have hqc := par_lt _ 0 c q hp
  rw [par_take M 0 c hc] at hp
  rw [entry_take M 2 hc] at h2
  rw [entry_take M 1 hc, entry_take M 1 (by omega)]
  exact h c q h2 hp

/-- The guard from the parent, when row 1 does not drop. -/
theorem guard_eq {M : Mat} {r P C : Nat} (hrP : Anc0 M r P) (hp : par M 0 C = some P)
    (hC : C < M.length) (hg : TRIO.le1 M r P) (hPr : P ≠ r) (h1 : entry M 1 P ≤ entry M 1 C) :
    TRIO.le1 M r C := by
  have hPC := par_lt M 0 C P hp
  have hrC : Anc0 M r C := Anc0.step hp hrP
  have hgP := (le1_window (by omega) hrP).mp hg
  rw [le1_window hC hrC]
  intro y hy1 hy2 hy3
  by_cases hyC : y = C
  · subst hyC
    exact lt_of_lt_of_le (hgP P hrP (Anc0.refl P) hPr) h1
  · exact hgP y hy1 (anc0_par hy2 hyC hp) hy3

/-! ## 種からの展開 -/

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

theorem Seed.rowJ (hJ : RowJ S)
    (hGr : 0 < d1 → ∀ q, 0 < q → q < L → par S 0 (r + q) = some r → TRIO.le1 S r (r + q))
    (hn : 1 ≤ n) : RowJ (TRIO.gexp S r L d0 d1 n) := by
  have hlS := hS.len
  have hL := hS.pos
  intro d p h2 hp
  have hdN : d < (TRIO.gexp S r L d0 d1 n).length := by
    by_contra h; exact h2 (entry_out (by omega) 2)
  rcases hS.parN hn hdN hp with ⟨hdl, hpS⟩ | ⟨c, q, P, hc1, hc, hq0, hq, rfl, hP, hrP, rfl⟩ |
      ⟨c, P, hc1, hc, rfl, hAs, hg, hP, hrP, rfl⟩ | ⟨c, hc1, hc, rfl, hd0, hd1, hpS⟩
  · have hpl := par_lt S 0 d p hpS
    rw [hS.eN_pre hn 2 hdl] at h2
    rw [hS.eN_pre hn 1 hdl, hS.eN_pre hn 1 (by omega)]
    exact hJ d p h2 hpS
  · have hPq := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rw [e2N_blk hS.len hc hq] at h2
    rw [e1N_blk hS.len hc hq, hS.e1N_sh hc hrP' (by omega)]
    have hj := hJ (r + q) P h2 hP
    rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
    · subst hd1; simpa using hj
    by_cases hgq : TRIO.le1 S r (r + q)
    · rw [if_pos hgq]; split_ifs <;> omega
    · rw [if_neg hgq]
      by_cases hgP : TRIO.le1 S r P
      · exfalso
        by_cases hPr : P = r
        · subst hPr; exact hgq (hGr hd1 q hq0 hq hP)
        · exact hgq (guard_eq hrP hP (by omega) hgP hPr hj)
      · rw [if_neg hgP]; omega
  · have hPs := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rw [hS.e2N_root hc] at h2
    rw [hS.e1N_root hc1 hc, hS.e1N_sh (by omega) hrP' (by omega)]
    have hj := hJ (r + L) P h2 hP
    have : (c - 1) * d1 ≥ 0 := Nat.zero_le _
    split_ifs <;> omega
  · subst hd0 hd1
    have hpr := par_lt S 0 _ _ hpS
    rw [hS.e2N_root hc, hS.e2s] at h2
    rw [hS.e1N_root hc1 hc, hS.eN_pre hn 1 (by omega), hS.e1s]
    have := hJ r p h2 hpS
    omega

end

/-! ## M から種へ -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
include hx

/-- `RowJ` passes to the seed when row 2 of the root is `0`, or (`t = 0`) the new parent is that of `r`. -/
theorem rowJ_seed {r d0 d1 : Nat} (hJ : RowJ M) (hrx : r < x)
    (hcase : entry M 2 r = 0 ∨ (d0 = 0 ∧ d1 = 0 ∧ par (seedOf M r d0 d1) 0 x = par M 0 r)) :
    RowJ (seedOf M r d0 d1) := by
  intro c q h2 hp
  have hcx : c ≤ x := by
    by_contra h; exact h2 (entry_out (by rw [seed_len hx]; omega) 2)
  have hqc := par_lt _ 0 c q hp
  rcases Nat.lt_or_ge c x with h | h
  · rw [seed_par_lt hx 0 h] at hp
    rw [seed_entry_lt hx 2 h] at h2
    rw [seed_entry_lt hx 1 h, seed_entry_lt hx 1 (by omega)]
    exact hJ c q h2 hp
  · have hce : c = x := by omega
    subst hce
    rw [seed_e2x hx] at h2
    rcases hcase with h0 | ⟨rfl, rfl, hpx⟩
    · exact absurd h0 h2
    · rw [hpx] at hp
      have hqr := par_lt M 0 r q hp
      rw [seed_e1x hx, seed_entry_lt hx 1 (by omega)]
      have := hJ r q h2 hp
      omega

/-- The children of `r` are guarded in the seed (`t = 2`). -/
theorem seed_child_guard (hR0 : R0P M) (hSD : SibDec M) {r d0 d1 : Nat} (h1 : par M 1 x = some r)
    {q : Nat} (hq : r + q < x) (hp : par (seedOf M r d0 d1) 0 (r + q) = some r) :
    TRIO.le1 (seedOf M r d0 d1) r (r + q) := by
  rw [seed_par_lt hx 0 hq] at hp
  have hc : r + q ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hlt := e1_child_r hx hR0 hSD h1 hc
  have hM : TRIO.le1 M r (r + q) :=
    guard_up (Anc0.refl r) hp (by omega) (le1_self (by have := par_lt M 0 _ _ hp; omega)) hlt
  exact TRIO.le1_of_agree (by rw [seed_len hx]; omega) (by omega)
    (fun j hj => seed_getD_lt hx (by omega)) hM

end

/-! ## 展開 -/

/-- `P_1 x = P_2 x` when `t = 2`. -/
theorem par1_of_par2 {M : Mat} {x r : Nat} (hZ2 : Z2 M) (hZ1 : Z1C M) (hxM : x < M.length)
    (h2 : par M 2 x = some r) : par M 1 x = some r := by
  have he2x : 0 < entry M 2 x := by
    obtain ⟨_, _, _, he2, _⟩ := (par2_iff M hxM).mp h2
    have : entry M 2 r < entry M 2 x := he2
    omega
  cases hm : par M 1 x with
  | none =>
    exfalso
    have : par M 2 x = climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 x)) (x + 1)
      (par M 1 x) := rfl
    rw [this, hm, climb_none] at h2; cases h2
  | some m =>
    have hA := anc0_of_par M 1 m x hm
    have hmx := par_lt M 1 x m hm
    have hm2 : entry M 2 m = 0 := e2_r_zero hm hA (by omega) hZ2 hZ1
    have : par M 2 x = climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 x)) (x + 1)
      (par M 1 x) := rfl
    rw [this, hm] at h2
    simp [climb, hm2, he2x] at h2
    rw [h2]

theorem rowJ_of_seed {M : Mat} {r d0 d1 x n : Nat} (hx : x + 1 = M.length) (hrx : r < x)
    (hS : Seed (seedOf M r d0 d1) r (x - r) d0 d1) (hJ : RowJ (seedOf M r d0 d1))
    (hGr : 0 < d1 → ∀ q, 0 < q → q < x - r → par (seedOf M r d0 d1) 0 (r + q) = some r →
      TRIO.le1 (seedOf M r d0 d1) r (r + q))
    (hn : 1 ≤ n) : RowJ (TRIO.gexp M r (x - r) d0 d1 n) := by
  have hc : TRIO.gexp (seedOf M r d0 d1) r (x - r) d0 d1 n = TRIO.gexp M r (x - r) d0 d1 n :=
    gexp_congr (by rw [seed_len hx]; omega) (by omega) (fun j hj => seed_getD_lt hx (by omega))
  rw [← hc]
  exact hS.rowJ hJ hGr hn

/-- `RowJ` survives every expansion (only `R0P`・`Z2`・`SibDec`・`Z1C` are used). -/
theorem rowJ_expand' {M : Mat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hJ : RowJ M) (n : Nat) : RowJ (expand M n) := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]; simpa using rowJ_take hJ 0
  rcases expand_cases M n (by omega) with he | ⟨r, hp, he⟩
  · rw [he]; exact rowJ_take hJ _
  rw [he]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [gexp_n0]; exact rowJ_take hJ r
  have hx : (M.length - 1) + 1 = M.length := by omega
  have hxM : M.length - 1 < M.length := by omega
  unfold TRIO.srow at hp ⊢
  by_cases h2 : 0 < TRIO.entry M 2 (M.length - 1)
  · simp only [h2, if_true] at hp ⊢
    have hrx := par_lt M 2 _ r hp
    obtain ⟨_, _, _, he2, hle, _⟩ := (par2_iff M hxM).mp hp
    have hA := anc0_of_par M 2 r _ hp
    have hx2 := hZ2 (M.length - 1)
    have he2' : entry M 2 r < entry M 2 (M.length - 1) := he2
    have h0lt := anc0_e0_lt hA (by omega)
    have h1lt : entry M 1 r < entry M 1 (M.length - 1) :=
      (le1_window hxM hA).mp hle _ hA (Anc0.refl _) (by omega)
    have he0 : entry M 0 r + (entry M 0 (M.length - 1) - entry M 0 r) = entry M 0 (M.length - 1) := by
      omega
    have he1 : entry M 1 r + (entry M 1 (M.length - 1) - entry M 1 r) = entry M 1 (M.length - 1) := by
      omega
    have hS := seed_seed_ge1 (d1 := entry M 1 (M.length - 1) - entry M 1 r) hx hrx hA he0 (fun _ =>
      TRIO.le1_of_agree_last (by rw [seed_len hx]; omega) hxM (fun j hj => seed_getD_lt hx hj)
        (by rw [seed_getD_x hx]; simp only; rw [← entry0_getD]; exact he0)
        (by rw [seed_getD_x hx]; simp only; rw [← entry1_getD]; exact he1) hle)
    have h1 := par1_of_par2 hZ2 hZ1 hxM hp
    exact rowJ_of_seed hx hrx hS (rowJ_seed hx hJ hrx (Or.inl (by omega)))
      (fun _ q _ hq hpq => seed_child_guard hx hR0 hSD h1 (by omega) hpq) hn
  · simp only [h2, if_false] at hp ⊢
    by_cases h1x : 0 < TRIO.entry M 1 (M.length - 1)
    · simp only [h1x, if_true] at hp ⊢
      have hrx := par_lt M 1 _ r hp
      have hA := anc0_of_par M 1 r _ hp
      have h0lt := anc0_e0_lt hA (by omega)
      have he0 : entry M 0 r + (entry M 0 (M.length - 1) - entry M 0 r) =
          entry M 0 (M.length - 1) := by omega
      have hS := seed_seed_ge1 (d1 := 0) hx hrx hA he0 (fun h => absurd h (by omega))
      have hr2 : entry M 2 r = 0 := e2_r_zero hp hA (by omega) hZ2 hZ1
      exact rowJ_of_seed hx hrx hS (rowJ_seed hx hJ hrx (Or.inl hr2))
        (fun h => absurd h (Nat.lt_irrefl 0)) hn
    · simp only [h1x, if_false] at hp ⊢
      have hrx := par_lt M 0 _ r hp
      have hS := seed_seed0 hx hp
      exact rowJ_of_seed hx hrx hS (rowJ_seed hx hJ hrx (Or.inr ⟨rfl, rfl, seed_par_x0 hx hp⟩))
        (fun h => absurd h (Nat.lt_irrefl 0)) hn

theorem rowJ_expand {M : Mat} (h : SInvX M) (hJ : RowJ M) (n : Nat) : RowJ (expand M n) :=
  rowJ_expand' h.r0p h.z2 h.loc.1 h.loc.2.1 hJ n

/-! ## SRO と Std -/

theorem sro_rowJ : RowJ SRO := by
  have := par0_of_lt (M := SRO) (P := fun c q => entry SRO 2 c ≠ 0 → entry SRO 1 q ≤ entry SRO 1 c)
    (by decide)
  exact fun c q h2 hp => this c q hp h2

theorem sro_sibDec : SibDec SRO := by
  have hsd : ∀ p, p < SRO.length → ∀ a ∈ children SRO p, ∀ b ∈ children SRO p, a < b →
      (∀ e ∈ children SRO p, ¬ (a < e ∧ e < b)) → colLe (col SRO b) (col SRO a) := by decide
  intro p l1 l2 a b hch
  obtain ⟨hab, ha, hb, hno⟩ := split_consec (children_sorted SRO p) hch
  have := mem_children ha
  exact hsd p (by omega) a ha b hb hab hno

theorem sro_z1c : Z1C SRO := by
  have hz1 : ∀ p, p < SRO.length → entry SRO 2 p = 1 → ∀ c ∈ children SRO p,
      entry SRO 1 c ≤ entry SRO 1 p := by decide
  intro p c h2 hc
  have := mem_children hc
  exact hz1 p (by omega) h2 c hc

/-- **Every standard matrix satisfies `RowJ`.** -/
theorem rowJ_std {M : Mat} (h : Std M) : RowJ M := by
  induction h with
  | sro => exact sro_rowJ
  | @exp M n hM ih =>
    rcases sInvX_std' hM with h | h
    · subst h
      obtain ⟨hR0, _, hZ2, _⟩ := sro_cols
      exact rowJ_expand' hR0 hZ2 sro_sibDec sro_z1c ih n
    · exact rowJ_expand h ih n

/-- **The structural invariants with `RowJ`** (every standard matrix other than SRO). -/
theorem sInvXJ_std {M : Mat} (h : Std M) (hne : M ≠ SRO) : SInvX M ∧ RowJ M :=
  ⟨(sInvX_std' h).resolve_left hne, rowJ_std h⟩

end Ytosk
