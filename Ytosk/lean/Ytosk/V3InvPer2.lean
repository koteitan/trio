/-
**周期的な種からの展開: 親子の組の性質（Z1C・BumpE2）。**

`Seed S r L d0 d1`: 長さ・ブロックは r の部分木・最後の列 s の列は col r + (d0, d1, 0)・
s の親は（t ≥ 1）ブロックの中で s のガードが立つか、（t = 0）r の親と同じで d0 = d1 = 0。
N の子 d は、s より前なら S と同じ親、ブロックの中なら S の親のずらし、コピーの根なら
前のブロックの「s の親」のずらし（t ≥ 1）か r の親（t = 0）。列のずれはガードつきで、
子のガードは親のガードを含む（`guard_par`）ので、行 1 の比較は S での比較に戻る。
-/
import Ytosk.V3InvPer

namespace Ytosk

open T Classical

/-- **A periodic seed**: the last column `s = r + L` is the column that the expansion puts there. -/
structure Seed (S : Mat) (r L d0 d1 : Nat) : Prop where
  len : r + L + 1 = S.length
  pos : 0 < L
  blk : ∀ q, q < L → Anc0 S r (r + q)
  colS : col S (r + L) = (entry S 0 r + d0, entry S 1 r + d1, entry S 2 r)
  root : (Anc0 S r (r + L) ∧ (0 < d1 → TRIO.le1 S r (r + L))) ∨
    (d0 = 0 ∧ d1 = 0 ∧ par S 0 (r + L) = par S 0 r)

theorem mul_pred_add {c d : Nat} (hc : 1 ≤ c) : c * d = d + (c - 1) * d := by
  cases c with
  | zero => omega
  | succ c' => simp [Nat.succ_mul]; omega

theorem le1_self {M : Mat} {r : Nat} (hr : r < M.length) : TRIO.le1 M r r :=
  ⟨hr, hr, Relation.ReflTransGen.refl⟩

theorem anc0_par_exists {M : Mat} {a b : Nat} (h : Anc0 M a b) (hne : a ≠ b) :
    ∃ p, par M 0 b = some p ∧ Anc0 M a p := by
  cases h with
  | refl => exact absurd rfl hne
  | step hp hA => exact ⟨_, hp, hA⟩

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

theorem Seed.e0s : entry S 0 (r + L) = entry S 0 r + d0 := by
  have := hS.colS; rw [col_eq_entries] at this; simp only [Prod.mk.injEq] at this; exact this.1
theorem Seed.e1s : entry S 1 (r + L) = entry S 1 r + d1 := by
  have := hS.colS; rw [col_eq_entries] at this; simp only [Prod.mk.injEq] at this; exact this.2.1
theorem Seed.e2s : entry S 2 (r + L) = entry S 2 r := by
  have := hS.colS; rw [col_eq_entries] at this; simp only [Prod.mk.injEq] at this; exact this.2.2

/-- **Positions of `N`**: before `s`, or `r + (c L + q)` with `c ≥ 1`. -/
theorem Seed.posN {d : Nat} (hd : d < (TRIO.gexp S r L d0 d1 n).length) :
    d < r + L ∨ ∃ c q, 1 ≤ c ∧ c < n ∧ q < L ∧ d = r + (c * L + q) := by
  rw [lenN hS.len] at hd
  rcases Nat.lt_or_ge d (r + L) with h | h
  · exact Or.inl h
  · right
    obtain ⟨c, q, hc, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hS.pos (by omega) hd
    refine ⟨c, q, ?_, hc, hq, rfl⟩
    by_contra h1
    have : c = 0 := by omega
    subst this; simp at h; omega

/-- Entries at a shifted position. -/
theorem Seed.e0N_sh {c P : Nat} (hc : c < n) (hrP : r ≤ P) (hP : P < r + L) :
    entry (TRIO.gexp S r L d0 d1 n) 0 (P + c * L) = entry S 0 P + c * d0 := by
  have := e0N_blk (d0 := d0) (d1 := d1) hS.len hc (q := P - r) (by omega)
  rw [show r + (c * L + (P - r)) = P + c * L by omega, show r + (P - r) = P by omega] at this
  exact this

theorem Seed.e1N_sh {c P : Nat} (hc : c < n) (hrP : r ≤ P) (hP : P < r + L) :
    entry (TRIO.gexp S r L d0 d1 n) 1 (P + c * L) =
      entry S 1 P + (if TRIO.le1 S r P then c * d1 else 0) := by
  have := e1N_blk (d0 := d0) (d1 := d1) hS.len hc (q := P - r) (by omega)
  rw [show r + (c * L + (P - r)) = P + c * L by omega, show r + (P - r) = P by omega] at this
  exact this

theorem Seed.e2N_sh {c P : Nat} (hc : c < n) (hrP : r ≤ P) (hP : P < r + L) :
    entry (TRIO.gexp S r L d0 d1 n) 2 (P + c * L) = entry S 2 P := by
  have := e2N_blk (d0 := d0) (d1 := d1) hS.len hc (q := P - r) (by omega)
  rw [show r + (c * L + (P - r)) = P + c * L by omega, show r + (P - r) = P by omega] at this
  exact this

/-- Entries at a copy root, in terms of `s`. -/
theorem Seed.e0N_root {c : Nat} (hc1 : 1 ≤ c) (hc : c < n) :
    entry (TRIO.gexp S r L d0 d1 n) 0 (r + c * L) = entry S 0 (r + L) + (c - 1) * d0 := by
  have := e0N_blk (d0 := d0) (d1 := d1) hS.len hc hS.pos (q := 0)
  simp only [Nat.add_zero] at this
  rw [this, hS.e0s, mul_pred_add hc1]
  omega

theorem Seed.e1N_root {c : Nat} (hc1 : 1 ≤ c) (hc : c < n) :
    entry (TRIO.gexp S r L d0 d1 n) 1 (r + c * L) = entry S 1 (r + L) + (c - 1) * d1 := by
  have := e1N_blk (d0 := d0) (d1 := d1) hS.len hc hS.pos (q := 0)
  simp only [Nat.add_zero] at this
  rw [this, if_pos (le1_self (by have := hS.len; omega)), hS.e1s, mul_pred_add hc1]
  omega

theorem Seed.e2N_root {c : Nat} (hc : c < n) :
    entry (TRIO.gexp S r L d0 d1 n) 2 (r + c * L) = entry S 2 (r + L) := by
  have := e2N_blk (d0 := d0) (d1 := d1) hS.len hc hS.pos (q := 0)
  simp only [Nat.add_zero] at this
  rw [this, hS.e2s]

theorem Seed.eN_pre (hn : 1 ≤ n) (y : Nat) {i : Nat} (hi : i < r + L) :
    entry (TRIO.gexp S r L d0 d1 n) y i = entry S y i := entry_gexp_pre hS.len hn y hi

end

/-! ## N の親子の組の分類 -/

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

/-- **The parent of a column of `N`.** -/
theorem Seed.parN (hn : 1 ≤ n) {d p : Nat} (hd : d < (TRIO.gexp S r L d0 d1 n).length)
    (hp : par (TRIO.gexp S r L d0 d1 n) 0 d = some p) :
    (d < r + L ∧ par S 0 d = some p) ∨
    (∃ c q P, 1 ≤ c ∧ c < n ∧ 0 < q ∧ q < L ∧ d = r + (c * L + q) ∧ par S 0 (r + q) = some P ∧
      Anc0 S r P ∧ p = P + c * L) ∨
    (∃ c P, 1 ≤ c ∧ c < n ∧ d = r + c * L ∧ Anc0 S r (r + L) ∧ (0 < d1 → TRIO.le1 S r (r + L)) ∧
      par S 0 (r + L) = some P ∧ Anc0 S r P ∧ p = P + (c - 1) * L) ∨
    (∃ c, 1 ≤ c ∧ c < n ∧ d = r + c * L ∧ d0 = 0 ∧ d1 = 0 ∧ par S 0 r = some p) := by
  rcases hS.posN hd with h | ⟨c, q, hc1, hc, hq, rfl⟩
  · left; exact ⟨h, by rw [← par0N_low hS.len hn h]; exact hp⟩
  · rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      simp only [Nat.add_zero] at hp ⊢
      rcases hS.root with ⟨hAs, hg⟩ | ⟨hd0, hd1, hps⟩
      · obtain ⟨P, hP, hrP⟩ := anc0_par_exists hAs (by have := hS.pos; omega)
        rw [par0N_root hS.len hc1 hc hrP hP hS.e0s] at hp
        exact Or.inr (Or.inr (Or.inl ⟨c, P, hc1, hc, rfl, hAs, hg, hP, hrP, (Option.some.inj hp).symm⟩))
      · rw [par0N_root0 hS.len hS.pos hS.blk hd0 hc] at hp
        exact Or.inr (Or.inr (Or.inr ⟨c, hc1, hc, rfl, hd0, hd1, hp⟩))
    · obtain ⟨P, hP, hrP⟩ := anc0_par_exists (hS.blk q hq) (by omega)
      rw [par0N_blk hS.len hS.blk hc hq0 hq hP] at hp
      exact Or.inr (Or.inl ⟨c, q, P, hc1, hc, hq0, hq, rfl, hP, hrP, (Option.some.inj hp).symm⟩)

/-! ## Z1C と BumpE2 -/

theorem Seed.z1c (hZ1 : Z1C S) (hn : 1 ≤ n) : Z1C (TRIO.gexp S r L d0 d1 n) := by
  have hlS := hS.len
  intro p d h2 hd
  have hdN := (mem_children hd).2
  have hpd := (mem_children_iff.mp hd).2
  rcases hS.parN hn hdN hpd with ⟨hdl, hpS⟩ | ⟨c, q, P, hc1, hc, hq0, hq, rfl, hP, hrP, rfl⟩ |
      ⟨c, P, hc1, hc, rfl, hAs, hg, hP, hrP, rfl⟩ | ⟨c, hc1, hc, rfl, hd0, hd1, hpS⟩
  · have hpl := par_lt S 0 d p hpS
    rw [hS.eN_pre hn 2 (by omega)] at h2
    rw [hS.eN_pre hn 1 hdl, hS.eN_pre hn 1 (by omega)]
    exact hZ1 p d h2 (mem_children_iff.mpr ⟨by omega, hpS⟩)
  · have hPq := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rw [hS.e2N_sh hc hrP' (by omega)] at h2
    rw [e1N_blk hS.len hc hq, hS.e1N_sh hc hrP' (by omega)]
    have hz := hZ1 P (r + q) h2 (mem_children_iff.mpr ⟨by omega, hP⟩)
    have hgd : TRIO.le1 S r (r + q) → TRIO.le1 S r P := guard_par hrP hP (by omega)
    split_ifs with h1 h3 <;> first | omega | exact absurd (hgd h1) h3
  · have hPs := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rw [hS.e2N_sh (by omega) hrP' (by omega)] at h2
    rw [hS.e1N_root hc1 hc, hS.e1N_sh (by omega) hrP' (by omega)]
    have hz := hZ1 P (r + L) h2 (mem_children_iff.mpr ⟨by omega, hP⟩)
    rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
    · subst hd1; split_ifs <;> omega
    · rw [if_pos (guard_par hrP hP (by omega) (hg hd1))]; omega
  · subst hd0 hd1
    have hpr := par_lt S 0 _ _ hpS
    rw [hS.eN_pre hn 2 (by omega)] at h2
    rw [hS.e1N_root hc1 hc, hS.eN_pre hn 1 (by omega), hS.e1s]
    have := hZ1 p r h2 (mem_children_iff.mpr ⟨by omega, hpS⟩)
    omega

theorem Seed.bumpE2 (hBE : BumpE2 S) (hn : 1 ≤ n) : BumpE2 (TRIO.gexp S r L d0 d1 n) := by
  have hlS := hS.len
  intro p d hd hb
  have hdN := (mem_children hd).2
  have hpd := (mem_children_iff.mp hd).2
  rw [col_eq_entries] at hb
  unfold bump at hb
  simp only [Prod.mk.injEq] at hb
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rcases hS.parN hn hdN hpd with ⟨hdl, hpS⟩ | ⟨c, q, P, hc1, hc, hq0, hq, rfl, hP, hrP, rfl⟩ |
      ⟨c, P, hc1, hc, rfl, hAs, hg, hP, hrP, rfl⟩ | ⟨c, hc1, hc, rfl, hd0, hd1, hpS⟩
  · have hpl := par_lt S 0 d p hpS
    rw [hS.eN_pre hn 0 hdl, hS.eN_pre hn 0 (by omega)] at hb0
    rw [hS.eN_pre hn 1 hdl, hS.eN_pre hn 1 (by omega)] at hb1
    rw [hS.eN_pre hn 2 hdl] at hb2
    rw [hS.eN_pre hn 2 (by omega)]
    apply hBE p d (mem_children_iff.mpr ⟨by omega, hpS⟩)
    rw [col_eq_entries]; unfold bump; rw [hb0, hb1, hb2]
  · have hPq := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rw [e0N_blk hS.len hc hq, hS.e0N_sh hc hrP' (by omega)] at hb0
    rw [e1N_blk hS.len hc hq, hS.e1N_sh hc hrP' (by omega)] at hb1
    rw [e2N_blk hS.len hc hq] at hb2
    rw [hS.e2N_sh hc hrP' (by omega)]
    have hgd : TRIO.le1 S r (r + q) → TRIO.le1 S r P := guard_par hrP hP (by omega)
    have he1 : entry S 1 (r + q) = entry S 1 P := by
      by_cases h1 : TRIO.le1 S r (r + q)
      · rw [if_pos h1, if_pos (hgd h1)] at hb1; omega
      · rw [if_neg h1] at hb1
        by_cases h3 : TRIO.le1 S r P
        · rw [if_pos h3] at hb1
          by_contra hne
          exact h1 (guard_up hrP hP (by omega) h3 (by omega))
        · rw [if_neg h3] at hb1; omega
    apply hBE P (r + q) (mem_children_iff.mpr ⟨by omega, hP⟩)
    rw [col_eq_entries]; unfold bump
    simp only [Prod.mk.injEq]; omega
  · have hPs := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rw [hS.e0N_root hc1 hc, hS.e0N_sh (by omega) hrP' (by omega)] at hb0
    rw [hS.e1N_root hc1 hc, hS.e1N_sh (by omega) hrP' (by omega)] at hb1
    rw [hS.e2N_root hc] at hb2
    rw [hS.e2N_sh (by omega) hrP' (by omega)]
    have he1 : entry S 1 (r + L) = entry S 1 P := by
      rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
      · subst hd1; split_ifs at hb1 <;> omega
      · rw [if_pos (guard_par hrP hP (by omega) (hg hd1))] at hb1; omega
    apply hBE P (r + L) (mem_children_iff.mpr ⟨by omega, hP⟩)
    rw [col_eq_entries]; unfold bump
    simp only [Prod.mk.injEq]; omega
  · subst hd0 hd1
    have hpr := par_lt S 0 _ _ hpS
    rw [hS.e0N_root hc1 hc, hS.eN_pre hn 0 (by omega), hS.e0s] at hb0
    rw [hS.e1N_root hc1 hc, hS.eN_pre hn 1 (by omega), hS.e1s] at hb1
    rw [hS.e2N_root hc, hS.e2s] at hb2
    rw [hS.eN_pre hn 2 (by omega)]
    apply hBE p r (mem_children_iff.mpr ⟨by omega, hpS⟩)
    rw [col_eq_entries]; unfold bump
    simp only [Prod.mk.injEq]; omega

end

end Ytosk
