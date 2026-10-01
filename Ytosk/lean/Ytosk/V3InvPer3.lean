/-
**周期的な種からの展開: 兄弟の順（SibDec）。**

N の隣り合う兄弟 (a, b) は、S の隣り合う兄弟のずらし（同じブロック、または根と前のブロックの s の兄弟）。
列のずれは行 0 が共通、行 1 はガードつきで、兄弟のガードは行 1 が小さい方から大きい方へ移る
（`guard_sib`）ので、`colLe` はずらしても保たれる（`colLe_sh`）。t = 0 の根どうしは同じ列。
-/
import Ytosk.V3InvPer2

namespace Ytosk

open T Classical

/-! ## リストの補題 -/

theorem split_consec {l l1 l2 : List Nat} {a b : Nat} (hs : l.Pairwise (· < ·))
    (h : l = l1 ++ a :: b :: l2) : a < b ∧ a ∈ l ∧ b ∈ l ∧ ∀ e ∈ l, ¬ (a < e ∧ e < b) := by
  subst h
  have hs' := List.pairwise_append.mp hs
  have hab : a < b := (List.pairwise_cons.mp hs'.2.1).1 b (by simp)
  refine ⟨hab, by simp, by simp, fun e he ⟨h1, h2⟩ => ?_⟩
  rcases List.mem_append.mp he with he | he
  · have := hs'.2.2 e he a (by simp); omega
  · simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · omega
    · omega
    · have := (List.pairwise_cons.mp (List.pairwise_cons.mp hs'.2.1).2).1 e he; omega

theorem consec_split : ∀ {l : List Nat} {a b : Nat}, l.Pairwise (· < ·) → a ∈ l → b ∈ l → a < b →
    (∀ e ∈ l, ¬ (a < e ∧ e < b)) → ∃ l1 l2, l = l1 ++ a :: b :: l2
  | [], _, _, _, ha, _, _, _ => absurd ha (by simp)
  | x :: t, a, b, hs, ha, hb, hab, hno => by
    have hs' := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with hax | ha'
    · -- the next element is `b`
      subst hax
      have hbt : b ∈ t := by
        rcases List.mem_cons.mp hb with h | h
        · omega
        · exact h
      cases t with
      | nil => simp at hbt
      | cons y t' =>
        have hy : y ≤ b := by
          rcases List.mem_cons.mp hbt with h | h
          · omega
          · exact le_of_lt ((List.pairwise_cons.mp hs'.2).1 b h)
        have hya : a < y := hs'.1 y (by simp)
        have hyb : y = b := by
          by_contra hne
          exact hno y (by simp) ⟨hya, by omega⟩
        subst hyb
        exact ⟨[], t', by simp⟩
    · have hxa : x < a := hs'.1 a ha'
      have hbt : b ∈ t := by
        rcases List.mem_cons.mp hb with h | h
        · omega
        · exact h
      obtain ⟨l1, l2, h⟩ := consec_split hs'.2 ha' hbt hab
        (fun e he => hno e (List.mem_cons_of_mem _ he))
      exact ⟨x :: l1, l2, by rw [h]; rfl⟩

/-- **`colLe` survives a common row-0 shift and guarded row-1 shifts.** -/
theorem colLe_sh {b0 b1 b2 a0 a1 a2 X Y : Nat} {gb ga : Prop} [Decidable gb] [Decidable ga]
    (h : colLe (b0, b1, b2) (a0, a1, a2)) (hg : b0 = a0 → b1 ≤ a1 → gb → ga) :
    colLe (b0 + X, b1 + (if gb then Y else 0), b2) (a0 + X, a1 + (if ga then Y else 0), a2) := by
  unfold colLe at h ⊢
  simp only at h ⊢
  rcases h with h | ⟨h0, h⟩
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    have hle : b1 ≤ a1 := by rcases h with h | ⟨h, _⟩ <;> omega
    by_cases hgb : gb
    · rw [if_pos hgb, if_pos (hg h0 hle hgb)]
      rcases h with h | ⟨h, h'⟩
      · left; omega
      · right; exact ⟨by omega, h'⟩
    · rw [if_neg hgb]
      by_cases hga : ga
      · rw [if_pos hga]
        rcases h with h | ⟨h, h'⟩
        · left; omega
        · rcases Nat.eq_zero_or_pos Y with hY | hY
          · right; exact ⟨by omega, h'⟩
          · left; omega
      · rw [if_neg hga]; exact h

/-- Uniqueness of the shifted positions. -/
theorem shift_unique {r L c c' P P' : Nat} (hP : r ≤ P) (hP' : P < r + L) (hQ : r ≤ P')
    (hQ' : P' < r + L) (h : P + c * L = P' + c' * L) : c = c' ∧ P = P' := by
  have := decomp_unique (L := L) (k := c) (q := P - r) (k' := c') (q' := P' - r) (by omega) (by omega)
    (by omega)
  omega

/-! ## SibDec -/

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

theorem Seed.colN_pre (hn : 1 ≤ n) {i : Nat} (hi : i < r + L) :
    col (TRIO.gexp S r L d0 d1 n) i = col S i := col_gexp_pre hS.len hn hi


theorem Seed.sibDec (hSD : SibDec S) (hn : 1 ≤ n) : SibDec (TRIO.gexp S r L d0 d1 n) := by
  have hlS := hS.len
  have hL := hS.pos
  have hlN := lenN (d0 := d0) (d1 := d1) (n := n) hS.len
  intro p l1 l2 a b hch
  obtain ⟨hab, ha, hb, hno⟩ := split_consec (children_sorted _ p) hch
  have haN := (mem_children ha).2
  have hbN := (mem_children hb).2
  have hpa := (mem_children_iff.mp ha).2
  have hpb := (mem_children_iff.mp hb).2
  -- an `S`-child of the parent between the two would give an `N`-child between
  have hSc : ∀ (P : Nat) (A B : Nat), A ∈ children S P → B ∈ children S P → A < B →
      (∀ e ∈ children S P, A < e → e < B →
        ∃ e', e' ∈ children (TRIO.gexp S r L d0 d1 n) p ∧ a < e' ∧ e' < b) →
      colLe (col S B) (col S A) := by
    intro P A B hA hB hAB hmap
    obtain ⟨m1, m2, hm⟩ := consec_split (children_sorted S P) hA hB hAB (fun e he ⟨h1, h2⟩ => by
      obtain ⟨e', he', h3, h4⟩ := hmap e he h1 h2; exact hno e' he' ⟨h3, h4⟩)
    exact hSD P m1 m2 A B hm
  rcases hS.parN hn hbN hpb with ⟨hbl, hpS⟩ | ⟨c, q, P, hc1, hc, hq0, hq, rfl, hP, hrP, rfl⟩ |
      ⟨c, P, hc1, hc, rfl, hAs, hg, hP, hrP, rfl⟩ | ⟨c, hc1, hc, rfl, hd0, hd1, hpS⟩
  · -- `b` before `s`
    have hal : a < r + L := by omega
    have hpaS : par S 0 a = some p := by rw [← par0N_low hS.len hn hal]; exact hpa
    rw [hS.colN_pre hn hbl, hS.colN_pre hn hal]
    exact hSc p a b (mem_children_iff.mpr ⟨by omega, hpaS⟩) (mem_children_iff.mpr ⟨by omega, hpS⟩) hab
      (fun e he h1 h2 => ⟨e, mem_children_iff.mpr ⟨by omega, by
        rw [par0N_low hS.len hn (by omega)]; exact (mem_children_iff.mp he).2⟩, h1, h2⟩)
  · -- `b` inside a block
    have hPq := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rcases hS.parN hn haN hpa with ⟨hal, hpaS⟩ | ⟨c', q', P', hc1', hc', hq0', hq', rfl, hP', hrP'', hpe⟩ |
        ⟨c', P', hc1', hc', rfl, _, _, hPs', hrPs', hpe⟩ | ⟨c', _, _, rfl, _, _, hpS'⟩
    · exfalso; have := par_lt S 0 _ _ hpaS
      have : L ≤ c * L := by have := Nat.mul_le_mul_right L hc1; simpa using this
      omega
    · have hPq' := par_lt S 0 _ _ hP'
      have hPL : P < r + L := by omega
      have hPL' : P' < r + L := by omega
      obtain ⟨rfl, rfl⟩ := shift_unique hrP' hPL hrP''.le hPL' hpe
      have hqq : q' < q := by omega
      have hcol := hSc P (r + q') (r + q) (mem_children_iff.mpr ⟨by omega, hP'⟩)
        (mem_children_iff.mpr ⟨by omega, hP⟩) (by omega) (fun e he h1 h2 => by
          have he0 : 0 < e - r := by omega
          have hpe : par S 0 (r + (e - r)) = some P := by
            rw [show r + (e - r) = e by omega]; exact (mem_children_iff.mp he).2
          refine ⟨r + (c * L + (e - r)), mem_children_iff.mpr ⟨?_, par0N_blk hS.len hS.blk hc he0 (by omega) hpe⟩,
            by omega, by omega⟩
          rw [hlN]; have : c * L + L ≤ n * L := by
            have := Nat.mul_le_mul_right L (show c + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
          omega)
      rw [col_eq_entries, col_eq_entries, e0N_blk hS.len hc hq, e1N_blk hS.len hc hq, e2N_blk hS.len hc hq,
        e0N_blk hS.len hc hq', e1N_blk hS.len hc hq', e2N_blk hS.len hc hq']
      rw [col_eq_entries, col_eq_entries] at hcol
      exact colLe_sh hcol (fun _ h1 hg => guard_sib hrP hP' hP (by omega) (by omega) hg h1)
    · exfalso
      have hPs := par_lt S 0 _ _ hPs'
      have hu := shift_unique hrPs'.le (by omega) hrP' (by omega) (show P' + (c' - 1) * L = P + c * L by omega)
      have h3 : c' * L = L + (c' - 1) * L := mul_pred_add hc1'
      have : c' - 1 = c := hu.1
      have : L ≤ c * L + L := by omega
      omega
    · exfalso; have := par_lt S 0 _ _ hpS'
      have : L ≤ c * L := by have := Nat.mul_le_mul_right L hc1; simpa using this
      omega
  · -- `b` a copy root, `t ≥ 1`
    have hPs := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · have hc1e : c = 1 := by omega
      subst hc1e
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero, Nat.one_mul] at hpa hab hno ha hb hbN hch hSc ⊢
      have hal : a < r + L := by omega
      have hpaS : par S 0 a = some P := by rw [← par0N_low hS.len hn hal]; exact hpa
      have hcolb : col (TRIO.gexp S r L d0 d1 n) (r + L) = col S (r + L) := by
        rw [col_eq_entries, col_eq_entries]
        have h0 := hS.e0N_root (n := n) (le_refl 1) hc
        have h1 := hS.e1N_root (n := n) (le_refl 1) hc
        have h2 := hS.e2N_root (n := n) hc
        simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero, Nat.one_mul] at h0 h1 h2
        rw [h0, h1, h2]
      rw [hcolb, hS.colN_pre hn hal]
      exact hSc P a (r + L) (mem_children_iff.mpr ⟨by omega, hpaS⟩) (mem_children_iff.mpr ⟨by omega, hP⟩)
        hab (fun e he h1 h2 => ⟨e, mem_children_iff.mpr ⟨by omega, by
          rw [par0N_low hS.len hn (by omega)]; exact (mem_children_iff.mp he).2⟩, h1, h2⟩)
    · rcases hS.parN hn haN hpa with ⟨hal, hpaS⟩ | ⟨c', q', P', hc1', hc', hq0', hq', rfl, hP', hrP'', hpe⟩ |
          ⟨c', P', hc1', hc', rfl, _, _, hPs', hrPs', hpe⟩ | ⟨c', _, _, rfl, _, _, hpS'⟩
      · exfalso; have := par_lt S 0 _ _ hpaS
        have : L ≤ (c - 1) * L := by have := Nat.mul_le_mul_right L (show 1 ≤ c - 1 by omega); simpa using this
        omega
      · have hPq' := par_lt S 0 _ _ hP'
        have hPL : P < r + L := by omega
        have hPL' : P' < r + L := by omega
        obtain ⟨hcc, hPP⟩ := shift_unique hrP''.le hPL' hrP' hPL hpe.symm
        subst hPP
        have hcol := hSc P' (r + q') (r + L) (mem_children_iff.mpr ⟨by omega, hP'⟩)
          (mem_children_iff.mpr ⟨by omega, hP⟩) (by omega) (fun e he h1 h2 => by
            have he0 : 0 < e - r := by omega
            have hpe : par S 0 (r + (e - r)) = some P' := by
              rw [show r + (e - r) = e by omega]; exact (mem_children_iff.mp he).2
            refine ⟨r + (c' * L + (e - r)), mem_children_iff.mpr ⟨?_, by
              rw [par0N_blk hS.len hS.blk hc' he0 (by omega) hpe, hcc]⟩, by omega, ?_⟩
            · rw [hlN]; have : c' * L + L ≤ n * L := by
                have := Nat.mul_le_mul_right L (show c' + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
              omega
            · rw [mul_pred_add hc1] ; omega)
        rw [col_eq_entries, col_eq_entries, hS.e0N_root hc1 hc, hS.e1N_root hc1 hc, hS.e2N_root hc,
          e0N_blk hS.len hc' hq', e1N_blk hS.len hc' hq', e2N_blk hS.len hc' hq', ← hcc]
        rw [col_eq_entries, col_eq_entries] at hcol
        have hcol' : colLe (entry S 0 (r + L), entry S 1 (r + L), entry S 2 (r + L))
            (entry S 0 (r + q'), entry S 1 (r + q'), entry S 2 (r + q')) := hcol
        rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
        · subst hd1
          have := colLe_sh (X := c' * d0) (Y := 0) (gb := True) (ga := True) hcol' (fun _ _ _ => trivial)
          simpa using this
        · have := colLe_sh (X := c' * d0) (Y := c' * d1) (gb := True) (ga := TRIO.le1 S r (r + q')) hcol'
            (fun _ h1 _ => guard_sib hrP'' hP' hP (by omega) (by omega) (hg hd1) h1)
          simpa using this
      · exfalso
        have hPs'' := par_lt S 0 _ _ hPs'
        obtain ⟨hcc, _⟩ := shift_unique hrPs'.le (by omega) hrP' (by omega) (show P' + (c' - 1) * L = P + (c - 1) * L by omega)
        have : c' = c := by omega
        subst this; omega
      · exfalso; have := par_lt S 0 _ _ hpS'
        have : L ≤ (c - 1) * L := by have := Nat.mul_le_mul_right L (show 1 ≤ c - 1 by omega); simpa using this
        omega
  · -- `b` a copy root, `t = 0`
    subst hd0 hd1
    have hpr := par_lt S 0 _ _ hpS
    have hcolR : ∀ c', 1 ≤ c' → c' < n → col (TRIO.gexp S r L 0 0 n) (r + c' * L) = col S (r + L) := by
      intro c' h1 h2
      rw [col_eq_entries, col_eq_entries, hS.e0N_root h1 h2, hS.e1N_root h1 h2, hS.e2N_root h2]; simp
    rcases hS.parN hn haN hpa with ⟨hal, hpaS⟩ | ⟨c', q', P', hc1', hc', hq0', hq', rfl, hP', hrP'', hpe⟩ |
        ⟨c', P', hc1', hc', rfl, _, _, hPs', hrPs', hpe⟩ | ⟨c', hc1', hc', rfl, _, _, hpS'⟩
    · -- `a` before `s`: then `b = r + L`
      have hc1e : c = 1 := by
        by_contra hne
        have hR1 : r + 1 * L ∈ children (TRIO.gexp S r L 0 0 n) p := mem_children_iff.mpr
          ⟨by rw [hlN]; have : 2 * L ≤ n * L := Nat.mul_le_mul_right L (by omega); omega,
           by rw [par0N_root0 hS.len hS.pos hS.blk rfl (by omega)]; exact hpS⟩
        have : 2 * L ≤ c * L := Nat.mul_le_mul_right L (by omega)
        exact hno _ hR1 ⟨by omega, by omega⟩
      subst hc1e
      have hpaS : par S 0 a = some p := by rw [← par0N_low hS.len hn hal]; exact hpa
      have hps : par S 0 (r + L) = some p := by
        rcases hS.root with ⟨hAs, _⟩ | ⟨_, _, hps⟩
        · exfalso
          have h1 := anc0_e0_lt hAs (by have := hS.pos; omega)
          have h2 := hS.e0s; omega
        · rw [hps]; exact hpS
      rw [hcolR 1 (le_refl 1) hc, hS.colN_pre hn hal]
      exact hSc p a (r + L) (mem_children_iff.mpr ⟨by omega, hpaS⟩) (mem_children_iff.mpr ⟨by omega, hps⟩)
        (by omega) (fun e he h1 h2 => ⟨e, mem_children_iff.mpr ⟨by omega, by
          rw [par0N_low hS.len hn (by omega)]; exact (mem_children_iff.mp he).2⟩, h1, by simpa using h2⟩)
    · exfalso; have := par_lt S 0 _ _ hP'
      have := hrP''.le
      have : L ≤ c' * L := by have := Nat.mul_le_mul_right L hc1'; simpa using this
      omega
    · exfalso; have := hrPs'.le
      have hpr' := par_lt S 0 _ _ hpS
      rw [hpe] at hpr'
      omega
    · rw [hcolR c' hc1' hc', hcolR c hc1 hc]
      unfold colLe; omega

end

end Ytosk
