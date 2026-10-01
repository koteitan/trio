/-
**周期的な種からの展開: のりしろの子の下の葉（BumpLeaf）。**

N のの実例 (k, j, c) は S の実例のずらし。j が s より前・ブロック内なら S の実例そのもの（行 1 の比較は
ガードで戻る）。c がコピーの根（s の写し）になるのは S で s が実例の「孫」になる場合で、種の仮定
`noBL` が禁じる。j がコピーの根なら、t ≥ 1 では col s = bump(s の親) となり `nbs` が禁じ、
t = 0 では r が g の最後の子になって s（g の子）と矛盾する。結論の「葉」「最後の子」は、N の子を
`parN` で分類して S の子に戻す。
-/
import Ytosk.V3InvPer3

namespace Ytosk

open T Classical

/-! ## リストの補題 -/

theorem last_le {l : List Nat} {c : Nat} (hs : l.Pairwise (· < ·)) (h : l.getLast? = some c) :
    ∀ e ∈ l, e ≤ c := by
  rcases List.eq_nil_or_concat l with h' | ⟨l', b, h'⟩
  · subst h'; simp at h
  · rw [List.concat_eq_append] at h'
    subst h'
    simp at h; subst h
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact le_of_lt ((List.pairwise_append.mp hs).2.2 e he _ (by simp))
    · simp at he; omega

theorem getLast_of {l : List Nat} {c : Nat} (hs : l.Pairwise (· < ·)) (hc : c ∈ l)
    (h : ∀ e ∈ l, e ≤ c) : l.getLast? = some c := by
  rcases List.eq_nil_or_concat l with h' | ⟨l', b, h'⟩
  · subst h'; simp at hc
  · rw [List.concat_eq_append] at h'
    subst h'
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq]
    have hb := h b (by simp)
    have hcb := last_le (c := b) hs (by simp) c hc
    omega

theorem nil_of_none {l : List Nat} (h : ∀ e, e ∉ l) : l = [] :=
  List.eq_nil_iff_forall_not_mem.mpr h

/-! ## のりしろの条件を S に戻す -/

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

/-- Bump inside a block. -/
theorem Seed.bump_blk {c q P : Nat} (hc : c < n) (hq : q < L) (hP : par S 0 (r + q) = some P)
    (hrP : Anc0 S r P)
    (hb : col (TRIO.gexp S r L d0 d1 n) (r + (c * L + q)) = bump (TRIO.gexp S r L d0 d1 n) (P + c * L)) :
    col S (r + q) = bump S P := by
  have hlS := hS.len
  have hPq := par_lt S 0 _ _ hP
  have hrP' := hrP.le
  rw [col_eq_entries] at hb
  unfold bump at hb ⊢
  simp only [Prod.mk.injEq] at hb
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rw [e0N_blk hS.len hc hq, hS.e0N_sh hc hrP' (by omega)] at hb0
  rw [e1N_blk hS.len hc hq, hS.e1N_sh hc hrP' (by omega)] at hb1
  rw [e2N_blk hS.len hc hq] at hb2
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
  rw [col_eq_entries]; simp only [Prod.mk.injEq]; omega

/-- Bump at a copy root (`t ≥ 1`). -/
theorem Seed.bump_root {c P : Nat} (hc1 : 1 ≤ c) (hc : c < n) (hP : par S 0 (r + L) = some P)
    (hrP : Anc0 S r P) (hg : 0 < d1 → TRIO.le1 S r (r + L))
    (hb : col (TRIO.gexp S r L d0 d1 n) (r + c * L) = bump (TRIO.gexp S r L d0 d1 n) (P + (c - 1) * L)) :
    col S (r + L) = bump S P := by
  have hlS := hS.len
  have hPs := par_lt S 0 _ _ hP
  have hrP' := hrP.le
  rw [col_eq_entries] at hb
  unfold bump at hb ⊢
  simp only [Prod.mk.injEq] at hb
  obtain ⟨hb0, hb1, hb2⟩ := hb
  rw [hS.e0N_root hc1 hc, hS.e0N_sh (by omega) hrP' (by omega)] at hb0
  rw [hS.e1N_root hc1 hc, hS.e1N_sh (by omega) hrP' (by omega)] at hb1
  rw [hS.e2N_root hc] at hb2
  have he1 : entry S 1 (r + L) = entry S 1 P := by
    rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
    · subst hd1; split_ifs at hb1 <;> omega
    · rw [if_pos (guard_par hrP hP (by omega) (hg hd1))] at hb1; omega
  rw [col_eq_entries]; simp only [Prod.mk.injEq]; omega

end

/-! ## N の子の分類 -/

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

theorem Seed.root_excl (hAs : Anc0 S r (r + L)) (hd0 : d0 = 0) : False := by
  have h1 := anc0_e0_lt hAs (by have := hS.pos; omega)
  have h2 := hS.e0s; omega

theorem Seed.par_s_t0 (hd0 : d0 = 0) : par S 0 (r + L) = par S 0 r := by
  rcases hS.root with ⟨hAs, _⟩ | ⟨_, _, h⟩
  · exact (hS.root_excl hAs hd0).elim
  · exact h

theorem Seed.bumpN_pre (hn : 1 ≤ n) {v : Nat} (hv : v < r + L) :
    bump (TRIO.gexp S r L d0 d1 n) v = bump S v := by
  unfold bump; rw [hS.eN_pre hn 0 hv, hS.eN_pre hn 1 hv]

/-- The children of a column before `s`: those of `S`, or a copy root when `s` hangs below it. -/
theorem Seed.children_pre (hn : 1 ≤ n) {v e : Nat} (hv : v < r + L)
    (he : e ∈ children (TRIO.gexp S r L d0 d1 n) v) :
    (e < r + L ∧ e ∈ children S v) ∨ par S 0 (r + L) = some v := by
  have hlS := hS.len
  have heN := (mem_children he).2
  have hpe := (mem_children_iff.mp he).2
  rcases hS.parN hn heN hpe with ⟨hel, hpS⟩ | ⟨c, q, P, hc1, hc, hq0, hq, rfl, hP, hrP, rfl⟩ |
      ⟨c, P, hc1, hc, rfl, hAs, hg, hP, hrP, hv'⟩ | ⟨c, hc1, hc, rfl, hd0, hd1, hpS⟩
  · exact Or.inl ⟨hel, mem_children_iff.mpr ⟨by omega, hpS⟩⟩
  · exfalso; have := hrP.le
    have : L ≤ c * L := by have := Nat.mul_le_mul_right L hc1; simpa using this
    omega
  · right
    have hrP' := hrP.le
    have hc1e : c = 1 := by
      by_contra hne
      have : L ≤ (c - 1) * L := by have := Nat.mul_le_mul_right L (show 1 ≤ c - 1 by omega); simpa using this
      omega
    subst hc1e
    simp at hv'; rw [hP, hv']
  · right; rw [hS.par_s_t0 hd0]; exact hpS

/-- The children of a shifted column `X + c L` (`c ≥ 1`): shifted children of `X`, or a copy root when
`s` hangs below `X`. -/
theorem Seed.children_shift (hn : 1 ≤ n) {X c e : Nat} (hrX : r ≤ X) (hX : X < r + L) (hc1 : 1 ≤ c)
    (hc : c < n) (he : e ∈ children (TRIO.gexp S r L d0 d1 n) (X + c * L)) :
    (∃ q, 0 < q ∧ q < L ∧ e = r + (c * L + q) ∧ r + q ∈ children S X) ∨ par S 0 (r + L) = some X := by
  have hlS := hS.len
  have heN := (mem_children he).2
  have hpe := (mem_children_iff.mp he).2
  rcases hS.parN hn heN hpe with ⟨hel, hpS⟩ | ⟨c', q, P, hc1', hc', hq0, hq, rfl, hP, hrP, hpe'⟩ |
      ⟨c', P, hc1', hc', rfl, hAs, hg, hP, hrP, hv'⟩ | ⟨c', hc1', hc', rfl, hd0, hd1, hpS⟩
  · exfalso; have := par_lt S 0 _ _ hpS
    have : L ≤ c * L := by have := Nat.mul_le_mul_right L hc1; simpa using this
    omega
  · have hPq := par_lt S 0 _ _ hP
    obtain ⟨rfl, rfl⟩ := shift_unique hrX hX hrP.le (by omega) hpe'
    exact Or.inl ⟨q, hq0, hq, rfl, mem_children_iff.mpr ⟨by omega, hP⟩⟩
  · have hPs := par_lt S 0 _ _ hP
    obtain ⟨_, rfl⟩ := shift_unique hrX hX hrP.le (by omega) hv'
    exact Or.inr hP
  · exfalso; have := par_lt S 0 _ _ hpS
    have : L ≤ c * L := by have := Nat.mul_le_mul_right L hc1; simpa using this
    omega

end

/-! ## BumpLeaf -/

section
variable {S : Mat} {r L d0 d1 n : Nat} (hS : Seed S r L d0 d1)
include hS

/-- **BumpLeaf survives the periodic expansion.** `hnoBL`: `s` is never the grandchild of an instance;
`hnbs` (`t ≥ 1`): `s` is not the bump column of its parent. -/
theorem Seed.bumpLeaf (hBL : BumpLeaf S)
    (hnoBL : ∀ K J, J ∈ children S K → col S J = bump S K → r + L ∈ children S J →
      entry S 1 K ≤ entry S 1 (r + L) → False)
    (hnbs : Anc0 S r (r + L) → ∀ P, par S 0 (r + L) = some P → col S (r + L) ≠ bump S P)
    (hn : 1 ≤ n) : BumpLeaf (TRIO.gexp S r L d0 d1 n) := by
  have hlS := hS.len
  have hL := hS.pos
  have hlN := lenN (d0 := d0) (d1 := d1) (n := n) hS.len
  have hsS : r + L < S.length := by omega
  intro k j c hj hb hc h1
  have hjN := (mem_children hj).2
  have hcN := (mem_children hc).2
  have hkj := (mem_children hj).1
  have hjc := (mem_children hc).1
  have hpc := (mem_children_iff.mp hc).2
  rcases hS.parN hn hjN (mem_children_iff.mp hj).2 with ⟨hjl, hkS⟩ |
      ⟨cj, qj, P, hcj1, hcj, hqj0, hqj, rfl, hP, hrP, rfl⟩ |
      ⟨cj, P, hcj1, hcj, rfl, hAs, hg, hP, hrP, rfl⟩ | ⟨cj, hcj1, hcj, rfl, hd0, hd1, hkS⟩
  · ---------------- `j` before `s`
    have hbS : col S j = bump S k := by
      rw [← hS.colN_pre hn hjl, ← hS.bumpN_pre hn (by omega)]; exact hb
    have hjS : j ∈ children S k := mem_children_iff.mpr ⟨by omega, hkS⟩
    rcases hS.parN hn hcN hpc with ⟨hcl, hjcS⟩ | ⟨c', q, Q, hc1', hc', hq0, hq, rfl, hQ, hrQ, hQe⟩ |
        ⟨c', Q, hc1', hc', rfl, hAs, hg, hQ, hrQ, hQe⟩ | ⟨c', hc1', hc', rfl, hd0, hd1, hjr⟩
    · have hcS : c ∈ children S j := mem_children_iff.mpr ⟨by omega, hjcS⟩
      rw [hS.eN_pre hn 1 (by omega), hS.eN_pre hn 1 hcl] at h1
      obtain ⟨h2, hleaf, hlc, hlj⟩ := hBL k j c hjS hbS hcS h1
      have hcle := last_le (children_sorted S j) hlc
      have hjle := last_le (children_sorted S k) hlj
      refine ⟨by rw [hS.eN_pre hn 2 hcl]; exact h2, nil_of_none (fun e he => ?_),
        getLast_of (children_sorted _ j) hc (fun e he => ?_), getLast_of (children_sorted _ k) hj (fun e he => ?_)⟩
      · rcases hS.children_pre hn hcl he with ⟨_, heS⟩ | hPs
        · rw [hleaf] at heS; simp at heS
        · have : r + L ∈ children S c := mem_children_iff.mpr ⟨hsS, hPs⟩
          rw [hleaf] at this; simp at this
      · rcases hS.children_pre hn hjl he with ⟨_, heS⟩ | hPs
        · exact hcle e heS
        · have := hcle (r + L) (mem_children_iff.mpr ⟨hsS, hPs⟩); omega
      · rcases hS.children_pre hn (by omega) he with ⟨_, heS⟩ | hPs
        · exact hjle e heS
        · have := hjle (r + L) (mem_children_iff.mpr ⟨hsS, hPs⟩); omega
    · exfalso; have := hrQ.le
      have : L ≤ c' * L := by have := Nat.mul_le_mul_right L hc1'; simpa using this
      omega
    · exfalso
      have hrQ' := hrQ.le
      have hc1e : c' = 1 := by
        by_contra hne
        have : L ≤ (c' - 1) * L := by
          have := Nat.mul_le_mul_right L (show 1 ≤ c' - 1 by omega); simpa using this
        omega
      subst hc1e
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at hQe
      subst hQe
      rw [hS.eN_pre hn 1 (by omega), hS.e1N_root (le_refl 1) hc'] at h1
      exact hnoBL k _ hjS hbS (mem_children_iff.mpr ⟨hsS, hQ⟩) (by simpa using h1)
    · exfalso
      subst hd1
      rw [hS.eN_pre hn 1 (by omega), hS.e1N_root hc1' hc'] at h1
      exact hnoBL k j hjS hbS (mem_children_iff.mpr ⟨hsS, by rw [hS.par_s_t0 hd0]; exact hjr⟩)
        (by simpa using h1)
  · ---------------- `j` inside a block
    have hPq := par_lt S 0 _ _ hP
    have hrP' := hrP.le
    have hbS := hS.bump_blk hcj hqj hP hrP hb
    have hjS : r + qj ∈ children S P := mem_children_iff.mpr ⟨by omega, hP⟩
    have hrJ : Anc0 S r (r + qj) := hS.blk qj hqj
    rcases hS.parN hn hcN hpc with ⟨hcl, _⟩ | ⟨c', qc, Q, hc1', hc', hqc0, hqc, rfl, hQ, hrQ, hQe⟩ |
        ⟨c', Q, hc1', hc', rfl, hAs, hg, hQ, hrQ, hQe⟩ | ⟨c', _, _, rfl, _, _, hjr⟩
    · exfalso
      have : L ≤ cj * L := by have := Nat.mul_le_mul_right L hcj1; simpa using this
      omega
    · -- an instance of `S`
      have hQq := par_lt S 0 _ _ hQ
      obtain ⟨rfl, rfl⟩ := shift_unique (show r ≤ r + qj by omega) (by omega) hrQ.le (by omega)
        (show r + qj + cj * L = Q + c' * L by omega)
      have hcS : r + qc ∈ children S (r + qj) := mem_children_iff.mpr ⟨by omega, hQ⟩
      have h1S : entry S 1 P ≤ entry S 1 (r + qc) := by
        rw [hS.e1N_sh hcj hrP' (by omega), e1N_blk hS.len hcj hqc] at h1
        by_cases hgC : TRIO.le1 S r (r + qc)
        · have hgJ := guard_par hrJ hQ (by omega) hgC
          have hgP := guard_par hrP hP (by omega) hgJ
          rw [if_pos hgC, if_pos hgP] at h1; omega
        · rw [if_neg hgC] at h1; split_ifs at h1 <;> omega
      obtain ⟨h2, hleaf, hlc, hlj⟩ := hBL P (r + qj) (r + qc) hjS hbS hcS h1S
      have hcle := last_le (children_sorted S _) hlc
      have hjle := last_le (children_sorted S _) hlj
      refine ⟨by rw [e2N_blk hS.len hcj hqc]; exact h2, nil_of_none (fun e he => ?_),
        getLast_of (children_sorted _ _) hc (fun e he => ?_), getLast_of (children_sorted _ _) hj (fun e he => ?_)⟩
      · rcases hS.children_shift hn (X := r + qc) (by omega) (by omega) hcj1 hcj
          (by rw [show r + qc + cj * L = r + (cj * L + qc) by omega]; exact he) with ⟨qe, _, _, _, heS⟩ | hPs
        · rw [hleaf] at heS; simp at heS
        · have : r + L ∈ children S (r + qc) := mem_children_iff.mpr ⟨hsS, hPs⟩
          rw [hleaf] at this; simp at this
      · rcases hS.children_shift hn (X := r + qj) (by omega) (by omega) hcj1 hcj
          (by rw [show r + qj + cj * L = r + (cj * L + qj) by omega]; exact he) with ⟨qe, _, _, rfl, heS⟩ | hPs
        · have := hcle _ heS; omega
        · have := hcle (r + L) (mem_children_iff.mpr ⟨hsS, hPs⟩); omega
      · rcases hS.children_shift hn hrP' (by omega) hcj1 hcj he with ⟨qe, _, _, rfl, heS⟩ | hPs
        · have := hjle _ heS; omega
        · have := hjle (r + L) (mem_children_iff.mpr ⟨hsS, hPs⟩); omega
    · -- `c` is the copy root `r + (cj + 1) L` under `j`: `s` would be a grandchild
      exfalso
      have hQs := par_lt S 0 _ _ hQ
      obtain ⟨h4, rfl⟩ := shift_unique (show r ≤ r + qj by omega) (by omega) hrQ.le (by omega)
        (show r + qj + cj * L = Q + (c' - 1) * L by omega)
      apply hnoBL P (r + qj) hjS hbS (mem_children_iff.mpr ⟨hsS, hQ⟩)
      rw [hS.e1N_sh hcj hrP' (by omega), hS.e1N_root hc1' hc', ← h4] at h1
      rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
      · subst hd1; split_ifs at h1 <;> simp at h1 <;> omega
      · have hgJ := guard_par hrJ hQ hsS (hg hd1)
        have hgP := guard_par hrP hP (by omega) hgJ
        rw [if_pos hgP] at h1; omega
    · exfalso; have := par_lt S 0 _ _ hjr
      have : L ≤ cj * L := by have := Nat.mul_le_mul_right L hcj1; simpa using this
      omega
  · ---------------- `j` a copy root, `t ≥ 1`
    exfalso
    exact hnbs hAs P hP (hS.bump_root hcj1 hcj hP hrP hg hb)
  · ---------------- `j` a copy root, `t = 0`
    exfalso
    subst hd0 hd1
    have hkr := par_lt S 0 _ _ hkS
    have hbS : col S r = bump S k := by
      rw [col_eq_entries] at hb ⊢
      unfold bump at hb ⊢
      rw [hS.e0N_root hcj1 hcj, hS.e1N_root hcj1 hcj, hS.e2N_root hcj, hS.eN_pre hn 0 (by omega),
        hS.eN_pre hn 1 (by omega), hS.e0s, hS.e1s, hS.e2s] at hb
      simpa using hb
    rcases hS.children_shift hn (X := r) (le_refl r) (by omega) hcj1 hcj
        (by simpa using hc) with ⟨qc, hqc0, hqc, rfl, hcS⟩ | hPs
    · rw [hS.eN_pre hn 1 (by omega), e1N_blk hS.len hcj hqc] at h1
      have h1S : entry S 1 k ≤ entry S 1 (r + qc) := by simpa using h1
      obtain ⟨_, _, _, hlj⟩ := hBL k r (r + qc) (mem_children_iff.mpr ⟨by omega, hkS⟩) hbS hcS h1S
      have := last_le (children_sorted S k) hlj (r + L)
        (mem_children_iff.mpr ⟨hsS, by rw [hS.par_s_t0 rfl]; exact hkS⟩)
      omega
    · rw [hS.par_s_t0 rfl, hkS] at hPs
      simp at hPs; omega

end

end Ytosk
