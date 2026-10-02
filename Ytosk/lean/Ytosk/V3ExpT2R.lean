/-
**3 行・t = 2: M[n] の依存の順位（抽象形）。**

N = M[n]、P = M[n − 1]、x = r + L、q = P_0(x)。N の x 以後は P の r 以後を L ずらしたもの（写しの対応）、
x より前は M と同じ構造（新しい辺は o(q) → o(x) と、q ≠ r で q が数えられるようになる o(p2) → o(q) だけ）。
順位は 4 段（実測: C′ の t = 2 の 3 万行列 × n = 2, 3, 4 で例外 0）:
- x より前で o(q)・o(p2) に依存しない呼び出し（M の順位）
- x 以後の写し（P の順位、底上げ B1）
- x より前で o(q) に依存する呼び出し（M の順位、底上げ B2）
- x より前で o(p2) に依存する呼び出し（M の順位、底上げ B3）
q = r では p2 = q とおく（3 段目と 4 段目が同じ集合）。
-/
import Ytosk.V3T2T

namespace Ytosk

open T Classical

/-- **The four-level ranking of `M[n]`** (`t = 2`). -/
noncomputable def rkN2 (M : Mat) (x L q p2 : Nat) (rkM rkP : Bool → Nat → Nat) (B1 B2 B3 : Nat) :
    Bool → Nat → Nat :=
  fun b i => if i < x then
      (if DepS M (SR p2) b i then B3 + rkM b i
       else if DepS M (SR q) b i then B2 + rkM b i else rkM b i)
    else B1 + rkP b (i - L)

section
variable {M : Mat} {x L q p2 : Nat} {rkM rkP : Bool → Nat → Nat} {B1 B2 B3 : Nat}

theorem rkN2_ge {b : Bool} {i : Nat} (hi : x ≤ i) :
    rkN2 M x L q p2 rkM rkP B1 B2 B3 b i = B1 + rkP b (i - L) := by
  unfold rkN2; rw [if_neg (by omega)]

theorem rkN2_base {b : Bool} {i : Nat} (hi : i < x) (h2 : ¬ DepS M (SR p2) b i) (h1 : ¬ DepS M (SR q) b i) :
    rkN2 M x L q p2 rkM rkP B1 B2 B3 b i = rkM b i := by
  unfold rkN2; rw [if_pos hi, if_neg h2, if_neg h1]

theorem rkN2_le {b : Bool} {i : Nat} (hi : i < x) (hB : B2 ≤ B3) :
    rkM b i ≤ rkN2 M x L q p2 rkM rkP B1 B2 B3 b i := by
  unfold rkN2; rw [if_pos hi]; split
  · omega
  · split <;> omega

theorem rkN2_ge_B2 {b : Bool} {i : Nat} (hi : i < x) (hB : B2 ≤ B3)
    (h : DepS M (SR p2) b i ∨ DepS M (SR q) b i) : B2 ≤ rkN2 M x L q p2 rkM rkP B1 B2 B3 b i := by
  unfold rkN2; rw [if_pos hi]
  by_cases h2 : DepS M (SR p2) b i
  · rw [if_pos h2]; omega
  · rw [if_neg h2, if_pos (h.resolve_left h2)]; omega

theorem rkN2_lt_B3 {b : Bool} {i : Nat} (hi : i < x) (hB : B2 + B1 ≤ B3) (hb : rkM b i < B1)
    (h2 : ¬ DepS M (SR p2) b i) : rkN2 M x L q p2 rkM rkP B1 B2 B3 b i < B3 := by
  unfold rkN2; rw [if_pos hi, if_neg h2]; split <;> omega

theorem rkN2_ge_B3 {b : Bool} {i : Nat} (hi : i < x) (h2 : DepS M (SR p2) b i) :
    B3 ≤ rkN2 M x L q p2 rkM rkP B1 B2 B3 b i := by
  unfold rkN2; rw [if_pos hi, if_pos h2]; omega

/-- **An edge of `M` below `x`, closed in both seeded sets, lowers the ranking.** -/
theorem rkN2_edge {b b' : Bool} {i j : Nat} (hi : i < x) (hj : j < x) (hB : B2 + B1 ≤ B3)
    (hbj : rkM b' j < B1) (hlt : rkM b' j < rkM b i)
    (c2 : DepS M (SR p2) b' j → DepS M (SR p2) b i) (c1 : DepS M (SR q) b' j → DepS M (SR q) b i) :
    rkN2 M x L q p2 rkM rkP B1 B2 B3 b' j < rkN2 M x L q p2 rkM rkP B1 B2 B3 b i := by
  unfold rkN2; rw [if_pos hi, if_pos hj]
  by_cases h2 : DepS M (SR p2) b' j
  · rw [if_pos h2, if_pos (c2 h2)]; omega
  · rw [if_neg h2]
    by_cases h1 : DepS M (SR q) b' j
    · rw [if_pos h1]
      by_cases h2' : DepS M (SR p2) b i
      · rw [if_pos h2']; omega
      · rw [if_neg h2', if_pos (c1 h1)]; omega
    · rw [if_neg h1]
      split
      · omega
      · split <;> omega

end

section
variable {M N P : Mat} {r L q p2 : Nat}

/-- **The ranking of `M[n]`** (`t = 2`) from the rankings of `M` and `M[n − 1]`, given the structural
correspondences: below `x` the structure of `M` (new edges only `o(q) → o(x)` and `o(p2) → o(q)`), from `x`
on the structure of `P` shifted by `L` (the copy root `x` reads its `v` from below `x`), and the targets
below `x` of the `v`-edges of the copies lie outside both seeded sets. -/
theorem rk_N_t2_abs
    (hNl : N.length = P.length + L) (hlen : r + L + 1 = M.length)
    (hq : par M 0 (r + L) = some q)
    (hpre : ∀ i, i < r + L → entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧
      par N 1 i = par M 1 i ∧ children N i = children M i ∧
      (∀ k, upg N i = some k → k < r + L ∧ upg M i = some k))
    (hcnt : ∀ i, i < r + L → ∀ c ∈ children N i, Counted N i c →
      Counted M i c ∨ (i = q ∧ c = r + L) ∨ (i = p2 ∧ c = q))
    (hbmp : ∀ i, i < r + L → ∀ j ∈ children N i, col N j = bump N i →
      col M j = bump M i ∧ ∀ k ∈ children N j, k < r + L)
    (hF2 : p2 ≠ q → ¬ DepS M (SR p2) true q)
    (hcp : ∀ a, r + L + a < N.length →
      children N (r + L + a) = (children P (r + a)).map (· + L) ∧
      (∀ d ∈ children P (r + a), (Counted N (r + L + a) (d + L) ↔ Counted P (r + a) d) ∧
        (col N (d + L) = bump N (r + L + a) ↔ col P d = bump P (r + a))) ∧
      entry N 2 (r + L + a) = entry P 2 (r + a))
    (hcp1 : ∀ a, 0 < a → r + L + a < N.length →
      (entry N 1 (r + L + a) ≠ 0 → entry P 1 (r + a) ≠ 0) ∧
      par N 1 (r + L + a) = (par P 1 (r + a)).map (fun t => if r ≤ t then t + L else t) ∧
      upg N (r + L + a) = (upg P (r + a)).map (fun t => if r ≤ t then t + L else t))
    (hcp0 : entry N 2 (r + L) = 0 ∧ (∀ m, par N 1 (r + L) = some m → m < r + L) ∧
      (∀ k, upg N (r + L) = some k → k < r + L))
    (htgt : ∀ g, g < r + L → (∃ a, r + L + a < N.length ∧ entry N 1 (r + L + a) ≠ 0 ∧
        (par N 1 (r + L + a) = some g ∨ (entry N 2 (r + L + a) = 0 ∧ upg N (r + L + a) = some g))) →
      ¬ DepS M (SR q) false g ∧ ¬ DepS M (SR p2) false g)
    {rkM rkP : Bool → Nat → Nat} (hRM : Rk M rkM) (hRP : Rk P rkP) :
    Rk N (rkN2 M (r + L) L q p2 rkM rkP (rkBound M rkM) (rkBound M rkM + rkBound P rkP)
      (rkBound M rkM + rkBound P rkP + rkBound M rkM)) := by
  set B1 := rkBound M rkM with hB1
  set B2 := rkBound M rkM + rkBound P rkP with hB2
  set B3 := rkBound M rkM + rkBound P rkP + rkBound M rkM with hB3
  set R := rkN2 M (r + L) L q p2 rkM rkP B1 B2 B3 with hR
  have hBB : B2 + B1 ≤ B3 := by omega
  have hxM : r + L < M.length := by omega
  have hqx := par_lt M 0 _ _ hq
  have hB23 : B2 ≤ B3 := by omega
  have hbM : ∀ b i, i < M.length → rkM b i < B1 := fun b i hi => rk_lt_bound M rkM hi b
  have hbP : ∀ b i, i < P.length → rkP b i < B2 - B1 := by
    intro b i hi; have := rk_lt_bound P rkP hi b; omega
  -- a copy call is below every seeded call
  have hcopy_lt : ∀ b' j b i, r + L ≤ j → j < N.length → i < r + L →
      (DepS M (SR p2) b i ∨ DepS M (SR q) b i) → R b' j < R b i := by
    intro b' j b i hj hjN hi hd
    rw [hR, rkN2_ge hj]
    have := hbP b' (j - L) (by omega)
    have := rkN2_ge_B2 (M := M) (L := L) (q := q) (p2 := p2) (rkM := rkM) (rkP := rkP) (B1 := B1)
      (b := b) hi hB23 hd
    omega
  -- a call below `x` outside both seeded sets is below every copy call
  have hbase_lt : ∀ g a b, g < r + L → r + L + a < N.length →
      ¬ DepS M (SR q) false g → ¬ DepS M (SR p2) false g → R false g < R b (r + L + a) := by
    intro g a b hg ha h1 h2
    rw [hR, rkN2_base hg h2 h1, rkN2_ge (by omega)]
    have := hbM false g (by omega); omega
  intro i hi
  rcases Nat.lt_or_ge i (r + L) with hix | hix
  · -- below `x`
    obtain ⟨he1, he2, hp1, hch, hup⟩ := hpre i hix
    obtain ⟨hR1, hR2, hR3⟩ := hRM i (by omega)
    refine ⟨?_, ?_, ?_⟩
    · exact rkN2_edge hix hix hBB (hbM false i (by omega)) hR1 DepS.ov DepS.ov
    · intro c hc hcb hcu
      have hcM : c ∈ children M i := hch ▸ hc
      have hcl := mem_children hcM
      -- the child at `x`: `i = q`, seeded
      have hxcase : c = r + L → R true c < R true i := by
        intro hcx
        have hiq : i = q := by
          have := (mem_children_iff.mp hcM).2
          rw [hcx, hq] at this; cases this; rfl
        exact hcopy_lt true c true i (by omega) (mem_children hc).2 hix
          (Or.inr (DepS.seed ⟨rfl, hiq⟩))
      rcases hcnt i hix c hc ⟨hcb, hcu⟩ with hcM' | ⟨_, hcx⟩ | ⟨hip, hcq⟩
      · rcases Nat.lt_or_ge c (r + L) with hcx | hcx
        · exact rkN2_edge hix hcx hBB (hbM true c (by omega)) (hR2 c hcM hcM'.1 hcM'.2)
            (DepS.ochild hcM hcM'.1 hcM'.2) (DepS.ochild hcM hcM'.1 hcM'.2)
        · exact hxcase (by omega)
      · exact hxcase hcx
      · -- the new edge `o(p2) → o(q)`
        have hci := (mem_children hc).1
        have hpq : p2 ≠ q := by intro h; rw [hip, h, ← hcq] at hci; omega
        have hcx : c < r + L := by
          have := (mem_children hc).1; rw [hcq] at this ⊢; omega
        have h3 := rkN2_ge_B3 (M := M) (x := r + L) (L := L) (q := q) (p2 := p2) (rkM := rkM) (rkP := rkP)
          (B1 := B1) (B2 := B2) (B3 := B3) (b := true) hix (by rw [hip]; exact DepS.seed ⟨rfl, rfl⟩)
        have h4 := rkN2_lt_B3 (M := M) (x := r + L) (L := L) (q := q) (p2 := p2) (rkM := rkM) (rkP := rkP)
          (B1 := B1) (B2 := B2) (B3 := B3) (b := true) hcx hBB (hbM true c (by omega))
          (by rw [hcq]; exact hF2 hpq)
        rw [hR]
        omega
    · intro h1
      have h1M : entry M 1 i ≠ 0 := by rwa [he1] at h1
      obtain ⟨hp, hu, hb⟩ := hR3 h1M
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        rw [hp1] at hm
        have hmi := par_lt M 1 i m hm
        exact rkN2_edge hix (by omega) hBB (hbM false m (by omega)) (hp m hm)
          (DepS.vpar h1M hm) (DepS.vpar h1M hm)
      · intro h2 k hk
        have h2M : entry M 2 i = 0 := by rwa [he2] at h2
        obtain ⟨hkx, hkM⟩ := hup k hk
        exact rkN2_edge hix hkx hBB (hbM false k (by omega)) (hu h2M k hkM)
          (DepS.vupg h1M h2M hkM) (DepS.vupg h1M h2M hkM)
      · intro h2 j hj hjb k hk
        have h2M : entry M 2 i ≠ 0 := by rwa [he2] at h2
        obtain ⟨hjb', hkx⟩ := hbmp i hix j hj hjb
        have hkx' := hkx k hk
        have hjk := (mem_children hk).1
        have hjM : j ∈ children M i := hch ▸ hj
        have hkM : k ∈ children M j := by
          have := (hpre j (by omega)).2.2.2.1; rw [this] at hk; exact hk
        exact rkN2_edge hix hkx' hBB (hbM true k (by omega)) (hb h2M j hjM hjb' k hkM)
          (DepS.vbump h1M h2M hjM hjb' hkM) (DepS.vbump h1M h2M hjM hjb' hkM)
  · -- the copies
    set a := i - (r + L) with ha
    have hia : i = r + L + a := by omega
    have hiN : r + L + a < N.length := by omega
    have hiP : r + a < P.length := by omega
    obtain ⟨hR1, hR2, hR3⟩ := hRP (r + a) hiP
    obtain ⟨hch, hcd, he2⟩ := hcp a hiN
    have hrki : ∀ b, R b i = B1 + rkP b (r + a) := by
      intro b; rw [hR, rkN2_ge hix]; congr 2; omega
    -- a shifted call
    have hsh : ∀ b d, r ≤ d → d < P.length → R b (d + L) = B1 + rkP b d := by
      intro b d hd hdP; rw [hR, rkN2_ge (by omega), Nat.add_sub_cancel]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrki, hrki]; omega
    · intro c hc hcb hcu
      rw [hia, hch] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      rw [hia] at hcb
      have hcount : Counted P (r + a) d := ((hcd d hd).1).mp ⟨hcb, hcu⟩
      have hdc := mem_children hd
      rw [hrki, hsh true d (by omega) hdc.2]
      have := hR2 d hd hcount.1 hcount.2
      omega
    · intro h1
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · -- the copy root: its `v` reads below `x`
        have hi0 : i = r + L := by omega
        obtain ⟨he20, hpm, hku⟩ := hcp0
        refine ⟨?_, ?_, ?_⟩
        · intro m hm
          rw [hi0] at hm h1
          have hmx := hpm m hm
          obtain ⟨n1, n2⟩ := htgt m hmx ⟨0, by omega, h1, Or.inl hm⟩
          rw [hi0]; exact hbase_lt m 0 false hmx (by omega) n1 n2
        · intro h2 k hk
          rw [hi0] at hk h1 h2
          have hkx := hku k hk
          obtain ⟨n1, n2⟩ := htgt k hkx ⟨0, by omega, h1, Or.inr ⟨h2, hk⟩⟩
          rw [hi0]; exact hbase_lt k 0 false hkx (by omega) n1 n2
        · intro h2; rw [hi0] at h2; exact absurd he20 h2
      · obtain ⟨he1P, hp1, hu1⟩ := hcp1 a h0 hiN
        have h1' : entry N 1 (r + L + a) ≠ 0 := by rw [← hia]; exact h1
        obtain ⟨hp, hu, hb⟩ := hR3 (he1P h1')
        refine ⟨?_, ?_, ?_⟩
        · intro m hm
          rw [hia, hp1] at hm
          cases ht : par P 1 (r + a) with
          | none => rw [ht] at hm; cases hm
          | some t =>
            rw [ht] at hm
            simp only [Option.map_some, Option.some.injEq] at hm
            have := hp t ht
            have htl := par_lt P 1 _ _ ht
            by_cases htr : r ≤ t
            · rw [if_pos htr] at hm
              subst hm
              rw [hrki, hsh false t htr (by omega)]; omega
            · rw [if_neg htr] at hm
              subst hm
              have hm' : par N 1 (r + L + a) = some t := by
                rw [hp1, ht]; simp [htr]
              obtain ⟨n1, n2⟩ := htgt t (by omega) ⟨a, hiN, h1', Or.inl hm'⟩
              rw [hia]; exact hbase_lt t a false (by omega) hiN n1 n2
        · intro h2 k hk
          have h2P : entry P 2 (r + a) = 0 := by rw [← he2, ← hia]; exact h2
          rw [hia, hu1] at hk
          cases ht : upg P (r + a) with
          | none => rw [ht] at hk; cases hk
          | some t =>
            rw [ht] at hk
            simp only [Option.map_some, Option.some.injEq] at hk
            have := hu h2P t ht
            have htl := upg_lt hiP ht
            by_cases htr : r ≤ t
            · rw [if_pos htr] at hk
              subst hk
              rw [hrki, hsh false t htr htl]; omega
            · rw [if_neg htr] at hk
              subst hk
              have hk' : upg N (r + L + a) = some t := by
                rw [hu1, ht]; simp [htr]
              obtain ⟨n1, n2⟩ := htgt t (by omega)
                ⟨a, hiN, h1', Or.inr ⟨by rw [← hia]; exact h2, hk'⟩⟩
              rw [hia]; exact hbase_lt t a false (by omega) hiN n1 n2
        · intro h2 j hj hjb k hk
          have h2P : entry P 2 (r + a) ≠ 0 := by rw [← he2, ← hia]; exact h2
          rw [hia, hch] at hj
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hj
          rw [hia] at hjb
          have hjb' := ((hcd d hd).2).mp hjb
          have hdc := mem_children hd
          have hdN : r + L + (d - r) < N.length := by omega
          rw [show d + L = r + L + (d - r) by omega, (hcp (d - r) hdN).1,
            show r + (d - r) = d by omega] at hk
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
          have hk'c := mem_children hk'
          rw [hrki, hsh true k' (by omega) hk'c.2]
          have := hb h2P d hd hjb' k' hk'
          omega

end

end Ytosk
