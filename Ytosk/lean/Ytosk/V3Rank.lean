/-
**3 行・t = 1・q ≠ r: M[n] の依存の順位。**

順位は 3 段: D に入らない x より前の呼び出し（M の順位）＜ 写しの列（P の順位、底上げ B1）＜ D の呼び出し
（M の順位、底上げ B2）。写しの列の P_1・上げが良い部分を指すとき、その呼び出しは D に入らない（仮定 `hnd`）。
-/
import Ytosk.V3T1

namespace Ytosk

open T

/-- Whether a child contributes to `o`. -/
def Counted (M : Mat) (i c : Nat) : Prop :=
  col M c ≠ bump M i ∧ ¬ (isUpg M c = true ∧ topped M c = true)

theorem cnt_eq_ite (M : Mat) (ρ : Valn) (i c : Nat) [Decidable (Counted M i c)] :
    cnt M ρ i c = if Counted M i c then ρ.o c else z := by
  unfold cnt Counted
  by_cases h1 : col M c = bump M i
  · rw [if_pos h1, if_neg (fun h => h.1 h1)]
  · rw [if_neg h1]
    by_cases h2 : isUpg M c = true ∧ topped M c = true
    · rw [if_pos h2, if_neg (fun h => h.2 h2)]
    · rw [if_neg h2, if_pos ⟨h1, h2⟩]

/-- Equal contributions for every valuation give the same decision. -/
theorem counted_of_cnt {M N : Mat} {i c : Nat} (h : ∀ ρ : Valn, cnt N ρ i c = cnt M ρ i c) :
    Counted N i c ↔ Counted M i c := by
  classical
  have h1 := h ⟨fun _ => one, fun _ => z⟩
  rw [cnt_eq_ite, cnt_eq_ite] at h1
  by_cases hN : Counted N i c <;> by_cases hM : Counted M i c
  · exact ⟨fun _ => hM, fun _ => hN⟩
  · rw [if_pos hN, if_neg hM] at h1; exact absurd h1 (by simp [one])
  · rw [if_neg hN, if_pos hM] at h1; exact absurd h1 (by simp [one])
  · exact ⟨fun h => absurd h hN, fun h => absurd h hM⟩

theorem omega_ne_z (x : T) : omega x ≠ z := by
  unfold omega
  split
  · simp
  · split <;> simp [one]

/-- Equal bump terms for every valuation give the same bump-child decision. -/
theorem bumpchild_of_bt {M N : Mat} {i j : Nat} (h : ∀ ρ : Valn, bumpTerm N ρ i j = bumpTerm M ρ i j) :
    col N j = bump N i ↔ col M j = bump M i := by
  have h1 := h ⟨fun _ => one, fun _ => z⟩
  unfold bumpTerm at h1
  by_cases hN : col N j = bump N i <;> by_cases hM : col M j = bump M i
  · exact ⟨fun _ => hM, fun _ => hN⟩
  · rw [if_pos hN, if_neg hM] at h1; exact absurd h1 (omega_ne_z _)
  · rw [if_neg hN, if_pos hM] at h1; exact absurd h1.symm (omega_ne_z _)
  · exact ⟨fun h => absurd h hN, fun h => absurd h hM⟩

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- The bump-child decision in a copy column is the shifted one. -/
theorem bumpchild_copy {a d : Nat} (ha : a < (n - 1) * L)
    (hd : d ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) :
    col (TRIO.gexp M r L d0 0 n) (d + L) = bump (TRIO.gexp M r L d0 0 n) (r + L + a) ↔
      col (TRIO.gexp M r L d0 0 (n - 1)) d = bump (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hdc := mem_children hd
  rw [hlP] at hdc
  have hda : d - r < (n - 1) * L := by omega
  rw [show d + L = r + L + (d - r) by omega, col_copy (d0 := d0) hlen hL hn hda,
    show r + (d - r) = d by omega]
  unfold bump
  rw [e0_copy (d0 := d0) hlen hL hn ha, e1_gexp_shift hlen hL hn ha, col_eq_entries]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

/-- The counted decision in a copy column is the shifted one. -/
theorem counted_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hz2 : entry M 2 r ≤ 1) {a d : Nat} (ha : a < (n - 1) * L)
    (hd : d ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)) :
    Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L) ↔
      Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hdc := mem_children hd
  rw [hlP] at hdc
  have hda : d - r < (n - 1) * L := by omega
  have hd' : d + L = r + L + (d - r) := by omega
  have hup : isUpg (TRIO.gexp M r L d0 0 n) (d + L) = isUpg (TRIO.gexp M r L d0 0 (n - 1)) d := by
    rw [hd', isUpg_copy hlen hL hA hd0e hn hpath hz2 (by omega) hda, show r + (d - r) = d by omega]
  have htop : topped (TRIO.gexp M r L d0 0 n) (d + L) = topped (TRIO.gexp M r L d0 0 (n - 1)) d := by
    rw [hd', topped_copy hlen hL hA hd0e hn hda, show r + (d - r) = d by omega]
  unfold Counted
  rw [ne_eq, ne_eq, bumpchild_copy hlen hL hA hd0e hn ha hd, hup, htop]

end

open Classical in
/-- **The three-level ranking of `M[n]`.** -/
noncomputable def rkN (M : Mat) (x L : Nat) (rkM rkP : Bool → Nat → Nat) (B1 B2 : Nat) :
    Bool → Nat → Nat :=
  fun b i => if i < x then (if DepX M x b i then B2 + rkM b i else rkM b i) else B1 + rkP b (i - L)

theorem rkN_lt_nodep {M : Mat} {x L : Nat} {rkM rkP : Bool → Nat → Nat} {B1 B2 : Nat} {b : Bool}
    {i : Nat} (hi : i < x) (hd : ¬ DepX M x b i) : rkN M x L rkM rkP B1 B2 b i = rkM b i := by
  unfold rkN; rw [if_pos hi, if_neg hd]

theorem rkN_lt_dep {M : Mat} {x L : Nat} {rkM rkP : Bool → Nat → Nat} {B1 B2 : Nat} {b : Bool}
    {i : Nat} (hi : i < x) (hd : DepX M x b i) : rkN M x L rkM rkP B1 B2 b i = B2 + rkM b i := by
  unfold rkN; rw [if_pos hi, if_pos hd]

theorem rkN_ge {M : Mat} {x L : Nat} {rkM rkP : Bool → Nat → Nat} {B1 B2 : Nat} {b : Bool}
    {i : Nat} (hi : x ≤ i) : rkN M x L rkM rkP B1 B2 b i = B1 + rkP b (i - L) := by
  unfold rkN; rw [if_neg (by omega)]

/-- A lower bound of the ranking below `x`. -/
theorem rkN_ge_rkM {M : Mat} {x L : Nat} {rkM rkP : Bool → Nat → Nat} {B1 B2 : Nat} {b : Bool}
    {i : Nat} (hi : i < x) : rkM b i ≤ rkN M x L rkM rkP B1 B2 b i := by
  unfold rkN; rw [if_pos hi]; split <;> omega

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **`M[n]` has a ranking** (`t = 1`, `q ≠ r`). -/
theorem rk_N_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hqr : ∀ q, par M 0 (r + L) = some q → q ≠ r) (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {rkM rkP : Bool → Nat → Nat} (hRM : Rk M rkM) (hRP : Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP) :
    Rk (TRIO.gexp M r L d0 0 n) (rkN M (r + L) L rkM rkP (rkBound M rkM)
      (rkBound M rkM + rkBound (TRIO.gexp M r L d0 0 (n - 1)) rkP)) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  set B1 := rkBound M rkM with hB1
  set B2 := rkBound M rkM + rkBound (TRIO.gexp M r L d0 0 (n - 1)) rkP with hB2
  set N := TRIO.gexp M r L d0 0 n with hN
  set P := TRIO.gexp M r L d0 0 (n - 1) with hP
  have hbM : ∀ b i, i < M.length → rkM b i < B1 := fun b i hi => rk_lt_bound M rkM hi b
  have hbP : ∀ b i, i < P.length → rkP b i < B2 - B1 := by
    intro b i hi; have := rk_lt_bound P rkP hi b; omega
  -- the copy root
  have hroot : ∀ b, rkN M (r + L) L rkM rkP B1 B2 b (r + L) = B1 + rkP b r := by
    intro b; rw [rkN_ge (Nat.le_refl _)]; congr 2; omega
  have hrootlt : ∀ b, rkN M (r + L) L rkM rkP B1 B2 b (r + L) < B2 := by
    intro b; rw [hroot]; have := hbP b r (by
      have : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
      omega); omega
  intro i hi
  rcases Nat.lt_or_ge i (r + L) with hix | hix
  · -- below `x`
    have SA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hqr hiu hiux i hix
    have hiM : i < M.length := by omega
    obtain ⟨hR1, hR2, hR3⟩ := hRM i hiM
    refine ⟨?_, ?_, ?_⟩
    · by_cases hdv : DepX M (r + L) false i
      · rw [rkN_lt_dep hix hdv, rkN_lt_dep hix (DepX.ov hdv)]; omega
      · rw [rkN_lt_nodep hix hdv]
        have := rkN_ge_rkM (L := L) (rkM := rkM) (rkP := rkP) (B1 := B1) (B2 := B2) (b := true) hix (M := M)
        omega
    · intro c hc hcb hcu
      rw [SA.ch] at hc
      have hcount : Counted M i c := (counted_of_cnt (fun ρ => SA.cnt c hc ρ)).mp ⟨hcb, hcu⟩
      have hcl := (mem_children hc).2
      rcases Nat.lt_or_ge c (r + L) with hcx | hcx
      · have hlt := hR2 c hc hcount.1 hcount.2
        by_cases hdc : DepX M (r + L) true c
        · have hdi := DepX.ochild hc hcount.1 hcount.2 hdc
          rw [rkN_lt_dep hcx hdc, rkN_lt_dep hix hdi]; omega
        · rw [rkN_lt_nodep hcx hdc]
          have := rkN_ge_rkM (L := L) (rkM := rkM) (rkP := rkP) (B1 := B1) (B2 := B2) (b := true) hix (M := M)
          omega
      · have hcx' : c = r + L := by omega
        subst hcx'
        have hdi := DepX.ochild hc hcount.1 hcount.2 DepX.leaf
        rw [rkN_lt_dep hix hdi]
        have := hrootlt true
        omega
    · intro h1
      rw [SA.e1] at h1
      obtain ⟨hp, hu, hb⟩ := hR3 h1
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        rw [SA.par1] at hm
        have hmi := par_lt M 1 i m hm
        by_cases hdm : DepX M (r + L) false m
        · have hdi := DepX.vpar h1 hm hdm
          rw [rkN_lt_dep (by omega) hdm, rkN_lt_dep hix hdi]; have := hp m hm; omega
        · rw [rkN_lt_nodep (by omega) hdm]
          have := rkN_ge_rkM (L := L) (rkM := rkM) (rkP := rkP) (B1 := B1) (B2 := B2) (b := false) hix (M := M)
          have := hp m hm; omega
      · intro h2 k hk
        rw [SA.e2] at h2
        rw [SA.upg] at hk
        have hkx := reads_lt_x hlen hx2 hix (Or.inr ⟨h2, hk⟩)
        by_cases hdk : DepX M (r + L) false k
        · have hdi := DepX.vupg h1 h2 hk hdk
          rw [rkN_lt_dep hkx hdk, rkN_lt_dep hix hdi]; have := hu h2 k hk; omega
        · rw [rkN_lt_nodep hkx hdk]
          have := rkN_ge_rkM (L := L) (rkM := rkM) (rkP := rkP) (B1 := B1) (B2 := B2) (b := false) hix (M := M)
          have := hu h2 k hk; omega
      · intro h2 j hj hjb k hk
        rw [SA.e2] at h2
        rw [SA.ch] at hj
        have hjb' : col M j = bump M i := (bumpchild_of_bt (fun ρ => SA.bt j hj ρ)).mp hjb
        have hjl := (mem_children hj).2
        -- `j` is not `x` (the copy root is not a bump child)
        have hjx : j < r + L := by
          rcases Nat.lt_or_ge j (r + L) with h | h
          · exact h
          · exfalso
            have hjx' : j = r + L := by omega
            subst hjx'
            have : (col M (r + L)).2.2 = 0 := hx2
            rw [hjb'] at this; unfold bump at this; simp at this
        rw [children_N_lt hlen hL hA hd0e hn hjx] at hk
        have hkl := (mem_children hk).2
        have hlt := hb h2 j hj hjb' k hk
        by_cases hdk : DepX M (r + L) true k
        · have hdi := DepX.vbump h1 h2 hj hjb' hk hdk
          rw [rkN_lt_dep hix hdi]
          rcases Nat.lt_or_ge k (r + L) with hkx | hkx
          · rw [rkN_lt_dep hkx hdk]; omega
          · have hkx' : k = r + L := by omega
            subst hkx'
            have := hrootlt true; omega
        · have hkx : k < r + L := by
            rcases Nat.lt_or_ge k (r + L) with h | h
            · exact h
            · have : k = r + L := by omega
              subst this; exact absurd DepX.leaf hdk
          rw [rkN_lt_nodep hkx hdk]
          have := rkN_ge_rkM (L := L) (rkM := rkM) (rkP := rkP) (B1 := B1) (B2 := B2) (b := false) hix (M := M)
          omega
  · -- the copies
    set a := i - (r + L) with ha
    have hia : i = r + L + a := by omega
    have haL : a < (n - 1) * L := by omega
    have hiP : r + a < P.length := by omega
    obtain ⟨hR1, hR2, hR3⟩ := hRP (r + a) hiP
    have hrki : ∀ b, rkN M (r + L) L rkM rkP B1 B2 b i = B1 + rkP b (r + a) := by
      intro b; rw [rkN_ge hix]; congr 2; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hrki, hrki]; omega
    · intro c hc hcb hcu
      rw [hia, children_shift hlen hL hA hd0e hn haL] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      rw [hia] at hcb
      have hcount : Counted P (r + a) d :=
        (counted_copy hlen hL hA hd0e hn hpath hz2 haL hd).mp ⟨hcb, hcu⟩
      have hdc := mem_children hd
      rw [hrki, rkN_ge (by omega), Nat.add_sub_cancel]
      have := hR2 d hd hcount.1 hcount.2
      omega
    · intro h1
      rw [hia, e1_gexp_shift hlen hL hn haL] at h1
      obtain ⟨hp, hu, hb⟩ := hR3 h1
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        rw [hia] at hm
        rw [hrki]
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · rw [h0, show r + L + 0 = r + L by omega, par1_root hlen hL hA hd0e hn hpath,
            ← par_gexp_pre (d0 := d0) (d1 := 0) (m := n - 1) hlen (by omega) 1 (by omega)] at hm
          rw [h0] at hp
          have hmr := par_lt _ 1 _ _ hm
          have hnd' := hnd m (by omega) 0 (by omega) (Or.inl (by simpa using hm))
          rw [rkN_lt_nodep (by omega) hnd']
          have := hbM false m (by omega); omega
        · rw [par1_copy hlen hL hA hd0e hn hpath h0 haL] at hm
          cases ht : par P 1 (r + a) with
          | none => rw [ht] at hm; cases hm
          | some t =>
            rw [ht] at hm
            simp only [Option.map_some, Option.some.injEq] at hm
            have := hp t ht
            by_cases htr : r ≤ t
            · rw [if_pos htr] at hm
              subst hm
              rw [rkN_ge (by omega), Nat.add_sub_cancel]; omega
            · rw [if_neg htr] at hm
              subst hm
              have hnd' := hnd t (by omega) a haL (Or.inl ht)
              rw [rkN_lt_nodep (by omega) hnd']
              have := hbM false t (by omega); omega
      · intro h2 k hk
        rw [hia, e2_copy (d0 := d0) hlen hL hn haL] at h2
        rw [hia] at hk
        rw [hrki]
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · rw [h0, show r + L + 0 = r + L by omega, upg_root hlen hL hA hd0e hn hpath hz2] at hk
          have hkr := upgP_root_lt hlen hL hA hd0e hn hk
          have hnd' := hnd k (by omega) 0 (by omega) (Or.inr (by simpa using hk))
          rw [rkN_lt_nodep (by omega) hnd']
          have := hbM false k (by omega); omega
        · rw [upg_copy hlen hL hA hd0e hn hpath h0 haL] at hk
          cases ht : upg P (r + a) with
          | none => rw [ht] at hk; cases hk
          | some t =>
            rw [ht] at hk
            simp only [Option.map_some, Option.some.injEq] at hk
            have := hu h2 t ht
            by_cases htr : r < t
            · rw [if_pos htr] at hk
              subst hk
              rw [rkN_ge (by omega), Nat.add_sub_cancel]; omega
            · rw [if_neg htr] at hk
              subst hk
              have hnd' := hnd t (by omega) a haL (Or.inr ht)
              rw [rkN_lt_nodep (by omega) hnd']
              have := hbM false t (by omega); omega
      · intro h2 j hj hjb k hk
        rw [hia, e2_copy (d0 := d0) hlen hL hn haL] at h2
        rw [hia, children_shift hlen hL hA hd0e hn haL] at hj
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hj
        rw [hia] at hjb
        have hjb' := (bumpchild_copy hlen hL hA hd0e hn haL hd).mp hjb
        have hdc := mem_children hd
        rw [hlP] at hdc
        rw [show d + L = r + L + (d - r) by omega,
          children_shift hlen hL hA hd0e hn (show d - r < (n - 1) * L by omega),
          show r + (d - r) = d by omega] at hk
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
        have hk'c := mem_children hk'
        rw [hrki, rkN_ge (by omega), Nat.add_sub_cancel]
        have := hb h2 d hd hjb' k' hk'
        omega

end

end Ytosk
