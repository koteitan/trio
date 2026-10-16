/-
**3 行・t = 2: のりしろの 2 欄 BumpKidsDec・BumpTermDec を M[n] へ運ぶ。**

- 写しの列: `BumpCopyFacts` で、のりしろの子の子の値は σ で移るか等しい（σ は順序を保つ、`pairwise_sh`）。
- x より前の v の種でない列: `BumpInfo` で M と同じか、最後ののりしろの子の最後の子だけ ◁ で下がる。
- v の種の列（`T2VSeedCol`）: 残り。
-/
import Ytosk.V3ExpT2CG
import Ytosk.V3ExpT2FO
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- The two bump fields at one column. -/
def BumpAt (N : Mat) (σ : Valn) (i : Nat) : Prop :=
  (entry N 1 i ≠ 0 → entry N 2 i ≠ 0 → ∀ j ∈ children N i, col N j = bump N i →
    ((children N j).map σ.o).Pairwise (fun a b => b ≤ a)) ∧
  (entry N 1 i ≠ 0 → entry N 2 i ≠ 0 →
    (nzs ((children N i).map (bumpTerm N σ i))).Pairwise (fun a b => b ≤ a))

theorem bump_fields_of {N : Mat} {σ : Valn} (h : ∀ i, BumpAt N σ i) :
    BumpKidsDec N σ ∧ BumpTermDec N σ :=
  ⟨fun i h1 h2 => (h i).1 h1 h2, fun i h1 h2 => (h i).2 h1 h2⟩

theorem nzs_map_sh {V V' : T} (l : List T) : nzs (l.map (sh V V')) = (nzs l).map (sh V V') := by
  unfold nzs
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  simp [Function.comp, sh_eq_z_iff]

/-- **The bump fields at the copy columns** from those of `P`. -/
theorem bump_copy {N P : Mat} {σ ρ : Valn} {r L : Nat} {V' : T} {g : Nat → Prop}
    (hF : BumpCopyFacts N P σ ρ r L V' g) (hGP : Good3 P ρ) (hrP : r < P.length)
    (hV' : isOT V' = true) (hVV : ρ.v r < V') (hR12 : R12 P) (he2r : entry P 2 r = 0)
    (hKD : BumpKidsDec P ρ) (hTD : BumpTermDec P ρ) :
    ∀ i, r ≤ i → i < P.length → BumpAt N σ (i + L) := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  intro i hri hi
  obtain ⟨he2, hch, hj⟩ := hF i hri hi
  have hri' : ∀ (h2 : entry N 2 (i + L) ≠ 0), r < i := by
    intro h2
    rcases Nat.lt_or_ge r i with h | h
    · exact h
    · have : i = r := by omega
      subst this; rw [he2] at h2; exact absurd he2r h2
  have hP12 : entry N 2 (i + L) ≠ 0 → entry P 1 i ≠ 0 ∧ entry P 2 i ≠ 0 := by
    intro h2
    rw [he2] at h2
    exact ⟨fun h1 => h2 (hR12 i h1), h2⟩
  -- the values of the children of a bump child
  have hval : ∀ (h2 : entry N 2 (i + L) ≠ 0) (j : Nat), j ∈ children P i → col P j = bump P i →
      (children P j).map (fun k => σ.o (k + L)) =
        if g i then ((children P j).map ρ.o).map (sh V V') else (children P j).map ρ.o := by
    intro h2 j hjP hjb
    obtain ⟨_, _, hk⟩ := hj j hjP
    split
    · rename_i hg
      rw [List.map_map]; apply List.map_congr_left; intro k hk'
      exact ((hk (hri' h2) hjb k hk').1 hg)
    · rename_i hg
      apply List.map_congr_left; intro k hk'
      exact ((hk (hri' h2) hjb k hk').2 hg)
  have hOTl : ∀ j, ∀ t ∈ (children P j).map ρ.o, isOT t = true := by
    intro j t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    exact hGP.ot_o k (mem_children hk).2
  refine ⟨fun h1 h2 j' hj' hjb' => ?_, fun h1 h2 => ?_⟩
  · rw [hch] at hj'
    obtain ⟨j, hjP, rfl⟩ := List.mem_map.mp hj'
    obtain ⟨hbmp, hchj, _⟩ := hj j hjP
    have hjb := (hbmp).mp hjb'
    obtain ⟨hP1, hP2⟩ := hP12 h2
    have hdec := hKD i hP1 hP2 j hjP hjb
    rw [hchj, List.map_map]
    have := hval h2 j hjP hjb
    simp only [Function.comp_def] at this ⊢
    rw [this]
    split
    · exact pairwise_sh hVo hV' hVV (hOTl j) hdec
    · exact hdec
  · obtain ⟨hP1, hP2⟩ := hP12 h2
    have hdec := hTD i hP1 hP2
    have hlist : (children N (i + L)).map (bumpTerm N σ (i + L)) =
        if g i then ((children P i).map (bumpTerm P ρ i)).map (sh V V')
        else (children P i).map (bumpTerm P ρ i) := by
      rw [hch, List.map_map]
      split
      · rename_i hg
        rw [List.map_map]
        apply List.map_congr_left
        intro j hjP
        obtain ⟨hbmp, hchj, _⟩ := hj j hjP
        simp only [Function.comp]
        unfold bumpTerm
        by_cases hjb : col P j = bump P i
        · rw [if_pos (hbmp.mpr hjb), if_pos hjb, hchj, List.map_map]
          have := hval h2 j hjP hjb
          simp only [Function.comp_def] at this ⊢
          rw [this, if_pos hg, sh_omega hVo hV' hVV (isOT_sumN _ (hOTl j)),
            sh_sumN hVo hV' hVV (hOTl j)]
        · rw [if_neg (fun h => hjb (hbmp.mp h)), if_neg hjb, sh_z]
      · rename_i hg
        apply List.map_congr_left
        intro j hjP
        obtain ⟨hbmp, hchj, _⟩ := hj j hjP
        simp only [Function.comp]
        unfold bumpTerm
        by_cases hjb : col P j = bump P i
        · rw [if_pos (hbmp.mpr hjb), if_pos hjb, hchj, List.map_map]
          have := hval h2 j hjP hjb
          simp only [Function.comp_def] at this ⊢
          rw [this, if_neg hg]
        · rw [if_neg (fun h => hjb (hbmp.mp h)), if_neg hjb]
    rw [hlist]
    split
    · rw [nzs_map_sh]
      apply pairwise_sh hVo hV' hVV _ hdec
      intro t ht
      unfold nzs at ht
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp ht).1
      exact isOT_bumpTerm hGP i j
    · exact hdec

end Ytosk

namespace Ytosk

open T Classical

/-- `ω^{ΣK + t'} ≤ ω^{ΣK + t}` for `t' ≤ t`. -/
theorem omega_sumN_snoc_le {l : List T} {t' t : T} (hl : ∀ u ∈ l, isOT u = true) (ht' : isOT t' = true)
    (ht : isOT t = true) (h : t' ≤ t) : omega (sumN (l ++ [t'])) ≤ omega (sumN (l ++ [t])) := by
  have hS := isOT_sumN l hl
  rw [sumN_snoc, sumN_snoc, sf_ot (isOT_add hS ht'), sf_ot (isOT_add hS ht)]
  rcases (le_iff _ _).mp (add_le_add_left (sumN l) h) with h' | h'
  · exact le_of_lt (omega_lt_omega (isOT_add hS ht') (isOT_add hS ht) h')
  · rw [h']

/-- **The bump fields of `N` at a column before `x`** from its `BumpInfo` against `M`. -/
theorem bump_below {M N : Mat} {ρ σ : Valn} {i x : Nat} (hGM : Good3 M ρ) (hCN : Cons N σ)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (he1 : entry N 1 i = entry M 1 i) (he2 : entry N 2 i = entry M 2 i)
    (hch : children N i = children M i)
    (hchj : ∀ j ∈ children M i, j < x → children N j = children M j)
    (hcolb : ∀ j ∈ children M i, (col N j = bump N i ↔ col M j = bump M i))
    (hjx : ∀ j ∈ children M i, col M j = bump M i → j < x)
    (hInfo : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → BumpInfo M N ρ σ i) : BumpAt N σ i := by
  have hOTM : ∀ (l : List Nat), (∀ k ∈ l, k < M.length) → ∀ u ∈ l.map ρ.o, isOT u = true := by
    intro l hl u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    exact hGM.ot_o k (hl k hk)
  refine ⟨fun h1 h2 j hj hjb => ?_, fun h1 h2 => ?_⟩
  · rw [he1] at h1; rw [he2] at h2
    rw [hch] at hj
    have hjbM := (hcolb j hj).mp hjb
    have hjx' := hjx j hj hjbM
    rcases hInfo h1 h2 with hsame | ⟨Lb, Kb, j0, k0, hchM, hchN, _, _, hchjM, hchjN, hKb, _, hLbv, hl, _⟩
    · rw [hchj j hj hjx', List.map_congr_left (fun k hk => hsame j hj hjbM k hk)]
      exact hKD i h1 h2 j hj hjbM
    · rw [hchM] at hj
      rcases List.mem_append.mp hj with hjL | hjL
      · rw [hchj j (by rw [hchM]; exact List.mem_append_left _ hjL) hjx',
          List.map_congr_left (fun k hk => hLbv j hjL hjbM k hk)]
        exact hKD i h1 h2 j (by rw [hchM]; exact List.mem_append_left _ hjL) hjbM
      · simp at hjL; subst hjL
        have hdec := hKD i h1 h2 j (by rw [hchM]; simp) hjbM
        rw [hchjM, List.map_append, List.map_singleton] at hdec
        rw [hchjN, List.map_append, List.map_singleton, List.map_congr_left hKb]
        have hp1 := List.pairwise_append.mp hdec
        refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun a ha b hb => ?_⟩
        simp at hb; rw [hb]
        exact le_trans (le_of_lt hl.1) (hp1.2.2 a ha (ρ.o k0) (List.mem_singleton_self _))
  · rw [he1] at h1; rw [he2] at h2
    have hdec := hTD i h1 h2
    rcases hInfo h1 h2 with hsame | ⟨Lb, Kb, j0, k0, hchM, hchN, hjb, hjbN, hchjM, hchjN, hKb, hLb, _, hl, hot⟩
    · have hlist : (children N i).map (bumpTerm N σ i) = (children M i).map (bumpTerm M ρ i) := by
        rw [hch]
        apply List.map_congr_left
        intro j hj
        unfold bumpTerm
        by_cases hjb : col M j = bump M i
        · rw [if_pos ((hcolb j hj).mpr hjb), if_pos hjb, hchj j hj (hjx j hj hjb),
            List.map_congr_left (fun k hk => hsame j hj hjb k hk)]
        · rw [if_neg (fun h => hjb ((hcolb j hj).mp h)), if_neg hjb]
      rw [hlist]; exact hdec
    · have hj0 : j0 ∈ children M i := by rw [hchM]; simp
      have hk0 : k0 ∈ children M j0 := by rw [hchjM]; simp
      have hKl : ∀ k ∈ Kb, k < M.length := fun k hk =>
        (mem_children (show k ∈ children M j0 by rw [hchjM]; exact List.mem_append_left _ hk)).2
      have hk0l := (mem_children hk0).2
      have htM : bumpTerm M ρ i j0 = omega (sumN (Kb.map ρ.o ++ [ρ.o k0])) := by
        unfold bumpTerm; rw [if_pos hjb, hchjM, List.map_append, List.map_singleton]
      have htN : bumpTerm N σ i j0 = omega (sumN (Kb.map ρ.o ++ [σ.o k0])) := by
        unfold bumpTerm; rw [if_pos hjbN, hchjN, List.map_append, List.map_singleton, List.map_congr_left hKb]
      have hle := omega_sumN_snoc_le (hOTM Kb hKl) hot (hGM.ot_o k0 hk0l) (le_of_lt hl.1)
      rw [← htN, ← htM] at hle
      have hnzN : bumpTerm N σ i j0 ≠ z := by rw [htN]; exact omega_ne_z _
      have hnzM : bumpTerm M ρ i j0 ≠ z := by rw [htM]; exact omega_ne_z _
      rw [hchM, List.map_append, List.map_singleton] at hdec
      rw [hchN, List.map_append, List.map_singleton, List.map_congr_left hLb]
      unfold nzs at hdec ⊢
      rw [List.filter_append] at hdec ⊢
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, hnzN, hnzM, ne_eq,
        not_false_eq_true, if_true] at hdec ⊢
      have hp1 := List.pairwise_append.mp hdec
      refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun a ha b hb => ?_⟩
      simp at hb; rw [hb]
      exact le_trans hle (hp1.2.2 a ha _ (List.mem_singleton_self _))

end Ytosk

namespace Ytosk

open T Classical

theorem bumpAt_out {N : Mat} {σ : Valn} {i : Nat} (hi : N.length ≤ i) : BumpAt N σ i := by
  have hch : children N i = [] := by
    rw [List.eq_nil_iff_forall_not_mem]; intro c hc; have := mem_children hc; omega
  refine ⟨fun _ _ j hj => by rw [hch] at hj; simp at hj, fun _ _ => by rw [hch]; simp [nzs]⟩

/-- The residual of the bump fields at the `v`-seed columns of `M[n]`. -/
def T2SeedBump (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ i, T2VSeedCol M r L i →
        BumpAt (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ i

/-- **`BumpKidsDec` and `BumpTermDec` of every `M[n]`** (`t = 2`, `n ≥ 1`). -/
theorem bumpFields_expand_t2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      BumpKidsDec (M.take (M.length - 1)) τ ∧ BumpTermDec (M.take (M.length - 1)) τ)
    (hSeed : T2SeedBump M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → BumpKidsDec (expand M n) σ ∧ BumpTermDec (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr hT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  have hd1 : 0 < d1 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (TRIO.gexp M r L d0 d1 m) σ → Good3 (TRIO.gexp M r L d0 d1 m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (TRIO.gexp M r L d0 d1 m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hXG : ∀ m, SInvX (TRIO.gexp M r L d0 d1 m) := fun m => by rw [← hexp m]; exact sInvX_expand hX m
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqx := par_lt M 0 _ _ hq
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  -- a bump child of a column before `x`, other than a `v`-seed, is before `x`
  have hjx : ∀ i j, i < r + L → ¬ T2VSeedCol M r L i → j ∈ children M i → col M j = bump M i → j < r + L := by
    intro i j hi hns hj hjb
    have := (mem_children hj).2
    by_contra h'
    have hjx' : j = r + L := by omega
    have hpj := (mem_children_iff.mp hj).2
    rw [hjx', hq] at hpj
    have hiq : q = i := Option.some.inj hpj
    by_cases hqr : q = r
    · rw [hjx', ← hiq, hqr] at hjb; exact hxbr hjb
    · exact hns (Or.inl ⟨q, hq, hqr, hiq.symm⟩)
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → ∀ i, BumpAt (TRIO.gexp M r L d0 d1 n) σ i := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ i
        rw [gexp_one_gen hlen] at hσ ⊢
        obtain ⟨hk, ht⟩ := hT σ hσ
        exact ⟨fun h1 h2 => hk i h1 h2, fun h1 h2 => ht i h1 h2⟩
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        have hm1 : 1 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        have hCP : Cons (TRIO.gexp M r L d0 d1 m) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hBP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hBEP : BumpE2 (TRIO.gexp M r L d0 d1 m) := (hXG m).loc.2.2.1
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBEP)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hX.loc.1
        have hF := bump_copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBEP)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (TRIO.gexp M r L d0 d1 (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (TRIO.gexp M r L d0 d1 m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have he2rP : entry (TRIO.gexp M r L d0 d1 m) 2 r = 0 := by
          rw [entry_gexp_pre hlen hm0 2 (by omega)]; exact he2r
        have hcopy := bump_copy hF hGP hrP hV' hVV (hXG m).r12 he2rP
          (fun i h1 h2 => (hBP i).1 h1 h2) (fun i h1 h2 => (hBP i).2 h1 h2)
        have hGN := hG (m + 1) hm1 σ hCN
        intro i
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2VSeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 σ hCN hGN i hsc
          · have hinfo := fun h1 h2 =>
              (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.2.2 hsc h1 h2
            apply bump_below (x := r + L) I.good hCN I.kd I.td (entry_gexp_pre hlen hm1 1 hix)
              (entry_gexp_pre hlen hm1 2 hix) (children_N2g hlen hL0 hA hq hd0e hn2 hix)
              (fun j _ hjx' => children_N2g hlen hL0 hA hq hd0e hn2 hjx')
              _ (fun j hj hjb => hjx i j hix hsc hj hjb) hinfo
            intro j hj
            rcases Nat.lt_or_ge j (r + L) with hjx' | hjx'
            · rw [col_gexp_pre hlen hm1 hjx']
              unfold bump; rw [entry_gexp_pre hlen hm1 0 hix, entry_gexp_pre hlen hm1 1 hix]
            · have hjeq : j = r + L := by have := (mem_children hj).2; omega
              subst hjeq
              constructor
              · intro h
                have := (bump_eq h).2.2
                have h2' : (col (TRIO.gexp M r L d0 d1 (m + 1)) (r + L)).2.2 =
                    entry (TRIO.gexp M r L d0 d1 (m + 1)) 2 (r + L) := rfl
                rw [h2', (entry_xprime_g (d1 := d1) hlen hL0 hA hq hd0e hn2).1, he2r] at this; omega
              · intro h; exact absurd (hjx i (r + L) hix hsc hj h) (lt_irrefl _)
        · rcases Nat.lt_or_ge i (r + (m + 1) * L) with hiN | hiN
          · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
            exact hcopy (r + a) (by omega) (by omega)
          · exact bumpAt_out (by omega)
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact bump_fields_of (key n hn σ hσ)

end Ytosk

namespace Ytosk

open T Classical

/-- **The bump fields at the `v`-seed columns hold**: at `q ≠ r` the bump children other than the lost
`x` keep their children and values (`vq_kids_N`), and `x − 1` (upgrading to `x`) has row 2 equal to `0`. -/
theorem t2SeedBump_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) : T2SeedBump M := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  intro r L hlen hr n hn σ hCN _ i hsc
  have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ r hr; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hL0 : 0 < L := by have := par_lt M 2 _ r hr; omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hm1 : 1 ≤ n := by omega
  rcases hsc with ⟨q, hq, hqr, rfl⟩ | ⟨hix, hu⟩
  · -- `q ≠ r`
    have hqx := par_lt M 0 _ _ hq
    have hrq : Anc0 M r i := anc0_par hA (by omega) hq
    have hrq' := hrq.le
    obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
    have hq' : par M 0 (r + L) = some (r + (i - r)) := by rw [show r + (i - r) = i by omega]; exact hq
    have hpq' : par M 0 (r + (i - r)) = some pq := by rw [show r + (i - r) = i by omega]; exact hpq
    obtain ⟨Txb, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
    rw [show r + (i - r) = i by omega] at Txb Tqb
    have hqb : ∀ a, par M 0 i = some a → col M i ≠ bump M a := by
      intro a ha; rw [hpq] at ha; cases ha; exact Tqb
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
    have hexp : expand M n = TRIO.gexp M r L d0 d1 n := by
      have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
      rw [h2, show M.length - 1 = r + L by omega] at h
      simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
        Nat.add_sub_cancel_left] at h
      exact h
    obtain ⟨rkN, hRN⟩ : ∃ rk, Rk (TRIO.gexp M r L d0 d1 n) rk := by
      obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank n hm1
      rw [hexp] at h'; exact ⟨rk', h'⟩
    have hUN : UAT (TRIO.gexp M r L d0 d1 n) := by rw [← hexp]; exact (sInvX_expand hX n).toSInv.uat
    have hkids := vq_kids_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 hqr Txb I.be hX.toSInv.uat hUN
      I.cons I.good hCN hRN
    have hchN : children (TRIO.gexp M r L d0 d1 n) i = children M i := children_N2g hlen hL0 hA hq hd0e hn hqx
    refine ⟨fun h1 h2' j hj hjb => ?_, fun h1 h2' => ?_⟩
    · obtain ⟨hjx, hjbM, hchj, hval⟩ := hkids j hj hjb
      rw [entry_gexp_pre hlen hm1 1 hqx] at h1; rw [entry_gexp_pre hlen hm1 2 hqx] at h2'
      rw [hchj, List.map_congr_left hval]
      exact I.kd i h1 h2' j (by rw [← hchN]; exact hj) hjbM
    · rw [entry_gexp_pre hlen hm1 1 hqx] at h1; rw [entry_gexp_pre hlen hm1 2 hqx] at h2'
      have hdec := I.td i h1 h2'
      have hxq : r + L ∈ children M i := mem_children_iff.mpr ⟨by omega, hq⟩
      have hsplit := split_last_max _ _ (children_sorted M i) hxq
        (fun d hd => by have := (mem_children hd).2; omega)
      set Lq := (children M i).filter (fun d => decide (d < r + L)) with hLq
      have hxnb : col (TRIO.gexp M r L d0 d1 n) (r + L) ≠ bump (TRIO.gexp M r L d0 d1 n) i := by
        intro h
        have := (bump_eq h).2.2
        have h2'' : (col (TRIO.gexp M r L d0 d1 n) (r + L)).2.2 = entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) := rfl
        rw [h2'', (entry_xprime_g (d1 := d1) hlen hL0 hA hq hd0e hn).1, he2r] at this; omega
      have hLq : Lq.map (bumpTerm (TRIO.gexp M r L d0 d1 n) σ i) = Lq.map (bumpTerm M ρ i) := by
        apply List.map_congr_left
        intro j hjL
        have hjx : j < r + L := by simpa using (List.mem_filter.mp hjL).2
        have hjM : j ∈ children M i := (List.mem_filter.mp hjL).1
        have hjN : j ∈ children (TRIO.gexp M r L d0 d1 n) i := by rw [hchN]; exact hjM
        unfold bumpTerm
        by_cases hjb : col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) i
        · obtain ⟨_, hjbM, hchj, hval⟩ := hkids j hjN hjb
          rw [if_pos hjb, if_pos hjbM, hchj, List.map_congr_left hval]
        · have hjbM : ¬ col M j = bump M i := by
            intro h; apply hjb
            rw [col_gexp_pre hlen hm1 hjx]; unfold bump
            rw [entry_gexp_pre hlen hm1 0 hqx, entry_gexp_pre hlen hm1 1 hqx]; exact h
          rw [if_neg hjb, if_neg hjbM]
      have htx : bumpTerm (TRIO.gexp M r L d0 d1 n) σ i (r + L) = z := by
        unfold bumpTerm; rw [if_neg hxnb]
      rw [hsplit, List.map_append, List.map_singleton] at hdec
      rw [hchN, hsplit, List.map_append, List.map_singleton, hLq, htx]
      unfold nzs at hdec ⊢
      rw [List.filter_append] at hdec ⊢
      simp only [List.filter_cons, List.filter_nil, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, if_false, List.append_nil]
      exact (List.pairwise_append.mp hdec).1
  · -- `x − 1` upgrading to `x`: row 2 is `0`
    have he2 : entry M 2 i = 0 := by
      have := (upg_e12 hu).2; have := hX.z2 i; omega
    refine ⟨fun _ h2' => absurd ?_ h2', fun _ h2' => absurd ?_ h2'⟩ <;>
      rw [entry_gexp_pre hlen hm1 2 (by omega)] <;> exact he2

end Ytosk

namespace Ytosk

open T Classical

/-- **`v_N(q)` in terms of `M`** (`q ≠ r`): `v_M(r) + ω^{1 + Σ bump terms of q before x}`. -/
theorem vq_eq_gexp {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L n q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hn : 2 ≤ n)
    {σ : Valn} (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) :
    σ.v q = add (ρ.v r) (omega (sumN (one ::
      ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)))) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ r hr; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hL0 : 0 < L := by have := par_lt M 2 _ r hr; omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hm1 : 1 ≤ n := by omega
  have hqx := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hrq' := hrq.le
  obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb Tqb
  have hqb : ∀ a, par M 0 q = some a → col M q ≠ bump M a := by
    intro a ha; rw [hpq] at ha; cases ha; exact Tqb
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
  have hexp : expand M n = TRIO.gexp M r L d0 d1 n := by
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  obtain ⟨rkN, hRN⟩ : ∃ rk, Rk (TRIO.gexp M r L d0 d1 n) rk := by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank n hm1
    rw [hexp] at h'; exact ⟨rk', h'⟩
  have hUN : UAT (TRIO.gexp M r L d0 d1 n) := by rw [← hexp]; exact (sInvX_expand hX n).toSInv.uat
  have hkids := vq_kids_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 hqr Txb I.be hX.toSInv.uat hUN
    I.cons I.good hCN hRN
  have hvr := vr_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 hX.toSInv.uat hUN I.cons hCN hRN
  have hchN : children (TRIO.gexp M r L d0 d1 n) q = children M q := children_N2g hlen hL0 hA hq hd0e hn hqx
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplit := split_last_max _ _ (children_sorted M q) hxq
    (fun d hd => by have := (mem_children hd).2; omega)
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLqd
  have hxnb : col (TRIO.gexp M r L d0 d1 n) (r + L) ≠ bump (TRIO.gexp M r L d0 d1 n) q := by
    intro h
    have := (bump_eq h).2.2
    have h2'' : (col (TRIO.gexp M r L d0 d1 n) (r + L)).2.2 = entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) := rfl
    rw [h2'', (entry_xprime_g (d1 := d1) hlen hL0 hA hq hd0e hn).1, he2r] at this; omega
  have hLq : Lq.map (bumpTerm (TRIO.gexp M r L d0 d1 n) σ q) = Lq.map (bumpTerm M ρ q) := by
    apply List.map_congr_left
    intro j hjL
    have hjx : j < r + L := by simpa using (List.mem_filter.mp hjL).2
    have hjM : j ∈ children M q := (List.mem_filter.mp hjL).1
    have hjN : j ∈ children (TRIO.gexp M r L d0 d1 n) q := by rw [hchN]; exact hjM
    unfold bumpTerm
    by_cases hjb : col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) q
    · obtain ⟨_, hjbM, hchj, hval⟩ := hkids j hjN hjb
      rw [if_pos hjb, if_pos hjbM, hchj, List.map_congr_left hval]
    · have hjbM : ¬ col M j = bump M q := by
        intro h; apply hjb
        rw [col_gexp_pre hlen hm1 hjx]; unfold bump
        rw [entry_gexp_pre hlen hm1 0 hqx, entry_gexp_pre hlen hm1 1 hqx]; exact h
      rw [if_neg hjb, if_neg hjbM]
  have htx : bumpTerm (TRIO.gexp M r L d0 d1 n) σ q (r + L) = z := by
    unfold bumpTerm; rw [if_neg hxnb]
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have hqN : q < (TRIO.gexp M r L d0 d1 n).length := by
    have := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n) hlen
    have : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega); omega
  have hv := (hCN q hqN).2
  unfold vRhs at hv
  rw [entry_gexp_pre hlen hm1 1 hqx, entry_gexp_pre hlen hm1 2 hqx, if_neg (by omega), if_neg (by omega),
    par_gexp_pre hlen hm1 1 hqx, par1_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 hqr Txb, hchN, hsplit,
    List.map_append, List.map_singleton, hLq, htx] at hv
  change σ.v q = sf (add (σ.v r) (omega (sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [z]))))) at hv
  have hOT : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  rw [← List.cons_append, sumN_snoc_z hOT, hvr] at hv
  rw [hv, sf_ot (isOT_add (I.good.ot_v r (by omega)) (isOT_omega (isOT_sumN _ hOT)))]

end Ytosk
