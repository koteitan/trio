/-
**3 行・t = 2: 写しの境界の事実 T2Base（写しの v が読む r より前の列の v は N と P で等しい）。**

- `agree_outside`: G.take x = M.take x で、r より前の列の子が M と同じなら、r より前で o(r) に依存しない呼び出しの
  値は G と M で等しい（`cons_agree`、E = 「r 以後か o(r) に依存」）。G = M[m]（m ≥ 1、M[1] = M.take x を含む）。
- 写しの列 i > r の P_1・上げの先 t < r は r の祖先で、背骨の条件を満たす（i は r の子孫、r と x の間は
  ガードで行 1 が e1(r) より大きい）。背骨の補題で v(t) は o(r) に依存しない。
-/
import Ytosk.V3ExpT2W
import Ytosk.V3T0V
import Ytosk.V3Spine

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **Agreement before `r` off the closure of `o(r)`**: a matrix `G` with the prefix `M.take x` and the
children of `M` before `r` has the values of `M` at the calls before `r` that do not depend on `o(r)`. -/
theorem agree_outside {M G : Mat} {ρ τ : Valn} {rkG : Bool → Nat → Nat} {r x : Nat}
    (hxM : x ≤ M.length) (hxG : x ≤ G.length) (hrx : r < x) (hT : G.take x = M.take x)
    (hUM : UAT M) (hUG : UAT G) (he2r : entry M 2 r = 0)
    (hch : ∀ i, i < r → children G i = children M i)
    (hchM : ∀ i c, i < r → c ∈ children M i → c ≤ r)
    (hCM : Cons M ρ) (hCG : Cons G τ) (hRG : Rk G rkG) :
    ∀ i, i < r → (¬ DepS M (SR r) true i → τ.o i = ρ.o i) ∧ (¬ DepS M (SR r) false i → τ.v i = ρ.v i) := by
  have hent : ∀ y j, j < x → entry G y j = entry M y j := fun y j hj => by
    rw [← entry_take G y hj, hT, entry_take M y hj]
  have hcol : ∀ j, j < x → col G j = col M j := fun j hj => by
    rw [← col_take G hj, hT, col_take M hj]
  have hbump : ∀ j, j < x → bump G j = bump M j := fun j hj => by
    rw [← bump_take G hj, hT, bump_take M hj]
  have hpar : ∀ k j, j < x → par G k j = par M k j := fun k j hj => by
    rw [← par_take G k j hj, hT, par_take M k j hj]
  have hupg : ∀ j, j + 1 < x → upg G j = upg M j := fun j hj => by
    rw [← upg_take G hj, hT, upg_take M hj]
  -- `r` is not an upgrade target
  have hrU : ∀ (H : Mat), entry H 2 r = 0 → isUpg H r = false := by
    intro H h2
    cases h : isUpg H r with
    | false => rfl
    | true =>
      exfalso
      unfold isUpg at h
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
      have := upg_target_e2 (of_decide_eq_true hk); omega
  have he2rG : entry G 2 r = 0 := by rw [hent 2 r hrx]; exact he2r
  -- counting of the children of a column before `r` agrees
  have hcntEq : ∀ i c, i < r → c ∈ children M i → (Counted G i c ↔ Counted M i c) := by
    intro i c hi hc
    have hcr := hchM i c hi hc
    unfold Counted
    rw [hcol c (by omega), hbump i (by omega)]
    rcases Nat.eq_or_lt_of_le hcr with rfl | hcr'
    · rw [hrU G he2rG, hrU M he2r]; simp
    · have htop : topped G c = topped M c :=
        topped_eq_of (hch c hcr') (fun d hd => hcol d (by
          have := hchM c d hcr' hd; omega)) (hbump c (by omega))
      rw [htop]
      by_cases ht : topped M c = true
      · rw [isUpg_topped_take hxM hxG hT hUM hUG (by omega) (by rw [htop]; exact ht) ht]
      · simp [ht]
  have hcnt : ∀ i c, i < r → c ∈ children M i → cnt G ρ i c = cnt M ρ i c := by
    intro i c hi hc
    rw [cnt_eq_ite, cnt_eq_ite]
    by_cases h : Counted M i c
    · rw [if_pos h, if_pos ((hcntEq i c hi hc).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((hcntEq i c hi hc).mp h'))]
  have hbt : ∀ i j, i < r → j ∈ children M i → bumpTerm G ρ i j = bumpTerm M ρ i j := by
    intro i j hi hj
    have hjr := hchM i j hi hj
    unfold bumpTerm
    rw [hcol j (by omega), hbump i (by omega)]
    by_cases hb : col M j = bump M i
    · have hjr' : j < r := by
        rcases Nat.eq_or_lt_of_le hjr with rfl | h
        · exfalso
          have := (bump_eq hb).2.2
          have h2' : (col M j).2.2 = entry M 2 j := rfl
          rw [h2', he2r] at this; omega
        · exact h
      rw [if_pos hb, if_pos hb, hch j hjr']
    · rw [if_neg hb, if_neg hb]
  -- the equations of `G` before `r`, with the values of `M`
  have hoEq : ∀ i, i < r → oRhs G ρ i = oRhs M ρ i := by
    intro i hi
    unfold oRhs
    rw [hch i hi]
    congr 3
    exact List.map_congr_left (fun c hc => hcnt i c hi hc)
  have hvEq : ∀ i, i < r → vRhs G ρ i = vRhs M ρ i := by
    intro i hi
    unfold vRhs
    rw [hent 1 i (by omega), hent 2 i (by omega), hpar 1 i (by omega), hupg i (by omega), hch i hi]
    rw [List.map_congr_left (fun j hj => hbt i j hi hj)]
  -- the agreement
  set E : Bool → Nat → Prop := fun b i => r ≤ i ∨ DepS M (SR r) b i with hE
  have hag := cons_agree E hCG hRG
    (fun i _ hi => by
      have hir : i < r := by by_contra h; exact hi (Or.inl (by omega))
      rw [hoEq i hir]; exact ((hCM i (by omega)).1))
    (fun i _ hi => by
      have hir : i < r := by by_contra h; exact hi (Or.inl (by omega))
      rw [hvEq i hir]; exact ((hCM i (by omega)).2))
    (by
      intro i _ hi
      have hir : i < r := by by_contra h; exact hi (Or.inl (by omega))
      have hD : ¬ DepS M (SR r) true i := fun h => hi (Or.inr h)
      refine ⟨fun h => ?_, fun c hc hcnt' => ?_⟩
      · rcases h with h | h
        · omega
        · exact hD (DepS.ov h)
      · rw [hch i hir] at hc
        have hcM := (hcntEq i c hir hc).mp hcnt'
        have hcr := hchM i c hir hc
        rintro (h | h)
        · have hcr' : c = r := by omega
          subst hcr'
          exact hD (DepS.ochild hc hcM.1 hcM.2 (DepS.seed ⟨rfl, rfl⟩))
        · exact hD (DepS.ochild hc hcM.1 hcM.2 h))
    (by
      intro i _ hi h1
      have hir : i < r := by by_contra h; exact hi (Or.inl (by omega))
      have hD : ¬ DepS M (SR r) false i := fun h => hi (Or.inr h)
      have h1M : entry M 1 i ≠ 0 := by rw [← hent 1 i (by omega)]; exact h1
      refine ⟨fun m hm => ?_, fun h2 k hk => ?_, fun h2 j hj hb k hk => ?_⟩
      · rw [hpar 1 i (by omega)] at hm
        have := par_lt M 1 i m hm
        rintro (h | h)
        · omega
        · exact hD (DepS.vpar h1M hm h)
      · rw [hupg i (by omega)] at hk
        have h2M : entry M 2 i = 0 := by rw [← hent 2 i (by omega)]; exact h2
        have hkl := upg_le hk
        rintro (h | h)
        · have hkr : k = r := by omega
          subst hkr
          have := upg_target_e2 hk; omega
        · exact hD (DepS.vupg h1M h2M hk h)
      · rw [hch i hir] at hj
        have hjr := hchM i j hir hj
        have h2M : entry M 2 i ≠ 0 := by rw [← hent 2 i (by omega)]; exact h2
        rw [hcol j (by omega), hbump i (by omega)] at hb
        have hjr' : j < r := by
          rcases Nat.eq_or_lt_of_le hjr with rfl | h
          · exfalso
            have := (bump_eq hb).2.2
            have h2' : (col M j).2.2 = entry M 2 j := rfl
            rw [h2', he2r] at this; omega
          · exact h
        rw [hch j hjr'] at hk
        have hkr := hchM j k hjr' hk
        rintro (h | h)
        · have hkr' : k = r := by omega
          subst hkr'
          exact hD (DepS.vbump h1M h2M hj hb hk (DepS.seed ⟨rfl, rfl⟩))
        · exact hD (DepS.vbump h1M h2M hj hb hk h))
  intro i hir
  have hiG : i < G.length := by omega
  obtain ⟨ho, hv⟩ := hag i hiG
  refine ⟨fun hD => ho ?_, fun hD => hv ?_⟩
  · rintro (h | h)
    · omega
    · exact hD h
  · rintro (h | h)
    · omega
    · exact hD h

/-! ## `M[m]` の r より前 -/

section
variable {M : Mat} {r L d0 d1 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

omit hd0e in
/-- The children of a column before `r` are at most `r`. -/
theorem children_le_r {i c : Nat} (hi : i < r) (hc : c ∈ children M i) : c ≤ r := by
  obtain ⟨hcl, hpc⟩ := mem_children_iff.mp hc
  by_contra h
  have hrc : Anc0 M r c := anc_between hA c (by omega) (by omega)
  have := (anc0_par hrc (by omega) hpc).le
  omega

/-- **The children before `r` of every `M[m]`** (`m ≥ 1`) are those of `M`. -/
theorem children_gexp_lt_r {m i : Nat} (hm : 1 ≤ m) (hi : i < r) :
    children (TRIO.gexp M r L d0 d1 m) i = children M i := by
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  rcases Nat.eq_or_lt_of_le hm with rfl | hm2
  · rw [gexp_one_gen hlen, children_take, List.filter_eq_self]
    intro c hc
    have := children_le_r hlen hL hA hi hc
    simp only [decide_eq_true_eq]; omega
  · exact children_N2g (d1 := d1) hlen hL hA hq hd0e hm2 (by omega)

/-- **The values before `r` off the closure of `o(r)`** in every `M[m]` (`m ≥ 1`) are those of `M`. -/
theorem agree_gexp {m : Nat} (hm : 1 ≤ m) (he2r : entry M 2 r = 0) (hUM : UAT M)
    (hUG : UAT (TRIO.gexp M r L d0 d1 m)) {ρ τ : Valn} {rkG : Bool → Nat → Nat} (hCM : Cons M ρ)
    (hCG : Cons (TRIO.gexp M r L d0 d1 m) τ) (hRG : Rk (TRIO.gexp M r L d0 d1 m) rkG) :
    ∀ i, i < r → (¬ DepS M (SR r) true i → τ.o i = ρ.o i) ∧ (¬ DepS M (SR r) false i → τ.v i = ρ.v i) := by
  have hlG : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
  have hmL : L ≤ m * L := by have := Nat.mul_le_mul_right L hm; simpa using this
  exact agree_outside (x := r + L) (by omega) (by omega) (by omega) (gexp_take_x hlen hm) hUM hUG he2r
    (fun i hi => children_gexp_lt_r hlen hL hA hd0e hm hi)
    (fun i c hi hc => children_le_r hlen hL hA hi hc) hCM hCG hRG

end

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
include hlen hL hA hd0e hn hd0 hd1 hgx he2r

/-- **The targets before `r` of the `v`-edges of the copies do not depend on `o(r)`** (spine lemma). -/
theorem tgt_lt_r_not_dep (hBL : BumpLeaf M) {i t : Nat} (hri : r < i)
    (hi : i < (TRIO.gexp M r L d0 d1 (n - 1)).length)
    (ht : par (TRIO.gexp M r L d0 d1 (n - 1)) 1 i = some t ∨ upg (TRIO.gexp M r L d0 d1 (n - 1)) i = some t)
    (htr : t < r) : ¬ DepS M (SR r) false t := by
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hm1 : 1 ≤ n - 1 := by omega
  have hU : UpS P t i := by
    rcases ht with h | h
    · exact upS_par1 h
    · obtain ⟨m, hm, hkm, he, hcase⟩ := upg_facts h
      rcases hcase with hk1 | ⟨hA', hki⟩
      · omega
      · exact upS_upg hm hkm he hA' hki
  obtain ⟨hti, htne, _, hbw⟩ := hU
  have hri' : Anc0 P r i := by
    obtain ⟨a, rfl⟩ : ∃ a, i = r + a := ⟨i - r, by omega⟩
    exact ancP_r hlen hL hA hd0e hn hd0 hd1 hgx (by omega)
  have htrP : Anc0 P t r := by
    rcases anc0_total hti hri' with h | h
    · exact h
    · have := h.le; omega
  have hcong : ∀ {u v : Nat}, v ≤ r → (Anc0 P u v ↔ Anc0 M u v) :=
    fun hv => anc0_congr_le (fun j hj => par_gexp_pre hlen hm1 0 (by omega)) hv
  have he1 : ∀ j, j < r + L → entry P 1 j = entry M 1 j := fun j hj => entry_gexp_pre hlen hm1 1 hj
  have htr' : Anc0 M t r := (hcong (le_refl _)).mp htrP
  have hle_tr : entry M 1 t ≤ entry M 1 r := by
    have := hbw r htrP hri' (by omega) (by omega)
    rwa [he1 t (by omega), he1 r (by omega)] at this
  have hI : InvC M (r + L) t := by
    intro w hw1 hw2 hw3 _
    rcases anc0_total hw2 hA with h | h
    · -- `w` between `t` and `r`
      have hwr := h.le
      have hwP : Anc0 P t w := (hcong hwr).mpr hw1
      have hwi : Anc0 P w i := Anc0.trans ((hcong (le_refl _)).mpr h) hri'
      have := hbw w hwP hwi hw3 (by omega)
      rwa [he1 t (by omega), he1 w (by omega)] at this
    · -- `w` between `r` and `x`
      by_cases hwr : w = r
      · subst hwr; exact hle_tr
      · have := (le1_window (show r + L < M.length by omega) hA).mp hgx w h hw2 hwr
        omega
  exact not_depS_spine hBL (Anc0.trans htr' hA) hI hA (by omega)

/-- **`T2Base` holds**: both `N` and `P` have the values of `M` at the targets. -/
theorem t2Base_gexp (hBL : BumpLeaf M) (hUM : UAT M) (hUN : UAT (TRIO.gexp M r L d0 d1 n))
    (hUP : UAT (TRIO.gexp M r L d0 d1 (n - 1))) {ρM σ ρ : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCM : Cons M ρM) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρ) (hRP : Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP) :
    T2Base (TRIO.gexp M r L d0 d1 (n - 1)) σ ρ r := by
  intro i t hri hi ht htr
  have hnd := tgt_lt_r_not_dep hlen hL hA hd0e hn hd0 hd1 hgx he2r hBL hri hi ht htr
  rw [(agree_gexp hlen hL hA hd0e (by omega) he2r hUM hUN hCM hCN hRN t htr).2 hnd,
    (agree_gexp hlen hL hA hd0e (by omega) he2r hUM hUP hCM hCP hRP t htr).2 hnd]

end

end Ytosk
