/-
**T2VRAPre を種の列の枠の形に帰着（2026-10-17、t1）。**

N = M[n]（t = 2）の x より前の段の道は M の段の道に枠ごとに写る:
- 種の列でない枠: FrameShape（T2BelowXS）で、N で書き換えるなら M でも同じ v・同じ状態・同じ添字で、引数は M の方が
  大きい（`frame_of_shape`）。
- q ≠ r の q: x は q ののりしろの子（t2_qn_struct）なので、q の子はすべてのりしろの列で、x より前に数える子はない。
- 種 p（q = r なら r、q ≠ r なら P_0 q）で子 c ≠ q: 名前つきの残り `T2SeedPreShape`（測定: d3s・t2ext・ext2・expP
  各 2000 行列で、N で書き換える枠は M でも同じ値で書き換える）。p の子 q の枠は N だけで書き換えることがあるが、
  q 自身が種の列なので T2VRAPre には効かない。
-/
import Ytosk.V3T2VRA
import Ytosk.V3T0VSRAllN

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **A rewriting frame of `N` with the shape of `M`** is a rewriting frame of `M`. -/
theorem frame_of_shape {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ)
    (hGN : Good3 N σ) (hS : FrameShape M N ρ σ i) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL N i = Lc ++ c :: R) {s y : T} (hsy : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v i) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v i) z z) (psi s y z) = true) :
    ∃ (Lc' R' : List Nat) (yM : T), CL M i = Lc' ++ c :: R' ∧ σ.v i = ρ.v i ∧ Lc'.map ρ.o = Lc.map σ.o ∧
      ρ.o c = psi s yM z ∧ y ≤ yM ∧
      (lt (spArg (ρ.v i) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v i) z z) (psi s yM z) = true) := by
  rcases hS with ⟨hv, hcl, hsame⟩ | ⟨hv, Lc0, c0, hclM, hclN, hsame, hl, hot, hchv, _⟩ | ⟨hN, _⟩
  · rw [hcl] at hCL
    have hmem : ∀ d ∈ Lc ++ [c], d ∈ CL M i := fun d hd => by
      rw [hCL]
      rcases List.mem_append.mp hd with h | h
      · exact List.mem_append_left _ h
      · simp at h; rw [h]; simp
    have hLo : Lc.map ρ.o = Lc.map σ.o :=
      List.map_congr_left (fun d hd => (hsame d (hmem d (List.mem_append_left _ hd))).symm)
    have hoc : ρ.o c = psi s y z := by rw [← hsame c (hmem c (by simp))]; exact hsy
    refine ⟨Lc, R, y, hCL, hv, hLo, hoc, le_refl _, ?_⟩
    rw [← hv, hLo]; exact ht
  · rw [hclN] at hCL
    by_cases hR : R = []
    · rw [hR] at hCL
      obtain ⟨h1, h2⟩ := List.append_inj' hCL rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h1; subst h2
      have hcM : c0 < M.length := (mem_children (cl_mem_children (show c0 ∈ CL M i by rw [hclM]; simp))).2
      have hcN : c0 < N.length := (mem_children (cl_mem_children (show c0 ∈ CL N i by rw [hclN]; simp))).2
      obtain ⟨yM, hyM⟩ := o_psi_sub hC hcM
      rw [sf_ot (hG.ot_v c0 hcM)] at hyM
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hcN
      rw [sf_ot (hGN.ot_v c0 hcN), hsy] at hy1
      simp only [psi.injEq] at hy1
      have hvc : σ.v c0 = ρ.v c0 := by
        by_contra hne
        have := hchv hne
        rw [hsy] at this; simp only [psi.injEq] at this
        exact absurd ht.1 (by rw [this.2.1]; exact T.not_lt_z _)
      have hsv : s = ρ.v c0 := by rw [hy1.1, hvc]
      rw [← hsv] at hyM
      have hle : psi s y z ≤ psi s yM z := by rw [← hsy, ← hyM]; exact le_of_lt hl.1
      have hyy := arg_le_of_psi_le hle
      have hLo : Lc0.map ρ.o = Lc0.map σ.o := List.map_congr_left (fun d hd => (hsame d hd).symm)
      refine ⟨Lc0, [], yM, hclM, hv, hLo, hyM, hyy, ?_⟩
      rw [← hv, hLo]; exact rw_up hyy ht
    · have hdl : (Lc ++ c :: R).dropLast = Lc0 := by rw [← hCL]; simp
      rw [List.dropLast_append_of_ne_nil (by simp)] at hdl
      have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
      have hcs : c ∈ Lc0 := by
        rw [← hdl]
        apply List.mem_append_right
        obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
        simp
      have hclM' : CL M i = Lc ++ c :: R := by rw [hclM, hCL]
      have hLo : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hsame d (hLs d hd)).symm)
      have hoc : ρ.o c = psi s y z := by rw [← hsame c hcs]; exact hsy
      refine ⟨Lc, R, y, hclM', hv, hLo, hoc, le_refl _, ?_⟩
      rw [← hv, hLo]; exact ht
  · rw [hN] at hCL; simp at hCL

/-- **R-seedpre**: the frames of `M[n]` at a seed `p` (`T2Seed`) with a child before `x` other than `q`
are frames of `M` with the same values and a larger argument. -/
def T2SeedPreShape (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
    ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ p, T2Seed M r L p → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) p = Lc ++ c :: R →
      c < r + L → (∀ q, par M 0 (r + L) = some q → c ≠ q) → ∀ s y, σ.o c = psi s y z →
      (lt (spArg (σ.v p) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v p) z z) (psi s y z) = true) →
      ∃ (Lc' R' : List Nat) (yM : T), CL M p = Lc' ++ c :: R' ∧ σ.v p = ρ.v p ∧ Lc'.map ρ.o = Lc.map σ.o ∧
        ρ.o c = psi s yM z ∧ y ≤ yM ∧
        (lt (spArg (ρ.v p) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v p) z z) (psi s yM z) = true)

/-- **The path levels before `x`** (away from `q ≠ r`) are levels of `M`. -/
theorem pathLvAll_pre_t2 {M N : Mat} {ρ σ : Valn} {r L : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons N σ) (hGN : Good3 N σ)
    (hshape : ∀ k, k < r + L → ¬ T2SeedCol M r L k → FrameShape M N ρ σ k)
    (hSP : ∀ p, T2Seed M r L p → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N p = Lc ++ c :: R →
      c < r + L → (∀ q, par M 0 (r + L) = some q → c ≠ q) → ∀ s y, σ.o c = psi s y z →
      (lt (spArg (σ.v p) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v p) z z) (psi s y z) = true) →
      ∃ (Lc' R' : List Nat) (yM : T), CL M p = Lc' ++ c :: R' ∧ σ.v p = ρ.v p ∧ Lc'.map ρ.o = Lc.map σ.o ∧
        ρ.o c = psi s yM z ∧ y ≤ yM ∧
        (lt (spArg (ρ.v p) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v p) z z) (psi s yM z) = true))
    (hqc : ∀ q, par M 0 (r + L) = some q → q ≠ r → ∀ c ∈ CL N q, ¬ c < r + L) :
    ∀ c u, PathLvAll N σ c u → c < r + L → (∀ q, par M 0 (r + L) = some q → q ≠ r → c ≠ q) →
      PathLvAll M ρ c u := by
  -- one frame of the path
  have hframe : ∀ k (Lc : List Nat) c (R : List Nat) s y, CL N k = Lc ++ c :: R → σ.o c = psi s y z →
      (lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v k) z z) (psi s y z) = true) →
      c < r + L → (∀ q, par M 0 (r + L) = some q → q ≠ r → c ≠ q) →
      (∀ q, par M 0 (r + L) = some q → q ≠ r → k ≠ q) ∧
      ∃ (Lc' R' : List Nat) (yM : T), CL M k = Lc' ++ c :: R' ∧ σ.v k = ρ.v k ∧
        ρ.o c = psi s yM z ∧
        (lt (spArg (ρ.v k) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v k) z z) (psi s yM z) = true) := by
    intro k Lc c R s y hcl hsy ht hcx hcq
    have hcCL : c ∈ CL N k := by rw [hcl]; simp
    have hkc := (mem_children (cl_mem_children hcCL)).1
    have hkq : ∀ q, par M 0 (r + L) = some q → q ≠ r → k ≠ q := by
      intro q hq hqr hkq; subst hkq; exact hqc k hq hqr c hcCL hcx
    refine ⟨hkq, ?_⟩
    by_cases hsc : T2SeedCol M r L k
    · rcases hsc with hsd | ⟨q, hq, hqr, hkq'⟩
      · obtain ⟨Lc', R', yM, h1, h2, _, h4, _, h6⟩ := hSP k hsd Lc c R hcl hcx
          (fun q hq => by
            by_cases hqr : q = r
            · intro hcq'; subst hcq'
              rcases hsd with ⟨_, hkr⟩ | ⟨q', hq', hq'r, _⟩
              · omega
              · rw [hq] at hq'; cases hq'; exact absurd hqr hq'r
            · exact hcq q hq hqr) s y hsy ht
        exact ⟨Lc', R', yM, h1, h2, h4, h6⟩
      · exact absurd hkq' (hkq q hq hqr)
    · obtain ⟨Lc', R', yM, h1, h2, _, h4, _, h6⟩ :=
        frame_of_shape hC hG hCN hGN (hshape k (by omega) hsc) hcl hsy ht
      exact ⟨Lc', R', yM, h1, h2, h4, h6⟩
  intro c u hp
  induction hp with
  | @top k c Lc R s y hcl hsy ht =>
    intro hcx hcq
    obtain ⟨_, Lc', R', yM, h1, h2, h4, h6⟩ := hframe k Lc c R s y hcl hsy ht hcx hcq
    rw [h2]; exact PathLvAll.top h1 h4 h6
  | @step k c Lc R s y u hcl hsy ht _ ih =>
    intro hcx hcq
    obtain ⟨hkq, Lc', R', yM, h1, _, h4, h6⟩ := hframe k Lc c R s y hcl hsy ht hcx hcq
    have hkc := (mem_children (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).1
    exact PathLvAll.step h1 h4 h6 (ih (by omega) hkq)

/-- **`q ≠ r` counts no child before `x`** in `M[n]`: `x` is the bump child of `q`, so all its children are. -/
theorem q_nocnt_t2 {M : Mat} {r L n : Nat} (hX : SInvX M) (hJ : RowJ M) (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hn : 1 ≤ n) {q : Nat} (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) :
    ∀ c ∈ CL (G2 M r L n) q, ¬ c < r + L := by
  intro c hcCL hcx
  set N := G2 M r L n with hN
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrx := par_lt M 2 _ r hr
  have hqx := par_lt M 0 _ q hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
  have hrq' : r < q := lt_of_le_of_ne hrq.le (Ne.symm hqr)
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨hxb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at hxb
  have htake : N.take (r + L) = M.take (r + L) := gexp_take_x hlen hn
  have hcch : c ∈ children N q := (List.mem_filter.mp hcCL).1
  have hcnt : Counted N q c := by simpa using (List.mem_filter.mp hcCL).2
  have hpc : par N 0 c = some q := (mem_children_iff.mp hcch).2
  have hpcM : par M 0 c = some q := by
    rw [← par_take M (k := r + L) 0 c hcx, ← htake, par_take N 0 c hcx]; exact hpc
  have hcM : c ∈ children M q := mem_children_iff.mpr ⟨by omega, hpcM⟩
  have hxM : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2 : entry M 2 q = 1 := hX.loc.2.2.1 q (r + L) hxM hxb
  have hmax : ∀ e ∈ children M q, e ≤ r + L := fun e he => by have := (mem_children he).2; omega
  have hsplit := split_last_max _ _ (children_sorted M q) hxM hmax
  have hall := all_bump_of_last hX.r0p hX.z2 hX.loc.1 hX.loc.2.1 he2 hsplit hxb c hcM
  apply hcnt.1
  rw [← col_take N hcx, htake, col_take M hcx, hall]
  show bump M q = bump N q
  unfold bump
  rw [← entry_take M 0 (show q < r + L by omega), ← entry_take M 1 (show q < r + L by omega), ← htake,
    entry_take N 0 (show q < r + L by omega), entry_take N 1 (show q < r + L by omega)]

/-- **`T2VRAPre` from `T2SeedPreShape`** (and t2's `T2BelowXRes`). -/
theorem t2VRAPre_of (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hSP : T2SeedPreShape M ρ) : T2VRAPre M ρ := by
  intro r L hlen hr n hn σ hCN hGN k hk hsc u hu
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXAll_of hB M ρ rk hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ r hr; omega
  have hL : M.length - 1 = r + L := by omega
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ :=
    fun m hm τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr
  have hshape : ∀ j, j < r + L → ¬ T2SeedCol M r L j → FrameShape M (G2 M r L n) ρ σ j :=
    fun j hj hsj => (hBS n hn (fun m hm1 _ τ hτ => hG m hm1 τ hτ) σ hCN
      (fun i _ hi => ⟨hGN.ot_o i hi, hGN.ot_v i hi⟩) j hj).2.2.2.1 hsj
  refine pathLvAll_pre_t2 I.cons I.good hCN hGN hshape (hSP r L hlen hr n hn σ hCN hGN)
    (fun q hq hqr => q_nocnt_t2 hX hJ hlen hr (by omega) hq hqr) k u hu hk ?_
  intro q hq hqr hkq
  exact hsc (Or.inr ⟨q, hq, hqr, hkq⟩)

end Ytosk
