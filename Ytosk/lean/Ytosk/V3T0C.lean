/-
**3 行・t = 0: 偽の欄を含む旧 Inv3 を使わない形（2026-10-16、t0）。**

t = 0 の組み立てに使う旧 Inv3 の欄は、構造の欄と Cons・Good3・Rk・VSmallF・FrameClosed・FrameOT・
BumpKidsDec・BumpTermDec・rootS・rootP だけ。これを `Inv3C`、Res3A の drop・abS を `Res3C` にまとめ、
旧の証明（std_gexp_t0C・t0_shape3C・t0IVResC_holds・t0VSD_atC・t0_vsmallF_atC）をこの束で写した。
証明の中身は旧と同じ（型だけ替えた）。Inv3 からも Inv3V2 ＋ SInv からもこの束が作れる。
-/
import Ytosk.V3T0TopU
import Ytosk.V3T0Sh3
import Ytosk.V3ExpT0H

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The core of `Inv3`** used by the `t = 0` engine: the structural fields and the value fields that are
true on standard matrices. -/
structure Inv3C (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  r0p : R0P M
  z2 : Z2 M
  sd : SibDec M
  z1 : Z1C M
  uat : UAT M
  uab : UAB M
  r12 : R12 M
  be : BumpE2 M
  r01 : R01 M
  e00 : entry M 0 0 = 0
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- The part of `Res3A` used by the `t = 0` engine (no `seed`). -/
structure Res3C (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  abS : AbsSR M ρ

theorem Inv3.toC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) : Inv3C M ρ rk :=
  ⟨I.r0p, I.z2, I.sd, I.z1, I.uat, I.uab, I.r12, I.be, I.r01, I.e00, I.cons, I.good, I.rank, I.vs, I.fc,
    I.fo, I.kd, I.td, I.rootS, I.rootP⟩

theorem Res3A.toC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (R : Res3A M ρ rk) : Res3C M ρ rk :=
  ⟨R.drop, R.abS⟩

/-- `T0Ctx` with the core bundles (the prefix slot is not used by the engine and is left `True`). -/
def T0CtxC (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat) (σ : Valn)
    (rkN : Bool → Nat → Nat) : Prop :=
  Std M ∧ M ≠ SRO ∧ Inv3C M ρ rk ∧ Res3C M ρ rk ∧ r + L + 1 = M.length ∧ 0 < L ∧
    par M 0 (r + L) = some r ∧ entry M 1 (r + L) = 0 ∧ True ∧
    2 ≤ n ∧ Cons (TRIO.gexp M r L 0 0 n) σ ∧ Rk (TRIO.gexp M r L 0 0 n) rkN ∧
    Good3 (TRIO.gexp M r L 0 0 n) σ ∧ FrameOT (TRIO.gexp M r L 0 0 n) σ ∧
    FrameClosed (TRIO.gexp M r L 0 0 n) σ ∧
    BumpKidsDec (TRIO.gexp M r L 0 0 n) σ ∧ BumpTermDec (TRIO.gexp M r L 0 0 n) σ

/-- **(iv)** with the core bundles. -/
def T0IVResC : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3C M ρ rk →
    Res3C M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true)

theorem std_gexp_t0C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (I : Inv3C M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    (n : Nat) : Std (TRIO.gexp M r L 0 0 n) := by
  have he2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hx : M.length - 1 = r + L := by omega
  have he0 : entry M 0 (r + L) ≠ 0 := by have := I.r0p _ _ hp; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨h0, _, _⟩
    rw [← entry_eq, hx] at h0; exact he0 h0
  have hs0 : TRIO.srow M (M.length - 1) = 0 := by
    unfold TRIO.srow
    rw [← entry_eq, ← entry_eq, hx, he1, he2]; rfl
  have he := expand_eq_gexp_t0 M n (by omega) hzT (by rw [hs0, hx]; exact hp) hs0
  rw [show M.length - 1 - r = L by omega] at he
  rw [← he]; exact Std.exp n hM


/-- **`T0Shape` (iii)**: a changed subscript of `o′(r)` in `M.take x` stays at least `Ω_{v(g)+1}`. -/
theorem t0_shape3C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3C M ρ rk) (R : Res3C M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) :
    ∀ g, par M 0 r = some g → ∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z := by
  intro g hg s' y' hs hne hhi
  obtain ⟨hSX, hJ⟩ := sInvXJ_std hM hS
  have hBL : BumpLeaf M := hSX.loc.2.2.2
  have hx : r + L + 1 = M.length := hlen
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hDr hC1 hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hgr : g < r := par_lt M 0 r g hg
  have hrM : r < M.length := by omega
  have hs' : s' = ρ'.v r := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hVT.g.ot_v r hrT)]
  have hCv : ChgX M (r + L) false r := by
    by_contra hn'; apply hne; rw [hs']; exact (hoff r (by omega)).2 hn'
  rw [lt_theta_iff] at hhi ⊢
  have hAgr : Anc0 M g r := Anc0.step hg (Anc0.refl g)
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  by_cases hP : par M 1 r = some g
  · -- `s′ = v′(r) > v′(g) = v(g)`
    have hng : ¬ ChgX M (r + L) false g := fun h =>
      (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab h).1 rfl (by omega) |>.2.2 r (by omega) hP
    have hvg : ρ'.v g = ρ.v g := (hoff g (by omega)).2 hng
    have h1r : entry (M.take (r + L)) 1 r ≠ 0 := by
      rw [entry_take M 1 (by omega)]; have := par1_entry_lt hP; omega
    have hPT : par (M.take (r + L)) 1 r = some g := by rw [par_take M 1 r (by omega)]; exact hP
    have hlt := v_par1_lt hC1 hVT.g hRk1 (rk false r) r g (le_refl _) hrT h1r hPT
    rw [hs', ← hvg]
    exact not_le.mpr hlt
  · exfalso
    apply hhi
    rcases chgX_false_cases hCv rfl with ⟨hrx, hup⟩ | ⟨h1, _, hcb⟩ | ⟨m, hm, hcm⟩ | ⟨k, hu, hck⟩ |
        ⟨j, h1, h2, hj, hjb⟩
    · -- `r = x − 1` lost its upgrade: the target is an ancestor `k`, and `v(r) = v(k) ≤ v(g)`
      have hL1 : L = 1 := by omega
      rw [← hrx] at hup
      obtain ⟨k, hu⟩ := Option.ne_none_iff_exists'.mp hup
      obtain ⟨m, hm1, _, hek, hcase⟩ := t0s_upg_facts hu
      have h12 := upg_e12 hu
      have h20 : entry M 2 r = 0 := by have := I.z2 r; omega
      rcases hcase with hk1 | ⟨hkA, hkr⟩
      · exfalso
        rw [hk1, show r + 1 = r + L by omega, he1] at hek
        exact h12.1 hek.symm
      · have hkg : Anc0 M k g := anc0_par hkA (by omega) hg
        have hsp := (upg_anc_spine I.r0p I.z2 I.uab I.be hJ I.cons I.good I.rank hrM hu hkA hkr g hkg hAgr
          (by omega)).2
        have hv := v_upg_eq I.cons hrM h12.1 h20 hu
          (by rw [hm1]; exact I.good.ot_v m (by have := par_lt M 1 r m hm1; omega))
          (fun j _ _ k' hk' => I.good.ot_o k' (mem_children hk').2)
        rw [hv]; exact hsp
    · -- `x` is not a bump child of `r` (its row 1 is `0`)
      have := e1_of_col hcb
      rw [he1] at this; exact absurd this.symm h1
    · -- `v(P_1 r)` does not change (`TopC`)
      have hmr := par_lt M 1 r m hm
      exact absurd hm ((chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hcm).1 rfl (by omega) |>.2.2 r
        (by omega))
    · -- an upgrade of `r` with a changed target: impossible
      obtain ⟨_, _, _, _, hcase⟩ := t0s_upg_facts hu
      rcases hcase with hk1 | ⟨hkA, hkr⟩
      · subst hk1
        have := leaf_of_upg_next I.r0p hu (r + L) (Anc0.step hp (Anc0.refl r))
        omega
      · exact absurd (no_anc_upg hx I.r0p I.z2 I.sd I.z1 I.uat I.uab
          ((chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hck).1 rfl (by omega)) (by omega) hu hkA hkr)
          (fun h => h)
    · -- a bump child of `r`: then `r` is the bump child of `g`, against `BumpLeaf`
      have hge : entry M 1 r ≤ entry M 1 g := by
        by_contra hlt
        exact hP (par1_of_child hg (by omega))
      have hle := hJ r g h2 hg
      have hr2 : entry M 2 r = 1 := by have := I.z2 r; omega
      have hcolr : col M r = bump M g := by
        rw [col_eq_entries, I.r0p r g hg, hr2]
        unfold bump; congr 2; omega
      have hrc : r ∈ children M g := mem_children_iff.mpr ⟨hrM, hg⟩
      have hje1 : entry M 1 j = entry M 1 r := e1_of_col hjb
      have hje2 : entry M 2 j = 1 := e2_of_col hjb
      have := (hBL g r j hrc hcolr hj (by omega)).1
      omega


/-- **`T0IVResC` holds.** -/
theorem t0IVResC_holds : T0IVResC := by
  intro M ρ rk r L hM hS I R hlen hL hp he1 n hn2 g hg hcnt hno Lc0 hCL s y hy
  have hn : 1 ≤ n := by omega
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hgr : g < r := par_lt M 0 r g hg
  -- `r` is not counted at `g` in `N`
  have h0 := hno 0 (by omega)
  rw [Nat.zero_mul, Nat.add_zero] at h0
  have hUT : isUpg (TRIO.gexp M r L 0 0 n) r = true ∧ topped (TRIO.gexp M r L 0 0 n) r = true := by
    by_contra hne
    apply h0
    refine ⟨?_, hne⟩
    rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
    exact hcnt.1
  have hTT : topped (M.take (r + L)) r = true := by
    have h := topped_copy0 hlen hL hp hn (k := 0) (q := 0) (by omega) hL
    simp only [Nat.zero_mul, Nat.add_zero] at h
    rw [← h]; exact hUT.2
  -- the upgrade to `r` comes from `r − 1`
  have hSN : SInv (TRIO.gexp M r L 0 0 n) :=
    sInv_std (std_gexp_t0C hM I hlen hL hp he1 n) (ne_SRO_of_rk (rk_N0 hlen hL hp hn I.r0p I.z2 hx2 hn2 I.rank))
  have hU := hUT.1
  unfold isUpg at hU
  obtain ⟨j, _, hju⟩ := List.any_eq_true.mp hU
  have hju' : upg (TRIO.gexp M r L 0 0 n) j = some r := by simpa using hju
  have hj1 : j + 1 = r := by
    by_contra hne
    have := hSN.uat j r hju' (fun h => hne h.symm)
    rw [hUT.2] at this; exact absurd this (by simp)
  have hr0 : 0 < r := by omega
  have huM : upg M (r - 1) = some r := by
    rw [← upg_pre0 hlen hL hp hn (show r - 1 + 1 < r + L by omega), show r - 1 = j by omega]; exact hju'
  -- an earlier counted child of `g`: the state is nonzero
  obtain ⟨c, hcM, hcr, hcc⟩ := cnt_before_next_upg I.r0p I.z2 I.sd I.uat r hr0 huM g hg
  have hcLc : c ∈ Lc0 := by
    have hcCL : c ∈ CL M g := by
      unfold CL; exact List.mem_filter.mpr ⟨hcM, by simpa using hcc⟩
    rw [hCL] at hcCL
    rcases List.mem_append.mp hcCL with h | h
    · exact h
    · simp at h; omega
  have hgM : g < M.length := by omega
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hgM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hLs := sumN_dec (Lc0.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  have hB : spArg (ρ.v g) z (sumN (Lc0.map ρ.o)) ≠ z := by
    apply spArg_ne_z
    right
    intro hz
    have h := hLs.2
    rw [hz] at h
    have hmem : ρ.o c ∈ Lc0.map ρ.o := List.mem_map_of_mem hcLc
    rw [← h] at hmem
    simp [summands] at hmem
  -- the counted children of `r` in `M`: only `x`
  have he2r : entry M 2 r = 1 := by have := upg_target_e2 huM; have := I.z2 r; omega
  have hrL : r < r + L := by omega
  have hbT : ∀ d ∈ children (M.take (r + L)) r, col M d = bump M r := by
    intro d hd
    unfold topped at hTT
    cases hl : (children (M.take (r + L)) r).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hd; simp at hd
    | some ℓ =>
      rw [hl] at hTT
      simp only [decide_eq_true_eq] at hTT
      have hlast : children (M.take (r + L)) r = (children (M.take (r + L)) r).dropLast ++ [ℓ] := by
        rw [List.dropLast_append_getLast? _ hl]
      have hall := all_bump_of_last (R0P_take I.r0p (r + L)) (Z2_take I.z2 (r + L)) (SibDec_take I.sd (r + L))
        (Z1C_take I.z1 (r + L)) (by rw [entry_take M 2 hrL]; exact he2r) hlast hTT d hd
      have hdx := (mem_children_take hd).1
      rwa [col_take M hdx, bump_take M hrL] at hall
  have hCLr : CL M r = [] ++ [r + L] := by
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    have hsplit := split_last_max _ _ (children_sorted M r) hxr
      (fun d hd => by have := (mem_children hd).2; omega)
    unfold CL
    rw [hsplit, List.filter_append]
    have hxc : Counted M r (r + L) := by
      refine ⟨fun h => ?_, fun h => by rw [isUpg_x0 hlen hL hp hx2] at h; exact absurd h.1 (by simp)⟩
      have := congrArg (fun t => t.2.2) h
      simp [col_eq_entries, bump] at this; omega
    rw [List.filter_eq_nil_iff.mpr]
    · simp [hxc]
    · intro d hd hcd
      rw [List.mem_filter] at hd
      have hdx : d < r + L := by simpa using hd.2
      have hdT : d ∈ children (M.take (r + L)) r := by
        rw [children_take, List.mem_filter]; exact ⟨hd.1, by simpa using hdx⟩
      exact (of_decide_eq_true hcd).1 (hbT d hdT)
  have hrM : r < M.length := by omega
  have hox := o_x_one0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.cons I.good
  have hsMr : ∀ d ∈ CL M r, Single (ρ.o d) := fun d hd => single_o I.cons I.good
    (mem_children (cl_mem_children hd)).2
  have hor := o_last_form I.cons hrM (I.good.ot_v r hrM) hCLr hsMr (cl_vals I.cons I.good hrM).2
    (show ρ.o (r + L) = psi z z z from hox)
  have hst : step (ρ.v r) (spArg (ρ.v r) z (sumN (([] : List Nat).map ρ.o))) z z z = one := by
    show step (ρ.v r) z z z z = one
    unfold step; rw [if_neg (fun h => T.not_lt_z _ h.1)]; rfl
  rw [hst] at hor
  rw [hor] at hy
  simp only [psi.injEq] at hy
  rw [← hy.2.1]
  rintro ⟨h1, _⟩
  exact hB (lt_one_iff.mp h1)



/-- **The `D` part of `VSmallF` of `N = M[n]`** at one matrix (`T0VSResD` for this `M`), from `T0DF`: a counted
child `c` whose `v` changes is the last counted child, has no counted child (`o = Ω_v`), and `v′(c) ◁ v(c)`
(`vs_changed_bound`). -/
theorem t0VSD_atC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hDF : T0DFH M ρ) :
    ∀ r L n σ rkN, T0CtxC M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  intro r L n σ rkN hctx i Lc c R hi hc hCL hv
  obtain ⟨hM, hS, I, _, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hdv : DepX M (r + L) false c := by
    by_contra hd
    apply hv
    rw [(hvD c (by rw [hlN]; omega)).2 (fun h' => hd h'.2), tau_v_lt hc]
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hlv : Lhd z (σ.v c) (ρ.v c) := ((hDF r L hlen hL hp he1 n hn2 σ hCN c hc).2 hdv).2
  have hvcot : isOT (σ.v c) = true := hGN.ot_v c hcN
  have hiM : i < M.length := by omega
  have hcM : c < M.length := by omega
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hclc : CL M c = [] := cl_nil_of_depv' hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2
    I.cons I.good hc hdv
  have hoM : ρ.o c = psi (ρ.v c) z z := o_of_no_counted I.cons hcM (I.good.ot_v c hcM) (no_cnt_of_cl_nil hclc)
  -- `c` is the last counted child of `i`
  have hDi : DepX M (r + L) true i := DepX.ochild hcch hccnt.1 hccnt.2 (DepX.ov hdv)
  have hR : R = [] := by
    rcases hOS_t1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp i (by omega) hDi with
      ⟨_, hall⟩ | ⟨_, Lp, c0, Rch, hch, _, _, hRch, hLnd⟩
    · exfalso
      rcases hall c hcch with h | h
      · exact hccnt.1 h
      · exact hccnt.2 h
    have hcc0 : c = c0 := by
      have hc' := hcch
      rw [hch] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact absurd (DepX.ov hdv) (hLnd c h hccnt)
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exfalso
          rcases hRch c h with h' | h'
          · exact hccnt.1 h'
          · exact hccnt.2 h'
    subst hcc0
    obtain ⟨hLs, _⟩ := sib_order (children_sorted M i) hch
    have hsCL : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ (children_sorted M i)
    rw [hCL] at hsCL
    obtain ⟨_, hcR⟩ := sib_order hsCL rfl
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdch : d ∈ children M i := cl_mem_children hdCL
    have hdcnt : Counted M i d := by unfold CL at hdCL; simpa using (List.mem_filter.mp hdCL).2
    have hcd := hcR d hd
    rw [hch] at hdch
    rcases List.mem_append.mp hdch with h | h
    · have := hLs d h; omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · rcases hRch d h with h' | h'
        · exact hdcnt.1 h'
        · exact hdcnt.2 h'
  subst hR
  -- the old frame of `i`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hiM
  have hsMc : ∀ d ∈ CL M i, Single (ρ.o d) := fun d hd => single_o I.cons I.good
    (mem_children (cl_mem_children hd)).2
  have hformM := o_last_form I.cons hiM (I.good.ot_v i hiM) hCL hsMc hpM hoM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  have hpL := List.pairwise_append.mp hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) hpL.1
  have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), psi (ρ.v c) z z ≤ q := by
    apply spArg_summands_ge ⟨ρ.v c, z, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq
      have := hpL.2.2 q hq (ρ.o c) (by simp)
      rwa [hoM] at this
    · simp [summands]
  have hot := I.good.ot_o i hiM
  rw [hformM] at hot
  exact vs_changed_bound hvcot hlv hBc (I.vs i hiM Lc c [] hCL) hot

/-- **`VSmallF` of `N = M[n]`** (`t = 0`) at one matrix, from the `D` part `hD` (for this `M`) and `T0VSResG`. -/
theorem t0_vsmallF_atC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hD : ∀ r L n σ rkN, T0CtxC M ρ rk r L n σ rkN →
      ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
        ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hIV : T0IVResC) :
    ∀ r L n σ rkN, T0CtxC M ρ rk r L n σ rkN → VSmallF (TRIO.gexp M r L 0 0 n) σ := by
  intro r L n σ rkN hctx
  obtain ⟨hM, hS, I, R, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hDr hC1 hRk1
  have hdrop := drop_all hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hDr.vst
    I.fc I.fo hDr.argT
    (bump_drop hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hDr.ab hDr.ws)
    hDr.ua
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => ⟨(hvC i hiN).1 (fun h => by omega), (hvC i hiN).2 (fun h => by omega)⟩
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good
  have hFO := qvs_of_vsmallF I.cons I.good I.vs
  have hFOT := qvs_of_vsmallF hC1 hVT.g hVT.vs
  apply vsmallF_of_qvs hCN hGN
  apply frameQ_N_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
    (ρ' := ρ') hFO hFOT hσB hoffD
  · -- the frame of `g` with `r` counted
    intro g hg hgc
    have hgr : g < r := par_lt M 0 r g hg
    have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := by
      apply (hoffD g hgr).2
      intro hdv
      exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
        (by omega) hdv hrg hgc
    apply g_frames_t0J hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
      hg hgc (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast
      (counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hgc)
      (fun Lc c R hCL => hFO g (by omega) Lc c R hCL)
    intro Lc j cv hCL hcv s y hsy g' hg'
    -- the state grows with the middle copies
    have hgM : g < M.length := by omega
    obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hgM
    rw [hCL] at hsM hpM
    simp only [List.map_append, List.map_singleton] at hsM hpM
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hsO : Single (omid M r L ρ) :=
      ⟨isOT_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN,
        by rw [hom]; exact ⟨_, _, rfl⟩⟩
    have hmono : spArg (ρ.v g) z (sumN (Lc.map ρ.o)) ≤
        spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      have hs : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), Single t := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hsM t (List.mem_append_left _ ht)
        · rw [(List.mem_replicate.mp ht).2]; exact hsO
      have hpw : (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := by
        have hp1 := List.pairwise_append.mp hpM
        refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
        intro a ha b hb
        rw [(List.mem_replicate.mp hb).2]
        exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
      rw [sumN_append_dec hs hpw, spArg_app]
      apply le_spArg
      exact isOT_sumN _ (fun t ht => (hs t (List.mem_append_right _ ht)).1)
    have hold : ∀ g'' ∈ comps (ρ.v g) (ρ.v r), g'' ≤ psi (ρ.v r) z z ∨
        g'' ≤ spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      intro g'' hg''
      rcases I.vs g hgM Lc r [] hCL g'' hg'' with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans h hmono)
    rcases hcv with rfl | ⟨rfl, hj0⟩
    · rw [hom] at hsy; simp only [psi.injEq] at hsy
      rw [← hsy.1] at hg' ⊢
      exact hold g' hg'
    · have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
      obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
      rw [hsy] at hy0; simp only [psi.injEq] at hy0
      have hv'ot := hVT.g.ot_v r hrT
      rw [sf_ot hv'ot] at hy0
      rw [hy0.1] at hg' ⊢
      by_cases hv : ρ'.v r = ρ.v r
      · rw [hv] at hg' ⊢; exact hold g' hg'
      -- the drop at `r`: `x` is a counted child of `r`, so `v′(r) ◁ v(r)`
      obtain ⟨hPO, hPV⟩ := hdrop r (by omega)
      have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
      have hxcnt : Counted M r (r + L) := by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have h2 : entry M 2 (r + L) = (bump M r).2.2 := by
            show (col M (r + L)).2.2 = _; rw [h]
          rw [hx2] at h2; simp [bump] at h2
        · obtain ⟨hu, _⟩ := h
          unfold isUpg at hu
          obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
          have hk' : upg M k = some (r + L) := by simpa using hk
          obtain ⟨m, _, _, hcol, _⟩ := upg_spec hk'
          have := e2_of_col hcol
          rw [hx2] at this; omega
      have hlv : Lhd z (ρ'.v r) (ρ.v r) := by
        rcases hPV.1 with h | ⟨_, _, hno⟩
        · rcases h with h | h
          · exact absurd h hv
          · exact h
        · exact absurd hxcnt (hno _ hxr)
      -- a changed `v(r)`: `o′(r) = ψ_{v′(r)}(0)`
      have hyz : y = z := by
        have hCv : ChgX M (r + L) false r := by
          by_contra hn'; exact hv ((hoff r (by omega)).2 hn')
        have hT := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hCv).1 rfl (by omega)
        have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
        rw [hsy, hy0.1] at ho; simp only [psi.injEq] at ho; exact ho.2.1
      obtain ⟨d, hd, hgd⟩ := hlv.2 (ρ.v g) (ρ.v r) hlv.1 (le_refl _) g' hg'
      rcases List.mem_append.mp hd with hd | hd
      swap
      · simp [Gc, comps] at hd
        rw [hd] at hgd
        exact Or.inr (le_trans hgd (z_le _))
      rcases I.vs g hgM Lc r [] hCL d hd with hdo | hdB
      swap
      · exact Or.inr (le_trans hgd (le_trans hdB hmono))
      set Bg := spArg (ρ.v g) z (sumN (Lc.map ρ.o)) with hBg
      by_cases hB0 : Bg = z ∧ j = 0
      · -- no middle copy root counts: the old frame does not rewrite at `r` (`T0IVResC`), and `o′(r) ◁ o(r)`
        obtain ⟨Y0, hY0⟩ : ∃ Y0, ρ.o r = psi (ρ.v r) (app Y0 one) z := ⟨_, hor⟩
        have hnt := hIV M ρ rk r L hM hS I R hlen hL hp he1 n hn2 g hg hgc (hj0 hB0.2) Lc hCL _ _ hY0
        have hsMc : ∀ d ∈ CL M g, Single (ρ.o d) := fun d hd => single_o I.cons I.good
          (mem_children (cl_mem_children hd)).2
        have hformM := o_last_form I.cons hgM (I.good.ot_v g hgM) hCL hsMc
          (by have := (cl_vals I.cons I.good hgM).2; exact this) hY0
        have hot := I.good.ot_o g hgM
        rw [hformM] at hot
        unfold step at hot
        rw [if_neg (by rw [← hBg, hB0.1]; rw [← hBg, hB0.1] at hnt; exact hnt)] at hot
        rw [← hBg, hB0.1] at hot
        have hot2 : isOT (psi (ρ.v g) (psi (ρ.v r) (app Y0 one) z) z) := hot
        rw [← hY0] at hot2
        have hl0 : LhdE (ρ'.o r) (ρ.o r) := by
          rcases hPO.1 with h | ⟨_, w, hw⟩
          · exact h
          · rw [hY0] at hw; simp only [psi.injEq] at hw
            exact absurd hw.2.1 (fun h => by cases Y0 <;> simp [app, one] at h)
        have hot' := ot_parent_lhd hot2 (single_o hC1 hVT.g hrT).1 hl0
        rw [hsy, hy0.1, hyz] at hot'
        by_cases hsa : ρ'.v r < ρ.v g
        · rw [comps_nil_of_lt hv'ot hsa] at hg'; simp at hg'
        · left
          apply le_of_lt
          apply ((isOT_psi_iff).mp hot').2.2.2.2 g'
          rw [comps_psi_z_of_ge hsa]
          simp [hg']
      · -- the state of `N` is at least `Ω_{v(r)}`
        right
        refine le_trans hgd (le_trans hdo ?_)
        have hs : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), Single t := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hsM t (List.mem_append_left _ ht)
          · rw [(List.mem_replicate.mp ht).2]; exact hsO
        have hpw : (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := by
          have hp1 := List.pairwise_append.mp hpM
          refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
          intro a ha b hb
          rw [(List.mem_replicate.mp hb).2]
          exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
        have hsd := sumN_dec _ hs hpw
        have hge : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), psi (ρ.v r) z z ≤ t := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · have := (List.pairwise_append.mp hpM).2.2 t ht (ρ.o r) (by simp)
            refine le_trans ?_ this
            rw [hor]; exact psi_le_psi_arg (z_le _)
          · rw [(List.mem_replicate.mp ht).2, hom]; exact psi_le_psi_arg (z_le _)
        have hne : Lc.map ρ.o ++ List.replicate j (omid M r L ρ) ≠ [] := by
          intro he
          apply hB0
          rw [List.append_eq_nil_iff, List.map_eq_nil_iff, List.replicate_eq_nil_iff] at he
          refine ⟨?_, he.2⟩
          rw [hBg, he.1]; rfl
        apply le_of_summands_ge
        · apply spArg_ne_z
          right
          intro hz
          have h1 := hsd.2
          rw [hz] at h1
          simp [summands] at h1
          exact hne (by simp [h1.1, h1.2])
        · apply spArg_summands_ge ⟨ρ.v r, z, rfl⟩ _ z hsd.1
          · rw [hsd.2]; exact hge
          · simp [summands]
  · -- the `D` frames before `r`
    intro i hi hng Lc c R hCL hDc s y hsy g' hg'
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcM : c ∈ children M i := cl_mem_children hcCL
    have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
    have hcr : c < r := by
      by_cases hig : par M 0 r = some i
      · have hle := children_g_le hlen hL hp hig hcM
        rcases Nat.lt_or_ge c r with h | h
        · exact h
        · exfalso; have : c = r := by omega
          rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hi hig hcM
    have hcN : c < N.length := by rw [hlN]; omega
    have he := o_cl_eq hCN hGN hcN
    rw [hsy] at he; simp only [psi.injEq] at he
    rw [he.1] at hg' ⊢
    by_cases hv : σ.v c = ρ.v c
    · rw [hv] at hg' ⊢
      exact I.vs i (by omega) Lc c R hCL g' hg'
    · exact hD r L n σ rkN hctx i Lc c R hi hcr hCL hv g' hg'


end Ytosk
