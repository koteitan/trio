/-
**t = 2, C2: the frame of `q` from `T2C2Kids` (2026-11-06).**

`C_frameV3` (V3SeedPF) proves `CL_N(q) = [x]` without the C1 condition `un`, and `v_N(x) = v_N(r) + last(v_N(q))`
from the parent and upgrade structure of `x′` in `N`.  With `σ.v r = ρ.v r` (a field of `T2C2Kids`) and
`v_N(q) = qnS` (`vq_eq_gexp`), `v_N(x) = v_N(q)`.  So the C2 residual `T2C2QKids` follows from `T2C2Kids`, and
`hN_of5` takes neither `T2VRASeed` nor `T2VRAPre` as an input.

The C2 seed frames of `q` (QVF for hN, QPF for hSF/hSP) use only these facts, as in C1 (`seed_frames_C3V3`,
`seed_frames_CV3`): `seedFr_q_C2`, `seedFrPF_q_C2`.  The bundles `SeedPFResV3R`, `SeedVFResV3R` keep the C2 seed
frames of `r` only; entry points `hSF_of2`, `hSP_of2`, `hN_of6`.
-/
import Ytosk.V3VRASeedU
import Ytosk.V3T2SmallV3U3

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The frame of `q` in `M[n]`** (`q ≠ r`, any C configuration): its only counted child is `x′ = r + L`, and
`v(x′) = v(r) + last(v(q))` once `v_N(r) = ρ.v r`. -/
theorem C_qframe {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} {rkN : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hvr : σ.v r = ρ.v r) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] ∧
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx0 : r < r + L := par_lt M 2 _ _ hr
  have hA0 : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrq0 : Anc0 M r q := anc0_par hA0 (by have := par_lt M 0 _ _ hq; omega) hq
  obtain ⟨pq, hpq0⟩ := par0_of_anc hrq0 (fun h => hqr h.symm)
  have hrq : r < q := by have := hrq0.le; omega
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  have hpq' := hpq0
  obtain ⟨Txb0, Tqb0, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq'
  have hpq : par M 0 (r + qp) = some r := by
    have he0lt' := anc0_e0_lt hA0 (by omega)
    obtain ⟨he2r', h1lt'⟩ := par2_facts hX.z2 (by omega) hr
    have hqb' : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
      intro i hi; rw [hpq0] at hi; cases hi; exact Tqb0
    exact qn_par0_q hlen (by omega) hA0 hq (d0 := entry M 0 (r + L) - entry M 0 r) (by omega) (le_refl 2)
      (d1 := entry M 1 (r + L) - entry M 1 r) (by omega) he2r' h1lt' hqb'
      (par1_x_r (by omega) I.z2 I.z1 hr) hqr Txb0 hJ hX.r0p I.be
  rw [hpq] at hpq0; cases hpq0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hvq := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb I.be I.uat hUN I.cons I.good hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hvx : σ.v (r + L) = add (ρ.v r) (last (σ.v (r + qp))) := by
    rw [(hCN (r + L) hxN).2]; unfold vRhs
    have he1 : entry N 1 (r + L) ≠ 0 := by
      have := entry1_xN hlen hL0 hA hq hd0e hn hd1e
      rw [← hN] at this; rw [this]; omega
    rw [if_neg he1, if_pos hx2N]
    have hp1 := par1_xN hlen hL0 hA hq hd0e hn hd1e
    rw [hr1, ← hN] at hp1
    have hu := upg_N_x_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb hJ hX.r0p I.be
    rw [← hN] at hu
    rw [hp1, hu]
    show sf (add (σ.v r) (last (σ.v (r + qp)))) = _
    rw [hvr, sf_ot (isOT_add hVot (isOT_last hvq.1))]
  exact ⟨hCLNq, hvx⟩

/-- **`T2C2QKids` from `T2C2Kids`** (C2). -/
theorem t2C2QKids_of_kids {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hK : T2C2Kids M ρ r L q) : T2C2QKids M r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  intro n hn σ hCN hGN
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  rw [hexp n] at hRN
  have hvr := (hK n hn σ hCN hGN).2.1
  obtain ⟨hCLq, hvx⟩ := C_qframe hM hS I hz h2 hlen hr hq hqr hn hCN hRN hvr
  have hvq : σ.v q = qnS M ρ r L q := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  refine ⟨hCLq, ?_⟩
  rw [hvx, hvq, qnS_vxs]

#print axioms t2C2QKids_of_kids

/-- **C2: the seed frame of `q`** (VSmallF, FrameOT, FrameClosed) from `T2C2Kids`: its only frame is `x′` with
`v(x′) = v(q) = qnS`, as in the C1 proof (`seed_frames_C3V3`). -/
theorem seedFr_q_C2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hK : T2C2Kids M ρ r L q) : SeedFr QVF M r L q := by
  have hqC := t2C2QKids_of_kids hM hS I hz h2 hlen hr hq hqr hK
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hrM : r < M.length := by omega
  have hs'ot : isOT (qnS M ρ r L q) = true := qnS_ot I hrM L q
  intro n hn _ σ hCN hGN Lc c R hcl
  obtain ⟨hCLq, hvxq⟩ := hqC n hn σ hCN hGN
  have hvq : σ.v q = qnS M ρ r L q := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hxN : r + L < (G2 M r L n).length := by
    rw [TRIO.gexp_length hlen]
    have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
    omega
  have hc : Lc = [] ∧ c = r + L := by
    rw [hCLq] at hcl
    rcases Lc with _ | ⟨a, l⟩
    · simp at hcl; exact ⟨rfl, hcl.1.symm⟩
    · simp at hcl
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
  rw [sf_ot (hGN.ot_v _ hxN), hvxq, hvq] at hy0
  refine ⟨?_, hGN.ot_o _ hxN, ?_⟩
  · show QVSF (σ.v q) ([] : List T) (σ.o (r + L))
    rw [hy0, hvq]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    rw [comps_eq_nil_of_lev (fun q hq => lev_lt_of_summand hs'ot hq)] at hg; simp at hg
  · show QFC (σ.v q) ([] : List T) (σ.o (r + L))
    rw [hy0, hvq]
    intro s y hsy _
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    exact frameDom_self (fun u _ => by rw [spArg_nil]; rfl)

#print axioms seedFr_q_C2

/-- **C2: the PH/FC3 seed frame of `q`** from `T2C2Kids`, as in the C1 proof (`seed_frames_CV3`). -/
theorem seedFrPF_q_C2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hK : T2C2Kids M ρ r L q) : SeedFr QPF M r L q := by
  have hqC := t2C2QKids_of_kids hM hS I hz h2 hlen hr hq hqr hK
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hVs' : ρ.v r < qnS M ρ r L q := qnS_gt M ρ r L q
  intro n hn _ σ hCN hGN Lc c R hcl
  obtain ⟨hCLq, hvxq⟩ := hqC n hn σ hCN hGN
  have hvq : σ.v q = qnS M ρ r L q := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hxN : r + L < (G2 M r L n).length := by
    rw [TRIO.gexp_length hlen]
    have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
    omega
  have hc : Lc = [] ∧ c = r + L := by
    rw [hCLq] at hcl
    rcases Lc with _ | ⟨a, l⟩
    · simp at hcl; exact ⟨rfl, hcl.1.symm⟩
    · simp at hcl
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
  rw [sf_ot (hGN.ot_v _ hxN), hvxq, hvq] at hy0
  refine ⟨fun s y c0 _ _ hB => absurd (spArg_nil _) (by simpa using hB), fun s y c0 hc _ _ _ => ?_⟩
  rw [hy0] at hc
  simp only [psi.injEq] at hc
  obtain ⟨rfl, _, _⟩ := hc
  rw [hvq]
  exact ⟨fun _ => ⟨ne_of_gt (lt_of_le_of_lt (z_le (ρ.v r)) hVs'), qnS_last_ne_one I r L q⟩, fun h => absurd rfl h⟩

#print axioms seedFrPF_q_C2

/-- The C2 residual `T2C2Kids` at every C2 configuration of `M`. -/
def C2Kids (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2Kids M ρ r L q

/-- `SeedPFResV3` with the C2 seed frames of `r` only (those of `q` follow from `T2C2Kids`). -/
structure SeedPFResV3R (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRRel M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → SVRel M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → QNRel M ρ r L q Lc
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRel M ρ r L q ∧ T2SeedCBig M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (h : SeedPFResV3R M ρ) (hK : C2Kids M ρ) : SeedPFResV3 M ρ :=
  ⟨h.qr, h.sv, h.qn, h.C1, fun r L q k hlen hr hq hqr hcl hu i hi => by
    rcases hi with rfl | rfl
    · exact h.C2r _ L q k hlen hr hq hqr hcl hu
    · exact seedFrPF_q_C2 hM hS I hz h2 hlen hr hq hqr (hK r L _ k hlen hr hq hqr hcl hu)⟩

/-- `SeedVFResV3` with the C2 seed frames of `r` only. -/
structure SeedVFResV3R (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDom M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (h : SeedVFResV3R M ρ) (hK : C2Kids M ρ) : SeedVFResV3 M ρ :=
  ⟨seedPFResV3_of hM hS I hz h2 h.pf hK, h.qnDom, h.cDom, fun r L q k hlen hr hq hqr hcl hu i hi => by
    rcases hi with rfl | rfl
    · exact h.C2r _ L q k hlen hr hq hqr hcl hu
    · exact seedFr_q_C2 hM hS I hz h2 hlen hr hq hqr (hK r L _ k hlen hr hq hqr hcl hu)⟩

/-- **The inputs hSF and hSP** with the C2 seed frames of `q` proved. -/
theorem hSF_of2 (hRes : T2AtV3 (fun M ρ => SeedPFResV3R M ρ)) (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2F M) :=
  hSF_of (fun M ρ rk C hz h2 => seedPFResV3_of C.std C.ne (coreW C.S C.I) hz h2 (hRes M ρ rk C hz h2)
    (hK M ρ rk C hz h2)) hC2

theorem hSP_of2 (hRes : T2AtV3 (fun M ρ => SeedPFResV3R M ρ)) (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2P M) :=
  hSP_of (fun M ρ rk C hz h2 => seedPFResV3_of C.std C.ne (coreW C.S C.I) hz h2 (hRes M ρ rk C hz h2)
    (hK M ρ rk C hz h2)) hC2

/-- **The input hN** without `T2VRASeed` and `T2VRAPre`: they come from `SeedPFResV3`, `T2C2Kids`, `T2VRAQNDom` and
`T2VRASeedC` (`hPre_of`, `t2VRASeed_ofV3`, `t2C2QKids_of_kids`). -/
theorem hN_of5 (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3 M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hK : T2AtV3 (fun M ρ => ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k →
      T2C2Kids M ρ r L q))
    (hQN : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M)) :
    T2SmallV3 := by
  have hPre : T2AtV3 (fun M ρ => T2VRAPre M ρ) := hPre_of hBXU (fun M ρ rk C hz h2 => (hVF M ρ rk C hz h2).pf) hK
  have hSeed : T2AtV3 (fun M _ => T2VRASeed M) := by
    intro M ρ rk C hz h2
    have I : Inv3W M ρ rk := coreW C.S C.I
    exact t2VRASeed_ofV3 (hBXU M ρ rk C hz h2) C.std C.ne I C hz h2 C.I.vra (hVF M ρ rk C hz h2).pf
      (hPre M ρ rk C hz h2) (hQN M ρ rk C hz h2) (hC M ρ rk C hz h2)
      (fun r L q k hlen hr hq hqr hcl hu =>
        t2C2QKids_of_kids C.std C.ne I hz h2 hlen hr hq hqr (hK M ρ rk C hz h2 r L q k hlen hr hq hqr hcl hu))
  exact hN_of4 hBXU hVF hFD hSeed hPre hCopy hVD hAG

#print axioms hN_of5

/-- **The input hN** with the C2 seed frames of `q` proved: residuals `SeedVFResV3R` (C2 only at `r`) and
`C2Kids`. -/
theorem hN_of6 (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3R M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hQN : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M)) :
    T2SmallV3 :=
  hN_of5 hBXU (fun M ρ rk C hz h2 => seedVFResV3_of C.std C.ne (coreW C.S C.I) hz h2 (hVF M ρ rk C hz h2)
    (hK M ρ rk C hz h2)) hFD hK hQN hC hCopy hVD hAG

#print axioms hSF_of2
#print axioms hSP_of2
#print axioms hN_of6

end Ytosk.V3Main.SeedPF
