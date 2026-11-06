/-
**t = 2, q ≠ r: the counted children before `x` away from `r` and `q` (2026-11-06).**

For `i < x` with `i ≠ r`, `i ≠ q`, the children of `i` in `N = M[n]` are those in `M`, none of them is `q` (whose
parent is `r`) or `x` (whose parent is `q`), and they count alike (`counted_NQ`), so `CL_N(i) = CL_M(i)` (`C_cl_eq`).
In C2, if the last counted child `c₀` of `r` has no counted children, `o_N(c₀) = ψ_v(0)` and the last field of
`T2C2Kids3` holds; `C2Kids4` keeps the earlier children and the case `CL_M(c₀) ≠ []`.
-/
import Ytosk.V3CanonLeaf

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem C_cl_eq {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {n : Nat} (hn : 2 ≤ n) {i : Nat}
    (hi : i < r + L) (hir : i ≠ r) (hiq : i ≠ q) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i = CL M i := by
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
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  unfold CL
  rw [hchN i hi]
  apply List.filter_congr
  intro c hc
  have hcx : c < r + L := by
    by_contra h'
    exact hiq (hxc i c hc (by omega)).2
  have hcq : c ≠ r + qp := by
    intro e; rw [e] at hc; rw [(mem_children_iff.mp hc).2] at hpq; cases hpq; exact hir rfl
  simp only [decide_eq_decide]
  exact hcntN i c hi hcx hcq

#print axioms C_cl_eq

/-- `T2C2Kids3` with the last field only when `c₀` has counted children. -/
def T2C2Kids4 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ Lc0 c0, CL M r = Lc0 ++ [c0] → (∀ d ∈ Lc0, σ.o d = ρ.o d) ∧
      (CL M c0 ≠ [] → ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM)

theorem t2C2Kids3_of4 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (h : T2C2Kids4 M ρ r L q) : T2C2Kids3 M ρ r L q := by
  intro n hn σ hCN hGN Lc0 c0 hT
  obtain ⟨hpre, hlast⟩ := h n hn σ hCN hGN Lc0 c0 hT
  refine ⟨hpre, fun s y hsy hy => ?_⟩
  by_cases hcl : CL M c0 = []
  · exfalso
    have hc0M : c0 ∈ CL M r := by rw [hT]; simp
    have hc0c := cl_mem_children hc0M
    have hpc0 : par M 0 c0 = some r := (mem_children_iff.mp hc0c).2
    have hrc0 : r < c0 := par_lt M 0 _ _ hpc0
    have hpq := par0_q_t2 hM hS I hlen hr hq hqr
    have hqx : q < r + L := par_lt M 0 _ _ hq
    -- `c₀` is before `q`
    have hc0q : c0 ≠ q := by
      intro e; subst e
      exact hncl ⟨Lc0, hT⟩
    have hc0x : c0 < r + L := by
      have hle : c0 ≤ q := by
        by_contra hlt
        have hcL := (mem_children hc0c).2
        have hcx : c0 ≠ r + L := by intro e; rw [e, hq] at hpc0; cases hpc0; exact hqr rfl
        have hA : Anc0 M q c0 := anc_between (anc0_of_par M 0 q (r + L) hq) c0 (by omega) (by omega)
        have := (anc0_par hA (by omega) hpc0).le; have := par_lt M 0 q r hpq; omega
      omega
    have hclN := C_cl_eq hM hS I hz h2 hlen hr hq hqr hn hc0x (by omega) hc0q
    rw [hcl] at hclN
    have hlN : (G2 M r L n).length = r + n * L := TRIO.gexp_length hlen
    have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
    have hoN := o_cl_eq hCN hGN (show c0 < (G2 M r L n).length by omega)
    rw [hclN, hsy] at hoN
    simp only [psi.injEq] at hoN
    exact hy (by rw [hoN.2.1]; rfl)
  · exact hlast hcl s y hsy hy

def C2Kids4 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2Kids4 M ρ r L q

theorem c2Kids3_of4 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (h : C2Kids4 M ρ) : C2Kids3 M ρ := fun r L q k hlen hr hq hqr hncl hu =>
  t2C2Kids3_of4 hM hS I hz h2 hlen hr hq hqr hncl (h r L q k hlen hr hq hqr hncl hu)

#print axioms c2Kids3_of4

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH : HCanonHard)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK4 : T2AtV3 (fun M ρ => C2Kids4 M ρ))
    (hC2R3 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2RootRel3 M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH hVF hK4 hC2R3 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`C2Kids4`). -/
theorem translation_order_res5
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res4 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH hVF
    (fun M ρ rk C hz h2 => c2Kids3_of4 C.std C.ne (coreW C.S C.I) hz h2 (hK4 M ρ rk C hz h2))
    hC2R3 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res5 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res4 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH hVF
    (fun M ρ rk C hz h2 => c2Kids3_of4 C.std C.ne (coreW C.S C.I) hz h2 (hK4 M ρ rk C hz h2))
    hC2R3 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res5
#print axioms translation_surj_res5

end Ytosk.V3Main.SeedPF
