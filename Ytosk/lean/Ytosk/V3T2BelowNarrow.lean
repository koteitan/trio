/-
**t = 2: the input hBXU without the fields that the context proves (2026-11-06).**

`T2BelowAtV3U M ρ` asks at the seed `p` (always `r`) `T2HardA = T2HardB ∧ v_N(p) = v_M(p)` with
`T2HardB = VSmallRA M ρ ∧ PH3cG M ρ ∧ (RClaimU at p) ∧ (REr of the argument of p)`.
- `VSmallRA M ρ` follows from `VSmallRAll M ρ` (the invariant `vra`): the last frame and `PathLvA ⊆ PathLvAll`.
- `PH3cG M ρ` is the invariant `ph`.
- `v_N(r) = v_M(r)` is `vr_N` (V3ExpT2X; `r` is sealed, the seeds of `N` lie in its subtree), for `q = r` and `q ≠ r`.
`T2BelowAtV3U2` keeps only `RClaimU` and `REr` at the seed.
-/
import Ytosk.V3C2Root

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem vsmallRA_of_all {M : Mat} {ρ : Valn} (h : VSmallRAll M ρ) : VSmallRA M ρ :=
  fun k c Lc s y hcl ho ht hs u hu hku g hg =>
    h k c Lc [] s y hcl ho ht hs u (hu.imp_right PathLvA.toAll) hku g hg

/-- `T2BelowResXU` with `T2HardA` replaced by its two value fields. -/
def T2BelowResXU2 (M : Mat) (ρ : Valn) (r L d0 d1 : Nat) : Prop :=
  ∀ n, 2 ≤ n → (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L d0 d1 m) τ → Good3 (TRIO.gexp M r L d0 d1 m) τ) →
    ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true) →
    (∀ p, T2Seed M r L p →
      (∀ U : T → Prop, (∀ u, U u → PathLvA M ρ p u) → RClaimU U ρ σ p) ∧
      (∀ X X', ρ.o p = psi (ρ.v p) X z → σ.o p = psi (ρ.v p) X' z → X' ≠ X → REr X X')) ∧
    (∀ p, T2Seed M r L p → Lhd z (σ.o p) (ρ.o p) ∧ isOT (σ.o p) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ p).Pairwise (fun a b => b ≤ a)) ∧
    (∀ q, par M 0 (r + L) = some q → q ≠ r → isOT (σ.o q) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ q).Pairwise (fun a b => b ≤ a)) ∧
    AbsWNxU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ ∧ NotBumpKidXU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ

def T2BelowAtV3U2 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    T2BelowResXU2 M ρ r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r)

theorem t2BelowAtV3U_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (h : T2BelowAtV3U2 M ρ) : T2BelowAtV3U M ρ := by
  have I : Inv3W M ρ rk := coreW C.S C.I
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  intro r L hlen hr n hn hlow σ hCN hOT
  obtain ⟨hH, hS, hQ, hA, hB⟩ := h r L hlen hr n hn hlow σ hCN hOT
  refine ⟨fun p hp => ⟨⟨vsmallRA_of_all C.I.vra, C.I.ph, (hH p hp).1, (hH p hp).2⟩, ?_⟩, hS, hQ, hA, hB⟩
  -- the seed is `r`
  have hpr : p = r := by
    rcases hp with ⟨_, rfl⟩ | ⟨q, hq, hqr, hpq⟩
    · rfl
    · rw [par0_q_t2 C.std C.ne I hlen hr hq hqr] at hpq; exact (Option.some.inj hpq).symm
  subst hpr
  -- `v_N(r) = v_M(r)` by `vr_N`
  have hrx : p < p + L := par_lt M 2 _ _ hr
  have hL0 : 0 < L := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hA : Anc0 M p (p + L) := anc0_of_par M 2 p (p + L) hr
  have hd0e : entry M 0 (p + L) = entry M 0 p + (entry M 0 (p + L) - entry M 0 p) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (show p + L < M.length by omega) hr
  have hd1e : entry M 1 (p + L) = entry M 1 p + (entry M 1 (p + L) - entry M 1 p) := by omega
  have hr1 : par M 1 (p + L) = some p := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨q, hq⟩ : ∃ q, par M 0 (p + L) = some q := by
    have := anc0_par_exists hA (by omega); obtain ⟨q, hq, _⟩ := this; exact ⟨q, hq⟩
  have hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
    intro i hi hb
    by_cases hqr : q = p
    · subst hqr
      have := e2_of_col (show col M q = (entry M 0 i + 1, entry M 1 i, 1) from hb); omega
    · rw [par0_q_t2 C.std C.ne I hlen hr hq hqr] at hi; cases hi
      obtain ⟨Txb, Tqb, _, _, _⟩ := t2_qn_struct hX hJ hlen hr (show par M 0 (p + L) = some (p + (q - p)) by
        rw [show p + (q - p) = q by have := (par_lt M 0 q p (par0_q_t2 C.std C.ne I hlen hr hq hqr)); omega]; exact hq)
        (by have := par_lt M 0 _ _ hq; have := par_lt M 0 q p (par0_q_t2 C.std C.ne I hlen hr hq hqr); omega)
        (by rw [show p + (q - p) = q by have := (par_lt M 0 q p (par0_q_t2 C.std C.ne I hlen hr hq hqr)); omega]
            exact par0_q_t2 C.std C.ne I hlen hr hq hqr)
      rw [show p + (q - p) = q by have := (par_lt M 0 q p (par0_q_t2 C.std C.ne I hlen hr hq hqr)); omega] at Tqb
      exact Tqb hb
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M p L (entry M 0 (p + L) - entry M 0 p)
      (entry M 1 (p + L) - entry M 1 p) m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = p + L by omega]; exact hr)
    rw [h2, show M.length - 1 = p + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT (TRIO.gexp M p L (entry M 0 (p + L) - entry M 0 p) (entry M 1 (p + L) - entry M 1 p) n) := by
    rw [← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  rw [hexp n] at hRN
  exact vr_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 I.uat hUN I.cons hCN hRN

#print axioms t2BelowAtV3U_of

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCan : HCanon)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK3 : T2AtV3 (fun M ρ => C2Kids3 M ρ))
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

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG

theorem desc3_res3 : Desc3 :=
  desc3_res2 hDI hF hAbsU hSeeds hQR hQN (fun M ρ rk C hz h2 => t2BelowAtV3U_of C hz h2 (hBXU2 M ρ rk C hz h2))
    hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (hBXU narrowed). -/
theorem translation_order_res3
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_res3 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG)
    hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res3 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_res3 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG)
    hFS hot hvN hlt

end

#print axioms translation_order_res3
#print axioms translation_surj_res3

end Ytosk.V3Main.SeedPF
