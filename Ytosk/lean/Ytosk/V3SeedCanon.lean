/-
**t = 2: the sibling value residual `HCanon` replaces `unc` and `T2SeedCBig` (2026-11-06).**

`CanonicalNeed` (V3SibConsumer, 10/24): at a row-2 root, adjacent children `a < b`, `a` upgraded from `a − 1` and topped,
`b` counted, have `v(b) ≤ v(a)`.  `HCanon` is this for every standard matrix and valuation.
- `QNRelR.unc` (the uncounted children `d < q` of `r` have `qnS < v(d)`) is `QNUncRes`: `qnUncRes_of_canonical`
  from `CanonicalNeed M`.
- `T2SeedCBig` (the same in `M.take x`, C1): `t2SeedCBig_of_canonical` moved to the V3 context
  (`t2SeedCBig_of_canonicalV3`: `Good3` of `M.take x` from `DropV3`, `vqP` from `un`), from `CanonicalNeed (M.take x)`.
Bundles `SeedPFResV3R3`, `SeedVFResV3R3` and entry points `hSF_of4`, `hSP_of4`, `hN_of8`.
-/
import Ytosk.V3SeedPFNarrow
import Ytosk.V3SibConsumer

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical in
/-- **`T2SeedCBig` from `CanonicalNeed` of `M.take x`** on the V3 context (`t2SeedCBig_of_canonical`, V3SibConsumer,
with the drop of `DropV3` and the C fields `decP`, `un`; `vqP` from `un`). -/
theorem t2SeedCBig_of_canonicalV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hun : upg M (r + L - 1) = none)
    (hdecP : ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
      ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s)
    (hSib : ∀ τ, Cons (M.take (r + L)) τ → Good3 (M.take (r + L)) τ → SibConsumer.CanonicalNeed (M.take (r + L)) τ) :
    T2SeedCBig M ρ r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hqnc := qP_C hM hS I hlen hr hq hqr hncl hun
  -- the drop and `M.take x`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hG1 := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hC1
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hG1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  obtain ⟨hXT, hJT⟩ := sInvXJ_std (std_take hM (r + L) (by omega)) hTS
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  -- the columns of the children of `r`
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := hX.loc.2.2.1 q (r + L) hxq Txb
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have he1x : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have hcolr : ∀ c ∈ children (M.take (r + L)) r, entry (M.take (r + L)) 1 c = entry (M.take (r + L)) 1 r + 1 ∧
      entry (M.take (r + L)) 2 c = 1 ∧ par (M.take (r + L)) 1 c = some r := by
    intro c hc
    have hcx : c < r + L := by have := (mem_children hc).2; omega
    have hpcT := (mem_children_iff.mp hc).2
    have hpc : par M 0 c = some r := by rwa [par_take M 0 c hcx] at hpcT
    have hcq : c ≤ q := by
      by_contra hlt
      have hA : Anc0 M q c := anc_between (anc0_of_par M 0 q (r + L) hq) c (by omega) (le_of_lt hcx)
      have := (anc0_par hA (by omega) hpc).le; omega
    have hcol := t_child_col hX hpq (by omega) he2q (by omega) (mem_children_iff.mpr ⟨by omega, hpc⟩) hcq
    have hcqx := t_col_x hX hpq (by omega) he2q (by omega)
    have h1 : entry M 1 c = entry M 1 r + 1 := by
      have : entry M 1 c = (col M c).2.1 := rfl; rw [this, hcol, hcqx]
    have h2 : entry M 2 c = 1 := by
      have : entry M 2 c = (col M c).2.2 := rfl; rw [this, hcol, hcqx]
    refine ⟨by rw [entry_take M 1 hcx, entry_take M 1 (by omega)]; exact h1,
      by rw [entry_take M 2 hcx]; exact h2, ?_⟩
    rw [par_take M 1 c hcx]; exact par1_of_child hpc (by omega)
  have hqT : q ∈ children (M.take (r + L)) r := by
    rw [children_take, List.mem_filter]
    exact ⟨mem_children_iff.mpr ⟨by omega, hpq⟩, by simpa using hqx⟩
  -- an uncounted child is topped and upgraded from the previous column
  have huncnt : ∀ c ∈ children (M.take (r + L)) r, ¬ Counted (M.take (r + L)) r c →
      topped (M.take (r + L)) c = true ∧ upg (M.take (r + L)) (c - 1) = some c := by
    intro c hc hnc
    have hb : col (M.take (r + L)) c ≠ bump (M.take (r + L)) r := by
      intro h
      have : entry (M.take (r + L)) 1 c = (col (M.take (r + L)) c).2.1 := rfl
      rw [h] at this; simp [bump] at this; have := (hcolr c hc).1; omega
    have hut : isUpg (M.take (r + L)) c = true ∧ topped (M.take (r + L)) c = true := by
      by_contra hn; exact hnc ⟨hb, hn⟩
    refine ⟨hut.2, ?_⟩
    unfold isUpg at hut
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hut.1
    have hu : upg (M.take (r + L)) i = some c := of_decide_eq_true hi
    by_cases hci : c = i + 1
    · rw [hci, Nat.add_sub_cancel]; rw [hci] at hu; exact hu
    · have := hXT.toSInv.uat i c hu hci; rw [this] at hut; simp at hut
  refine ⟨fun τ hτ => ?_⟩
  have hG : Good3 (M.take (r + L)) τ := good3_congr hG1 (agree_of_cons hC1 hτ hRk1)
  have hrT : r < (M.take (r + L)).length := by omega
  -- counted children are above `s′`
  have hcntd : ∀ d ∈ children (M.take (r + L)) r, Counted (M.take (r + L)) r d → qnS M ρ r L q < τ.v d := by
    intro d hd hcnt
    have hdCL : d ∈ CL (M.take (r + L)) r := List.mem_filter.mpr ⟨hd, decide_eq_true hcnt⟩
    obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
    rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨Lc, c0, hLc⟩
    · rw [hnil] at hdCL; simp at hdCL
    rw [List.concat_eq_append] at hLc
    obtain ⟨s, y, hc0, hs⟩ := hdecP τ hτ Lc c0 hLc
    have hc0T : c0 < (M.take (r + L)).length :=
      (mem_children (cl_mem_children (show c0 ∈ CL (M.take (r + L)) r by rw [hLc]; simp))).2
    have hdT := (mem_children hd).2
    have hvc0 : τ.v c0 = s := by
      rw [o_cl_eq hτ hG hc0T] at hc0; simp only [psi.injEq] at hc0; exact hc0.1
    have hle : τ.o c0 ≤ τ.o d := by
      rw [hLc] at hdCL hdec
      rcases List.mem_append.mp hdCL with h | h
      · exact (List.pairwise_append.mp (List.pairwise_map.mp hdec)).2.2 d h c0 (by simp)
      · simp at h; rw [h]
    have hl := lev_le_of_le hle
    rw [o_cl_eq hτ hG hc0T, o_cl_eq hτ hG hdT] at hl
    simp only [lev_psi] at hl
    rw [hvc0] at hl
    exact lt_of_lt_of_le hs hl
  -- induction from the right
  have key : ∀ n d, q - d ≤ n → d ∈ children (M.take (r + L)) r → d < q → qnS M ρ r L q < τ.v d := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro d hn hd hdq
    by_cases hcnt : Counted (M.take (r + L)) r d
    · exact hcntd d hd hcnt
    -- the next sibling
    have hex : ∃ e, e ∈ children (M.take (r + L)) r ∧ d < e := ⟨q, hqT, hdq⟩
    let dn := Nat.find hex
    obtain ⟨hdn, hddn⟩ := Nat.find_spec hex
    have hcons : ∀ e ∈ children (M.take (r + L)) r, d < e → dn ≤ e :=
      fun e he hde => Nat.find_min' hex ⟨he, hde⟩
    have hdnq : dn ≤ q := hcons q hqT hdq
    by_cases hu : upg (M.take (r + L)) (dn - 1) = some dn
    swap
    · -- `dn` is not upgraded from `dn − 1`: it is counted and below `q`, and `v(dn) ≤ v(d)`
      have hdnc : Counted (M.take (r + L)) r dn := by
        by_contra hdnc; exact hu (huncnt dn hdn hdnc).2
      have hle := hSib τ hτ hG r d dn hd hdn hddn hcons
        (hcolr d hd).1 (hcolr d hd).2.1 (hcolr d hd).2.2
        (hcolr dn hdn).1 (hcolr dn hdn).2.1 (hcolr dn hdn).2.2
        (huncnt d hd hcnt).2 (huncnt d hd hcnt).1 hu hdnc
      exact lt_of_lt_of_le (hcntd dn hdn hdnc) hle
    have hlt := upg_next_lt hXT hτ hG hd hdn hddn hcons (hcolr d hd).1 (hcolr d hd).2.1 (hcolr d hd).2.2
      (hcolr dn hdn).2.1 (hcolr dn hdn).2.2 (huncnt d hd hcnt).1 hu
    have hlt' : τ.v dn < τ.v d := hlt
    rcases Nat.eq_or_lt_of_le hdnq with h | h
    · rw [h] at hlt'; rw [← c_vqP_of_un hM hS I hlen hr hq hqr hun τ hτ]; exact hlt'
    · exact lt_trans (ih (q - dn) (by omega) dn le_rfl hdn h) hlt'
  intro d hd hdq _
  exact key (q - d) d le_rfl hd hdq

/-- **Residual: `CanonicalNeed` of every standard matrix.** -/
def HCanon : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → SibConsumer.CanonicalNeed N σ

/-- `QNRelR` without `unc`. -/
structure QNRelR3 (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  base : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ρ.v r < t1

/-- `SeedPFResV3R2` without `unc` and `T2SeedCBig`. -/
structure SeedPFResV3R3 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRRelR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → SVRel M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → QNRelR3 M ρ r L q Lc
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRelR M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R2_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (hCan : HCanon)
    (h : SeedPFResV3R3 M ρ) : SeedPFResV3R2 M ρ := by
  refine ⟨h.qr, h.sv, fun r L q hlen hr hq hqr Lc hLc => ⟨?_, (h.qn r L q hlen hr hq hqr Lc hLc).base⟩,
    fun r L q hlen hr hq hqr hncl hun => ⟨h.C1 r L q hlen hr hq hqr hncl hun, ?_⟩, h.C2r⟩
  · exact SibConsumer.qnUncRes_of_canonical hM hS I hlen hr hq hqr hLc (hCan M ρ rk hM hS I.cons I.rank I.good)
  · have hrx : r < r + L := par_lt M 2 _ _ hr
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
    rw [show M.length - 1 = r + L by omega] at hRk1
    have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
    have hTstd : Std (M.take (r + L)) := std_take hM (r + L) (by omega)
    exact t2SeedCBig_of_canonicalV3 hM hS I Ctx hlen hr hq hqr hncl hun
      (h.C1 r L q hlen hr hq hqr hncl hun).decP
      (fun τ hτ hG => hCan _ τ rk hTstd hTS hτ hRk1 hG)

/-- `SeedVFResV3R2` without `unc` and `T2SeedCBig`. -/
structure SeedVFResV3R3 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R3 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDom M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R2_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (hCan : HCanon)
    (h : SeedVFResV3R3 M ρ) : SeedVFResV3R2 M ρ :=
  ⟨seedPFResV3R2_of hM hS I Ctx hCan h.pf, h.qnDom, h.cDom, h.C2r⟩

/-- **The inputs hSF, hSP and hN** with `HCanon` in place of `unc` and `T2SeedCBig`. -/
theorem hSF_of4 (hCan : HCanon) (hRes : T2AtV3 (fun M ρ => SeedPFResV3R3 M ρ))
    (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2F M) :=
  hSF_of3 (fun M ρ rk C hz h2 => seedPFResV3R2_of C.std C.ne (coreW C.S C.I) C hCan (hRes M ρ rk C hz h2)) hK hC2

theorem hSP_of4 (hCan : HCanon) (hRes : T2AtV3 (fun M ρ => SeedPFResV3R3 M ρ))
    (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2P M) :=
  hSP_of3 (fun M ρ rk C hz h2 => seedPFResV3R2_of C.std C.ne (coreW C.S C.I) C hCan (hRes M ρ rk C hz h2)) hK hC2

theorem hN_of8 (hCan : HCanon) (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hQN : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M)) :
    T2SmallV3 :=
  hN_of7 hBXU (fun M ρ rk C hz h2 => seedVFResV3R2_of C.std C.ne (coreW C.S C.I) C hCan (hVF M ρ rk C hz h2))
    hFD hK hQN hC hCopy hVD hAG

#print axioms t2SeedCBig_of_canonicalV3
#print axioms hSF_of4
#print axioms hSP_of4
#print axioms hN_of8

end Ytosk.V3Main.SeedPF
