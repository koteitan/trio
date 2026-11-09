import Ytosk.V3DecPShape
import Ytosk.V3DecPTopWire2

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G

/-- Adjacent columns in the decP sibling chain agree, using R1S and sibling decrease. -/
theorem decPColEq_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) :
    DecPColEq M r L q := by
  intro Lc c0 hCL htop w w' hw hw' hc0w hww' hw'q hnb
  obtain ⟨hpq, hnqT, hxb⟩ := c_q_facts hM hS I hlen hr hq hqr hncl
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hwx : w < r + L := by omega
  have hw'x : w' < r + L := by omega
  have he2r : entry M 2 r = 0 := (par2_facts I.z2 (by omega) hr).1
  -- A child after the last counted child is upgraded and topped in the prefix.
  have hafter : ∀ d, d ∈ children M r → c0 < d → d ≤ q →
      isUpg (M.take (r + L)) d = true ∧ topped (M.take (r + L)) d = true := by
    intro d hd hc0d hdq
    have hdx : d < r + L := by omega
    have hdN : d ∈ children (M.take (r + L)) r := by
      rw [children_take]
      exact List.mem_filter.mpr ⟨hd, by simpa using hdx⟩
    have hnc : ¬ Counted (M.take (r + L)) r d := by
      intro hc
      have hdCL : d ∈ CL (M.take (r + L)) r := List.mem_filter.mpr ⟨hdN, by simpa using hc⟩
      have hs : (CL (M.take (r + L)) r).Pairwise (· < ·) := (children_sorted _ r).filter _
      rw [hCL] at hdCL hs
      rcases List.mem_append.mp hdCL with hdL | hdlast
      · have := (List.pairwise_append.mp hs).2.2 d hdL c0 (by simp)
        omega
      · simp only [List.mem_singleton] at hdlast
        omega
    have hnotb : col M d ≠ bump M r := by
      intro hb
      have := I.be r d hd hb
      omega
    by_contra hn
    apply hnc
    exact ⟨by rw [col_take M hdx, bump_take M hrx]; exact hnotb, hn⟩
  -- Toppedness transfers to M, including q whose last child is x.
  have htopM : ∀ d, d < r + L → topped (M.take (r + L)) d = true → topped M d = true := by
    intro d hdx hdtop
    by_cases hdq : d = q
    · subst d
      have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
      unfold topped
      rw [children_split_x hlen hxq, List.getLast?_append]
      simp [hxb]
    · have hno : r + L ∉ children M d := by
        intro h
        have hp := (mem_children_iff.mp h).2
        rw [hq] at hp
        exact hdq (Option.some.inj hp).symm
      rw [← topped_take_eq hlen hdx hno]
      exact hdtop
  obtain ⟨hU, htopt'⟩ := hafter w' hw' (by omega) hw'q
  have htop' : topped M w' = true := htopM w' hw'x htopt'
  obtain ⟨i, hix, hui⟩ := (isUpg_take M (by omega) w').mp hU
  obtain ⟨m, hm1, hm2, hcoli, hcase⟩ := upg_spec hui
  have heq : w' = i + 1 := by
    rcases hcase with heq | ⟨hA, hlt⟩
    · exact heq
    · have hf := I.uat i w' hui (by omega)
      rw [htop'] at hf
      cases hf
  have hupg : upg M (w' - 1) = some w' := by
    rw [show w' - 1 = i by omega]
    exact hui
  have hmr : m = r := by
    apply anc0_eq_of_e0 (anc0_of_par M 1 m w' hm2) (anc0_of_child hw')
    have h0 := congrArg Prod.fst hcoli
    have h0r := I.r0p w' r (mem_children_iff.mp hw').2
    change entry M 0 w' = entry M 0 m + 1 at h0
    omega
  subst m
  have hp1i : par M 1 (w' - 1) = some r := by
    rw [show w' - 1 = i by omega]
    exact hm1
  have he : EndAt M w (w' - 1) := endAt_sib hw hw' hww' hnb
  have hAw : Anc0 M w (w' - 1) := he.2.1 _ he.1 le_rfl
  have hrw : r < w := (mem_children hw).1
  have he1eq : entry M 1 w = entry M 1 (w' - 1) := by
    have hR1 := (sInvXJ_std hM hS).1.r1s w r (mem_children_iff.mp hw).2
    have hlow := par1_entry_lt hp1i
    have hbet := par1_between hp1i w hAw hrw
    omega
  have he1' : entry M 1 w' = entry M 1 w := by
    have h1 := congrArg (fun c : Nat × Nat × Nat => c.2.1) hcoli
    change entry M 1 w' = entry M 1 i at h1
    rw [show i = w' - 1 by omega] at h1
    omega
  have he2' : entry M 2 w' = 1 := by
    have h2 := congrArg (fun c : Nat × Nat × Nat => c.2.2) hcoli
    change entry M 2 w' = entry M 2 r + 1 at h2
    omega
  have he0w : entry M 0 w = entry M 0 r + 1 := I.r0p w r (mem_children_iff.mp hw).2
  have he0' : entry M 0 w' = entry M 0 r + 1 := I.r0p w' r (mem_children_iff.mp hw').2
  -- Sibling decrease and equal rows 0 and 1 force row 2 of w to be 1.
  have hcle : colLe (col M w') (col M w) := by
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hw
    have hw'l2 : w' ∈ l2 := by
      have hmem : w' ∈ l1 ++ w :: l2 := by rw [← hsplit]; exact hw'
      rcases List.mem_append.mp hmem with hleft | hright
      · exfalso
        have hs := children_sorted M r
        rw [hsplit] at hs
        have := (List.pairwise_append.mp hs).2.2 w' hleft w (by simp)
        omega
      · rcases List.mem_cons.mp hright with heq | hmem
        · omega
        · exact hmem
    exact sib_le I.sd l2 l1 w hsplit w' hw'l2
  have he2w : entry M 2 w = 1 := by
    have hbound := I.z2 w
    change colLe (entry M 0 w', entry M 1 w', entry M 2 w')
      (entry M 0 w, entry M 1 w, entry M 2 w) at hcle
    unfold colLe at hcle
    simp only at hcle
    rw [he0w, he0', he1', he2'] at hcle
    omega
  change (entry M 0 w', entry M 1 w', entry M 2 w') =
    (entry M 0 w, entry M 1 w, entry M 2 w)
  rw [he0w, he0', he1', he2', he2w]

#print axioms decPColEq_holds

/-- Seed residuals with decP reduced to the untopped value bound. -/
structure SeedPFResV3R12 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRNoSwitch M ρ r L Lc
  C1ut : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → DecPUntop M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R11_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (h : SeedPFResV3R12 M ρ) : SeedPFResV3R11 M ρ :=
  ⟨h.qr, fun r L q hlen hr hq hqr hncl _hun =>
    decPColEq_holds (r := r) (L := L) (q := q) hM hS I hlen hr hq hqr hncl,
    h.C1ut, h.C2r⟩

/-- `SeedVFResV3R13` with `SeedPFResV3R12`. -/
structure SeedVFResV3R14 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R12 M ρ
  qnDomF : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDomF M ρ r L q Lc
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R13_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (h : SeedVFResV3R14 M ρ) : SeedVFResV3R13 M ρ :=
  ⟨seedPFResV3R11_of hM hS I h.pf, h.qnDomF, h.C2r⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF14 : T2AtV3 (fun M ρ => SeedVFResV3R14 M ρ))
    (hK5 : T2AtV3 (fun M ρ => C2Kids5 M ρ))
    (hC2R4 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2RootRel4 M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF14 hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`SeedVFResV3R14`). -/
theorem translation_order_res19
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res18 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R13_of C.std C.ne (coreW C.S C.I) (hVF14 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res19 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res18 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2
    (fun M ρ rk C hz h2 => seedVFResV3R13_of C.std C.ne (coreW C.S C.I) (hVF14 M ρ rk C hz h2))
    hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res19
#print axioms translation_surj_res19

end Ytosk.V3Main.SeedPF
