import Ytosk.V3DecPSplit2

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G

/-- Adjacent siblings in the chain have equal columns. -/
def DecPColEq (M : Mat) (r L q : Nat) : Prop :=
  ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] → topped (M.take (r + L)) c0 = true →
    ∀ w w', w ∈ children M r → w' ∈ children M r → c0 ≤ w → w < w' → w' ≤ q →
      (∀ c ∈ children M r, ¬ (w < c ∧ c < w')) → col M w' = col M w

theorem decPShape2_of_colEq {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hce : DecPColEq M r L q) : DecPShape2 M r L q := by
  intro Lc c0 hCL htop w w' hw hw' hc0w hww' hw'q hnb
  obtain ⟨hpq, hnqT, hxb⟩ := c_q_facts hM hS I hlen hr hq hqr hncl
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hwx : w < r + L := by omega
  have hw'x : w' < r + L := by omega
  have he2r : entry M 2 r = 0 := (par2_facts I.z2 (by omega) hr).1
  have hcol : col M w' = col M w := hce Lc c0 hCL htop w w' hw hw' hc0w hww' hw'q hnb
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
  have he2i : entry M 2 (w' - 1) = 0 := by
    have hne := (upg_e12 hupg).2
    have hbound := I.z2 (w' - 1)
    omega
  have he1eq : entry M 1 w = entry M 1 (w' - 1) := by
    have h1 := congrArg (fun c : Nat × Nat × Nat => c.2.1) hcoli
    have h1' := congrArg (fun c : Nat × Nat × Nat => c.2.1) hcol
    change entry M 1 w' = entry M 1 i at h1
    change entry M 1 w' = entry M 1 w at h1'
    rw [show w' - 1 = i by omega]
    omega
  have he2w : entry M 2 w = 1 := by
    have h2 := congrArg (fun c : Nat × Nat × Nat => c.2.2) hcoli
    have h2' := congrArg (fun c : Nat × Nat × Nat => c.2.2) hcol
    change entry M 2 w' = entry M 2 r + 1 at h2
    change entry M 2 w' = entry M 2 w at h2'
    omega
  have he : EndAt M w (w' - 1) := endAt_sib hw hw' hww' hnb
  have heM : w' - 1 < M.length := by omega
  have htopwT : topped (M.take (r + L)) w = true := by
    rcases Nat.eq_or_lt_of_le hc0w with heq | hlt
    · rw [← heq]; exact htop
    · exact (hafter w hw hlt (by omega)).2
  have htopw : topped M w = true := htopM w hwx htopwT
  have hchb : ∃ b, b ∈ children M w ∧ (∀ c ∈ children M w, c ≤ b) ∧ col M b = bump M w := by
    unfold topped at htopw
    cases hl : (children M w).getLast? with
    | none =>
      exfalso
      have hnil : children M w = [] := List.getLast?_eq_none_iff.mp hl
      have hwe := endAt_leaf he heM (fun c hc => by rw [hnil] at hc; simp at hc)
      rw [hwe] at he2w
      omega
    | some b =>
      rw [hl] at htopw
      have hb : b ∈ children M w := List.mem_of_getLast? hl
      refine ⟨b, hb, ?_, by simpa using htopw⟩
      intro c hc
      obtain ⟨l, hl'⟩ := List.getLast?_eq_some_iff.mp hl
      have hs := children_sorted M w
      rw [hl'] at hs hc
      rcases List.mem_append.mp hc with hc | hc
      · exact le_of_lt ((List.pairwise_append.mp hs).2.2 c hc b (by simp))
      · simp only [List.mem_singleton] at hc
        omega
  obtain ⟨b, hb, hbmax, hbb⟩ := hchb
  have hbe : EndAt M b (w' - 1) := endAt_last hb hbmax he heM
  have hbx : b < r + L := by have := hbe.1; omega
  have he2b : entry M 2 b = 1 := by
    have h2 := congrArg (fun c : Nat × Nat × Nat => c.2.2) hbb
    exact h2
  have hbi : b ≠ w' - 1 := by intro h; rw [h] at he2b; omega
  have hAbi : Anc0 M b (w' - 1) := hbe.2.1 _ hbe.1 le_rfl
  obtain ⟨k1, hk1, hAk⟩ := child_toward hAbi hbi heM
  have hrk : r < k1 := by
    have hrw := (mem_children hw).1
    have hwb := (mem_children hb).1
    have hbk := (mem_children hk1).1
    omega
  have he1k : entry M 1 w ≤ entry M 1 k1 := by
    rw [he1eq]
    exact par1_between hp1i k1 hAk hrk
  have hBL : BumpLeaf M := (sInvXJ_std hM hS).1.loc.2.2.2
  have hleaf : children M k1 = [] := (hBL w b k1 hb hbb hk1 he1k).2.1
  have hik : w' - 1 = k1 := anc0_leaf hleaf hAk
  exact ⟨b, hb, hbx, hbb, hik ▸ hk1, hupg⟩

#print axioms decPShape2_of_colEq

end Ytosk.V3Main.SeedPF
