import Ytosk.V3T0Weak
import Ytosk.V3T0DepU
import Ytosk.V3T0Sh3

namespace Ytosk.T0ArgB
open T

/-- Natural indices are standard as well as in range. -/
theorem valid_nat {a b : T} (hb : b ≠ z) (k : Nat) : Valid (psi a b z) (natT k) := by
  refine ⟨isOT_natT k, ?_⟩
  have hv := validLt_natT (a := a) hb k
  unfold ValidLt at hv
  cases hc : cof (psi a b z) with
  | zero => simp only [hc] at hv
  | succ =>
    have h := (cof_props (psi a b z)).2 hc
    simp only [isSucc, last, beq_iff_eq, one, psi.injEq] at h
    exact False.elim (hb h.2.1)
  | omega => exact ⟨k,rfl⟩
  | big μ => simpa only [hc] using hv

/-- The finite middle-copy node is a standard FS term of the old parent. -/
theorem copies_ot {a B v Y0 : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q) :
    isOT (psi a (spArg a B (mulT (psi v Y0 z) m)) z) = true := by
  have hArg : spArg a B (psi v (app Y0 one) z) ≠ z := by
    intro h
    have := lt_spArg a (b := B) hX (by simp)
    rw [h] at this
    exact T.not_lt_z _ this
  have hfs : ∃ k, psi a (spArg a B (mulT (psi v Y0 z) m)) z =
      fs (psi a (spArg a B (psi v (app Y0 one) z)) z) (natT k) := by
    by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
    · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
      · exact ⟨m-1,(t0_frame_swallow hm hX hO htr hbad.1 hbad.2).symm⟩
      · exact ⟨m,(t0_frame_trig hm hOld hX hO htr hbad).symm⟩
    · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
        have h1 := isOT_arg hOld
        rw [spArg_single] at h1
        unfold step at h1
        rw [if_neg htr, add_eq_app_of_ge ⟨_,_,rfl⟩ _ hBX] at h1
        exact h1
      exact ⟨m,(t0_frame_notrig m hXapp htr hBX).symm⟩
  obtain ⟨k,hk⟩ := hfs
  rw [hk]
  exact isOT_fs hOld (valid_nat hArg k)

/-- The exact weak seed conclusion needed at the parent g. Argument Lhd is
not asserted: it is false on some generated tuples satisfying these premises. -/
theorem weak_seed {a B v Y0 w' : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hW : WkVA w' v) (hWC : WCS a w') (hc' : isOT (psi w' z z) = true)
    (hva : v ≤ a) :
    let X := spArg a B (psi v (app Y0 one) z)
    let X' := spArg a (spArg a B (mulT (psi v Y0 z) m)) (psi w' z z)
    isOT (psi a X' z) = true ∧ Lhd z (psi a X' z) (psi a X z) ∧
      (split X' (psi (succ a) z z)).1 = (split X (psi (succ a) z z)).1 ∧
      (split X' (psi (succ a) z z)).2 ≠ z := by
  dsimp only
  set B' := spArg a B (mulT (psi v Y0 z) m) with hB'
  have hwa : w' < a := lt_of_lt_of_le hW.1 hva
  have hOX : psi v Y0 z < psi v (app Y0 one) z :=
    psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl,lt_app_one Y0⟩)
  have hB'O : ∀ q ∈ summands B', psi v Y0 z ≤ q :=
    spArg_summands_ge ⟨v,Y0,rfl⟩ _ B (isOT_mulT hO ⟨_,_,rfl⟩ m)
      (fun q hq => by rw [summands_mulT ⟨_,_,rfl⟩ m q hq])
      (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
  have hleafO : psi w' z z < psi v Y0 z := psi_lt_psi_z_iff.mpr (Or.inl hW.1)
  have hB'leaf : ∀ q ∈ summands B', psi w' z z ≤ q :=
    fun q hq => le_trans (le_of_lt hleafO) (hB'O q hq)
  have hnew : spArg a B' (psi w' z z) = app B' (psi w' z z) := by
    rw [spArg_single,step_leaf]
    exact add_eq_app_of_ge ⟨w',z,rfl⟩ B' hB'leaf
  have hmid := copies_ot hm hOld hX hO hBX
  change isOT (psi a B' z) = true at hmid
  have harg := isOT_app_of (isOT_arg hmid) hc' hB'leaf
  have hot : isOT (psi a (spArg a B' (psi w' z z)) z) = true := by
    rw [hnew,isOT_psi_iff]
    refine ⟨isOT_sub hmid,harg,rfl,z_le _,?_⟩
    intro g hg
    rw [comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact lt_of_lt_of_le (comps_lt hmid g hg) (le_app_self _ _)
    · simp only [comps, if_pos (show lt w' a = true from hwa), List.append_nil, List.not_mem_nil] at hg
  have hlow : (split (spArg a B' (psi w' z z)) (psi (succ a) z z)).2 ≠ z := by
    rw [hnew]
    exact lo_ne_of_low_change (by simp) (by
      change psi w' z z < psi (succ a) z z
      exact psi_lt_psi_z_iff.mpr (Or.inl (lt_trans hwa (lt_succ_self a))))
  have hcls := s1_core_cls hm hX hO hBX ⟨hc',w',z,rfl⟩ (le_of_lt hleafO)
    (by intro s y h hs; simp only [psi.injEq] at h; exact h.2.1.symm)
    (by intro s y h hs hn; exact False.elim (hn (psi_lt_psi_z_iff.mpr
      (Or.inl (lt_of_le_of_lt hva (lt_succ_self a))))))
  change ClsNode a (spArg a B' (psi w' z z)) _ at hcls
  have hhi : (split (spArg a B' (psi w' z z)) (psi (succ a) z z)).1 =
      (split (spArg a B (psi v (app Y0 one) z)) (psi (succ a) z z)).1 := by
    rcases hcls with h | h | h
    · exact h.1
    · exact False.elim (hlow h.1)
    · have hz := split_snd_z_of_ge (split_fst_ge (psi (succ a) z z)
          (spArg a B (psi v (app Y0 one) z)))
      rw [← h] at hz
      exact False.elim (hlow hz)
  exact ⟨hot,s1_core_weak hm hOld hX hO hBX hW hWC hc',hhi,hlow⟩

/-- A lost t=0 upgrade is to an ancestor, so its old value is at most
that of its row0 parent. All inputs are existing structural/value fields. -/
theorem index_le_of_upg {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r g k : Nat}
    (hR0 : R0P M) (hZ2 : Z2 M) (hUAB : UAB M) (hBE : BumpE2 M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk)
    (hrM : r < M.length) (hg : par M 0 r = some g)
    (hz : entry M 1 (r+1) = 0) (hu : upg M r = some k) : ρ.v r ≤ ρ.v g := by
  obtain ⟨m,hm1,_,hcol,hcase⟩ := upg_spec hu
  have h12 := upg_e12 hu
  have h20 : entry M 2 r = 0 := by have := hZ2 r; omega
  rcases hcase with hk | ⟨hA,hkr⟩
  · have he1 := e1_of_col hcol
    rw [hk,hz] at he1
    exact False.elim (h12.1 he1.symm)
  · have hkg : Anc0 M k g := anc0_par hA (by omega) hg
    have hgr : Anc0 M g r := Anc0.step hg (Anc0.refl g)
    have hsp := (upg_anc_spine hR0 hZ2 hUAB hBE hJ hC hG hR hrM hu hA hkr
      g hkg hgr (by have := par_lt M 0 r g hg; omega)).2
    have hv := v_upg_eq hC hrM h12.1 h20 hu
      (by rw [hm1]; exact hG.ot_v m (by have := par_lt M 1 r m hm1; omega))
      (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
    rw [hv]
    exact hsp

/-- CntX at a genuinely counted final child supplies the lost upgrade,
so the weak branch needs no additional ancestor hypothesis. -/
theorem index_le_of_cntx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r g : Nat}
    (hR0 : R0P M) (hZ2 : Z2 M) (hUAB : UAB M) (hBE : BumpE2 M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk)
    (hrM : r < M.length) (hg : par M 0 r = some g)
    (hz : entry M 1 (r+1) = 0) (hCX : CntX M ρ r)
    (hc : r+1 ∈ children M r) (hcnt : Counted M r (r+1)) : ρ.v r ≤ ρ.v g := by
  rcases hCX with hn | ⟨_,_,k,W,_,hu,_,_,_⟩
  · exact False.elim (hn (r+1) hc hcnt)
  · exact index_le_of_upg hR0 hZ2 hUAB hBE hJ hC hG hR hrM hg hz hu

/-- The same-high class only needs node Lhd to give RClaimU. -/
theorem rclaim_of_same_high {U : T → Prop} {ρ σ : Valn} {i : Nat} {a X X' : T}
    (hX : ρ.o i = psi a X z) (hX' : σ.o i = psi a X' z)
    (hot : isOT (psi a X z) = true) (hot' : isOT (psi a X' z) = true)
    (hl : Lhd z (psi a X' z) (psi a X z))
    (hhi : (split X' (psi (succ a) z z)).1 = (split X (psi (succ a) z z)).1) :
    RClaimU U ρ σ i := by
  intro p y y' q hy hy' _ _
  rw [hX] at hy
  rw [hX'] at hy'
  simp only [psi.injEq] at hy hy'
  obtain ⟨rfl,rfl,-⟩ := hy
  obtain ⟨-,rfl,-⟩ := hy'
  have hlt : X' < X := by
    rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨_,h⟩
    · exact False.elim (lt_irrefl' _ h)
    · exact h
  have e := split_app (psi (succ a) z z) X
  have e' := split_app (psi (succ a) z z) X'
  have hlo : (split X' (psi (succ a) z z)).2 < (split X (psi (succ a) z z)).2 := by
    rw [← e,← e',hhi] at hlt
    exact (app_lt_app_left_iff _).mp hlt
  exact relR_H_samehiU hot' hot (Or.inr hl) hhi hlo

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN

theorem t0_S1AW_node {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hw : ∃ w', ρ'.o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ WCS (ρ.v g) w' ∧ isOT (psi w' z z) = true)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hrN : Counted (TRIO.gexp M r L 0 0 n) g r)
    (hva : ρ.v r ≤ ρ.v g) :
    ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧
      isOT (psi (ρ.v g) X' z) = true ∧ Lhd z (psi (ρ.v g) X' z) (psi (ρ.v g) X z) ∧
      ∀ U : T → Prop, RClaimU U ρ σ g := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  -- the counted children in `M`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set Lc := F.filter (fun d => decide (Counted M g d)) with hLcdef
  have hclM : CL M g = Lc ++ [r] := by
    unfold CL; rw [hchM, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
    rfl
  -- the counted children in `N`
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hroots : [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) =
      (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
    have e1 : (List.range n).map f = [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [hfdef, Nat.add_sub_cancel]
    have e2 : (List.range n).map f = (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ, List.map_append]; simp [hfdef]
    rw [← e1, e2]
  set Cm := ((List.range (n - 1)).map f).filter
    (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) with hCmdef
  have hclN : CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] := by
    unfold CL
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
      List.filter_append]
    have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) = Lc := by
      apply List.filter_congr
      intro d hd
      have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
      simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hgr hdr]
    rw [hF', List.append_assoc]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hLast]
    rfl
  have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hσLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  have hLcv : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hσLc
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  have hsO0 : Single (omid M r L ρ) :=
    ⟨isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN, by
      rw [(o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG).2]; exact ⟨_, _, rfl⟩⟩
  have hsLr : Single (ρ'.o r) := single_o hC1 hGT (by rw [List.length_take]; omega)
  have hsCL : ∀ d ∈ CL (TRIO.gexp M r L 0 0 n) g, Single (σ.o d) := by
    intro d hd
    rw [hclN] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · have hdF := (List.mem_filter.mp hd).1
        have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
        rw [hσLc d hd]
        exact single_o hC hG (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
        rw [hσmid k (by have := List.mem_range.mp hk; omega)]; exact hsO0
    · simp at hd; rw [hd, hσlast]; exact hsLr
  have hsN : ∀ t ∈ (CL (TRIO.gexp M r L 0 0 n) g).map σ.o, Single t := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hsCL d hd
  rw [hclM] at hsM hpM
  rw [hclN] at hsN
  simp only [List.map_append, List.map_singleton] at hsM hpM hsN
  rw [hLcv, hCmv, hσlast] at hsN
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  -- the decrease at `g` in `N`
  have hpN : (Lc.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r]).Pairwise
      (fun a b => b ≤ a) := by
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hlo : ρ'.o r ≤ omid M r L ρ := by
      obtain ⟨w', hw', hWk, _, _⟩ := hw
      rw [hw', hom]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hWk.1))
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hp1.1,
      List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha b hb => ?_⟩, by simp, fun a ha b hb => ?_⟩
    · rw [(List.mem_replicate.mp hb).2]
      exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
    · simp at hb; rw [hb]
      rcases List.mem_append.mp ha with ha | ha
      · exact le_trans hlo (le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp)))
      · rw [(List.mem_replicate.mp ha).2]; exact hlo
  have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) g).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hclN]; simp only [List.map_append, List.map_singleton]; rw [hLcv, hCmv, hσlast]; exact hpN
  set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map
    (cnt M ρ r))) with hY0
  set v := ρ.v r with hv
  set a := ρ.v g with ha
  set Lv := Lc.map ρ.o with hLv
  set m := Cm.length with hm
  have hOv : omid M r L ρ = psi v Y0 z := hom
  -- the sums
  have hsO : Single (omid M r L ρ) := by
    exact hsO0
  have hsumN : sumN (Lv ++ List.replicate m (omid M r L ρ) ++ [ρ'.o r]) =
      app (app (sumN Lv) (mulT (omid M r L ρ) m)) (ρ'.o r) := by
    have hp1 := List.pairwise_append.mp hpN
    rw [sumN_append_dec hsN hpN, sumN_append_dec (fun t ht => hsN t (List.mem_append_left _ ht)) hp1.1,
      sumN_replicate hsO m, sumN_singleton (hsN _ (by simp))]
  have hsumM : sumN (Lv ++ [ρ.o r]) = app (sumN Lv) (ρ.o r) := by
    rw [sumN_append_dec hsM hpM, sumN_singleton (hsM _ (by simp))]
  have hoN : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (omid M r L ρ) m))
      (ρ'.o r)) z := by
    rw [o_cl_loc hCN hgN (by rw [hσvg]; exact hG.ot_v g hgM) hsCL hpN0, hclN]
    simp only [List.map_append, List.map_singleton]
    rw [hLcv, hCmv, hσlast, hsumN, spArg_app, spArg_app, hσvg]
  have hoM : ρ.o g = psi a (spArg a (spArg a z (sumN Lv)) (ρ.o r)) z := by
    rw [o_cl_eq hC hG hgM, hclM]
    simp only [List.map_append, List.map_singleton]
    rw [hsumM, spArg_app]
  have hLs := sumN_dec Lv (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  have hm1' : (∃ k, k + 1 < n ∧ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) → 1 ≤ m := by
    rintro ⟨k, hk, hkc⟩
    have : r + k * L ∈ Cm := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩,
      by simpa using hkc⟩
    rw [hm]; exact List.length_pos_of_mem this
  have hXot : isOT (ρ.o r) = true := hG.ot_o r (by omega)
  rw [hor] at hoM hXot
  have hOld : isOT (psi a (spArg a (spArg a z (sumN Lv)) (psi v (app Y0 one) z)) z) = true := by
    rw [← hoM]; exact hG.ot_o g hgM
  have hBXs : ∀ q ∈ summands (spArg a z (sumN Lv)), psi v (app Y0 one) z ≤ q := by
    apply spArg_summands_ge ⟨v, _, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq
      have := (List.pairwise_append.mp hpM).2.2 q hq (ρ.o r) (by simp)
      rwa [hor] at this
    · simp [summands]
  have hO0 : isOT (psi v Y0 z) = true := by rw [← hOv]; exact hsO.1
  have hOT' : isOT (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (psi v Y0 z) m)) (ρ'.o r)) = true :=
    isOT_spArg a _ _ (isOT_spArg a _ _ (isOT_spArg a _ _ rfl hLs.1) (isOT_mulT hO0 ⟨_, _, rfl⟩ m)) hsLr.1
  have hm : 1 ≤ m := hm1' ⟨0, by omega, by simpa using hrN⟩
  have hX'O : ρ'.o r ≤ psi v Y0 z := by
    have hp1 := List.pairwise_append.mp hpN
    rw [← hOv]
    exact hp1.2.2 (omid M r L ρ) (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
      (ρ'.o r) (by simp)
  have hoN' : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (psi v Y0 z) m)) (ρ'.o r)) z := by
    rw [hoN, hOv]
  obtain ⟨w',hw',hWk,hWC,hcw⟩ := hw
  have hweak := weak_seed hm hOld hXot hO0 hBXs hWk hWC hcw hva
  rw [← hw'] at hweak
  refine ⟨_,_,hoM,hoN',hweak.1,hweak.2.1,?_⟩
  intro U
  exact rclaim_of_same_high hoM hoN' hOld hweak.1 hweak.2.1 hweak.2.2.1

end

#print axioms t0_S1AW_node
#print axioms index_le_of_cntx
#print axioms index_le_of_upg
#print axioms rclaim_of_same_high
#print axioms weak_seed
end Ytosk.T0ArgB
