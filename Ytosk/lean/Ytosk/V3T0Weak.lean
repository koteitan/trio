/-
**t = 0・r = x − 1 で x − 1 が上げを失う場合の g の枠（2026-10-17）。**

r = x − 1 が M では祖先へ上げ、M.take x では上げを失うと（std_a 1 件・std_b 105 件）、M[n] の最後の写しの
o は X′ = ψ_{w′}(0)（w′ = v′(r) < v(r)）で、o(r) = ψ_{v(r)}(Y0 + 1) にも omid = ψ_{v(r)}(Y0) にも ◁ で下がらない
（`s1_core` の仮定 hl が偽）。しかし M[n] の g では omid の写しが m ≥ 1 個あり、
ψ_a(B + omid·m) は ψ_a(B + o(r)) の基本列の項（`t0_frame_*`）なので ◁ で下がる。そこに弱い葉 X′ を足しても、
X′ の成分が X′ 以下か a の成分以下なら（WCS a w′、落とす補題の PV の弱い枝の WCSP）◁ は保たれる
（`lhd_weak_childA`）。これが `s1_core_weak`。
-/
import Ytosk.V3T0F
import Ytosk.V3DropRel

namespace Ytosk

open T

/-- **The core of the `g` frame with a weak last child** (`t = 0`, `r = x − 1`): the children `ψ_v(Y0)` × m
(`m ≥ 1`) and then a weak leaf `ψ_{w′}(0)` (`w′ < v`, the components of `w′` below `Ω_1` or dominated by
`a`) against the single child `ψ_v(Y0 + 1)`. -/
theorem s1_core_weak {a B v Y0 w' : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hW : WkVA w' v) (hWC : WCS a w') (hc' : isOT (psi w' z z) = true) :
    Lhd z (psi a (spArg a (spArg a B (mulT (psi v Y0 z) m)) (psi w' z z)) z)
      (psi a (spArg a B (psi v (app Y0 one) z)) z) := by
  set O := psi v Y0 z with hOdef
  set F := spArg a B (psi v (app Y0 one) z) with hF
  set B' := spArg a B (mulT O m) with hB'
  have hOX : O < psi v (app Y0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  have hnr := no_rw_after (a := a) (B := B) hO hm
  rw [← hOdef, ← hB'] at hnr
  have hB'O : ∀ q ∈ summands B', O ≤ q :=
    spArg_summands_ge ⟨v, Y0, rfl⟩ (mulT O m) B (isOT_mulT hO ⟨_, _, rfl⟩ m)
      (fun q hq => by rw [summands_mulT ⟨_, _, rfl⟩ m q hq])
      (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
  have hX'O : psi w' z z < O := psi_lt_psi_z_iff.mpr (Or.inl hW.1)
  have hB'X : ∀ q ∈ summands B', psi w' z z ≤ q := fun q hq => le_trans (le_of_lt hX'O) (hB'O q hq)
  -- the fundamental-sequence terms `ψ_a(B + O·k)`
  have hArg : F ≠ z := by
    intro h
    have := lt_spArg a (b := B) hX (by simp)
    rw [hF] at h; rw [h] at this; exact T.not_lt_z _ this
  have hfs : ∀ n, 1 ≤ n → ∃ k, psi a (spArg a B (mulT O n)) z = fs (psi a F z) (natT k) := by
    intro n hn
    by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
    · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
      · refine ⟨n - 1, ?_⟩
        exact (t0_frame_swallow (n := n) hn hX hO htr hbad.1 hbad.2).symm
      · exact ⟨n, (t0_frame_trig (n := n) hn hOld hX hO htr hbad).symm⟩
    · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
        have h1 := isOT_arg hOld
        rw [hF, spArg_single] at h1; unfold step at h1
        rw [if_neg htr, add_eq_app_of_ge ⟨_, _, rfl⟩ _ hBX] at h1
        exact h1
      exact ⟨n, (t0_frame_notrig n hXapp htr hBX).symm⟩
  have hlfs : ∀ n, 1 ≤ n → Lhd z (psi a (spArg a B (mulT O n)) z) (psi a F z) := by
    intro n hn
    obtain ⟨k, hk⟩ := hfs n hn
    rw [hk]; exact lhd_natT_z (lhd_fs hOld (validLt_natT hArg k))
  have hl : Lhd z (psi a B' z) (psi a F z) := hlfs m hm
  -- `B′ + X′ < B′ + O = B + O·(m + 1) < F`
  have hMid : spArg a B (mulT O (m + 1)) = step a B' v Y0 z := by
    rw [mulT_succ', spArg_app, hOdef, spArg_single]
  have hlt1 : app B' (psi w' z z) < step a B' v Y0 z := leaf_lt_step hO hB'O hX'O
  have hlt2 : step a B' v Y0 z < F := by
    have h := (hlfs (m + 1) (by omega)).1
    rw [hMid] at h
    rcases psi_lt_psi_z_iff.mp h with h' | ⟨_, h'⟩
    · exact absurd h' (lt_irrefl' _)
    · exact h'
  have hsp : spArg a B' (psi w' z z) = app B' (psi w' z z) := by
    rw [spArg_single, step_leaf]; exact add_eq_app_of_ge ⟨w', z, rfl⟩ B' hB'X
  rw [hsp]
  exact lhd_weak_childA hl (by simp)
    (fun u hu g hg => (self_small_weakA hWC hW.2.1 u hu g hg).imp
      (fun h => le_trans h (le_app_of_ge B' hB'X)) id) (lt_trans hlt1 hlt2)

/-- **The drop at a column with a counted child**: `o′(i) ◁ o(i)`, or `o′(i)` is a weak leaf `ψ_{w′}(0)` with
`w′ < v(i)` and the components of `w′` dominated by the parent's subscript (the weak branch of the drop lemma). -/
theorem po_lhd_or_weak {M : Mat} {x : Nat} {ρ ρ' : Valn} {i p : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hiM : i < M.length) (hix : i < x)
    (hPO : PO ρ ρ' i) (hPV : PV M ρ ρ' i) (hp : par M 0 i = some p) (hnz : ∀ w, ρ.o i ≠ psi w z z)
    (hlt : ρ'.o i < ρ.o i) :
    Lhd z (ρ'.o i) (ρ.o i) ∨
      CntX M ρ i ∧ ∃ w', ρ'.o i = psi w' z z ∧ WkVA w' (ρ.v i) ∧ WCS (ρ.v p) w' ∧ isOT (psi w' z z) = true := by
  rcases hPO.1 with h | ⟨⟨w', w, X, h1, h2, hW⟩, hw | hnl⟩
  · rcases h with h | h
    · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
    · exact Or.inl h
  · obtain ⟨w0, hw0⟩ := hw
    exact absurd hw0 (hnz w0)
  · rcases hPV.1 with hv | ⟨hWv, hWC, hCX⟩
    · exact absurd hv hnl
    · right
      have hiT : i < (M.take x).length := by rw [List.length_take]; omega
      obtain ⟨y0, hy0⟩ := o_psi_sub hC' hiT
      rw [sf_ot hPV.2] at hy0
      have hw'v : w' = ρ'.v i := by
        rw [h1] at hy0; simp only [psi.injEq] at hy0; exact hy0.1
      subst hw'v
      exact ⟨hCX, _, h1, hWv, hWC.wcs hp, by rw [← h1]; exact hPO.2.1⟩

/-- **The drop at the parent `r` of a `t = 0` column `x`, outside the weak case**: `r ≠ x − 1` (no absorption
needed) or the parent of `x − 1` is a bump child (the strong absorption from `UpgAbsXW`). -/
theorem lhd_t0_of {M : Mat} {x : Nat} {ρ ρ' : Valn} {r : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrM : r < M.length) (hPO : PO ρ ρ' r) (hPV : PV M ρ ρ' r)
    (hnz : ∀ w, ρ.o r ≠ psi w z z) (hlt : ρ'.o r < ρ.o r) (h : r ≠ x - 1 ∨ ¬ NBPar M (x - 1))
    (h3 : NoBad3 M ρ) :
    Lhd z (ρ'.o r) (ρ.o r) := by
  have hE : LhdE (ρ'.o r) (ρ.o r) ∨ (WkOA (ρ'.o r) (ρ.o r) ∧ ∃ w, ρ.o r = psi w z z) := by
    by_cases hr : r = x - 1
    · have hnb := h.resolve_left (fun h' => h' hr)
      exact PO.zero_of_strong hx (hUA.toX_xm1 hx1 (by rw [← hr]; exact hp) hnb) hC hG hrM hPO hPV
    · exact PO.zero_of_ne (by omega) hC hG hrM hPO hPV h3
  rcases hE with hE | ⟨_, w, hw⟩
  · exact lhd_of_lhdE_lt hE hlt
  · exact absurd hw (hnz w)

/-- **The drop at the parent `r` of a `t = 0` column `x`**: `◁`, or (when `r = x − 1` and its parent `g` is
not a bump child) a weak leaf whose components are dominated by `v(g)`. -/
theorem lhd_or_weak_t0 {M : Mat} {x : Nat} {ρ ρ' : Valn} {r g : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r) (hg : par M 0 r = some g)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hrM : r < M.length)
    (hPO : PO ρ ρ' r) (hPV : PV M ρ ρ' r) (hnz : ∀ w, ρ.o r ≠ psi w z z) (hlt : ρ'.o r < ρ.o r)
    (h3 : NoBad3 M ρ) :
    Lhd z (ρ'.o r) (ρ.o r) ∨
      r = x - 1 ∧ NBPar M (x - 1) ∧ CntX M ρ r ∧
        ∃ w', ρ'.o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ WCS (ρ.v g) w' ∧ isOT (psi w' z z) = true := by
  by_cases h : r ≠ x - 1 ∨ ¬ NBPar M (x - 1)
  · exact Or.inl (lhd_t0_of hx hUA hx1 hp hC hG hrM hPO hPV hnz hlt h h3)
  · have hr : r = x - 1 := by by_contra h'; exact h (Or.inl h')
    have hnb : NBPar M (x - 1) := by by_contra h'; exact h (Or.inr h')
    rcases po_lhd_or_weak hC hG hC' hrM (by have := par_lt M 0 x r hp; omega) hPO hPV hg hnz hlt with
      h' | ⟨hCX, hw⟩
    · exact Or.inl h'
    · exact Or.inr ⟨hr, hnb, hCX, hw⟩

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

omit hSD hZ1 hUAT hUAB he1 hC hG hCN hGN in
/-- **The first copy root `r` counts at `g` in `M[n]`** when it does in `M` and its row 2 is `0`
(then nothing upgrades to it). -/
theorem counted_first0 {g : Nat} (hg : par M 0 r = some g) (hc : Counted M g r) (he2r : entry M 2 r = 0) :
    Counted (TRIO.gexp M r L 0 0 n) g r := by
  have hgr : g < r := par_lt M 0 r g hg
  have hcN : col (TRIO.gexp M r L 0 0 n) r = col M r := by
    have := col_copy0 hlen (k := 0) (q := 0) (by omega) hL (M := M) (n := n)
    simpa using this
  have hbN : bump (TRIO.gexp M r L 0 0 n) g = bump M g := bump_pre0 hlen hL hp hn (by omega)
  refine ⟨by rw [hcN, hbN]; exact hc.1, ?_⟩
  rintro ⟨hU, _⟩
  unfold isUpg at hU
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hU
  have h1 := upg_target_e2 (of_decide_eq_true hk)
  have h2 : entry (TRIO.gexp M r L 0 0 n) 2 r = entry M 2 r := by
    rw [col_eq_entries, col_eq_entries] at hcN; simp only [Prod.mk.injEq] at hcN; exact hcN.2.2
  omega

/-- **Seed S1 with a weak last copy** (`r = x − 1` lost its upgrade in `M.take x`): `o′(r) = ψ_{w′}(0)`,
`w′ < v(r)`, the components of `w′` dominated at `g`; `r` itself counts at `g` in `N` (a middle copy). -/
theorem t0_S1W {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hF : FrameClosed M ρ)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hw : ∃ w', ρ'.o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ WCS (ρ.v g) w' ∧ isOT (psi w' z z) = true)
    (hrN : Counted (TRIO.gexp M r L 0 0 n) g r) :
    Lhd z (σ.o g) (ρ.o g) := by
  obtain ⟨w', hw', hWk, hWC, hwot⟩ := hw
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
  have hLcv : Lc.map σ.o = Lc.map ρ.o := by
    apply List.map_congr_left
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  have hsN := cl_valsT hCN hGN (i := g)
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
    rw [← hσmid 0 (by omega)]; simpa using single_oT hCN hGN (show r + 0 * L < _ by rw [hlN]; omega)
  have hsumN : sumN (Lv ++ List.replicate m (omid M r L ρ) ++ [ρ'.o r]) =
      app (app (sumN Lv) (mulT (omid M r L ρ) m)) (ρ'.o r) := by
    have hp1 := List.pairwise_append.mp hpN
    rw [sumN_append_dec hsN hpN, sumN_append_dec (fun t ht => hsN t (List.mem_append_left _ ht)) hp1.1,
      sumN_replicate hsO m, sumN_singleton (hsN _ (by simp))]
  have hsumM : sumN (Lv ++ [ρ.o r]) = app (sumN Lv) (ρ.o r) := by
    rw [sumN_append_dec hsM hpM, sumN_singleton (hsM _ (by simp))]
  have hoN : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (omid M r L ρ) m))
      (ρ'.o r)) z := by
    rw [o_cl_eqT hCN hGN hgN hpN0, hclN]
    simp only [List.map_append, List.map_singleton]
    rw [hLcv, hCmv, hσlast, hsumN, spArg_app, spArg_app, hσvg]
  have hoM : ρ.o g = psi a (spArg a (spArg a z (sumN Lv)) (ρ.o r)) z := by
    rw [o_cl_eq hC hG hgM, hclM]
    simp only [List.map_append, List.map_singleton]
    rw [hsumM, spArg_app]
  have hLs := sumN_dec Lv (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  rw [hoN, hoM, hOv]
  have hXot : isOT (ρ.o r) = true := hG.ot_o r (by omega)
  rw [hor] at hoM hXot ⊢
  have hOld : isOT (psi a (spArg a (spArg a z (sumN Lv)) (psi v (app Y0 one) z)) z) = true := by
    rw [← hoM]; exact hG.ot_o g hgM
  have hm1 : 1 ≤ m := by
    have hr0 : r + 0 * L = r := by simp
    have hmem : r ∈ Cm := by
      rw [hCmdef, List.mem_filter]
      refine ⟨List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp [hfdef]⟩, by simpa using hrN⟩
    exact List.length_pos_of_mem hmem
  rw [hw']
  apply s1_core_weak hm1 hOld hXot (by rw [← hOv]; exact hsO.1) _ hWk hWC hwot
  apply spArg_summands_ge ⟨v, _, rfl⟩ (sumN Lv) z hLs.1
  · rw [hLs.2]; intro q hq
    have := (List.pairwise_append.mp hpM).2.2 q hq (ρ.o r) (by simp)
    rwa [hor] at this
  · simp [summands]

end

end Ytosk
