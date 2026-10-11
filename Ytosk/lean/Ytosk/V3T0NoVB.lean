/-
**3 行・t = 0: T0Shape の (iv) と VSmallF の g の残りを、1 つの構造の性質 NoVB に帰着。**

NoVB: t = 0（x = r + L、P_0(x) = r、e1(x) = 0）で e2(r) ≠ 0 なら、1 列落としで v(r) は変わらない。
実測: C′・deep2・deep3 の 35482 件で例外 0。今の構造の不変条件（S1・S4・PH3c を含む）からは出ない
（非標準形 (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(4,0,0) が反例、FC3 だけが偽）。

- (iv)（`t0_iv_of_noVB`）: 中間の写しの根がどれも数えられないなら、最初の写しの根 r は N で上げの先かつ topped。
  上げの先は行 2 が 1 以上なので NoVB で v′(r) = v(r)。topped (M.take x) r から、r の数える子は 1 列落としで
  変わらない（変わる子は ICC で次の列が r の上げの子になり行 2 が 2、または x − 1 の祖先で最後の子 = r の上げの子）。
  よって o′(r) = omid。
- VSmallF の g の残り（`t0VSResG_of_noVB`）: v′(r) ≠ v(r) なら NoVB で e2(r) = 0、r は上げの先にならないので
  M.take x でも数えられ、g の数える子の並びは M と同じ。落とす補題の VSmallNew がちょうど残りの形。
-/
import Ytosk.V3T0VS

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **NoVB**: at `t = 0`, a root `r` with row 2 nonzero keeps its `v` in the one-column drop. -/
def T0NoVB : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    entry M 2 r ≠ 0 → (drop1 M (r + L) rk).v r = ρ.v r

/-- A counted child of `r` (below `x`) keeps its counted status in `M.take x` when row 2 of `r` is nonzero. -/
theorem counted_take_r {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hR0 : R0P M) (hZ2 : Z2 M)
    (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M) (hp : par M 0 (r + L) = some r)
    (h2r : entry M 2 r ≠ 0) {c : Nat} (hc : c ∈ children M r) (hcx : c < r + L) :
    Counted (M.take (r + L)) r c ↔ Counted M r c := by
  by_contra h
  have hcr := (mem_children hc).1
  rcases cnt_change (show r + L + 1 = M.length from hlen) (by omega) hcx h with
    hx | hu
  · have := (mem_children_iff.mp hx).2
    rw [hp] at this; cases this; omega
  · obtain ⟨m, hm1, hm0, _, _⟩ := upg_facts hu
    obtain ⟨m', hm1', _, hcol, _⟩ := upg_spec hu
    rw [hm1] at hm1'; cases hm1'
    rw [(mem_children_iff.mp hc).2] at hm0; cases hm0
    have := e2_of_col hcol
    have := hZ2 c
    omega

/-- **`T0Shape` (iv) from NoVB.** -/
theorem t0_iv_of_noVB (hN : T0NoVB) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hlen : r + L + 1 = M.length)
    (hL : 0 < L) (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) :
    ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      (drop1 M (r + L) rk).o r = omid M r L ρ := by
  classical
  intro n hn2 g hg hgc hno
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hgr : g < r := par_lt M 0 r g hg
  -- the first copy root is an upgrade target and topped in `N`
  have hnc : ¬ Counted (TRIO.gexp M r L 0 0 n) g r := by
    have := hno 0 (by omega); simpa using this
  have hcolN : col (TRIO.gexp M r L 0 0 n) r ≠ bump (TRIO.gexp M r L 0 0 n) g := by
    rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hgc.1
  have hUT : isUpg (TRIO.gexp M r L 0 0 n) r = true ∧ topped (TRIO.gexp M r L 0 0 n) r = true := by
    by_contra h; exact hnc ⟨hcolN, h⟩
  have htop : topped (M.take (r + L)) r = true := by
    have := topped_copy0 hlen hL hp hn (k := 0) (q := 0) (by omega) hL
    simp only [Nat.zero_mul, Nat.add_zero] at this
    rw [← this]; exact hUT.2
  have h2r : entry M 2 r ≠ 0 := by
    obtain ⟨w, _, hw⟩ := List.any_eq_true.mp hUT.1
    have := upg_target_e2 (of_decide_eq_true hw)
    rw [entry_pre0 hlen hn 2 (by omega)] at this
    omega
  -- the drop
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hv : ρ'.v r = ρ.v r := hN M ρ rk r L hM hS I R hlen hL hp he1 h2r
  -- the counted children of `r` keep their values
  have hval : ∀ c ∈ children M r, c < r + L → Counted M r c → ρ'.o c = ρ.o c := by
    intro c hc hcx hcc
    apply (hoff c hcx).1
    intro hch
    have hcr := (mem_children hc).1
    have hcpr : par M 0 c = some r := (mem_children_iff.mp hc).2
    by_cases hA : Anc0 M c (r + L - 1)
    · -- `c` is the last child of `r` in `M.take x`, the bump child (topped)
      have hcT : c ∈ children (M.take (r + L)) r := by
        rw [children_take, List.mem_filter]; exact ⟨hc, by simpa using hcx⟩
      have hmax : ∀ d ∈ children (M.take (r + L)) r, d ≤ c := by
        intro d hd
        rw [children_take, List.mem_filter] at hd
        have hdx : d < r + L := by simpa using hd.2
        have hdpr : par M 0 d = some r := (mem_children_iff.mp hd.1).2
        by_contra hlt
        have hAd : Anc0 M c d := anc_between hA d (by omega) (by omega)
        have := (anc0_par hAd (by omega) hdpr).le
        omega
      have hsplit := split_last_max _ _ (children_sorted (M.take (r + L)) r) hcT hmax
      have htop' := htop
      unfold topped at htop'
      rw [hsplit] at htop'
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, decide_eq_true_eq] at htop'
      rw [col_take M hcx, bump_take M (show r < r + L by omega)] at htop'
      exact hcc.1 htop'
    · obtain ⟨c', hNc, hc'x, hu, _⟩ := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hch).2 c hcx
        (Anc0.refl c) hA
      obtain ⟨m, hm1, hm0, _, _⟩ := upg_facts hu
      obtain ⟨m', hm1', _, hcol, _⟩ := upg_spec hu
      rw [hm1] at hm1'; cases hm1'
      obtain ⟨_, hmr⟩ := next_parent hcpr hp hcx hNc hm0
      subst hmr
      have := e2_of_col hcol
      have := I.z2 c'
      omega
  -- the two values
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  rw [(hC1 r hrT).1]
  unfold oRhs omid
  rw [hv, children_take]
  congr 3
  apply List.map_congr_left
  intro c hc
  rw [List.mem_filter] at hc
  have hcx : c < r + L := by simpa using hc.2
  rw [cnt_eq_ite, cnt_eq_ite]
  have hiff := counted_take_r hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hp h2r hc.1 hcx
  by_cases hcc : Counted M r c
  · rw [if_pos (hiff.mpr hcc), if_pos hcc, hval c hc.1 hcx hcc]
  · rw [if_neg (fun h => hcc (hiff.mp h)), if_neg hcc]

/-- **The residual (G) of `VSmallF` from NoVB** (with `VSmallNew` of the drop). -/
theorem t0VSResG_of_noVB (hN : T0NoVB) : T0VSResG := by
  classical
  intro M ρ rk r L n σ rkN hctx g hg hgc Lc hCL hv g' hg'
  obtain ⟨hM, hS, I, R, hlen, hL, hp, he1, _⟩ := id hctx
  have hx : r + L + 1 = M.length := hlen
  have hgr : g < r := par_lt M 0 r g hg
  have h2r : entry M 2 r = 0 := by
    by_contra h; exact hv (hN M ρ rk r L hM hS I R hlen hL hp he1 h)
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  -- the counted children of `g` are the same in `M.take x`
  have hCLT : CL (M.take (r + L)) g = Lc ++ [r] := by
    rw [← hCL]
    unfold CL
    rw [children_take_ne_r hlen hL hp (by omega)]
    apply List.filter_congr
    intro d hd
    have hdr : d ≤ r := children_g_le hlen hL hp hg hd
    simp only [decide_eq_decide]
    by_cases hdr' : d = r
    · subst hdr'
      constructor
      · intro _; exact hgc
      · intro hc
        refine ⟨by rw [col_take M (by omega), bump_take M (by omega)]; exact hc.1, ?_⟩
        rintro ⟨hu, _⟩
        obtain ⟨w, _, hw⟩ := List.any_eq_true.mp hu
        have := upg_target_e2 (of_decide_eq_true hw)
        rw [entry_take M 2 (by omega)] at this
        omega
    · by_contra h
      rcases cnt_change (show r + L + 1 = M.length from hlen) (by omega)
          (by omega) h with hxd | hu
      · have := (mem_children_iff.mp hxd).2
        rw [hp] at this; cases this; exact hdr' rfl
      · obtain ⟨_, _, _, _, hcase⟩ := upg_facts hu
        rcases hcase with h1 | ⟨hA, _⟩
        · omega
        · have hdr2 : d < r := by omega
          have hAdr : Anc0 M d r := anc_between hA r (by omega) (by omega)
          have hdg := anc0_par hAdr (by omega) hg
          have := hdg.le
          have := (mem_children hd).1
          omega
  exact hDr.vst g (by omega) Lc r hCLT hv g' hg'

/-- **The class residuals without (iv)**: (i) at nonzero states and (ii). -/
def T0ShapeR3 : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true) ∧
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      σ.v c ≠ ρ.v c → par M 1 c ≠ some i → ¬ psi (ρ.v c) z z < psi (succ (ρ.v i)) z z →
      ¬ psi (σ.v c) z z < psi (succ (ρ.v i)) z z)

theorem t0ShapeR2_of (hN : T0NoVB) (h : T0ShapeR3) : T0ShapeR2 := by
  intro M ρ rk r L hM hS I R hlen hL hp he1
  obtain ⟨h1, h2⟩ := h M ρ rk r L hM hS I R hlen hL hp he1
  exact ⟨h1, h2, t0_iv_of_noVB hN hM hS I R hlen hL hp he1⟩

/-- `T0RestH` with `VSmallF` reduced to the residual `T0VSResD`. -/
structure T0RestH2 : Prop where
  vsD : T0VSResD
  ad : T0Field AbsD
  au : T0Field AbsU
  tplo : T0Field TPLo
  auw : T0Field AbsUW
  tplon : T0Field TPLoN
  adn : T0Field AbsDN
  tplow : T0Field TPLoW
  adw : T0Field AbsDW
  res : T0Res3H

theorem T0RestH2.toRestH (hN : T0NoVB) (h : T0RestH2) : T0RestH :=
  ⟨t0_vsmallF h.vsD (t0VSResG_of_noVB hN), h.ad, h.au, h.tplo, h.auw, h.tplon, h.adn, h.tplow, h.adw, h.res⟩

/-- **`hExp` for `t = 0`, the current residuals**: the structural fact `T0NoVB`, the class residuals
`T0ShapeR3` ((i) at nonzero states, (ii)), `T0RestH2` (`T0VSResD`, the other value fields, `Res3H`), and the
shadow frames `T0RWResC`. -/
theorem hExp_t0_mainN
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hN : T0NoVB) (hS : T0ShapeR3) (hRest : T0RestH2) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN :=
  hExp_t0_mainH hLast (t0ShapeR2_of hN hS) (hRest.toRestH hN) hC1 hC1W hCT

end Ytosk
