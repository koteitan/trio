/-
**3 行・t = 0: T0Shape の (iii) を構造から。**

(iii): g = P_0(r)、M.take x の o′(r) = ψ_{s′}(y′) で s′ ≠ v(r)、v(r) ≥ v(g) + 1 なら s′ ≥ v(g) + 1。

- P_1(r) = g のとき: v(g) は 1 列落としで変わらない（v が変わる列は x より前の列の P_1 にならない、`TopC`）。
  s′ = v′(r) > v′(g) = v(g)。
- P_1(r) ≠ g のとき: v(r) ≤ v(g) を示す（仮定と矛盾）。v(r) が変わる理由は「r = x − 1 の上げが祖先 k に
  向かう」だけ（ほかは `TopC`・`no_anc_upg`・`BumpLeaf` で矛盾）。このとき v(r) = v(k) で、k から g への道の
  列 y はどれも v(k) ≤ v(y)（`upg_anc_spine`: y の行 1 が k より大きければ P_1 の鎖、等しく行 2 が 0 なら
  upg(y) = k、行 2 が 1 なら y は親の上げの子で、k まで遡ると UAB に反する）。
-/
import Ytosk.V3ExpT0
import Ytosk.V3InvJ
import Ytosk.V3ExpT2C
import Ytosk.V3ValT1R

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `par1_facts`（V3Spine）の写し（V3Spine の import は V3GroupA と衝突するので避ける）。 -/
theorem t0s_par1_facts {M : Mat} {i m : Nat} (hm : par M 1 i = some m) :
    Anc0 M m i ∧ m < i ∧ entry M 1 m < entry M 1 i ∧
      ∀ w, Anc0 M m w → Anc0 M w i → w ≠ m → w ≠ i → entry M 1 i ≤ entry M 1 w := by
  obtain ⟨hmem, hlt, hmax⟩ := (par1_some_iff M i m).mp hm
  refine ⟨anc0_of_mem_ancL hmem, mem_ancL_lt hmem, hlt, fun w h1 h2 h3 h4 => hmax w (mem_ancL_of_anc h2 h4) ?_⟩
  have := h1.le; omega

/-- `upg_facts`（V3Spine）の写し。 -/
theorem t0s_upg_facts {M : Mat} {i k : Nat} (hk : upg M i = some k) :
    ∃ m, par M 1 i = some m ∧ par M 0 k = some m ∧ entry M 1 k = entry M 1 i ∧
      (k = i + 1 ∨ (Anc0 M k i ∧ k < i)) := by
  obtain ⟨m, hm1, hm2, hcol, hcase⟩ := upg_spec hk
  refine ⟨m, hm1, par0_of_upgshape hm2 ?_, ?_, hcase⟩
  · have : entry M 0 k = (col M k).1 := rfl; rw [this, hcol]
  · have : entry M 1 k = (col M k).2.1 := rfl; rw [this, hcol]

/-- **The upgrade to an ancestor target, from the shape.** -/
theorem upg_of_anc_target {M : Mat} {y k m : Nat} (hyM : y + 1 < M.length) (h1 : entry M 1 y ≠ 0)
    (h2 : entry M 2 y = 0) (hm : par M 1 y = some m) (hmk : par M 1 k = some m)
    (hcol : col M k = (entry M 0 m + 1, entry M 1 y, entry M 2 m + 1)) (hky : Anc0 M k y) (hne : k ≠ y)
    (hnext : entry M 0 m + 1 < entry M 0 (y + 1)) : upg M y = some k := by
  have hek : entry M 0 k = entry M 0 m + 1 := e0_of_col hcol
  unfold upg
  rw [if_neg (by omega), hm]
  dsimp only
  rw [if_neg (fun h => by have := e0_of_col h.2; omega), upgClimb_find, find?_dec (ancL_pairwise M y)]
  refine ⟨mem_ancL_of_anc hky hne, ?_, ?_⟩
  · simp only [decide_eq_true_eq]
    exact ⟨hmk, hcol, by omega⟩
  · intro w hw hkw
    simp only [decide_eq_false_iff_not, not_and]
    intro _ hcw
    have hA : Anc0 M k w := anc_between hky w (by omega) (le_of_lt (mem_ancL_lt hw))
    have := anc0_e0_lt hA (by omega)
    have := e0_of_col hcw
    omega

/-- **Along the path from an ancestor upgrade target `k = upg(r)` to `r`**: every column `y` (not `r`) has
`v(k) ≤ v(y)`, and no column other than `k` has the row 1 of `k` with row 2 equal to `1`. -/
theorem upg_anc_spine {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hR0 : R0P M) (hZ2 : Z2 M) (hUAB : UAB M) (hBE : BumpE2 M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk)
    {r k : Nat} (hrM : r < M.length) (hu : upg M r = some k) (hk : Anc0 M k r) (hkr : k < r) :
    ∀ y, Anc0 M k y → Anc0 M y r → y ≠ r →
      (y ≠ k → entry M 1 y = entry M 1 k → entry M 2 y = 1 → False) ∧ ρ.v k ≤ ρ.v y := by
  obtain ⟨m, hm1, hmk, hcol, _⟩ := upg_spec hu
  have hpf := t0s_par1_facts hm1
  have hpk := t0s_par1_facts hmk
  have hek1 : entry M 1 k = entry M 1 r := e1_of_col hcol
  have hek0 : entry M 0 k = entry M 0 m + 1 := e0_of_col hcol
  have hek2 : entry M 2 k = entry M 2 m + 1 := e2_of_col hcol
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hky hyr hyr'
  by_cases hyk : y = k
  · subst hyk; exact ⟨fun h => absurd rfl h, le_refl _⟩
  have hkyl : k < y := lt_of_le_of_ne hky.le (Ne.symm hyk)
  have hyrl : y < r := lt_of_le_of_ne hyr.le hyr'
  have hmy : Anc0 M m y := Anc0.trans hpk.1 hky
  have hym : y ≠ m := by have := hpk.2.1; omega
  have he1y : entry M 1 r ≤ entry M 1 y := hpf.2.2.2 y hmy hyr hym hyr'
  rcases Nat.lt_or_ge (entry M 1 k) (entry M 1 y) with hlt | hge
  · -- a larger row 1: through `P_1`
    obtain ⟨m', hm', hkm', hAkm'⟩ := par1_near hky (Ne.symm hyk) hlt
    have hm'y := t0s_par1_facts hm'
    have hm'r : Anc0 M m' r := Anc0.trans hm'y.1 hyr
    have hIH := (ih m' hm'y.2.1 hAkm' hm'r (by have := hm'y.2.1; omega)).2
    have hlt' := v_par1_lt hC hG hR (rk false y) y m' (le_refl _) (by omega) (by omega) hm'
    exact ⟨fun _ h => by omega, le_of_lt (lt_of_le_of_lt hIH hlt')⟩
  · have heq : entry M 1 y = entry M 1 k := by omega
    have h2y := hZ2 y
    rcases Nat.lt_or_ge (entry M 2 y) 1 with h20 | h21
    · -- row 2 is `0`: `upg(y) = k`
      have h20 : entry M 2 y = 0 := by omega
      have hy1 : entry M 1 y ≠ 0 := by have := hpf.2.2.1; omega
      have hm1y : par M 1 y = some m := by
        rw [par1_some_iff]
        refine ⟨mem_ancL_of_anc hmy (Ne.symm hym), by have := hpf.2.2.1; omega, fun w hw hmw => ?_⟩
        have hwy := anc0_of_mem_ancL hw
        have hwyl := mem_ancL_lt hw
        have := hpf.2.2.2 w (anc_between hmy w (le_of_lt hmw) (le_of_lt hwyl)) (Anc0.trans hwy hyr)
          (by omega) (by omega)
        omega
      have hy0 : entry M 0 (y + 1) = entry M 0 y + 1 := hR0 _ _ (child_succ hyr hyr')
      have hky0 := anc0_e0_lt hky (Ne.symm hyk)
      have hu' : upg M y = some k :=
        upg_of_anc_target (by omega) hy1 h20 hm1y hmk (by rw [hcol, heq, hek1]) hky (Ne.symm hyk)
          (by omega)
      have hv := v_upg_eq hC (by omega) hy1 h20 hu' (by rw [hm1y]; exact hG.ot_v m (by have := hpf.2.1; omega))
        (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
      exact ⟨fun _ _ h => by omega, by rw [hv]⟩
    · -- row 2 is `1`: `y` is the bump child of its parent, back to `k`
      exfalso
      have h21' : entry M 2 y = 1 := by omega
      obtain ⟨y', hpy, hky'⟩ : ∃ y', par M 0 y = some y' ∧ Anc0 M k y' := by
        cases hky with
        | refl => exact absurd rfl hyk
        | step hp ha => exact ⟨_, hp, ha⟩
      have hy'y : y' < y := par_lt M 0 y y' hpy
      have hy'r : Anc0 M y' r := Anc0.trans (Anc0.step hpy (Anc0.refl y')) hyr
      have hJy := hJ y y' (by omega) hpy
      have he1y' : entry M 1 r ≤ entry M 1 y' := by
        by_cases hy'k : y' = k
        · rw [hy'k, hek1]
        · exact hpf.2.2.2 y' (Anc0.trans hpk.1 hky') hy'r (by have := hky'.le; have := hpk.2.1; omega)
            (by omega)
      have hcolb : col M y = bump M y' := by
        rw [col_eq_entries, hR0 y y' hpy, h21']
        unfold bump; congr 2; omega
      have hyc : y ∈ children M y' := mem_children_iff.mpr ⟨by omega, hpy⟩
      by_cases hy'k : y' = k
      · subst hy'k
        exact hUAB r y' hu (by omega) y hyc hcolb hyr
      · have h2y' := hBE y' y hyc hcolb
        exact (ih y' hy'y hky' hy'r (by omega)).1 hy'k (by omega) h2y'

/-- The cases of a changed `v` in the one-column drop. -/
theorem chgX_false_cases {M : Mat} {x : Nat} {b : Bool} {d : Nat} (h : ChgX M x b d) (hb : b = false) :
    (d = x - 1 ∧ upg M (x - 1) ≠ none) ∨
    (entry M 1 d ≠ 0 ∧ x ∈ children M d ∧ col M x = bump M d) ∨
    (∃ m, par M 1 d = some m ∧ ChgX M x false m) ∨
    (∃ k, upg M d = some k ∧ ChgX M x false k) ∨
    (∃ j, entry M 1 d ≠ 0 ∧ entry M 2 d ≠ 0 ∧ j ∈ children M d ∧ col M j = bump M d) := by
  cases h with
  | leaf => cases hb
  | supg hne => exact Or.inl ⟨rfl, hne⟩
  | scnt => cases hb
  | snb h1 _ hx hb' => exact Or.inr (Or.inl ⟨h1, hx, hb'⟩)
  | ochild => cases hb
  | ov => cases hb
  | vpar _ hm hc => exact Or.inr (Or.inr (Or.inl ⟨_, hm, hc⟩))
  | vupg _ _ hu hc => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hu, hc⟩)))
  | vbump h1 h2 hj hjb _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h1, h2, hj, hjb⟩)))

/-- **`T0Shape` (iii)**: a changed subscript of `o′(r)` in `M.take x` stays at least `Ω_{v(g)+1}`. -/
theorem t0_shape3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
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

/-- **`T0Shape` without (iii)**: the residual class facts (i), (ii), (iv). -/
def T0ShapeR : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true) ∧
    (∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) false c →
      par M 1 c ≠ some i →
      entry M 2 c = 0 ∧ upg M c = some (c + 1) ∧ c + 1 < r ∧
      (∃ j ∈ children M (c + 1), col M j = bump M (c + 1)) ∧
      par M 1 i = par M 1 c ∧ entry M 2 i = 1 ∧ ∀ d ∈ children M i, col M d ≠ bump M i) ∧
    (∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true))

theorem t0Shape_of (h : T0ShapeR) : T0Shape := by
  intro M ρ rk r L hM hS I R hlen hL hp he1
  obtain ⟨h1, h2, h4⟩ := h M ρ rk r L hM hS I R hlen hL hp he1
  exact ⟨h1, h2, t0_shape3 hM hS I R hlen hL hp he1, h4⟩

/-- **`hExp` for `t = 0`** with `T0Shape` (iii) proved. -/
theorem hExp_t0_mainR
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hS : T0ShapeR) (hRest : T0Rest) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  hExp_t0_mainC hLast (t0Shape_of hS) hRest hC1 hC1W hCT

end Ytosk
