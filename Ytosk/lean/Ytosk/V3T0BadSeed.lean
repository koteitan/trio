/-
**Bad2・t = 0 の種の事実のうち易しい場合（2026-10-25）。**

- `T0NCtx`・`t0NCtx_of`: `N = M[n]` の任意の評価 σ についての文脈（写しの値、`o′(r) < o(r)` など）を、落とす補題の
  結論 `T0DropF` から出す（`t0_otdG` の前半の写し）。
- `bad2_t0_cases`: Bad2・t = 0 では `r = P_0(x)` は Bad2 の `g`・`p`・`x − 1` のどれか。
- `r = x − 1` の S1 の節（`t0_S1N_x1`、旧の補題 `po_lhd_or_weak`・`counted_first0`・`index_le_of_cntx`・`t0_S1N_of`）と
  S2（前件が偽: `x − 1` は上げを持つので行 2 = 0、bump 子は行 2 = 1）、`r = p` の S1 の節（前件が偽: bump 子は数えない）。
- 残り `T0BadSeedsH`: `r = g` の S1 の節、`r ≠ x − 1` の S2、S3。`t0BadSeeds_of` で `T0BadSeeds`。
-/
import Ytosk.V3T0BadOut

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The context of a valuation of `N = M[n]`** (`t = 0`): the drop `M.take x`, the values of `N` before `r` and
on the copies, and the drop at `r`. -/
structure T0NCtx (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat) (σ : Valn) : Prop where
  C1 : Cons (M.take (r + L)) (drop1 M (r + L) rk)
  GT : Good3 (M.take (r + L)) (drop1 M (r + L) rk)
  offD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧ (¬ DepX M (r + L) false i → σ.v i = ρ.v i)
  σB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
    σ.o i = (tauN r L n ρ (drop1 M (r + L) rk) (omid M r L ρ)).o i ∧
    σ.v i = (tauN r L n ρ (drop1 M (r + L) rk) (omid M r L ρ)).v i
  σmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ
  σlast : σ.o (r + (n - 1) * L) = (drop1 M (r + L) rk).o r
  lt : (drop1 M (r + L) rk).o r < ρ.o r
  le : (drop1 M (r + L) rk).o r ≤ omid M r L ρ
  y' : ∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r → y' = z
  nz : ∀ w, ρ.o r ≠ psi w z z

theorem t0NCtx_of {M : Mat} {ρ : Valn} {rkM : Bool → Nat → Nat} {r L : Nat} (I : Inv3C M ρ rkM)
    (D : T0DropF M ρ rkM) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {n : Nat} (hn2 : 2 ≤ n) {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) :
    T0NCtx M ρ rkM r L n σ := by
  have hR0 := I.r0p; have hZ2 := I.z2; have hSD := I.sd; have hZ1 := I.z1; have hUAT := I.uat
  have hUAB := I.uab; have hC := I.cons; have hG := I.good; have hRM := I.rank
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDP := D.po
  have hDV := D.vt
  rw [show M.length - 1 = r + L by omega] at hDP hDV
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  set ρ' := drop1 M (r + L) rkM with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hdrop : ∀ k, k < r + L → PO ρ ρ' k ∧ PV M ρ ρ' k := hDP
  have hoff := chg_off (show r + L + 1 = M.length from hlen) hC hG hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' := hDV
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  have hRN := rk_N0 hlen hL hp hn hR0 hZ2 hx2 hn2 hRM
  have hvC := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i :=
    fun i hri hiN => (hvC i hiN).1 (fun h => by omega)
  have hσBv : ∀ i, r ≤ i → i < N.length → σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => (hvC i hiN).2 (fun h => by omega)
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG
  have hlt0 : ρ'.o r < ρ.o r :=
    hD true r (depLike_r hlen hL hp hx2 (depLike_depX M (r + L))) (by omega)
  have hO'le : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := (hdrop r (by omega)).1.2
    have h := hlt0
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
    intro s' y' hs hne
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    have hv'ot := (hdrop r (by omega)).2.2
    rw [sf_ot hv'ot] at hy0
    have hCv : ChgX M (r + L) false r := by
      by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by omega)
    have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
    rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
  have hnzr : ∀ w, ρ.o r ≠ psi w z z := by
    intro w hw
    rw [hor] at hw; simp only [psi.injEq] at hw
    have := lt_app_one (spArg (ρ.v r) z
      (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r))))
    rw [hw.2.1] at this; exact T.not_lt_z _ this
  exact ⟨hC1, hVT.g, hoffD, fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩, hσmid, hσlast, hlt0, hO'le,
    hy', hnzr⟩

/-- **The three positions of `r = P_0(x)`** in a `Bad2` matrix at `t = 0`: `x` lies under `g` (row 2 of `x` is `0`),
so `r` is `g`, `p` or `x − 1`. -/
theorem bad2_t0_cases {M : Mat} {r L : Nat} (hB : Bad2 M) (hlen : r + L + 1 = M.length)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) (hR12 : R12 M) :
    ∃ k p g, upg M (r + L - 1) = some k ∧ par M 0 (r + L - 1) = some p ∧ par M 0 p = some g ∧
      col M p = bump M g ∧ (r = g ∨ r = p ∨ r = r + L - 1) := by
  obtain ⟨⟨k, hu⟩, p, g, hp', hg, hb, hcase⟩ := hB
  have hx : M.length - 1 = r + L := by omega
  have hx2 : M.length - 2 = r + L - 1 := by omega
  rw [hx2] at hu hp'
  rw [hx] at hcase
  have hAg : Anc0 M g (r + L) := by
    rcases hcase with ⟨h | h, _⟩ | ⟨_, h, _⟩
    · exact h
    · exact absurd (hR12 _ he1) h
    · exact absurd he1 h
  refine ⟨k, p, g, hu, hp', hg, hb, ?_⟩
  have hrx := par_lt M 0 _ _ hp
  have hpx := par_lt M 0 _ _ hp'
  have hgp := par_lt M 0 _ _ hg
  have hgr : Anc0 M g r := anc0_par hAg (by omega) hp
  have hrx1 : Anc0 M r (r + L - 1) :=
    anc_xm1 (x := r + L) (by omega) (Anc0.step hp (Anc0.refl r)) hrx
  by_cases h1 : r = r + L - 1
  · exact Or.inr (Or.inr h1)
  have hrp : Anc0 M r p := anc0_par hrx1 h1 hp'
  by_cases h2 : r = p
  · exact Or.inr (Or.inl h2)
  exact Or.inl (anc0_antisymm (anc0_par hrp h2 hg) hgr)

/-- **Seed S1 as a node when `r = x − 1`** (`Bad2`, `t = 0`): the drop at `r` is `◁` or a weak leaf; in the weak case
the first copy root counts at `g` in `N` (row 2 of `r` is `0`: `r` has an upgrade target) and `v(r) ≤ v(g)`
(`index_le_of_cntx`). -/
theorem t0_S1N_x1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3C M ρ rk) (D : T0DropF M ρ rk) (hB : Bad2 M) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) (hrx : r = r + L - 1)
    {n : Nat} (hn2 : 2 ≤ n) {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) :
    ∀ g, par M 0 r = some g → Counted M g r → ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧
      isOT (psi (ρ.v g) X' z) = true ∧ Lhd z (psi (ρ.v g) X' z) (psi (ρ.v g) X z) ∧
      ∀ U : T → Prop, RClaimU U ρ σ g := by
  intro g hg hcnt
  have K := t0NCtx_of I D hlen hL hp he1 hn2 hCN
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDP := D.po
  rw [show M.length - 1 = r + L by omega] at hDP
  obtain ⟨hPO, hPV⟩ := hDP r (by omega)
  obtain ⟨k, _, _, hk, -⟩ := bad2_t0_cases hB hlen hp he1 I.r12
  rw [← hrx] at hk
  have he2r : entry M 2 r = 0 := by have := I.z2 r; have := (upg_e12 hk).2; omega
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hxcnt : Counted M r (r + L) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 : entry M 2 (r + L) = (bump M r).2.2 := by
        show (col M (r + L)).2.2 = _; rw [h]
      rw [hx2] at h2; simp [bump] at h2
    · obtain ⟨hu, _⟩ := h
      unfold isUpg at hu
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
      have := upg_target_e2 (of_decide_eq_true hk)
      omega
  have hl' := po_lhd_or_weak I.cons I.good K.C1 (by omega) (by omega) hPO hPV hg K.nz K.lt
  have hl2 : Lhd z ((drop1 M (r + L) rk).o r) (ρ.o r) ∨
      (∃ w', (drop1 M (r + L) rk).o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ WCS (ρ.v g) w' ∧
        isOT (psi w' z z) = true) ∧
        (Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r) ∧ (Counted M g r → ρ.v r ≤ ρ.v g) := by
    rcases hl' with hl | ⟨hCX, hw⟩
    · exact Or.inl hl
    · refine Or.inr ⟨hw, fun hc => counted_first0 hlen hL hp (by omega) I.r0p I.z2 hx2 hn2 hg hc he2r,
        fun _ => ?_⟩
      exact T0ArgB.index_le_of_cntx I.r0p I.z2 I.uab I.be (sInvXJ_std hM hS).2 I.cons I.good I.rank (by omega) hg
        (by simpa only [show r + 1 = r + L by omega] using he1) hCX
        (by simpa only [show r + 1 = r + L by omega] using hxr)
        (by simpa only [show r + 1 = r + L by omega] using hxcnt)
  exact t0_S1N_of hlen hL hp (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hg K.C1 K.GT
    K.offD K.σmid K.σlast hl2 K.y'
    (fun hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hc)
    (t0_shape3C hM hS I D hlen hL hp he1 g hg)
    (t0IVResC_holds M ρ rk r L hM hS I hlen hL hp he1 n hn2 g hg) hcnt

/-- **Residual: the hard seeds of a `Bad2` matrix at `t = 0`**: all seeds when `r ≠ x − 1` (`r` is `g` or `p`;
for `r = p` the node S1 is empty, as the bump child does not count), and S3 when `r = x − 1`. -/
def T0BadSeedsH : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      (r ≠ r + L - 1 → T0SeedsN M ρ r L n σ) ∧
      (r = r + L - 1 → ∀ g, par M 0 r = some g → ∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 →
        entry M 2 pp ≠ 0 → col M g = bump M pp → Lhd z (σ.v pp) (ρ.v pp))

/-- **`T0BadSeeds` from the hard seeds**: for `r = x − 1`, S1 is `t0_S1N_x1` and S2 is empty (`x − 1` has row 2
`= 0`, a bump child has row 2 `= 1`). -/
theorem t0BadSeeds_of (hDU : HDropU) (hH : T0BadSeedsH) : T0BadSeeds := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1 n hn2 σ hCN
  obtain ⟨hne, hx1⟩ := hH M ρ rk hM hS hB I r L hlen hL hp he1 n hn2 σ hCN
  by_cases hrx : r = r + L - 1
  · have S := sInv_std hM hS
    have IC := I.toC S
    have D := T0DropF.of_U hDU hM hS (by omega) I
    intro g hg
    refine ⟨t0_S1N_x1 hM hS IC D hB hlen hL hp he1 hrx hn2 hCN g hg, fun hb _ _ => ?_, hx1 hrx g hg⟩
    exfalso
    obtain ⟨k, _, _, hk, -⟩ := bad2_t0_cases hB hlen hp he1 S.r12
    rw [← hrx] at hk
    have he2r : entry M 2 r = 0 := by have := S.z2 r; have := (upg_e12 hk).2; omega
    have h2 : entry M 2 r = (bump M g).2.2 := by show (col M r).2.2 = _; rw [hb]
    rw [he2r] at h2; simp [bump] at h2
  · exact hne hrx

end Ytosk
