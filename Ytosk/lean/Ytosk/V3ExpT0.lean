/-
**3 行・t = 0: 最上位の帰納法の仮定 hExp のうち t = 0 の分（n ≥ 2）。**

N = M[n] = TRIO.gexp M r L 0 0 n（r = P_0(x)、x = r + L、Δ = 0）の評価 σ（`t0_core` が作るもの）について、
`Inv3V N σ rkN ∧ Res3A N σ rkN` を組み立てる。

- `t0_core` から: Cons・Rk・Good3・FrameOT・FrameClosed・BumpKidsDec・BumpTermDec・根の順序。rootS は Good3 から。
- 残り（明示した仮定）:
  - `T0OTD`: r より前の D の列の o の値が標準形（`t0_core` の `hOTD`）。`t0OTD_of_shape` で `T0Shape` から。
  - `T0Rest`: 値の不変条件の残りの欄（VSmallF と 11 項目）と N の `Res3A`。
    文脈として M の不変条件と、接頭辞 M.take x の不変条件（帰納法で 1 列落としから出る）を渡す。
-/
import Ytosk.V3T0OT
import Ytosk.V3T0Last
import Ytosk.V3IndV
import Ytosk.V3FsdComp

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The shape of a `t = 0` matrix**: the last column `x = r + L` has row 1 equal to 0 and row-0 parent `r`,
and every expansion is the copy expansion `TRIO.gexp M r L 0 0 n`. -/
theorem t0_shape {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0) :
    ∃ r L, r + L + 1 = M.length ∧ 0 < L ∧ par M 0 (r + L) = some r ∧ entry M 1 (r + L) = 0 ∧
      ∀ n, expand M n = TRIO.gexp M r L 0 0 n := by
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hrx : r < M.length - 1 := par_lt M _ _ r hr
  rw [hs0] at hr
  have he1 : entry M 1 (M.length - 1) = 0 := by
    unfold TRIO.srow at hs0
    rw [← entry_eq, ← entry_eq] at hs0
    split_ifs at hs0 <;> omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hz
    rw [col_eq_entries, entry_eq, entry_eq, entry_eq, h0, h1, h2]
  refine ⟨r, M.length - 1 - r, by omega, by omega, by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact hr,
    by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact he1, fun n => ?_⟩
  exact expand_eq_gexp_t0 M n (by omega) hzT (by rw [hs0]; exact hr) hs0

/-! ## 3 つの欄 -/

/-- `TP1C` as a rewriting-frame property. -/
def PTP1 (_a B _s y : T) : Prop := OHole y → lt B (fsD y (psi (holeLev y) one z)) = true

/-- `TP1WC` as a rewriting-frame property. -/
def PTP1W (_a B _s y : T) : Prop := cof y = .omega → OHole y → lt B (fsD y one) = true

/-- `TrigOmC` as a rewriting-frame property. -/
def PTrig (_a B _s y : T) : Prop := ∀ ν, y = psi (succ ν) z z → B = z

theorem rwc_tp1 {M : Mat} {ρ : Valn} : RWC PTP1 M ρ ↔ TP1C M ρ := Iff.rfl

theorem rwc_tp1w {M : Mat} {ρ : Valn} : RWC PTP1W M ρ ↔ TP1WC M ρ := Iff.rfl

theorem rwc_trig {M : Mat} {ρ : Valn} : RWC PTrig M ρ ↔ TrigOmC M ρ := by
  constructor
  · intro h i L c R hch hcnt s ν hsy hlt htr
    exact h i L c R hch hcnt s _ hsy hlt htr ν rfl
  · intro h i L c R hch hcnt s y hsy hlt htr ν hy
    subst hy
    exact h i L c R hch hcnt s ν hsy hlt htr


/-! ## 型 A の D の枠では書き換える枠の 3 つの欄が成り立つ -/

theorem ohole_app_inv0 : ∀ {P c : T}, c ≠ z → OHole (app P c) → OHole c
  | z, c, _, h => by simpa using h
  | psi a b P, c, hc, h => by
    simp only [app_psi] at h
    have hPc : app P c ≠ z := fun he => hc (app_eq_z he).2
    have h' : OHole (app P c) := by
      cases hX : app P c with
      | z => exact absurd hX hPc
      | psi => rw [hX] at h; exact h
    exact ohole_app_inv0 hc h'

/-- Class A of the pair `(y′, y)` at the level `s`. -/
def ClsA (s y' y : T) : Prop :=
  (split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 ∧ (split y' (psi (succ s) z z)).2 ≠ z

/-- In class A with the new frame rewriting, the state is at most the common high part, below `y′`. -/
theorem classA_state {B s y y' : T} (hc : isOT (psi s y z) = true) (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hl : y' < y) (hA : ClsA s y' y) (ht : lt B y' = true) :
    B ≤ (split y' (psi (succ s) z z)).1 := by
  rw [hA.1]; exact B_le_hi hc (lt_trans (show B < y' from ht) hl) hBc

/-- Past the high part: a nonzero change of the low part stays above it. -/
theorem classA_fsD {B s y' η : T} (hB : B ≤ (split y' (psi (succ s) z z)).1)
    (hlo : (split y' (psi (succ s) z z)).2 ≠ z) (hO : OHole y') (hη : η ≠ z) :
    lt B (fsD y' η) = true := by
  have e := split_app (psi (succ s) z z) y'
  rw [← e] at hO ⊢
  rw [fsD_app _ hlo]
  have hO' := ohole_app_inv0 hlo hO
  exact lt_of_le_of_lt hB (lt_app_of (fsD_ne_z_oh hO' hη))

theorem ptp1_classA {a B s y y' : T} (hc : isOT (psi s y z) = true) (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hl : y' < y) (hA : ClsA s y' y) (ht : lt B y' = true) : PTP1 a B s y' := fun hO =>
  classA_fsD (classA_state hc hBc hl hA ht) hA.2 hO (by simp)

theorem ptp1w_classA {a B s y y' : T} (hc : isOT (psi s y z) = true) (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hl : y' < y) (hA : ClsA s y' y) (ht : lt B y' = true) : PTP1W a B s y' := fun _ hO =>
  classA_fsD (classA_state hc hBc hl hA ht) hA.2 hO (by simp [one])

theorem ptrig_classA {a B s y y' : T} (hc : isOT (psi s y z) = true) (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hl : y' < y) (hA : ClsA s y' y) (ht : lt B y' = true) : PTrig a B s y' := by
  intro ν hy'
  have hB := classA_state hc hBc hl hA ht
  have hlo := hA.2
  rw [hy'] at hB hlo
  unfold split at hB hlo
  split_ifs at hB hlo with hθ
  · simp only at hB
    rcases (le_iff _ _).mp hB with h | h
    · exact absurd h (T.not_lt_z _)
    · exact h
  · simp [split] at hlo

/-! ## 状態が 0 か引数の先頭部分なら 3 つの欄は成り立つ -/

/-- A state that is `0` or a proper prefix of `y′` stays below `fsD(y′, η)` at a hole. -/
theorem prefix_fsD {B y' η : T} (hlt : lt B y' = true) (hpre : B = z ∨ ∃ R, y' = app B R)
    (hO : OHole y') (hη : η ≠ z) : lt B (fsD y' η) = true := by
  rcases hpre with rfl | ⟨R, rfl⟩
  · show z < fsD y' η
    exact lt_of_le_of_ne (z_le _) (Ne.symm (fsD_ne_z_oh hO hη))
  · have hR : R ≠ z := by
      rintro rfl; rw [app_z_right] at hlt; exact absurd hlt (lt_irrefl' _)
    rw [fsD_app _ hR]
    exact lt_app_of (fsD_ne_z_oh (ohole_app_inv0 hR hO) hη)

theorem ptp1_prefix {a B s y' : T} (hlt : lt B y' = true) (hpre : B = z ∨ ∃ R, y' = app B R) :
    PTP1 a B s y' := fun hO => prefix_fsD hlt hpre hO (by simp)

theorem ptp1w_prefix {a B s y' : T} (hlt : lt B y' = true) (hpre : B = z ∨ ∃ R, y' = app B R) :
    PTP1W a B s y' := fun _ hO => prefix_fsD hlt hpre hO (by simp [one])

theorem ptrig_prefix {a B s y' : T} (hlt : lt B y' = true) (hpre : B = z ∨ ∃ R, y' = app B R) :
    PTrig a B s y' := by
  intro ν hy'
  rcases hpre with h | ⟨R, hR⟩
  · exact h
  · subst hy'
    cases B with
    | z => rfl
    | psi b1 b2 b3 =>
      exfalso
      simp only [app_psi, psi.injEq] at hR
      obtain ⟨rfl, rfl, h3⟩ := hR
      obtain ⟨rfl, rfl⟩ := app_eq_z h3.symm
      exact absurd hlt (lt_irrefl' _)

/-- **The residual `hOTD`** of `t0_core`: the `o` values of the `D` columns before `r` are standard. -/
def T0OTD : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → DepX M (r + L) true i → isOT (σ.o i) = true

/-- **The class residuals** of the `D` frames of `N = M[n]` (`t = 0`), which give `T0OTD` (`t0_otd`;
the class of the argument pairs passes up the frames by `cls_node`): (i) at a frame before `r` whose last
counted child keeps its `v` and whose child pair has no low part in either (class B0), a rewrite of the old
frame is one of the new frame; (ii) a changed `v` of such a child whose row-1 parent is not `i` stays at
least `Ω_{a+1}` when the old one is (with row-1 parent `i` it is above `v(i)`, `v_gt_par1_at`); (iii) the same for the value `o′(r)` of
`M.take x` at `g = P_0(r)` (then the class at `g` is `s1_core_cls`; proved, `t0_shape3`); (iv) at `g` when no
middle copy root counts, the old frame of `g` does not rewrite at `r` (then `o′(r)` replaces `o(r)` in the frame,
`s0_core`; C′ と Std の追加の 8 件で例外 0). -/
def T0Shape : Prop :=
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
    (∀ g, par M 0 r = some g → ∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z) ∧
    (∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true))

/-- **The `D` columns of `N` from the class residuals**: standard, and with the same `v` their
arguments drop by `◁`. -/
theorem t0_D_of_shape (hU0 : OldUpgAbs) (h : T0Shape) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L n : Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hlen : r + L + 1 = M.length)
    (hL : 0 < L) (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) (hn : 2 ≤ n)
    {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) :
    ∀ i, i < r → DepX M (r + L) true i → isOT (σ.o i) = true ∧ (σ.v i = ρ.v i →
      ∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X) ∧
      (σ.v i ≠ ρ.v i → σ.o i = psi (σ.v i) z z) := by
  obtain ⟨h1, h2, h3, h4⟩ := h M ρ rk r L hM hS I R hlen hL hp he1
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.lo r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  exact (t0_otd hU0) hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    h1 h2 h3 h4 n hn σ hCN

/-- **`T0OTD` from the class residuals.** -/
theorem t0OTD_of_shape (hU0 : OldUpgAbs) (h : T0Shape) : T0OTD := by
  intro M ρ rk r L n hM hS I R hlen hL hp he1 hn σ hCN i hi hd
  exact ((t0_D_of_shape hU0) h hM hS I R hlen hL hp he1 hn hCN i hi hd).1

/-- **The residual of a rewriting-frame field `P` at `N = M[n]`** (`t = 0`): the frames before `r`
whose last counted child is in `D`, and the first copy root of `g` (the middle value or `o′(r)` after the
counted siblings of `r`). The other frames come from `M` and `M.take x` (`rwc_N_t0`). -/
def T0RWRes (P : T → T → T → T → Prop) : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        QP P (ρ.v i) (Lc.map ρ.o) (σ.o c)) ∧
    (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rk).o r) → QP P (ρ.v g) (Lc.map ρ.o) cv)

/-- **The residual of a rewriting-frame field `P` outside class A**: `T0RWRes P` with the `D` frames
only where the argument pair of the child is not of class A. -/
def T0RWResB (P : T → T → T → T → Prop) : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y → ¬ ClsA s y' y →
          QP P (ρ.v i) (Lc.map ρ.o) (σ.o c)) ∧
    (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rk).o r) → QP P (ρ.v g) (Lc.map ρ.o) cv)

/-- **The class-A frames are free**: `T0RWRes P` from `T0RWResB P` when `P` holds at class-A rewrites. -/
theorem t0RWRes_of (hU0 : OldUpgAbs) (P : T → T → T → T → Prop)
    (hPA : ∀ a B s y y', isOT (psi s y z) = true → (∀ q ∈ summands B, psi s y z ≤ q) → y' < y →
      ClsA s y' y → lt B y' = true → P a B s y')
    (hS : T0Shape) (hB : T0RWResB P) : T0RWRes P := by
  intro M ρ rk r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN
  obtain ⟨hD, hG0⟩ := hB M ρ rk r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN
  refine ⟨?_, hG0⟩
  intro i hi hng Lc c Rr hCL hDc s1 y1 hcv ht1 ht2
  have hx : r + L + 1 = M.length := hlen
  have he2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hlN := lenN0 hlen (show 1 ≤ n by omega) (M := M) (L := L)
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcM : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hcr : c < r := by
    by_cases hig : par M 0 r = some i
    · have hle := children_g_le hlen hL hp hig hcM
      rcases Nat.lt_or_ge c r with h | h
      · exact h
      · exfalso; have : c = r := by omega
        rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
    · exact children_lt_r hlen hL hp hi hig hcM
  have hcMl : c < M.length := by omega
  have hiM : i < M.length := by omega
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; have := Nat.le_mul_of_pos_left L (show 0 < n by omega); omega
  -- the state's summands are at least the old child
  set a := ρ.v i
  set B := spArg a z (sumN (Lc.map ρ.o)) with hBdef
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hiM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_cons] at hsM hpM
  have hpL := List.pairwise_append.mp hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) hpL.1
  have hBc : ∀ q ∈ summands B, ρ.o c ≤ q := by
    obtain ⟨s0, y0, hs0⟩ := (single_o I.cons I.good hcMl).2
    rw [hs0]
    apply spArg_summands_ge ⟨s0, y0, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq
      have := hpL.2.2 q hq (ρ.o c) (by simp)
      rwa [hs0] at this
    · simp [summands]
  have hDc' := (t0_D_of_shape hU0) hS hM hSRO I R hlen hL hp he1 hn hCN c hcr hDc
  by_cases hvc : σ.v c = ρ.v c
  · obtain ⟨_, hArg, _⟩ := (t0_D_of_shape hU0) hS hM hSRO I R hlen hL hp he1 hn hCN c hcr hDc
    obtain ⟨X, X', hX, hX', hlX⟩ := hArg hvc
    rw [hcv] at hX'
    simp only [psi.injEq] at hX'
    obtain ⟨rfl, rfl, -⟩ := hX'
    by_cases hA : ClsA (ρ.v c) y1 X
    · have hcX : isOT (psi (ρ.v c) X z) = true := by rw [← hX]; exact I.good.ot_o c hcMl
      exact hPA a B (ρ.v c) X y1 hcX (fun q hq => by rw [← hX]; exact hBc q hq) hlX.1 hA ht1
    · exact hD i hi hng Lc c Rr hCL hDc (ρ.v c) X y1 hX hcv hlX hA (ρ.v c) y1 hcv ht1 ht2
  · -- a changed `v`: the child has argument `0` and does not rewrite
    have h0 := hDc'.2.2 hvc
    rw [hcv] at h0
    simp only [psi.injEq] at h0
    rw [h0.2.1] at ht1
    exact absurd ht1 (T.not_lt_z _)

/-- **The context of a residual field of `N = M[n]`** (`t = 0`): `M` with its invariants, the prefix
`M.take x` with its invariants (from the one-column drops in the induction), and the valuation of `N` built by
`t0_core` (which already has `Cons`, `Rk`, `Good3`, `FrameOT`, `FrameClosed`, `BumpKidsDec`, `BumpTermDec`). -/
def T0Ctx (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat) (σ : Valn)
    (rkN : Bool → Nat → Nat) : Prop :=
  Std M ∧ M ≠ SRO ∧ Inv3 M ρ rk ∧ Res3A M ρ rk ∧ r + L + 1 = M.length ∧ 0 < L ∧
    par M 0 (r + L) = some r ∧ entry M 1 (r + L) = 0 ∧
    (∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT) ∧
    2 ≤ n ∧ Cons (TRIO.gexp M r L 0 0 n) σ ∧ Rk (TRIO.gexp M r L 0 0 n) rkN ∧
    Good3 (TRIO.gexp M r L 0 0 n) σ ∧ FrameOT (TRIO.gexp M r L 0 0 n) σ ∧
    FrameClosed (TRIO.gexp M r L 0 0 n) σ ∧
    BumpKidsDec (TRIO.gexp M r L 0 0 n) σ ∧ BumpTermDec (TRIO.gexp M r L 0 0 n) σ

/-- **A residual value field `F` of `N = M[n]`** (`t = 0`), in the context `T0Ctx`. -/
def T0Field (F : Mat → Valn → Prop) : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → F (TRIO.gexp M r L 0 0 n) σ

/-- **The residual `Res3A` of `N = M[n]`** (`t = 0`), given the value invariants of `N`. -/
def T0Res3A : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → Inv3V (TRIO.gexp M r L 0 0 n) σ rkN →
    Res3A (TRIO.gexp M r L 0 0 n) σ rkN

/-- **The remaining value fields of `N = M[n]`** (`t = 0`) and its `Res3A`, one named residual each
(groupA's ◁-lowering lemmas for the first seven, wip's forms of `TPLoW`・`AbsDW`, drop-fix's `Res3A`). -/
structure T0Rest : Prop where
  vs : T0Field VSmallF
  ad : T0Field AbsD
  au : T0Field AbsU
  tplo : T0Field TPLo
  auw : T0Field AbsUW
  tplon : T0Field TPLoN
  adn : T0Field AbsDN
  tplow : T0Field TPLoW
  adw : T0Field AbsDW

/-- **`hExp` for `t = 0`** (`n ≥ 2`), from the residuals `T0OTD` and `T0Rest`, with the invariants of the
prefix `M.take x` given. -/
theorem hExp_t0 (hOTD : T0OTD) (hRest : T0Rest) (hR1 : T0RWRes PTP1) (hR1W : T0RWRes PTP1W)
    (hRT : T0RWRes PTrig) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0)
    (hT : ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
      ∃ τ rkT, Inv3 (M.take j) τ rkT ∧ Res3A (M.take j) τ rkT)
    (n : Nat) (hn2 : 2 ≤ n) :
    ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shape I hz hs0
  rw [hexp n]
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.lo r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have hcore := t0_core hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab (sInvXJ_std hM hS).2 (sInvXJ_std hM hS).1.loc.2.2.2 I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab (T0AbsW.of_strong hab0) hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (fun n hn σ hCN => ⟨hOTD M ρ rk r L n hM hS I R hlen hL hp he1 hn σ hCN,
      t0_vsmallNewN hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.cons I.good I.rank hn hCN⟩)
    n hn2
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN, hRWN, hpN, _⟩ := hcore
  -- the prefix `M.take x`
  have hTx : ∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT := by
    apply hT (r + L) (by omega)
    · intro h
      have hRk1 : Rk (M.take (r + L)) rk :=
        rk_take (by omega) I.rank (by
          have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
          rwa [show M.length - 1 = r + L by omega] at this)
      rw [h] at hRk1; exact not_val_SRO _ (val_of_rk hRk1)
    · intro h
      have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left (by omega)] at this
      simp only [List.length_nil] at this; omega
  have hctx : T0Ctx M ρ rk r L n σ rkN :=
    ⟨hM, hS, I, R, hlen, hL, hp, he1, hTx, hn2, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN⟩
  have hvs := hRest.vs _ _ _ _ _ _ _ _ hctx
  have had := hRest.ad _ _ _ _ _ _ _ _ hctx
  have hau := hRest.au _ _ _ _ _ _ _ _ hctx
  have htplo := hRest.tplo _ _ _ _ _ _ _ _ hctx
  have hauw := hRest.auw _ _ _ _ _ _ _ _ hctx
  have htplon := hRest.tplon _ _ _ _ _ _ _ _ hctx
  have hadn := hRest.adn _ _ _ _ _ _ _ _ hctx
  have htplow := hRest.tplow _ _ _ _ _ _ _ _ hctx
  have hadw := hRest.adw _ _ _ _ _ _ _ _ hctx
  -- the rewriting-frame fields, with the prefix valuation `drop1`
  have hRk1 : Rk (M.take (r + L)) rk :=
    rk_take (by omega) I.rank (by
      have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
      rwa [show M.length - 1 = r + L by omega] at this)
  obtain ⟨τ, rkT, IT, _⟩ := hTx
  have hAg : ∀ i, i < (M.take (r + L)).length →
      τ.o i = (drop1 M (r + L) rk).o i ∧ τ.v i = (drop1 M (r + L) rk).v i :=
    agree_of_cons IT.cons (cons_of_rk hRk1) IT.rank
  have hP : ∀ P, RWC P M ρ → RWC P (M.take (r + L)) τ → T0RWRes P → RWC P (TRIO.gexp M r L 0 0 n) σ := by
    intro P hPM hPT hres
    obtain ⟨hD, hG0⟩ := hres M ρ rk r L n hM hS I R hlen hL hp he1 hn2 σ hCN hGN
    exact hRWN P hPM (rwc_congr hPT hAg) hD hG0
  have htp1 : TP1C (TRIO.gexp M r L 0 0 n) σ := hP PTP1 I.tp1 IT.tp1 hR1
  have htp1w : TP1WC (TRIO.gexp M r L 0 0 n) σ := hP PTP1W I.tp1w IT.tp1w hR1W
  have htrig : TrigOmC (TRIO.gexp M r L 0 0 n) σ :=
    rwc_trig.mp (hP PTrig (rwc_trig.mpr I.trig) (rwc_trig.mpr IT.trig) hRT)
  have V : Inv3V (TRIO.gexp M r L 0 0 n) σ rkN := ⟨hCN, hGN, hRN, hvs, hFCN, hFON, hKDN, hTDN, had, hau, htp1,
    htplo, htp1w, htplow, hauw, hadw, htrig, htplon, hadn, rootS_of_good hCN hGN, hpN⟩
  exact ⟨σ, rkN, V⟩

/-- **`hExp` for `t = 0` in the shape of the top theorem**, with the prefix invariants from the
one-column drop `hLast` (`hTake_of_last`). -/
theorem hExp_t0_of_last
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hOTD : T0OTD) (hRest : T0Rest) (hR1 : T0RWRes PTP1) (hR1W : T0RWRes PTP1W) (hRT : T0RWRes PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz hs0 n hn2
  apply hExp_t0 hOTD hRest hR1 hR1W hRT hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩


/-- **`hExp` for `t = 0`, the current residuals**: the class residual `T0Shape` (for `hOTD`), the
rewriting-frame fields outside class A (`T0RWResB` for `TP1C`・`TP1WC`・`TrigOmC`), and `T0Rest`. -/
theorem hExp_t0_main (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hS : T0Shape) (hRest : T0Rest) (hB1 : T0RWResB PTP1) (hB1W : T0RWResB PTP1W)
    (hBT : T0RWResB PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  hExp_t0_of_last hLast ((t0OTD_of_shape hU0) hS) hRest
    ((t0RWRes_of hU0) PTP1 (fun _ _ _ _ _ hc hBc hl hA ht => ptp1_classA hc hBc hl hA ht) hS hB1)
    ((t0RWRes_of hU0) PTP1W (fun _ _ _ _ _ hc hBc hl hA ht => ptp1w_classA hc hBc hl hA ht) hS hB1W)
    ((t0RWRes_of hU0) PTrig (fun _ _ _ _ _ hc hBc hl hA ht => ptrig_classA hc hBc hl hA ht) hS hBT)


/-- `QP` only where the state is not `0` and not a prefix of the argument (the shadow frames). -/
abbrev QPS (P : T → T → T → T → Prop) (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true → lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) ≠ z → (¬ ∃ R, y = app (spArg a z (sumN Lv)) R) → P a (spArg a z (sumN Lv)) s y

theorem qp_of_qps {P : T → T → T → T → Prop}
    (hPpre : ∀ a B s y', lt B y' = true → (B = z ∨ ∃ R, y' = app B R) → P a B s y')
    {a : T} {Lv : List T} {cv : T} (h : QPS P a Lv cv) : QP P a Lv cv := by
  intro s y hcv hlt htr
  by_cases hB : spArg a z (sumN Lv) = z
  · exact hPpre _ _ _ _ hlt (Or.inl hB)
  by_cases hpre : ∃ R, y = app (spArg a z (sumN Lv)) R
  · exact hPpre _ _ _ _ hlt (Or.inr hpre)
  exact h s y hcv hlt htr hB hpre

/-- **The residual of a rewriting-frame field `P` on the shadow frames**: `T0RWResB P` where moreover
the state is not `0` and not a prefix of the argument. -/
def T0RWResC (P : T → T → T → T → Prop) : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y → ¬ ClsA s y' y →
          QPS P (ρ.v i) (Lc.map ρ.o) (σ.o c)) ∧
    (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rk).o r) → QPS P (ρ.v g) (Lc.map ρ.o) cv)

theorem t0RWResB_of (P : T → T → T → T → Prop)
    (hPpre : ∀ a B s y', lt B y' = true → (B = z ∨ ∃ R, y' = app B R) → P a B s y')
    (hC : T0RWResC P) : T0RWResB P := by
  intro M ρ rk r L n hM hS I R hlen hL hp he1 hn σ hCN hGN
  obtain ⟨hD, hG0⟩ := hC M ρ rk r L n hM hS I R hlen hL hp he1 hn σ hCN hGN
  exact ⟨fun i hi hng Lc c Rr hCL hDc s y y' h1 h2 h3 h4 => qp_of_qps hPpre (hD i hi hng Lc c Rr hCL hDc s y y' h1 h2 h3 h4),
    fun g hg hc Lc hcl cv hcv => qp_of_qps hPpre (hG0 g hg hc Lc hcl cv hcv)⟩

/-- **`hExp` for `t = 0` with the shadow residuals**: `T0Shape`, `T0Rest`, and `T0RWResC` (the
rewriting frames where the state is neither `0` nor a prefix of the argument, at `D` frames outside
class A and at the first copy root of `g`). -/
theorem hExp_t0_mainC (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hS : T0Shape) (hRest : T0Rest) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  (hExp_t0_main hU0) hLast hS hRest
    (t0RWResB_of PTP1 (fun _ _ _ _ hlt hpre => ptp1_prefix hlt hpre) hC1)
    (t0RWResB_of PTP1W (fun _ _ _ _ hlt hpre => ptp1w_prefix hlt hpre) hC1W)
    (t0RWResB_of PTrig (fun _ _ _ _ hlt hpre => ptrig_prefix hlt hpre) hCT)

end Ytosk
