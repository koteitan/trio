/-
**3 行・t = 2: トップへの接続。**

- `drop_n0_gen`: n = 0（M[0] = M.take r）。M.take x から M.take r への鎖（DropRes）は型によらない
  （`drop_n0r` と同じ）。最後の M → M.take x の狭義の減少を仮定に取る。
-/
import Ytosk.V3Top
import Ytosk.V3T2T

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`n = 0` from `n = 1`**: the chain `root(M.take r) ≤ … ≤ root(M.take x)` of the drops of the
prefixes, then the strict last step `root(M.take x) < root(M)` (a hypothesis). -/
theorem drop_n0_gen {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hRM : Rk M rkM) (hI : ValInv M ρ)
    (hdr : DropRes M (r + L) ρ (drop1 M (r + L) rkM))
    (hres : ∀ j, r ≤ j → j < r + L →
      DropRes (M.take (j + 1)) j (drop1 M (j + 1) rkM) (drop1 M j rkM))
    (hlast : root (M.take (r + L)) (drop1 M (r + L) rkM) < root M ρ) :
    ∃ ρN rkN, Cons (M.take r) ρN ∧ Rk (M.take r) rkN ∧
      isOT (root (M.take r) ρN) = true ∧ root (M.take r) ρN < root M ρ := by
  have hlj : ∀ j, j ≤ r + L → (M.take (j + 1)).length = j + 1 := by
    intro j hj; rw [List.length_take]; omega
  have hUATt := fun k => UAT_take hR0 hZ2 hSD hZ1 hUAB k
  -- the ranking of every prefix
  have hRkj : ∀ m j, r + L - j ≤ m → j ≤ r + L → Rk (M.take j) rkM := by
    intro m
    induction m with
    | zero =>
      intro j hm hj
      have hjx : j = r + L := by omega
      subst hjx
      exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
    | succ m ih =>
      intro j hm hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
      · have hN := ih (j + 1) (by omega) hjx
        have hcnt := counted_take_last (M := M.take (j + 1)) (by rw [hlj j (by omega)]; omega)
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
        rw [hlj j (by omega), show j + 1 - 1 = j by omega] at hcnt
        have := rk_take (by rw [hlj j (by omega)]; omega) hN hcnt
        rwa [take_take_succ] at this
  have hRk : ∀ j, j ≤ r + L → Rk (M.take j) rkM := fun j h => hRkj _ j (le_refl _) h
  have hCj : ∀ j, j ≤ r + L → Cons (M.take j) (drop1 M j rkM) := fun j h => cons_of_rk (hRk j h)
  -- the invariants of `M.take x`
  have hIx : ValInv (M.take (r + L)) (drop1 M (r + L) rkM) :=
    drop_pres (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hI hdr (hCj _ (le_refl _)) (hRk _ (le_refl _))
  -- down the chain
  have hIj : ∀ m j, r + L - j ≤ m → r ≤ j → j ≤ r + L → ValInv (M.take j) (drop1 M j rkM) := by
    intro m
    induction m with
    | zero =>
      intro j hm _ hj
      have hjx : j = r + L := by omega
      subst hjx; exact hIx
    | succ m ih =>
      intro j hm hrj hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · subst hjx; exact hIx
      · have hN := ih (j + 1) (by omega) (by omega) hjx
        have := drop_pres (N := M.take (j + 1)) (x := j) (hlj j (by omega)).symm
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
          (UAB_take hUAB _) (hCj _ hjx) hN (hres j hrj hjx)
          (by rw [take_take_succ]; exact hCj j (by omega))
          (by rw [take_take_succ]; exact hRk j (by omega))
        rwa [take_take_succ] at this
  have hone : ∀ j, r ≤ j → j < r + L →
      isOT (root (M.take j) (drop1 M j rkM)) = true ∧
        root (M.take j) (drop1 M j rkM) ≤ root (M.take (j + 1)) (drop1 M (j + 1) rkM) := by
    intro j hrj hjx
    have hD := (DropHypV.of (hIj _ (j + 1) (le_refl _) (by omega) hjx) (hres j hrj hjx)).toDropHyp
      (UAT_take hR0 hZ2 hSD hZ1 hUAB _) (UAB_take hUAB _)
    have h := drop_root_le (N := M.take (j + 1)) (x := j) (hlj j (by omega)).symm
      (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) hD
      (hCj (j + 1) (by omega))
      (by rw [take_take_succ]; exact hCj j (by omega))
      (by rw [take_take_succ]; exact hRk j (by omega))
    rwa [take_take_succ] at h
  have hchain : ∀ m, r + m ≤ r + L →
      root (M.take r) (drop1 M r rkM) ≤ root (M.take (r + m)) (drop1 M (r + m) rkM) := by
    intro m
    induction m with
    | zero => intro _; exact le_refl _
    | succ m ih =>
      intro hm
      exact le_trans (ih (by omega)) (hone (r + m) (by omega) (by omega)).2
  exact ⟨drop1 M r rkM, rkM, hCj r (by omega), hRk r (by omega), (hone r (le_refl _) (by omega)).1,
    lt_of_le_of_lt (hchain L (le_refl _)) hlast⟩

theorem gexp_one_gen {M : Mat} {r L d0 d1 : Nat} (hlen : r + L + 1 = M.length) :
    TRIO.gexp M r L d0 d1 1 = M.take (r + L) := by
  have hl : (TRIO.gexp M r L d0 d1 1).length = r + 1 * L := TRIO.gexp_length hlen
  rw [← gexp_take_x (d0 := d0) (d1 := d1) hlen (le_refl 1), List.take_of_length_le (by omega)]

theorem gexp_zero_gen (M : Mat) (r L d0 d1 : Nat) : TRIO.gexp M r L d0 d1 0 = M.take r := by
  unfold TRIO.gexp TRIO.gcopies; simp

/-- The absorption hypothesis before `x` from `BumpAbsC` (whose side condition fails: the parent of `x`
is not a bump child). -/
theorem abs_of_absC {M : Mat} {x q : Nat} {ρ : Valn} (hAbsC : BumpAbsC M x ρ)
    (hpx : par M 0 x = some q) (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i) :
    ∀ i, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ s ∈ summands (vOpt ρ (par M 1 i)),
      ¬ s < psi z two z → s < bumpW M ρ i → Lhd z s (bumpW M ρ i) := by
  intro i _ h1 h2
  apply hAbsC i h1 h2
  intro j hj hjb hjx
  exfalso
  have hxj : x ∈ children M j := by rw [hjx]; simp
  have hpx' := (mem_children_iff.mp hxj).2
  rw [hpx] at hpx'; cases hpx'
  exact hqb i (mem_children_iff.mp hj).2 hjb

/-! ## 残りの仮定の束（t = 2） -/

/-- The value hypothesis `hVNN` (a changed last counted child is small). -/
def VNNc (M : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i, i < bnd → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
    ∀ s y, ρ.o cs = psi s y z →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
      VSmallV (σ.v cs)

/-- The seed condition at `p`: `o_N(p) = ψ_{v(p)}(X)` with `X` closed and below a term of the
fundamental sequence of `o_M(p)`. -/
def SeedC (ρ σ : Valn) (p : Nat) : Prop :=
  ∃ X K, σ.o p = psi (ρ.v p) X z ∧ Closed (ρ.v p) X ∧ psi (ρ.v p) X z ≤ fs (ρ.o p) (natT K)

/-- The `o` shape of `D = DepS M S` (with weak calls `W`). -/
def OShW (M : Mat) (S W : Bool → Nat → Prop) (bnd : Nat) : Prop :=
  ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S true i → ¬ DepS M S false i →
    ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M S true c ∧
      (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M S true d)

/-- The `o` shape of `D = DepS M S` (no weak calls). -/
def OSh (M : Mat) (S : Bool → Nat → Prop) (bnd : Nat) : Prop :=
  ∀ i, i < bnd → ¬ S true i → DepS M S true i → ¬ DepS M S false i →
    ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M S true c ∧
      (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M S true d)

/-- The `v` shape of `D = DepS M S`. -/
def VSh (M : Mat) (S : Bool → Nat → Prop) (bnd : Nat) : Prop :=
  ∀ i, i < bnd → ¬ S false i → DepS M S false i →
    (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧
    (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
      children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M S true d) ∧
      (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e))

/-- **`q ≠ r`** (`x` a bump child of `q = r + qp`, `P_0 q = pq`). -/
structure T2QN (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L qp pq : Nat) : Prop where
  xb : col M (r + L) = bump M (r + qp)
  qb : col M (r + qp) ≠ bump M pq
  e2pq : entry M 2 pq = 0
  clq : CL M (r + qp) = []
  clpq : CL M pq ≠ []
  un : upg M (r + L - 1) = none
  p1 : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m
  qL : ∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
    ¬ DepS M (SQ (r + qp) pq) true e
  dv : ∀ c, c < r + L → DepS M (SQ (r + qp) pq) false c → CL M c = []
  os : OShW M (SQ (r + qp) pq) (WQ (r + qp)) (r + L)
  vsh : VSh M (SQ (r + qp) pq) (r + L)
  vnn1 : VNNc M (r + L) ρ (drop1 M (r + L) rk)
  seed1 : SeedC ρ (drop1 M (r + L) rk) pq
  big : ∀ n d0 d1 σ, 2 ≤ n → Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ c, c < r + L → c ≠ r + qp → topped M c = true →
      isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c) ∧ VNNc M (r + L) ρ σ ∧ SeedC ρ σ pq

/-- **`q = r`, `x − 1` upgrades to `x`.** -/
structure T2SV (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat) : Prop where
  p1 : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m
  dv : ∀ c, c < r + L → DepS M (SV r (r + L - 1)) false c → CL M c = []
  os : OSh M (SV r (r + L - 1)) (r + L)
  vsh : VSh M (SV r (r + L - 1)) (r + L)
  vnn1 : VNNc M (r + L) ρ (drop1 M (r + L) rk)
  seed1 : SeedC ρ (drop1 M (r + L) rk) r
  big : ∀ n d0 d1 σ, 2 ≤ n → Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ c, c < r + L → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c) ∧
    VNNc M (r + L) ρ σ ∧ SeedC ρ σ r

/-- **`q = r`, `x − 1` upgrades nowhere** (`n ≤ 1`). -/
structure T2QR (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat) : Prop where
  dv : ∀ c, c < r + L → DepS M (SR r) false c → CL M c = []
  os : OSh M (SR r) (r + L)
  vsh : VSh M (SR r) (r + L)
  vnn1 : VNNc M (r + L) ρ (drop1 M (r + L) rk)
  seed1 : SeedC ρ (drop1 M (r + L) rk) r

/-- **`q = r`, `x − 1` upgrades to `k < x`** (`n ≤ 1`). -/
structure T2QU (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L k : Nat) : Prop where
  kT : topped M k = false
  p1 : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m
  dv : ∀ c, c < r + L → c ≠ r → DepS M (SV r (r + L - 1)) false c → CL M c = []
  vr : r ≠ r + L - 1 → ¬ DepS M (SV r (r + L - 1)) false r
  os : OSh M (SV r (r + L - 1)) (r + L)
  vsh : VSh M (SV r (r + L - 1)) (r + L)
  vnn1 : VNNc M (r + L) ρ (drop1 M (r + L) rk)
  seed1 : r ≠ r + L - 1 → SeedC ρ (drop1 M (r + L) rk) r

/-- **`q = r`.** -/
structure T2R (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat) : Prop where
  rb : ∀ p, par M 0 r = some p → col M r ≠ bump M p
  rcl : CL M r ≠ []
  rU : isUpg M r = false
  xb : col M (r + L) ≠ bump M r
  sv : upg M (r + L - 1) = some (r + L) → T2SV M ρ rk r L
  nn : upg M (r + L - 1) = none → T2QR M ρ rk r L
  up : ∀ k, upg M (r + L - 1) = some k → k < r + L → T2QU M ρ rk r L k
  big : upg M (r + L - 1) ≠ some (r + L) → ∀ n d0 d1 σ, 2 ≤ n → Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c) ∧
    Counted (TRIO.gexp M r L d0 d1 n) r (r + L) ∧ VNNc M (r + L) ρ σ ∧ SeedC ρ σ r

/-- **The remaining hypotheses of `t = 2`** (`x = r + L`, `r = P_2(x)`). -/
structure Res3T2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  e2r : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → entry M 2 r = 0
  qn : ∀ r L qp pq, r + L + 1 = M.length → par M 2 (r + L) = some r →
    par M 0 (r + L) = some (r + qp) → 0 < qp → par M 0 (r + qp) = some pq → T2QN M ρ rk r L qp pq
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    T2R M ρ rk r L

/-- **Step 1 for `t = 2`**: from the invariants, the remaining hypotheses (`Res3`, `Res3T2`) and a
valuation of each `M[n]` (`n ≥ 2`), every expansion drops the root value. -/
theorem t2_drops {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3 M ρ rk) (R : Res3 M ρ rk) (R2 : Res3T2 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hNval : ∀ n, 2 ≤ n → ∃ σ rkN, Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧ Good3 (expand M n) σ) :
    ∀ n, DropsAt M ρ n := by
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  have he2r := R2.e2r r L hlen hr
  have hexp : ∀ n, expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  -- the valuation of `M.take x`
  have hdr : DropRes M (r + L) ρ (drop1 M (r + L) rk) := by
    have := R.drop; rw [hL] at this; exact this
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rk) :=
    good3_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := (anc0_par hA (by omega) hq).le
  have hqx : q < r + L := par_lt M 0 _ q hq
  -- `n ≤ 1`: the drop to `M.take x`
  have hlast : isOT (root (M.take (r + L)) (drop1 M (r + L) rk)) = true ∧
      root (M.take (r + L)) (drop1 M (r + L) rk) < root M ρ := by
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hAbs := abs_of_absC hdr.ab hq T.rb
      cases hux : upg M (r + L - 1) with
      | none =>
        have T' := T.nn hux
        exact t2_qr_take hlen hL0 hq T.xb I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r T.rb T.rcl T.rU hux
          T'.dv T'.os T'.vsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs T'.vnn1 T'.seed1
      | some k =>
        have hkl := upg_lt (by omega) hux
        by_cases hkx : k = r + L
        · rw [hkx] at hux
          have T' := T.sv hux
          exact t2_sv_take hlen hL0 hq hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r T.rb T.rcl T.rU
            T'.p1 T'.dv T'.os T'.vsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
            T'.vnn1 T'.seed1
        · have hk : k < r + L := by omega
          have T' := T.up k hux hk
          exact t2_qu_take hlen hL0 hq T.xb I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r T.rb T.rcl T.rU hux hk
            T'.kT T'.p1 T'.dv T'.vr T'.os T'.vsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
            hdr.ua hAbs T'.vnn1 T'.seed1
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      have hAbs := abs_of_absC hdr.ab hq' (fun i h => by rw [hpq'] at h; cases h; exact T.qb)
      exact t2_qn_take hlen hL0 hA hq' (by omega) T.xb I.be I.z2 I.uat I.r12 I.r01 I.e00 hpq' T.qb T.e2pq
        T.clq T.clpq T.un T.p1 T.qL T.dv T.os T.vsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
        hAbs T.vnn1 T.seed1
  -- `n ≥ 2`
  have hbig : ∀ n, 2 ≤ n → ∀ σ rkN,
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) σ) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ <
        root M ρ := by
    intro n hn σ rkN hCN hRN hGN
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hAbs := abs_of_absC hdr.ab hq T.rb
      by_cases hux : upg M (r + L - 1) = some (r + L)
      · have T' := T.sv hux
        obtain ⟨hIUt, hVNN, hseed⟩ := T'.big n _ _ σ hn hCN
        exact t2_sv_main hlen hL0 hq hd0e hn hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r T.rb T.rcl hIUt
          T'.p1 T'.dv T'.os T'.vsh I.cons I.good I.rank hCN hGN hRN I.fc I.vs I.td I.kd hAbs hVNN hseed
      · obtain ⟨hIU, hxcN, hVNN, hseed⟩ := T.big hux n _ _ σ hn hCN
        have hXu : ∀ i, upg M i ≠ some (r + L) := by
          intro i hu
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
          have hi : i < M.length := by
            by_contra h
            exact (upg_e12 hu).1 (entry_out (by omega) 1)
          rcases hcase with h | ⟨_, h⟩
          · exact hux (by rw [show r + L - 1 = i by omega]; exact hu)
          · omega
        exact t2_qr_main hlen hL0 hq hd0e hn hXu T.xb T.rb he2r hIU I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
          I.be I.r01 I.e00 I.cons I.good I.rank hCN hGN hRN I.fc I.vs I.td I.kd hdr.ab hVNN hxcN hseed
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      have hAbs := abs_of_absC hdr.ab hq' (fun i h => by rw [hpq'] at h; cases h; exact T.qb)
      obtain ⟨hIUt, hVNN, hseed⟩ := T.big n _ _ σ hn hCN
      exact t2_qn_main hlen hL0 hA hq' (by omega) hd0e hn T.xb I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hpq'
        T.qb T.e2pq T.clq T.clpq hIUt T.p1 T.qL T.dv T.os T.vsh I.cons I.good I.rank hCN hGN hRN
        I.fc I.vs I.td I.kd hAbs hVNN hseed
  intro n
  rcases n with _ | _ | n
  · apply dropsAt_of (by rw [hexp 0, gexp_zero_gen])
    exact drop_n0_gen hlen hL0 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr (fun j _ hj => R.chain j (by omega)) hlast.2
  · apply dropsAt_of (by rw [hexp 1, gexp_one_gen hlen])
    exact ⟨_, _, hC1, hRk1, hlast⟩
  · obtain ⟨σ, rkN, hCN, hRN, hGN⟩ := hNval (n + 2) (by omega)
    rw [hexp] at hCN hRN hGN
    apply dropsAt_of (hexp (n + 2))
    exact ⟨σ, rkN, hCN, hRN, hbig (n + 2) (by omega) σ rkN hCN hRN hGN⟩

end Ytosk
