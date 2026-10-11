/-
**3 行・t = 2: トップへの接続。**

- `drop_n0_gen`: n = 0（M[0] = M.take r）。M.take x から M.take r への鎖（DropRes）は型によらない
  （`drop_n0r` と同じ）。最後の M → M.take x の狭義の減少を仮定に取る。
-/
import Ytosk.V3Top
import Ytosk.V3T2T
import Ytosk.V3T2QNU
import Ytosk.V3InvT2
import Ytosk.V3T2DS
import Ytosk.V3InvPer
import Ytosk.V3TopB

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

/-- The absorption hypothesis before `x` from `BumpAbsS` (whose side condition fails: the parent of `x`
is not a bump child). -/
theorem abs_of_absC {M : Mat} {x q : Nat} {ρ : Valn} (hAbsC : BumpAbsS M x ρ)
    (hpx : par M 0 x = some q) (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i) :
    ∀ i, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ s ∈ summands (vOpt ρ (par M 1 i)),
      ¬ s < psi z two z → s < bumpW M ρ i → Lhd z s (bumpW M ρ i) := by
  intro i _ h1 h2
  refine hAbsC i h1 h2 (fun j hj hjb hjx => ?_) (Or.inr (Or.inl fun q' i' hq' hi' => ?_))
  · exfalso
    have hxj : x ∈ children M j := by rw [hjx]; simp
    have hpx' := (mem_children_iff.mp hxj).2
    rw [hpx] at hpx'; cases hpx'
    exact hqb i (mem_children_iff.mp hj).2 hjb
  · rw [hpx] at hq'; cases hq'; exact hqb i' hi'



/-- **`M[n]` (`t = 2`, `n ≥ 2`) is not SRO**: `x′` would be the column `(3,1,0)` (the only one with row 2 zero
and row 1 positive), and the next column `(2,0,0)` would be below `x` in row 0. -/
theorem gexp_ne_SRO {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hd1 : entry M 1 (r + L) = entry M 1 r + d1) (he2r : entry M 2 r = 0)
    (h1 : entry M 1 r < entry M 1 (r + L)) (hn2 : 2 ≤ n) :
    TRIO.gexp M r L d0 d1 n ≠ SRO := by
  intro he
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  rw [he] at hlN
  have hl5 : SRO.length = 5 := rfl
  have hnL : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hx' := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
    (k := 1) (q := 0) hlen (by omega) hL
  rw [show r + (1 * L + 0) = r + L by omega, Nat.add_zero,
    if_pos ⟨by omega, by omega, Relation.ReflTransGen.refl⟩, he] at hx'
  have hj : r + L < 5 := by omega
  have h3 : r + L = 3 := by
    have key : ∀ j, j < 5 → (SRO.getD j (0, 0, 0)).2.2 = 0 → 1 ≤ (SRO.getD j (0, 0, 0)).2.1 → j = 3 := by
      decide
    apply key _ hj
    · rw [hx']; exact he2r
    · rw [hx']; show 1 ≤ entry M 1 r + 1 * d1; omega
  have hx3 : entry M 0 (r + L) = 3 := by
    have h := congrArg (fun c : Nat × Nat × Nat => c.1) hx'
    rw [h3] at h
    have : (SRO.getD 3 (0, 0, 0)).1 = 3 := rfl
    simp only at h
    rw [this] at h
    show entry M 0 (r + L) = 3
    have : entry M 0 r + 1 * d0 = 3 := h.symm
    omega
  obtain ⟨k, q, hk, hq, hkq⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) (p := 4) hL
    (by omega) (by omega)
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this; omega
  have h4 := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
    (k := k) (q := q) hlen hk hq
  rw [← hkq, he] at h4
  have h40 := congrArg (fun c : Nat × Nat × Nat => c.1) h4
  have : (SRO.getD 4 (0, 0, 0)).1 = 2 := rfl
  simp only at h40
  rw [this] at h40
  have hrq : entry M 0 r ≤ entry M 0 (r + q) := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0; simp
    · exact (anc0_e0_lt (anc_between hA (r + q) (by omega) (by omega)) (by omega)).le
  have : d0 ≤ k * d0 := Nat.le_mul_of_pos_left d0 hk1
  have h2' : 2 = entry M 0 (r + q) + k * d0 := h40
  omega

/-! ## 残りの仮定の束（t = 2） -/

/-- The seed at `p` in `M[n]` (`n ≥ 2`): `o_N(p) ◁ o_M(p)`. (The sufficient condition `SeedC`, closedness
of the new argument and a bound by a term of the fundamental sequence, fails on 61 cases of C′; the
`◁` itself has no exception there.) -/
def SeedL (ρ σ : Valn) (p : Nat) : Prop := Lhd z (σ.o p) (ρ.o p)

/-- **The seed of `M.take x` from the drop lemma**: `PO` at `p` with counted children in `M` and a
changed value gives `◁`. -/
theorem lhd_of_po {M : Mat} {ρ ρ' : Valn} {p : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hpM : p < M.length) (hcl : CL M p ≠ []) (hPO : PO ρ ρ' p) (hne : ρ'.o p ≠ ρ.o p) :
    Lhd z (ρ'.o p) (ρ.o p) := by
  rcases hPO.1 with hE | ⟨_, w, hw⟩
  · apply lhd_of_lhdE_lt hE
    rcases (le_iff _ _).mp hE.le with h | h
    · exact h
    · exact absurd h hne
  · exfalso
    have hor := o_cl_eq hC hG hpM
    have harg := arg_lt_of_cl hC hG hpM hcl
    rw [hw] at hor; simp only [psi.injEq] at hor
    rw [← hor.2.1] at harg; exact lt_irrefl' _ harg

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

/-- **`r = P_2(x)`**: row 2 of `r` is `0` and row 1 of `r` is below that of `x`. -/
theorem par2_facts {M : Mat} {x r : Nat} (hZ2 : Z2 M) (hxM : x < M.length) (h2 : par M 2 x = some r) :
    entry M 2 r = 0 ∧ entry M 1 r < entry M 1 x := by
  obtain ⟨_, _, hrx, he2, hle, _⟩ := (par2_iff M hxM).mp h2
  have hA := anc0_of_par M 2 r x h2
  have hx2 := hZ2 x
  have he2' : entry M 2 r < entry M 2 x := he2
  have h1lt : entry M 1 r < entry M 1 x :=
    (le1_window hxM hA).mp hle x hA (Anc0.refl x) (by omega)
  exact ⟨by omega, h1lt⟩

/-- **The shape of `D = DepS M {o(r)}`** (`q = r`, no upgrade into `x`), from the structure of `M`. -/
theorem qr_shapes {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L)) (hXb : col M (r + L) ≠ bump M r)
    (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M) :
    (∀ c, c < r + L → DepS M (SR r) false c → CL M c = []) ∧ OSh M (SR r) (r + L) ∧
      VSh M (SR r) (r + L) := by
  have hx : r + L + 1 = M.length := hlen
  have hXbD : ∀ p, par M 0 (r + L) = some p → col M (r + L) ≠ bump M p := by
    intro p h'; rw [hp] at h'; cases h'; exact hXb
  have hiff : ∀ b i, i < r + L → (DepS M (SR r) b i ↔ DepX M (r + L) b i) :=
    fun b i hi => depS_iff_depX hlen hL hp hXu hXb hrb hi
  refine ⟨fun c hc hd => ?_, fun i hi hns hD hv => ?_, fun i hi _ hD => ?_⟩
  · unfold CL; rw [List.filter_eq_nil_iff]
    intro d hdc
    simp only [decide_eq_true_eq]
    exact uncnt_of_depvX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXbD hp hc ((hiff false c hc).mp hd) hdc
  · have hir : i ≠ r := fun h => hns ⟨rfl, h⟩
    rcases hOS_t1X hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXbD hp i hi ((hiff true i hi).mp hD) with
      ⟨hvX, _⟩ | ⟨_, Lp, c0, R, hch, hcb0, hcu0, hR, hLnd⟩
    · exact absurd ((hiff false i hi).mpr hvX) hv
    · cases hD with
      | seed h => exact absurd h hns
      | ov h => exact absurd h hv
      | @ochild _ c hc hcb hcu hdc =>
        have hcnt : Counted M i c := ⟨hcb, hcu⟩
        have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
          rcases hR d h with h' | h'
          · exact hd.1 h'
          · exact hd.2 h'
        have hcl' := (mem_children hc).2
        have hxi : ∀ d ∈ children M i, d < r + L := by
          intro d hd
          have := (mem_children hd).2
          by_contra h'
          have hd' : d = r + L := by omega
          have hpd := (mem_children_iff.mp hd).2
          rw [hd', hp] at hpd; cases hpd; exact hir rfl
        have hcx : c < r + L := hxi c hc
        have hcc0 : c = c0 := by
          have hc' := hc
          rw [hch] at hc'
          rcases List.mem_append.mp hc' with h | h
          · exact absurd ((hiff true c hcx).mp hdc) (hLnd c h hcnt)
          · rcases List.mem_cons.mp h with h | h
            · exact h
            · exact absurd hcnt (hcR c h)
        rw [← hcc0] at hch
        refine ⟨Lp, c, R, hch, hcnt, hdc, hcR, fun d hd hdc' h => ?_⟩
        have hdM : d ∈ children M i := by rw [hch]; simp [hd]
        exact hLnd d hd hdc' ((hiff true d (hxi d hdM)).mp h)
  · have hDX := (hiff false i hi).mp hD
    obtain ⟨_, hpnd, hcase⟩ := dv_shapeX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXbD hp hi hDX
    refine ⟨fun m hm h => hpnd m hm ((hiff false m (by have := par_lt M 1 i m hm; omega)).mp h),
      fun h2 => ?_⟩
    rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j, k, hch, hjb, hchj, _, hKnd, hLnd⟩
    · exact absurd h2' h2
    · have hj : j ∈ children M i := by rw [hch]; simp
      have hjl := (mem_children hj).2
      have hjx : j < r + L := by
        by_contra h'
        have : j = r + L := by omega
        have h' := (mem_children_iff.mp hj).2; rw [this, hp] at h'; cases h'
        rw [this] at hjb; exact hXb hjb
      have hk : k ∈ children M j := by rw [hchj]; simp
      have hkl := (mem_children hk).2
      have hkx : k < r + L := by
        by_contra h'
        have : k = r + L := by omega
        have hpk := (mem_children_iff.mp hk).2
        rw [this, hp] at hpk; cases hpk
        exact hrb i (mem_children_iff.mp hj).2 hjb
      have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
      exact ⟨Lb, Kb, j, k, hch, hjb, hchj,
        fun d hd h => hKnd d hd ((hiff true d (by have := hKk d hd; omega)).mp h),
        fun d hd e he h => (hLnd d hd e he).2 ((hiff true e (hLnd d hd e he).1).mp h)⟩

/-- `DepS` is monotone in the seeds. -/
theorem DepS.mono {M : Mat} {S S' : Bool → Nat → Prop} (hS : ∀ b i, S b i → S' b i) {b : Bool} {i : Nat}
    (h : DepS M S b i) : DepS M S' b i := by
  induction h with
  | seed hs => exact DepS.seed (hS _ _ hs)
  | ochild hc hcb hcu _ ih => exact DepS.ochild hc hcb hcu ih
  | ov _ ih => exact DepS.ov ih
  | vpar h1 hpm _ ih => exact DepS.vpar h1 hpm ih
  | vupg h1 h2 hu _ ih => exact DepS.vupg h1 h2 hu ih
  | vbump h1 h2 hj hjb hk _ ih => exact DepS.vbump h1 h2 hj hjb hk ih

/-- **`r = x − 1`**: below `x`, `D` from `{o(r), v(r)}` is `D` from `{o(r)}` plus `v(r)`. -/
theorem depS_SV_sub {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hp : par M 0 (r + L) = some r)
    (hL1 : r = r + L - 1) (hXu : ∀ i, upg M i ≠ some (r + L))
    (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p) (he2r : entry M 2 r = 0)
    {b : Bool} {i : Nat} (h : DepS M (SV r (r + L - 1)) b i) :
    i < r + L → DepS M (SR r) b i ∨ (b = false ∧ i = r) := by
  have hxc : ∀ i c, c ∈ children M i → ¬ c < r + L → i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have h' := (mem_children_iff.mp hc).2
    rw [show c = r + L by omega, hp] at h'; exact (Option.some.inj h').symm
  induction h with
  | seed hs =>
    intro _
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, h⟩
    · exact Or.inl (DepS.seed ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, by omega⟩
  | @ochild i c hc hcb hcu hdc ih =>
    intro hi
    by_cases hcx : c < r + L
    · rcases ih hcx with h | ⟨h, _⟩
      · exact Or.inl (DepS.ochild hc hcb hcu h)
      · cases h
    · exact Or.inl (DepS.seed ⟨rfl, hxc i c hc hcx⟩)
  | @ov i _ ih =>
    intro hi
    rcases ih hi with h | ⟨_, hir⟩
    · exact Or.inl (DepS.ov h)
    · exact Or.inl (DepS.seed ⟨rfl, hir⟩)
  | @vpar i m h1 hpm _ ih =>
    intro hi
    have hmi := par_lt M 1 i m hpm
    rcases ih (by omega) with h | ⟨_, hmr⟩
    · exact Or.inl (DepS.vpar h1 hpm h)
    · omega
  | @vupg i k h1 h2 hu _ ih =>
    intro hi
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    have hkx : k < r + L := by
      have hk : k ≠ r + L := fun e => hXu i (e ▸ hu)
      rcases hcase with h | ⟨_, h⟩ <;> omega
    rcases ih hkx with h | ⟨_, hkr⟩
    · exact Or.inl (DepS.vupg h1 h2 hu h)
    · have := upg_target_e2 hu; rw [hkr] at this; omega
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hi
    by_cases hkx : k < r + L
    · rcases ih hkx with h | ⟨h, _⟩
      · exact Or.inl (DepS.vbump h1 h2 hj hjb hk h)
      · cases h
    · have hjr := hxc j k hk hkx
      rw [hjr] at hj hjb
      exact absurd hjb (hrb i (mem_children_iff.mp hj).2)

/-- **The shape of `D = DepS M {o(r), v(r)}`** (`q = r = x − 1`, `x − 1` upgrades below `x`), from the
structure of `M`. -/
theorem qu_shapes {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (hL1 : r = r + L - 1) (hXu : ∀ i, upg M i ≠ some (r + L))
    (hXb : col M (r + L) ≠ bump M r) (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p)
    (he2r : entry M 2 r = 0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M) :
    (∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
    (∀ c, c < r + L → c ≠ r → DepS M (SV r (r + L - 1)) false c → CL M c = []) ∧
    OSh M (SV r (r + L - 1)) (r + L) ∧ VSh M (SV r (r + L - 1)) (r + L) := by
  have hx : r + L + 1 = M.length := hlen
  have hsub := fun {b} {i} (h : DepS M (SV r (r + L - 1)) b i) => depS_SV_sub hlen hp hL1 hXu hrb he2r h
  have hmono : ∀ {b i}, DepS M (SR r) b i → DepS M (SV r (r + L - 1)) b i :=
    fun h => DepS.mono (fun b i hs => Or.inl hs) h
  have hiff : ∀ b i, i < r + L → (DepS M (SR r) b i ↔ DepX M (r + L) b i) :=
    fun b i hi => depS_iff_depX hlen hL hp hXu hXb hrb hi
  obtain ⟨dvR, osR, vshR⟩ := qr_shapes hlen hL hp hXu hXb hrb hR0 hZ2 hSD hZ1 hUAT hUAB
  have hxc : ∀ i c, c ∈ children M i → ¬ c < r + L → i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have h' := (mem_children_iff.mp hc).2
    rw [show c = r + L by omega, hp] at h'; exact (Option.some.inj h').symm
  refine ⟨fun m hm hd => ?_, fun c hc hcr hd => ?_, fun i hi hns hD hv => ?_, fun i hi hns hD => ?_⟩
  · rw [← hL1] at hm
    have hmr := par_lt M 1 r m hm
    rcases hsub hd (by omega) with h | ⟨_, h⟩
    · have hDX := (hiff false m (by omega)).mp h
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hDX)).1 rfl (by omega) |>.2.2 r
        (by omega) hm
    · omega
  · rcases hsub hd hc with h | ⟨_, h⟩
    · exact dvR c hc h
    · exact absurd h hcr
  · have hir : i ≠ r := fun h => hns (Or.inl ⟨rfl, h⟩)
    have hDR : DepS M (SR r) true i := by
      rcases hsub hD hi with h | ⟨h, _⟩
      · exact h
      · cases h
    obtain ⟨Lp, c, R, hch, hcnt, hdc, hR, hLp⟩ :=
      osR i hi (fun h => hir h.2) hDR (fun h => hv (hmono h))
    refine ⟨Lp, c, R, hch, hcnt, hmono hdc, hR, fun d hd hcd h => hLp d hd hcd ?_⟩
    have hdM : d ∈ children M i := by rw [hch]; simp [hd]
    have hdx : d < r + L := by
      by_contra h'; exact hir (hxc i d hdM h')
    rcases hsub h hdx with h' | ⟨h', _⟩
    · exact h'
    · cases h'
  · have hir : i ≠ r := fun h => hns (Or.inr ⟨rfl, by omega⟩)
    have hDR : DepS M (SR r) false i := by
      rcases hsub hD hi with h | ⟨_, h⟩
      · exact h
      · exact absurd h hir
    obtain ⟨hpm, hb⟩ := vshR i hi (fun h => by cases h.1) hDR
    refine ⟨fun m hm h => ?_, fun h2 => ?_⟩
    · have hmi := par_lt M 1 i m hm
      rcases hsub h (by omega) with h' | ⟨_, hmr⟩
      · exact hpm m hm h'
      · omega
    · obtain ⟨Lb, Kb, j, k, hchi, hjb, hchj, hKnd, hLnd⟩ := hb h2
      have hj : j ∈ children M i := by rw [hchi]; simp
      have hjr : j ≠ r := fun e => by
        rw [e] at hjb; exact hrb i (by rw [← e]; exact (mem_children_iff.mp hj).2) hjb
      refine ⟨Lb, Kb, j, k, hchi, hjb, hchj, fun d hd h => hKnd d hd ?_, fun d hd e he h => hLnd d hd e he ?_⟩
      · have hdM : d ∈ children M j := by rw [hchj]; simp [hd]
        have hdx : d < r + L := by
          by_contra h'; exact hjr (hxc j d hdM h')
        rcases hsub h hdx with h' | ⟨h', _⟩
        · exact h'
        · cases h'
      · have hdM : d ∈ children M i := by rw [hchi]; simp [hd]
        have hLj : d < j := (sib_order (children_sorted M i) (R := []) (by rw [hchi])).1 d hd
        have hex : e < r + L := by
          by_contra h'
          have hdr := hxc d e he h'
          have hjl := (mem_children hj).2
          have hjx : j = r + L := by omega
          have hpj := (mem_children_iff.mp hj).2
          rw [hjx, hp] at hpj
          exact hir (Option.some.inj hpj).symm
        rcases hsub h hex with h' | ⟨h', _⟩
        · exact h'
        · cases h'

/-- No column upgrades into `x` (`q ≠ r`). -/
theorem upg_not_x' {M : Mat} {r L qp : Nat} (hlen : r + L + 1 = M.length)
    (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : 0 < qp)
    (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M) : ∀ i, upg M i ≠ some (r + L) := by
  intro i hu
  have := upg_succ_lt hu
  have hqx := par_lt M 0 _ _ hp
  exact upg_not_x hlen hA hp hxb hBE hu (le_refl _) (by omega)

/-- **`o(pq)` is a change** (`q ≠ r`): through `o(q)` if `q` counts at `pq`, else through `x − 1`... the
upgrade `q − 1 → q`. -/
theorem chg_pq {M : Mat} {r L qp pq : Nat} (hlen : r + L + 1 = M.length)
    (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : 0 < qp)
    (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M) (hR0 : R0P M) (hZ2 : Z2 M) (hUAT : UAT M)
    (hR12 : R12 M) (hpq : par M 0 (r + qp) = some pq) (hqb : col M (r + qp) ≠ bump M pq) (he1q : entry M 1 (r + qp) ≠ 0) :
    ChgX M (r + L) true pq := by
  have hXu := upg_not_x' hlen hA hp hqp hxb hBE
  have hqx := par_lt M 0 _ _ hp
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have he2q : entry M 2 (r + qp) ≠ 0 := by rw [hBE _ _ hxq hxb]; omega
  have hsnb : ChgX M (r + L) false (r + qp) := ChgX.snb he1q he2q hxq hxb
  have hqpq : r + qp ∈ children M pq := mem_children_iff.mpr ⟨by omega, hpq⟩
  by_cases hcu : isUpg M (r + qp) = true ∧ topped M (r + qp) = true
  · obtain ⟨hiu, htop⟩ := hcu
    unfold isUpg at hiu
    obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
    have hu : upg M k0 = some (r + qp) := of_decide_eq_true hk0
    have hk0q : k0 + 1 = r + qp := by
      by_contra hne
      have := hUAT k0 (r + qp) hu (fun h => hne h.symm)
      rw [this] at htop; cases htop
    obtain ⟨m, hm1, hmq, hcol, _⟩ := upg_spec hu
    have hpqq := par_lt M 0 _ _ hpq
    have hAmq := anc0_of_par M 1 m (r + qp) hmq
    have hApq : Anc0 M pq (r + qp) := Anc0.step hpq (Anc0.refl pq)
    have hme : m = pq := by
      apply anc0_eq_of_e0 hAmq hApq
      have := e0_of_col hcol; have := hR0 _ _ hpq; omega
    subst hme
    have hAk0 := anc0_of_par M 1 m k0 hm1
    have hk0l : k0 < M.length := by omega
    obtain ⟨he1k, he2k⟩ := upg_e12 hu
    have he2k0 : entry M 2 k0 = 0 := by have := hZ2 k0; omega
    have hSC1 : ∀ b i, (fun b i => b = false ∧ i = r + qp : Bool → Nat → Prop) b i → ChgX M (r + L) b i := by
      rintro b i ⟨rfl, rfl⟩; exact hsnb
    have hD : DepS M (fun b i => b = false ∧ i = r + qp) true k0 :=
      DepS.ov (DepS.vupg he1k he2k0 hu (DepS.seed ⟨rfl, rfl⟩))
    have hDm := path_upS hUAT hZ2 hR12 hBE (k0 - m) m k0 (le_refl _) hk0l hAk0 (ne_of_e2z he2k0) hD
      (fun t hmt htk => ⟨k0, hk0l, Anc0.refl k0, fun hA => by
        rw [hk0q] at hA
        have htq : t ≠ r + qp := by have := htk.le; omega
        have := (anc0_par hA htq hpq).le; omega⟩)
    exact depS_chgX hlen hXu hSC1 hDm (by omega)
  · exact ChgX.ochild hqpq hqb hcu (ChgX.ov hsnb)

/-- **The shape of `D = DepS M {v(q), o(pq)}`** (`q ≠ r`), from the structure of `M`. -/
theorem qn_shapes {M : Mat} {r L qp pq : Nat} (hlen : r + L + 1 = M.length)
    (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : 0 < qp)
    (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M) (hR12 : R12 M)
    (hpq : par M 0 (r + qp) = some pq) (hqb : col M (r + qp) ≠ bump M pq) :
    (∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m) ∧
    (∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
      ¬ DepS M (SQ (r + qp) pq) true e) ∧
    (∀ c, c < r + L → DepS M (SQ (r + qp) pq) false c → CL M c = []) ∧
    OShW M (SQ (r + qp) pq) (WQ (r + qp)) (r + L) ∧ VSh M (SQ (r + qp) pq) (r + L) := by
  have hx : r + L + 1 = M.length := hlen
  have hXu := upg_not_x' hlen hA hp hqp hxb hBE
  have hqx := par_lt M 0 _ _ hp
  have hpqq := par_lt M 0 _ _ hpq
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have he2q : entry M 2 (r + qp) = 1 := hBE _ _ hxq hxb
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0
    have := e2_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    omega
  have hAq : Anc0 M (r + qp) (r + L) := Anc0.step hp (Anc0.refl _)
  have hSC : ∀ b i, (SQ (r + qp) pq) b i → ChgX M (r + L) b i := by
    rintro b i (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ChgX.snb he1q (by omega) hxq hxb
    · exact chg_pq hlen hA hp hqp hxb hBE hR0 hZ2 hUAT hR12 hpq hqb he1q
  have hSA : ∀ b i, (SQ (r + qp) pq) b i → Anc0 M i (r + L) ∧ i < r + L := by
    rintro b i (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hAq, hqx⟩
    · exact ⟨Anc0.step hp (Anc0.step hpq (Anc0.refl _)), by omega⟩
  refine ⟨fun m hm hd => ?_, fun d hd _ e he hD => ?_, fun c hc hd => ?_, fun i hi hns hnw hD hv => ?_,
    fun i hi hns hD => vsh_S hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hi hns hD⟩
  · have hmq := par_lt M 1 _ m hm
    exact (topC_of_depS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA (by omega) hd).2.2 _ hqx hm
  · have hdx : d < r + L := by have := (mem_children he).1; have := (mem_children he).2; omega
    exact nodep_below_q hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hp hd hdx hD
      (Anc0.step (mem_children_iff.mp he).2 (Anc0.refl d))
  · unfold CL; rw [List.filter_eq_nil_iff]
    intro d hdc hcnt
    apply uncnt_of_depvS hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hc hd hdc _ (of_decide_eq_true hcnt)
    intro hxc hcx
    have hcq : c = r + qp := by
      have := (mem_children_iff.mp hxc).2; rw [hp] at this; exact (Option.some.inj this).symm
    rw [hcq] at hcx; exact hcx.1 hxb
  · apply os_S hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hSC hSA hi hns hD hv
    intro d hd hxd
    have hdq : d = r + qp := by
      have := (mem_children_iff.mp hxd).2; rw [hp] at this; exact (Option.some.inj this).symm
    have hipq : i = pq := by
      have := (mem_children_iff.mp hd).2; rw [hdq, hpq] at this; exact (Option.some.inj this).symm
    exact hns (Or.inr ⟨rfl, hipq⟩)

/-- **The first child counts** when it is not a bump child (`UAT`: an upgrade into it would come from `p`). -/
theorem first_child_counted {M : Mat} {p d : Nat} (hR0 : R0P M) (hUAT : UAT M) (hA : Anc0 M p d)
    (hpd : p ≠ d) (hnb : col M (p + 1) ≠ bump M p) : p + 1 ∈ children M p ∧ Counted M p (p + 1) := by
  have hpl := hA.le
  have hdl : d < M.length := anc0_lt_len hA hpd
  have hA1 : Anc0 M p (p + 1) := anc_between hA (p + 1) (by omega) (by omega)
  obtain ⟨p1, hp1⟩ := par0_of_anc hA1 (by omega)
  have hp1ge := (anc0_par hA1 (by omega) hp1).le
  have hp1lt := par_lt M 0 _ _ hp1
  have hp1e : p1 = p := by omega
  rw [hp1e] at hp1
  refine ⟨mem_children_iff.mpr ⟨by omega, hp1⟩, hnb, ?_⟩
  rintro ⟨hu, ht⟩
  unfold isUpg at hu
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
  have hk' : upg M k = some (p + 1) := of_decide_eq_true hk
  have hkp : k = p := by
    by_contra hne
    have := hUAT k (p + 1) hk' (by omega)
    rw [ht] at this; cases this
  rw [hkp] at hk'
  obtain ⟨m, hm, _, hcol, _⟩ := upg_spec hk'
  have := anc0_e0_lt (anc0_of_par M 1 m p hm) (by have := par_lt M 1 p m hm; omega)
  have h0 : entry M 0 (p + 1) = entry M 0 m + 1 := by rw [col_eq_entries] at hcol; exact (Prod.mk.inj hcol).1
  have := hR0 _ _ hp1
  omega

/-- `r ≠ x − 1` when `x − 1` upgrades to `x` (`r = P_2(x)`). -/
theorem rx_of_sv {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hZ2 : Z2 M) (hZ1 : Z1C M)
    (hr : par M 2 (r + L) = some r) (hu : upg M (r + L - 1) = some (r + L)) : r ≠ r + L - 1 := by
  have h1 := par1_of_par2 hZ2 hZ1 (by omega) hr
  obtain ⟨m, hm, hmx, _, _⟩ := upg_spec hu
  rw [h1] at hmx; cases hmx
  have := par_lt M 1 _ _ hm; omega

/-- **`r` counts a child** when `x − 1` upgrades to `x` (`q = r`): the first child of `r`. -/
theorem rcl_sv {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hp : par M 0 (r + L) = some r)
    (hr : par M 2 (r + L) = some r) (hu : upg M (r + L - 1) = some (r + L)) (hZ2 : Z2 M) (hZ1 : Z1C M)
    (hR0 : R0P M) (hUAT : UAT M) (hBE : BumpE2 M) (he2r : entry M 2 r = 0) : CL M r ≠ [] := by
  have hrx := rx_of_sv hlen hZ2 hZ1 hr hu
  have hA : Anc0 M r (r + L) := Anc0.step hp (Anc0.refl r)
  have hrl := par_lt M 0 _ _ hp
  have hAa : Anc0 M r (r + L - 1) := anc_between hA _ (by omega) (by omega)
  have hnb : col M (r + 1) ≠ bump M r := by
    intro hb
    have hc : r + 1 ∈ children M r := by
      have hA1 : Anc0 M r (r + 1) := anc_between hA (r + 1) (by omega) (by omega)
      obtain ⟨p1, hp1⟩ := par0_of_anc hA1 (by omega)
      have := (anc0_par hA1 (by omega) hp1).le
      have := par_lt M 0 _ _ hp1
      have hpe : p1 = r := by omega
      rw [hpe] at hp1
      exact mem_children_iff.mpr ⟨by omega, hp1⟩
    have := hBE r (r + 1) hc hb; omega
  obtain ⟨hc, hcnt⟩ := first_child_counted hR0 hUAT hAa hrx hnb
  intro hnil
  have hin : r + 1 ∈ CL M r := by
    unfold CL; rw [List.mem_filter]; exact ⟨hc, decide_eq_true hcnt⟩
  rw [hnil] at hin; simp at hin

/-- **The shape of `D = DepS M {o(r), v(x − 1)}`** (`q = r`, `x − 1` upgrades, `r ≠ x − 1`), from the
structure of `M`. -/
theorem sv_shapes {M : Mat} {r L k : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (hu : upg M (r + L - 1) = some k) (hrx : r ≠ r + L - 1)
    (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p) (he2r : entry M 2 r = 0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) :
    (∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧ ¬ DepS M (SV r (r + L - 1)) false r ∧
    (∀ c, c < r + L → DepS M (SV r (r + L - 1)) false c → CL M c = []) ∧ OSh M (SV r (r + L - 1)) (r + L) ∧ VSh M (SV r (r + L - 1)) (r + L) := by
  have hx : r + L + 1 = M.length := hlen
  have hA : Anc0 M r (r + L) := Anc0.step hp (Anc0.refl r)
  have hAa : Anc0 M r (r + L - 1) := anc_between hA _ (by omega) (by omega)
  obtain ⟨he1a, he2a'⟩ := upg_e12 hu
  have he2a : entry M 2 (r + L - 1) = 0 := by have := hZ2 (r + L - 1); omega
  have hXu : ∀ i, upg M i = some (r + L) → i = r + L - 1 := by
    intro i hi
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hi
    have := upg_succ_lt hi
    rcases hcase with h | ⟨_, h⟩ <;> omega
  -- `o(r)` is a change: up the path from `x − 1`
  have hor : ChgX M (r + L) true r := by
    have hSC1 : ∀ b i, (fun b i => b = false ∧ i = r + L - 1 : Bool → Nat → Prop) b i → ChgX M (r + L) b i := by
      rintro b i ⟨rfl, rfl⟩; exact ChgX.supg (by rw [show r + L - 1 = r + L - 1 from rfl, hu]; simp)
    have hD : DepS M (fun b i => b = false ∧ i = r + L - 1) true (r + L - 1) := DepS.ov (DepS.seed ⟨rfl, rfl⟩)
    have hDr := path_upS hUAT hZ2 hR12 hBE (r + L - 1 - r) r (r + L - 1) (le_refl _) (by omega) hAa
      (ne_of_e2z he2a) hD (fun t hrt hta => ⟨r + L - 1, by omega, Anc0.refl _, fun hAt => by
        rw [show r + L - 1 + 1 = r + L by omega] at hAt
        have htx : t ≠ r + L := by have := hta.le; omega
        have := (anc0_par hAt htx hp).le; omega⟩)
    exact depS_chgX2 hx hSC1 (fun i hi => ⟨rfl, hXu i hi⟩) hDr (by omega)
  have hSC : ∀ b i, (SV r (r + L - 1)) b i → ChgX M (r + L) b i := by
    rintro b i (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hor
    · exact ChgX.supg (by rw [hu]; simp)
  have hSA : ∀ b i, (SV r (r + L - 1)) b i → (Anc0 M i (r + L) ∧ i < r + L) ∨ (b = false ∧ i = r + L - 1) := by
    rintro b i (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨hA, by omega⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hXu2 : ∀ i, upg M i = some (r + L) → (SV r (r + L - 1)) false i := fun i hi => Or.inr ⟨rfl, hXu i hi⟩
  -- `v(r)` is not in `D`: `r` is not topped in `M.take x`
  have hvr : ¬ DepS M (SV r (r + L - 1)) false r := by
    intro hd
    have hT := topC_of_depS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 (by omega) hd
    obtain ⟨c, hrc, hca⟩ := anc0_child hAa hrx
    have hcl : c ≤ r + L - 1 := hca.le
    have hcM : c ∈ children M r := mem_children_iff.mpr ⟨by omega, hrc⟩
    have hcT : c ∈ children (M.take (r + L)) r := mem_take_children hcM (by omega)
    have hmax : ∀ e ∈ children (M.take (r + L)) r, e ≤ c := by
      intro e he
      rw [children_take, List.mem_filter] at he
      have hex : e < r + L := by simpa using he.2
      have hpe : par M 0 e = some r := (mem_children_iff.mp he.1).2
      by_contra hlt
      have hAe := anc_between hca e (by omega) (by omega)
      have := (anc0_par hAe (by omega) hpe).le
      have := (mem_children hcM).1; omega
    have hsplit := split_last_max _ _ (children_sorted (M.take (r + L)) r) hcT hmax
    have htop := hT.1
    unfold topped at htop
    rw [hsplit] at htop
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, decide_eq_true_eq] at htop
    rw [col_take M (by omega), bump_take M (by omega)] at htop
    have := hBE r c hcM htop
    omega
  refine ⟨fun m hm hd => ?_, hvr, fun c hc hd => ?_, fun i hi hns hD hv => ?_,
    fun i hi hns hD => vsh_S2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2
      (fun q hq h2 => by rw [hp] at hq; cases hq; exact absurd he2r h2)
      (fun q i hq hqi => by rw [hp] at hq; cases hq; exact hrb i (mem_children_iff.mp hqi).2) hi hns hD⟩
  · have hma := par_lt M 1 _ m hm
    exact (topC_of_depS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 (by omega) hd).2.2 _ (by omega) hm
  · unfold CL; rw [List.filter_eq_nil_iff]
    intro d hdc hcnt
    apply uncnt_of_depvS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 hc hd hdc _ (of_decide_eq_true hcnt)
    intro hxc
    have hcr : c = r := by
      have := (mem_children_iff.mp hxc).2; rw [hp] at this; exact (Option.some.inj this).symm
    rw [hcr] at hd; exact absurd hd hvr
  · apply os_S2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 hi hns hD hv
    · intro hxi; rw [hp] at hxi; cases hxi; exact absurd (Or.inl ⟨rfl, rfl⟩) hns
    · intro d _ hxd
      have hdr : d = r := by
        have := (mem_children_iff.mp hxd).2; rw [hp] at this; exact (Option.some.inj this).symm
      rw [hdr]; exact hvr

/-- **The shape of `D = DepS M {v(q), o(q), o(pq), v(x − 1)}`** (`q ≠ r`, `x − 1` upgrades), from the
structure of `M`. -/
theorem qnu_shapes {M : Mat} {r L qp pq k : Nat} (hlen : r + L + 1 = M.length)
    (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : 0 < qp)
    (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M) (hR12 : R12 M)
    (hpq : par M 0 (r + qp) = some pq) (hqb : col M (r + qp) ≠ bump M pq)
    (hu : upg M (r + L - 1) = some k) :
    (∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m) ∧
    (∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m) ∧
    (∃ Lb d Kb e, children M (r + qp) = Lb ++ [d, r + L] ∧ children M d = Kb ++ [e] ∧
      (∀ f ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true f) ∧
      (∀ d' ∈ Lb, ∀ e' ∈ children M d', ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e')) ∧
    (∀ c, c < r + L → DepS M (SQU (r + qp) pq (r + L - 1)) false c → CL M c = []) ∧
    OSh M (SQU (r + qp) pq (r + L - 1)) (r + L) ∧ VSh M (SQU (r + qp) pq (r + L - 1)) (r + L) := by
  have hx : r + L + 1 = M.length := hlen
  have hXu := upg_not_x' hlen hA hp hqp hxb hBE
  have hqx := par_lt M 0 _ _ hp
  have hpqq := par_lt M 0 _ _ hpq
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have he2q : entry M 2 (r + qp) = 1 := hBE _ _ hxq hxb
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0
    have := e2_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    omega
  obtain ⟨he1a, he2a'⟩ := upg_e12 hu
  have he2a : entry M 2 (r + L - 1) = 0 := by have := hZ2 (r + L - 1); omega
  have hAq : Anc0 M (r + qp) (r + L) := Anc0.step hp (Anc0.refl _)
  have hsnb : ChgX M (r + L) false (r + qp) := ChgX.snb he1q (by omega) hxq hxb
  have hSC : ∀ b i, (SQU (r + qp) pq (r + L - 1)) b i → ChgX M (r + L) b i := by
    rintro b i (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · cases b
      · exact hsnb
      · exact ChgX.ov hsnb
    · exact chg_pq hlen hA hp hqp hxb hBE hR0 hZ2 hUAT hR12 hpq hqb he1q
    · exact ChgX.supg (by rw [hu]; simp)
  have hSA : ∀ b i, (SQU (r + qp) pq (r + L - 1)) b i → (Anc0 M i (r + L) ∧ i < r + L) ∨ (b = false ∧ i = r + L - 1) := by
    rintro b i (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨hAq, hqx⟩
    · exact Or.inl ⟨Anc0.step hp (Anc0.step hpq (Anc0.refl _)), by omega⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hXu2 : ∀ i, upg M i = some (r + L) → (SQU (r + qp) pq (r + L - 1)) false i := fun i hi => absurd hi (hXu i)
  have hT := fun {m} (hm : m < r + L) (hd : DepS M (SQU (r + qp) pq (r + L - 1)) false m) =>
    topC_of_depS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 hm hd
  -- the shape below `q`
  have hqsh : ∃ Lb d Kb e, children M (r + qp) = Lb ++ [d, r + L] ∧ children M d = Kb ++ [e] ∧
      (∀ f ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true f) ∧
      (∀ d' ∈ Lb, ∀ e' ∈ children M d', ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e') := by
    have hAqa : Anc0 M (r + qp) (r + L - 1) := anc_between hAq _ (by omega) (by omega)
    have hqa : r + qp ≠ r + L - 1 := by intro h; rw [h] at he2q; omega
    obtain ⟨d, hqd, hda⟩ := anc0_child hAqa hqa
    have hdl : d ≤ r + L - 1 := hda.le
    have hdM : d ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hqd⟩
    have hqdl := (mem_children hdM).1
    have hall := all_bump_of_last hR0 hZ2 hSD hZ1 he2q (children_split_x hlen hxq) hxb
    have he2d : entry M 2 d = 1 :=
      e2_of_col (show col M d = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hall d hdM)
    have hda' : d ≠ r + L - 1 := by intro h; rw [h] at he2d; omega
    obtain ⟨e, hde, hea⟩ := anc0_child hda hda'
    have hel : e ≤ r + L - 1 := hea.le
    have heM : e ∈ children M d := mem_children_iff.mpr ⟨by omega, hde⟩
    have hdel := (mem_children heM).1
    -- `d` is the last child of `q` before `x`, `e` the last child of `d`
    have hF := split_last_max ((children M (r + qp)).filter (fun c => decide (c < r + L))) d
      ((children_sorted M _).filter _) (List.mem_filter.mpr ⟨hdM, by simpa using (show d < r + L by omega)⟩)
      (fun c hc => by
        have hcM := (List.mem_filter.mp hc).1
        have hcx : c < r + L := by simpa using (List.mem_filter.mp hc).2
        by_contra hlt
        have hAc := anc_between hda c (by omega) (by omega)
        have := (anc0_par hAc (by omega) (mem_children_iff.mp hcM).2).le; omega)
    have hE := split_last_max (children M d) e (children_sorted M d) heM (fun c hc => by
      have hcl := (mem_children hc).2
      have hcx : c ≠ r + L := by
        intro h; have := (mem_children_iff.mp hc).2; rw [h, hp] at this
        have := Option.some.inj this; omega
      by_contra hlt
      have hAc := anc_between hea c (by omega) (by omega)
      have := (anc0_par hAc (by omega) (mem_children_iff.mp hc).2).le; omega)
    refine ⟨((children M (r + qp)).filter (fun c => decide (c < r + L))).filter (fun c => decide (c < d)),
      d, (children M d).filter (fun c => decide (c < e)), e, ?_, hE, fun f hf hD => ?_,
      fun d' hd' e' he' hD => ?_⟩
    · rw [children_split_x hlen hxq]
      conv_lhs => rw [hF]
      simp
    · have hfM := (List.mem_filter.mp hf).1
      have hfe : f < e := by simpa using (List.mem_filter.mp hf).2
      exact nodep_not_lastS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 (by omega) hfM heM hfe (by omega) hD
        (Anc0.refl f)
    · have hd'M := (List.mem_filter.mp hd').1
      have hd'd : d' < d := by simpa using (List.mem_filter.mp hd').2
      exact nodep_not_lastS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 (by omega) (List.mem_filter.mp hd'M).1
        hdM hd'd (by omega) hD (Anc0.step (mem_children_iff.mp he').2 (Anc0.refl d'))
  refine ⟨fun m hm hd => ?_, fun m hm hd => ?_, hqsh, fun c hc hd => ?_, fun i hi hns hD hv => ?_,
    fun i hi hns hD => vsh_S2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2
      (fun q hq _ => by rw [hp] at hq; cases hq; exact Or.inl rfl)
      (fun q i hq hqi => by
        rw [hp] at hq; cases hq
        have := (mem_children_iff.mp hqi).2; rw [hpq] at this; cases this; exact hqb) hi hns hD⟩
  · have hmq := par_lt M 1 _ m hm
    exact (hT (by omega) hd).2.2 _ hqx hm
  · have hma := par_lt M 1 _ m hm
    exact (hT (by omega) hd).2.2 _ (by omega) hm
  · unfold CL; rw [List.filter_eq_nil_iff]
    intro d hdc hcnt
    apply uncnt_of_depvS2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 hc hd hdc _ (of_decide_eq_true hcnt)
    intro hxc hcx
    have hcq : c = r + qp := by
      have := (mem_children_iff.mp hxc).2; rw [hp] at this; exact (Option.some.inj this).symm
    rw [hcq] at hcx; exact hcx.1 hxb
  · apply os_S2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hSC hSA hXu2 hi hns hD hv
    · intro hxi; rw [hp] at hxi; cases hxi; exact absurd (Or.inl rfl) hns
    · intro d hd hxd
      have hdq : d = r + qp := by
        have := (mem_children_iff.mp hxd).2; rw [hp] at this; exact (Option.some.inj this).symm
      have hipq : i = pq := by
        have := (mem_children_iff.mp hd).2; rw [hdq, hpq] at this; exact (Option.some.inj this).symm
      exact absurd (Or.inr (Or.inl ⟨rfl, hipq⟩)) hns

/-- **A topped column before `x` is upgraded in `N` iff in `M`**, when `N` and `M` agree before `x` and both
satisfy `UAT` (an upgrade into a topped column comes from the column just before it). -/
theorem isUpg_topped_take {M N : Mat} {x c : Nat} (hxM : x ≤ M.length) (hxN : x ≤ N.length)
    (hT : N.take x = M.take x) (hUM : UAT M) (hUN : UAT N) (hc : c < x)
    (htN : topped N c = true) (htM : topped M c = true) : isUpg N c = isUpg M c := by
  have hup : ∀ i, i + 1 < x → upg N i = upg M i := fun i hi => by
    rw [← upg_take N hi, hT, upg_take M hi]
  apply Bool.eq_iff_iff.mpr
  unfold isUpg
  simp only [List.any_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · rintro ⟨i, _, hu⟩
    have hci : c = i + 1 := by
      by_contra h; have := hUN i c hu h; rw [htN] at this; cases this
    exact ⟨i, by omega, by rw [← hup i (by omega)]; exact hu⟩
  · rintro ⟨i, _, hu⟩
    have hci : c = i + 1 := by
      by_contra h; have := hUM i c hu h; rw [htM] at this; cases this
    exact ⟨i, by omega, by rw [hup i (by omega)]; exact hu⟩

/-- `topped` agrees when the children agree with the same columns. -/
theorem topped_eq_of {M N : Mat} {c : Nat} (hch : children N c = children M c)
    (hcol : ∀ d ∈ children M c, col N d = col M d) (hb : bump N c = bump M c) :
    topped N c = topped M c := by
  unfold topped
  rw [hch]
  cases h : (children M c).getLast? with
  | none => rfl
  | some d =>
    have hd : d ∈ children M c := List.mem_of_getLast? h
    simp only
    rw [hcol d hd, hb]

/-- **`q ≠ r`** (`x` a bump child of `q = r + qp`, `P_0 q = pq`). -/
structure T2QN (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L qp pq : Nat) : Prop where
  seed1 : (drop1 M (r + L) rk).o pq ≠ ρ.o pq
  big : ∀ n σ, 2 ≤ n → Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    SeedL ρ σ pq

/-- **`q = r`, `x − 1` upgrades to `x`.** -/
structure T2SV (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat) : Prop where
  seed1 : (drop1 M (r + L) rk).o r ≠ ρ.o r
  big : ∀ n σ, 2 ≤ n → Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    SeedL ρ σ r

/-- **`q = r`, `x − 1` upgrades nowhere** (`n ≤ 1`). -/
structure T2QR (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat) : Prop where
  seed1 : (drop1 M (r + L) rk).o r ≠ ρ.o r

/-- **`q = r`, `x − 1` upgrades to `k < x`** (`n ≤ 1`). -/
structure T2QU (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L k : Nat) : Prop where
  seed1 : r ≠ r + L - 1 → (drop1 M (r + L) rk).o r ≠ ρ.o r

/-- **`q = r`.** -/
structure T2R (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat) : Prop where
  sv : upg M (r + L - 1) = some (r + L) → T2SV M ρ rk r L
  nn : upg M (r + L - 1) = none → T2QR M ρ rk r L
  up : ∀ k, upg M (r + L - 1) = some k → k < r + L → T2QU M ρ rk r L k
  big : upg M (r + L - 1) ≠ some (r + L) → ∀ n σ, 2 ≤ n → Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    SeedL ρ σ r

/-- **The remaining hypotheses of `t = 2`** (`x = r + L`, `r = P_2(x)`). -/
structure Res3T2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  qn : ∀ r L qp pq, r + L + 1 = M.length → par M 2 (r + L) = some r →
    par M 0 (r + L) = some (r + qp) → 0 < qp → par M 0 (r + qp) = some pq → T2QN M ρ rk r L qp pq
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    T2R M ρ rk r L

/-- **Step 1 for `t = 2`**: from the invariants, the remaining hypotheses (`Res3`, `Res3T2`) and a
valuation of each `M[n]` (`n ≥ 2`), every expansion drops the root value. -/
theorem t2_drops {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3 M ρ rk) (R : Res3 M ρ rk) (R2 : Res3T2 M ρ rk) (hX : SInvX M) (hJ : RowJ M)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hNval : ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
      ∃ σ rkN, Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧ Good3 (expand M n) σ) :
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
  obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hXu_of : upg M (r + L - 1) ≠ some (r + L) → ∀ i, upg M i ≠ some (r + L) := by
    intro hux i hu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    have hi : i < M.length := by
      by_contra h
      exact (upg_e12 hu).1 (entry_out (by omega) 1)
    rcases hcase with h | ⟨_, h⟩
    · exact hux (by rw [show r + L - 1 = i by omega]; exact hu)
    · omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hrU : isUpg M r = false := by
    cases h : isUpg M r with
    | false => rfl
    | true =>
      exfalso
      unfold isUpg at h
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
      have := upg_target_e2 (of_decide_eq_true hk); omega
  have hrcl_of : par M 0 (r + L) = some r → upg M (r + L - 1) ≠ some (r + L) → CL M r ≠ [] := by
    intro hq hux hnil
    have hcnt : Counted M r (r + L) := ⟨hxbr, by rw [isUpg_x_false (hXu_of hux)]; simp⟩
    have hxin : r + L ∈ CL M r := by
      unfold CL; rw [List.mem_filter]
      exact ⟨mem_children_iff.mpr ⟨by omega, hq⟩, by simpa using hcnt⟩
    rw [hnil] at hxin; simp at hxin
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
  have hAS : BumpAbsS M (r + L) ρ := by
    have := R.abS.1 h2; rw [hL] at this; exact this
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rk) :=
    good3_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
  have hdrop := drop_all (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws)
    hdr.ua
  have hseed1 : ∀ p, p < r + L → CL M p ≠ [] → (drop1 M (r + L) rk).o p ≠ ρ.o p →
      Lhd z ((drop1 M (r + L) rk).o p) (ρ.o p) :=
    fun p hp hcl hne => lhd_of_po I.cons I.good (by omega) hcl (hdrop p hp).1 hne
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := (anc0_par hA (by omega) hq).le
  have hqx : q < r + L := par_lt M 0 _ q hq
  -- `n ≤ 1`: the drop to `M.take x`
  have hlast : isOT (root (M.take (r + L)) (drop1 M (r + L) rk)) = true ∧
      root (M.take (r + L)) (drop1 M (r + L) rk) < root M ρ := by
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hAbs := abs_of_absC hAS hq hrb
      cases hux : upg M (r + L - 1) with
      | none =>
        have T' := T.nn hux
        obtain ⟨hdv, hos, hvsh⟩ := qr_shapes hlen hL0 hq (hXu_of (by rw [hux]; simp)) hxbr hrb
          I.r0p I.z2 I.sd I.z1 I.uat I.uab
        exact t2_qr_take hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (hrcl_of hq (by rw [hux]; simp)) hrU hux
          hdv hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
          (hseed1 r (by omega) (hrcl_of hq (by rw [hux]; simp)) T'.seed1)
      | some k =>
        have hkl := upg_lt (by omega) hux
        by_cases hkx : k = r + L
        · rw [hkx] at hux
          have T' := T.sv hux
          obtain ⟨Sp1, _, Sdv, Sos, Svsh⟩ := sv_shapes hlen hL0 hq hux (rx_of_sv hlen I.z2 I.z1 hr hux) hrb he2r
            I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be
          exact t2_sv_take hlen hL0 hq hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) hrU
            Sp1 Sdv Sos Svsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
            (hseed1 r (by omega) (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) T'.seed1)
        · have hk : k < r + L := by omega
          have T' := T.up k hux hk
          obtain ⟨hp1, hdv, hos, hvsh⟩ :
              (∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
              (∀ c, c < r + L → c ≠ r → DepS M (SV r (r + L - 1)) false c → CL M c = []) ∧
              OSh M (SV r (r + L - 1)) (r + L) ∧ VSh M (SV r (r + L - 1)) (r + L) := by
            by_cases hrx : r = r + L - 1
            · exact qu_shapes hlen hL0 hq hrx (hXu_of (by rw [hux]; intro h; cases h; omega)) hxbr hrb he2r
                I.r0p I.z2 I.sd I.z1 I.uat I.uab
            · obtain ⟨h1, _, h3, h4, h5⟩ := sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat
                I.uab I.r12 I.be
              exact ⟨h1, fun c hc _ hd => h3 c hc hd, h4, h5⟩
          exact t2_qu_take hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (hrcl_of hq (by rw [hux]; intro h; cases h; omega)) hrU hux hk
            (I.uat _ k hux (by omega)) hp1 hdv
            (fun hrx => (sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be).2.1)
            hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
            hdr.ua hAbs
            (fun h => hseed1 r (by omega) (hrcl_of hq (by rw [hux]; intro h'; cases h'; omega)) (T'.seed1 h))
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      obtain ⟨Tp1, TqL, Tdv, Tos, Tvsh⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
        I.uat I.uab I.r12 hpq' Tqb
      have hAbs := abs_of_absC hAS hq' (fun i h => by rw [hpq'] at h; cases h; exact Tqb)
      have hs1 := hseed1 pq (by have := par_lt M 0 _ _ hpq; omega) Tclpq T.seed1
      cases hux : upg M (r + L - 1) with
      | none =>
        exact t2_qn_take hlen hL0 hA hq' (by omega) Txb I.be I.z2 I.uat I.r12 I.r01 I.e00 hpq' Tqb Te2pq
          Tclq Tclpq hux Tp1 TqL Tdv Tos Tvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
          hAbs hs1
      | some k =>
        obtain ⟨Up1, Up1a, Uqsh, Udv, Uos, Uvsh⟩ := qnu_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd
          I.z1 I.uat I.uab I.r12 hpq' Tqb hux
        exact t2_qnu_take hlen hL0 hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1 I.uat I.r12 I.r01 I.e00
          hpq' Tqb Te2pq Tclq Tclpq hux Up1 Up1a Uqsh Udv Uos Uvsh I.cons I.good I.rank hC1 hG1
          hRk1 I.fc I.vs I.td I.kd hdr.ua hAbs hs1
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
    have hT : (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).take
        (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
    have hUN : UAT (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) := by
      rw [← hexp n]; exact (sInvX_expand hX n).toSInv.uat
    have hlN := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := entry M 0 (r + L) - entry M 0 r)
      (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
    have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
    have hcolN : ∀ d, d < r + L →
        col (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) d = col M d :=
      fun d hd => col_gexp_pre hlen (by omega) hd
    have hbN : ∀ c, c < r + L →
        bump (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c = bump M c :=
      fun c hc => by unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hAbs := abs_of_absC hAS hq hrb
      by_cases hux : upg M (r + L - 1) = some (r + L)
      · have T' := T.sv hux
        obtain ⟨Sp1, _, Sdv, Sos, Svsh⟩ := sv_shapes hlen hL0 hq hux (rx_of_sv hlen I.z2 I.z1 hr hux) hrb he2r
          I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be
        have hseed := T'.big n σ hn hCN
        have hIUt : ∀ c, c < r + L → topped M c = true →
            isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
              isUpg M c := by
          intro c hc htM
          have hcr : c ≠ r := by
            intro hcr'
            rw [hcr'] at htM
            have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
            have hsplit := children_split_x hlen hxr
            unfold topped at htM; rw [hsplit] at htM; simp at htM
            exact hxbr htM
          have hch := children_N2 (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e (by omega) hn hc
          apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
          rw [topped_eq_of hch (fun d hd => hcolN d (by
            have := (mem_children hd).2
            by_contra h'
            have hdx : d = r + L := by omega
            have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcr (Option.some.inj this).symm))
            (hbN c hc)]
          exact htM
        exact t2_sv_main hlen hL0 hq hd0e hn hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) hIUt
          Sp1 Sdv Sos Svsh I.cons I.good I.rank hCN hGN hRN I.fc I.vs I.td I.kd hAbs hseed
      · have hseed := T.big hux n σ hn hCN
        have hIU : ∀ c, c < r + L → topped M c = true →
            isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
              isUpg M c := by
          intro c hc htM
          apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
          rw [topped_N2 (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e hn (hXu_of hux) hxbr he2r hc]
          exact htM
        have hxcN : Counted (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
            (entry M 1 (r + L) - entry M 1 r) n) r (r + L) := by
          have hx2 := (entry_xprime (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e (by omega) hn).1
          refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
          · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
          · unfold isUpg at hiu
            obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
            have := upg_target_e2 (of_decide_eq_true hk0); omega
        exact t2_qr_main hlen hL0 hq hd0e hn (hXu_of hux) hxbr hrb he2r hIU I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
          I.be I.r01 I.e00 I.cons I.good I.rank hCN hGN hRN I.fc I.vs I.td I.kd hAS hxcN hseed
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      obtain ⟨Tp1, TqL, Tdv, Tos, Tvsh⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
        I.uat I.uab I.r12 hpq' Tqb
      have hAbs := abs_of_absC hAS hq' (fun i h => by rw [hpq'] at h; cases h; exact Tqb)
      have hseed := T.big n σ hn hCN
      have hIUt : ∀ c, c < r + L → c ≠ r + (q - r) → topped M c = true →
          isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
            isUpg M c := by
        intro c hc hcq htM
        have hch := children_N2Q (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hA hq' (by omega) hd0e
          (by omega) hn hc
        apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
        rw [topped_eq_of hch (fun d hd => hcolN d (by
          have := (mem_children hd).2
          by_contra h'
          have hdx : d = r + L := by omega
          have := (mem_children_iff.mp hd).2; rw [hdx, hq'] at this; exact hcq (Option.some.inj this).symm))
          (hbN c hc)]
        exact htM
      exact t2_qn_main hlen hL0 hA hq' (by omega) hd0e hn Txb I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hpq'
        Tqb Te2pq Tclq Tclpq hIUt Tp1 TqL Tdv Tos Tvsh I.cons I.good I.rank hCN hGN hRN
        I.fc I.vs I.td I.kd hAbs hseed
  intro n
  rcases n with _ | _ | n
  · apply dropsAt_of (by rw [hexp 0, gexp_zero_gen])
    exact drop_n0_gen hlen hL0 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr (fun j _ hj => R.chain j (by omega)) hlast.2
  · apply dropsAt_of (by rw [hexp 1, gexp_one_gen hlen])
    exact ⟨_, _, hC1, hRk1, hlast⟩
  · have hne := gexp_ne_SRO (n := n + 2) hlen hL0 hA hd0e
      (show entry M 1 (r + L) = entry M 1 r + (entry M 1 (r + L) - entry M 1 r) by omega) he2r h1lt
      (by omega)
    have hnil : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n + 2)
        ≠ [] := by
      intro h
      have hl := TRIO.gexp_length (M := M) (j0 := r) (Lb := L)
        (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r) (n := n + 2) hlen
      rw [h] at hl
      have : L ≤ (n + 2) * L := Nat.le_mul_of_pos_left L (by omega)
      simp at hl; omega
    obtain ⟨σ, rkN, hCN, hRN, hGN⟩ := hNval (n + 2) (by omega) (by rw [hexp]; exact hne)
      (by rw [hexp]; exact hnil)
    rw [hexp] at hCN hRN hGN
    apply dropsAt_of (hexp (n + 2))
    exact ⟨σ, rkN, hCN, hRN, hbig (n + 2) (by omega) σ rkN hCN hRN hGN⟩

/-- **`hT2` of `trio_terminatesA`** from the remaining hypotheses `Res3T2`: the valuation of `M[n]`
(`n ≥ 2`) comes from the top hypothesis `HInvA` (`M[n]` is standard, not SRO, not empty). -/
theorem t2_hT2
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    HInvA → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n := by
  intro hInv M ρ rk hM I R hz h2
  have hne : M ≠ SRO := by intro h; subst h; revert h2; decide
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hne
  apply t2_drops I R (hR2 M ρ rk hM I R hz h2) hX hJ hz h2
  intro n _ hS hE
  unfold HInvA at hInv
  obtain ⟨⟨rkN, hRN⟩, hall⟩ := hInv _ (Std.exp n hM) hS hE
  have hCN := cons_of_rk hRN
  exact ⟨_, rkN, hCN, hRN, (hall _ rkN hCN hRN).1.good⟩

/-- **Termination of the 3-row BMS from SRO**, with `t = 2` reduced to `Res3T2`: the remaining
hypotheses are the top hypothesis `HInvA` and `Res3T2` on standard matrices with `t = 2`. -/
theorem trio_terminates_T2 (hInv : HInvA)
    (hR2 : ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk) :
    WellFounded Step' :=
  trio_terminatesA hInv (t2_hT2 hR2)

end Ytosk
