/-
**3 行・t = 2・q ≠ r: 組み立て。**

q = P_0(x) ≠ r（x は q の bump 子）のとき、種は v(q)（bump の項 1 が消える）と o(P_0 q)、弱い呼び出しは
o(q)（N で x′ が数えられて引数が増えるが、添字 v(q) が下がるので o_N(q) < o_M(q)）。
`t2_assemble` に入れる。x より前で N と M の構造が同じこと、x へ上げる列がないこと（`upg_not_x`）、
根の祖先が D に入ること（`path_upS` を P_0 q から）を示す。
-/
import Ytosk.V3T2QS

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The seeds for `q ≠ r`: `v(q)` and `o(P_0 q)`. -/
def SQ (q pq : Nat) : Bool → Nat → Prop := fun b i => (b = false ∧ i = q) ∨ (b = true ∧ i = pq)

/-- The weak call for `q ≠ r`: `o(q)`. -/
def WQ (q : Nat) : Bool → Nat → Prop := fun b i => b = true ∧ i = q

theorem children_last_nil {M : Mat} {x : Nat} (hx : x + 1 = M.length) : children M x = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  have := mem_children hc; omega

section
variable {M : Mat} {r L d0 d1 n qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
include hlen hL hA hp hqp hd0e hn2 hxb hBE

omit hL hA hqp hd0e hn2 in
theorem e2_q : entry M 2 (r + qp) = 1 :=
  hBE (r + qp) (r + L) (mem_children_iff.mpr ⟨by omega, hp⟩) hxb

omit hlen hL hA hp hqp hd0e hn2 hBE in
theorem e2_x : entry M 2 (r + L) = 1 :=
  e2_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)

omit hL hqp hd0e hn2 in
/-- **No column before `x` upgrades to `x`.** -/
theorem upg_not_x {i k : Nat} (hu : upg M i = some k) (hk : r + L ≤ k) (hi : i < r + L) : False := by
  obtain ⟨m, _, hmk, hcol, hcase⟩ := upg_spec hu
  have hkx : k = r + L := by rcases hcase with h | ⟨_, h⟩ <;> omega
  subst hkx
  have hmx := par_lt M 1 (r + L) m hmk
  have hAm : Anc0 M m (r + L) := anc0_of_par M 1 m (r + L) hmk
  have hAmq : Anc0 M m (r + qp) := anc0_par hAm (by omega) hp
  have he0 := e0_of_col hcol
  have he0' := e0_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
  have he2 := e2_of_col hcol
  rw [e2_x hxb] at he2
  have he2q := e2_q hlen hp hxb hBE
  have hmq : m ≠ r + qp := by intro h; rw [h] at he2; omega
  have := anc0_e0_lt hAmq hmq
  omega

omit hxb hBE in
/-- **Upgrades before `x`** are the same in `N` and `M`. -/
theorem upg_NQ (he2r : entry M 2 r = 0) (hnu : upg M (r + L - 1) ≠ some (r + L)) {i : Nat}
    (hi : i < r + L) : upg (TRIO.gexp M r L d0 d1 n) i = upg M i := by
  rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
  · rw [← upg_take _ h, gexp_take_x hlen (by omega), upg_take M h]
  · have : i = r + L - 1 := by omega
    rw [this]; exact upg_N2_xm1Q hlen hL hA hp hqp hd0e (by omega) hn2 he2r hnu

omit hBE in
/-- **`topped` before `x`, off `q`,** is the same. -/
theorem topped_NQ {c : Nat} (hc : c < r + L) (hcq : c ≠ r + qp) :
    topped (TRIO.gexp M r L d0 d1 n) c = topped M c := by
  unfold topped
  rw [children_N2Q hlen hL hA hp hqp hd0e (by omega) hn2 hc]
  cases hl : (children M c).getLast? with
  | none => rfl
  | some d =>
    have hd := List.mem_of_getLast? hl
    have hdl := (mem_children hd).2
    simp only
    rcases Nat.lt_or_ge d (r + L) with h | h
    · rw [col_gexp_pre hlen (by omega) h, show bump (TRIO.gexp M r L d0 d1 n) c = bump M c by
        unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]]
    · have hdx : d = r + L := by omega
      subst hdx
      have h' := (mem_children_iff.mp hd).2; rw [hp] at h'
      exact absurd (Option.some.inj h').symm hcq

omit hBE in
/-- **Counting before `x`, off `P_0 q`,** is the same (given the upgrades into topped columns). -/
theorem counted_NQ
    (hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true →
      isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
    {i c : Nat} (hi : i < r + L) (hc : c < r + L) (hcq : c ≠ r + qp) :
    Counted (TRIO.gexp M r L d0 d1 n) i c ↔ Counted M i c := by
  unfold Counted
  rw [col_gexp_pre hlen (by omega) hc, show bump (TRIO.gexp M r L d0 d1 n) i = bump M i by
      unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi],
    topped_NQ hlen hL hA hp hqp hd0e hn2 hxb hc hcq]
  by_cases ht : topped M c = true
  · rw [hIUt c hc hcq ht]
  · simp [ht]

omit hxb hBE in
/-- **Row 0 at or after `x` in `N` is positive.** -/
theorem e0_NQ_pos {j : Nat} (hj0 : r + L ≤ j) (hj : j < r + n * L) :
    0 < entry (TRIO.gexp M r L d0 d1 n) 0 j := by
  obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hj
  have hk1 : 1 ≤ k := by
    by_contra h; have : k = 0 := by omega
    subst this; omega
  have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
    (k := k) (q := q) hlen hk hq
  have he : entry (TRIO.gexp M r L d0 d1 n) 0 (r + (k * L + q)) = entry M 0 (r + q) + k * d0 := by
    unfold entry; rw [h]; rfl
  have hR := anc0_e0_lt hA (by omega)
  have : d0 ≤ k * d0 := Nat.le_mul_of_pos_left d0 hk1
  rw [he]; omega

omit hBE in
/-- **`t = 2`, `q ≠ r`, all `n ≥ 2`**: the root value of `N` is standard and below that of `M`. -/
theorem t2_qn_main (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) (he2r : entry M 2 r = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ [])
    (hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m)
    (hqL : ∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
      ¬ DepS M (SQ (r + qp) pq) true e)
    (hDvNil : ∀ c, c < r + L → DepS M (SQ (r + qp) pq) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ SQ (r + qp) pq true i → ¬ WQ (r + qp) true i →
      DepS M (SQ (r + qp) pq) true i → ¬ DepS M (SQ (r + qp) pq) false i →
      ∃ L c R, children M i = L ++ c :: R ∧ Counted M i c ∧ DepS M (SQ (r + qp) pq) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ L, Counted M i d → ¬ DepS M (SQ (r + qp) pq) true d))
    (hVSh : ∀ i, i < r + L → ¬ SQ (r + qp) pq false i → DepS M (SQ (r + qp) pq) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQ (r + qp) pq) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQ (r + qp) pq) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQ (r + qp) pq) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hGN : Good3 (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hVNN : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hseed : ∃ X K, σ.o pq = psi (ρ.v pq) X z ∧ Closed (ρ.v pq) X ∧
      psi (ρ.v pq) X z ≤ fs (ρ.o pq) (natT K)) :
    isOT (root (TRIO.gexp M r L d0 d1 n) σ) = true ∧ root (TRIO.gexp M r L d0 d1 n) σ < root M ρ := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hqx : r + qp < r + L := by omega
  have hqM : r + qp < M.length := by omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have hpqq : pq < r + qp := par_lt M 0 _ _ hpq
  have he2q := e2_q hlen hp hxb hBE
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0; have := e2_x hxb; omega
  have hxN2 : entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL hA hp hqp hd0e (by omega) hn2).1, he2r]
  have hcolN : ∀ i, i < r + L → col (TRIO.gexp M r L d0 d1 n) i = col M i := fun i hi => col_gexp_pre hlen (by omega) hi
  have hbumpN : ∀ i, i < r + L → bump (TRIO.gexp M r L d0 d1 n) i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hchN : ∀ i, i < r + L → children (TRIO.gexp M r L d0 d1 n) i = children M i :=
    fun i hi => children_N2Q hlen hL hA hp hqp hd0e (by omega) hn2 hi
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hp hxb hBE h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg (TRIO.gexp M r L d0 d1 n) i = upg M i := fun i hi =>
    upg_NQ hlen hL hA hp hqp hd0e hn2 he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hcntS : ∀ i c, i < r + L → i ≠ pq → c ∈ children M i → c < r + L →
      (Counted (TRIO.gexp M r L d0 d1 n) i c ↔ Counted M i c) := by
    intro i c hi hipq hc hcx
    apply counted_NQ hlen hL hA hp hqp hd0e hn2 hxb hIUt hi hcx
    intro h; apply hipq
    have h' := (mem_children_iff.mp hc).2; rw [h, hpq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children (TRIO.gexp M r L d0 d1 n) i → r + L ≤ j → col (TRIO.gexp M r L d0 d1 n) j ≠ bump (TRIO.gexp M r L d0 d1 n) i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL hA hp hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 i + 1, entry (TRIO.gexp M r L d0 d1 n) 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) pq) (bnd := r + L) hC hCN hRN (by omega) (by rw [hlN]; omega)
    hchN (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (DepS.seed (Or.inr ⟨rfl, h⟩))) hc hcx)
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
  -- the seed `v(q)`
  have hcqM : children M (r + qp) =
      (children M (r + qp)).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have hvq : Lhd z (σ.v (r + qp)) (ρ.v (r + qp)) := by
    apply v_bump_lost (L := (children M (r + qp)).filter (fun d => decide (d < r + L))) (j := r + L)
      hC hG hCN hqM (by rw [hlN]; omega) he1q (by omega)
      (entry_gexp_pre hlen (by omega) 1 hqx) (entry_gexp_pre hlen (by omega) 2 hqx)
    · rw [par_gexp_pre hlen (by omega) 1 hqx]
      cases hm : par M 1 (r + qp) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1q m hm)
    · exact hcqM
    · rw [hchN _ hqx]; exact hcqM
    · intro d hd
      have hdx : d < r + L := by have := (List.mem_filter.mp hd).2; simpa using this
      have hdM : d ∈ children M (r + qp) := (List.mem_filter.mp hd).1
      apply bumpTerm_eq_of
      · rw [hcolN d hdx, hbumpN _ hqx]
      · intro hb
        rw [hchN d hdx]
        apply List.map_congr_left
        intro e he
        have hex : e < r + L := by
          have hel := (mem_children he).2
          by_contra h'
          have hex' : e = r + L := by omega
          have h'' := (mem_children_iff.mp he).2
          rw [hex', hp] at h''
          have hdq : d = r + qp := (Option.some.inj h'').symm
          have := (mem_children hdM).1
          omega
        exact (hoff e hex).1 (hqL d hdM hb e he)
    · unfold bumpTerm; rw [if_pos hxb, children_last_nil hlen]; exact omega_z
    · unfold bumpTerm
      rw [if_neg]
      intro hb
      have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 (r + qp) + 1, entry (TRIO.gexp M r L d0 d1 n) 1 (r + qp), 1) from hb)
      omega
  -- the weak call `o(q)`
  have hWle : ∀ i, i < r + L → WQ (r + qp) true i → σ.o i ≤ ρ.o i := by
    intro i _ hw
    obtain ⟨-, hi⟩ := hw
    rw [hi]
    have hvot := hG.ot_v (r + qp) hqM
    rw [o_of_no_counted hC hqM hvot (no_cnt_of_cl_nil hCLq)]
    obtain ⟨y, hy⟩ := o_psi_sub hCN (show r + qp < (TRIO.gexp M r L d0 d1 n).length by rw [hlN]; omega)
    rw [hy, sf_ot (hGN.ot_v _ (by rw [hlN]; omega))]
    exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hvq.1))
  -- the roots
  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M (SQ (r + qp) pq) true R ∧ ¬ WQ (r + qp) true R := by
    intro R hR hRA hR0
    have he2R : entry M 2 R = 0 := e2_of_col hR0
    have hRq : R ≠ r + qp := by intro h; rw [h] at he2R; omega
    have hRq' : Anc0 M R (r + qp) := anc0_par hRA (by omega) hp
    have hRpq : Anc0 M R pq := anc0_par hRq' hRq hpq
    refine ⟨?_, fun h => hRq h.2⟩
    apply path_upS hUAT hZ2 hR12 hBE (pq - R) R pq (le_refl _) (by omega) hRpq (ne_of_e2z he2pq)
      (DepS.seed (Or.inr ⟨rfl, rfl⟩))
    intro t _ htpq
    have := htpq.le
    exact ⟨r + L, by omega, Anc0.step hp (Anc0.step hpq (Anc0.refl pq)), not_anc_out (by omega) (by omega)⟩
  have hCLnil : ∀ c, c < r + L → ¬ WQ (r + qp) true c → CL M c = [] → CL (TRIO.gexp M r L d0 d1 n) c = [] := by
    intro c hc hw hcl
    by_cases hcpq : c = pq
    · exact (hpqCL (by rw [← hcpq]; exact hcl)).elim
    · have hcq : c ≠ r + qp := fun h => hw ⟨rfl, h⟩
      unfold CL at hcl ⊢
      rw [hchN c hc, ← hcl]
      apply List.filter_congr
      intro d hd
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h'
        exact hcq (hxc c d hd (by omega)).2
      simp only [hcntS c d hc hcpq hd hdx]
  have hSeed : ∀ b i, SQ (r + qp) pq b i → i < r + L → DepS M (SQ (r + qp) pq) b i →
      (∀ i, i < r + L → (¬ DepS M (SQ (r + qp) pq) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SQ (r + qp) pq) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SQ (r + qp) pq) b' i' → i' < r + L →
        ¬ WQ (r + qp) b' i' → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i) := by
    rintro b i (⟨hb, hi'⟩ | ⟨hb, hi'⟩) _ _ _ _
    · subst hb; rw [hi']; exact hvq
    · subst hb; rw [hi']
      show Lhd z (σ.o pq) (ρ.o pq)
      obtain ⟨X, K, hXo, hcl', hle⟩ := hseed
      have hpqM : pq < M.length := by omega
      have hor := o_cl_eq hC hG hpqM
      have harg := arg_lt_of_cl hC hG hpqM hpqCL
      rw [hXo]
      rw [hor] at hle ⊢
      exact seed_closed (by rw [← hor]; exact hG.ot_o pq hpqM) (ne_of_gt harg) hcl' hle
  exact t2_assemble (S := SQ (r + qp) pq) (W := WQ (r + qp)) (bnd := r + L) hC hG hRM hCN hGN hRN
    hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlN]; omega) hchN
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (Or.inr ⟨rfl, h⟩)) hc hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inr ⟨rfl, rfl⟩)
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by obtain ⟨_, rfl⟩ := hxc i j hj hjx; exact Or.inl ⟨rfl, rfl⟩)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
    (fun j hj0 hj => by
      have := e0_NQ_pos (d1 := d1) hlen hL hA hp hqp hd0e hn2 hj0 (by rw [hlN] at hj; exact hj); omega)
    (by have := anc0_e0_lt hA (by omega); omega)
    (fun i h => by obtain ⟨-, hi⟩ := h; rw [hi]; exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i h => by cases h.1)
    (fun i c hc _ h => by
      obtain ⟨-, hc'⟩ := h
      have h' := (mem_children_iff.mp hc).2; rw [hc', hpq] at h'; cases h'
      exact Or.inr ⟨rfl, rfl⟩)
    (fun i j c _ _ hj hjb hc h => by
      obtain ⟨-, hc'⟩ := h
      have h' := (mem_children_iff.mp hc).2; rw [hc', hpq] at h'; cases h'
      have := e2_of_col (show col M _ = (entry M 0 i + 1, entry M 1 i, 1) from hjb)
      omega)
    (fun c hc _ hd => hDvNil c hc hd)
    hCLnil hOS hVSh hRD hWle hAbs hVNN hSeed

end

end Ytosk
