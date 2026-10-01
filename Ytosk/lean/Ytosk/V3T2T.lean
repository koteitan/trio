/-
**3 行・t = 2: n = 0, 1（M[n] = M.take x）。**

`t2_assemble` を N = M.take x に使う（子の並びが違うのは x の親 p = P_0(x) だけ）。
- q ≠ r（`t2_qn_take`）: 種は v(q)（bump の項 1 が子 x ごと消える、`v_bump_drop`）と o(P_0 q)、
  弱い呼び出しは o(q)。
- q = r で x − 1 が x へ上げる（`t2_sv_take`）: 種は o(r) と v(x − 1)（x − 1 が最後の列になって上げない、
  `v_upg_lost`）。
数え方が変わるのは x の親と upg(x − 1) の行き先だけ（`cnt_change`）。
-/
import Ytosk.V3T2V

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The lost bump term, with the child dropped**: `v_N(i) = V + ω^S ◁ V + ω^(S+1) = v_M(i)`. -/
theorem v_bump_drop {M N : Mat} {ρ σ : Valn} {i j : Nat} {L : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L)
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = one) :
    Lhd z (σ.v i) (ρ.v i) := by
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  have hPot : ∀ t ∈ one :: L.map (bumpTerm M ρ i), isOT t = true := fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hSot : isOT (sumN (one :: L.map (bumpTerm M ρ i))) = true := isOT_sumN _ hPot
  have ev : ρ.v i = add (vOpt ρ (par M 1 i)) (omega (succ (sumN (one :: L.map (bumpTerm M ρ i))))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hchM, List.map_append, List.map_singleton, hbjM, ← List.cons_append,
      sumN_snoc, add_one_eq_succ hSot, sf_ot (isOT_succ hSot),
      sf_ot (isOT_add hVot (isOT_omega (isOT_succ hSot)))]
  have ev' : σ.v i = add (vOpt ρ (par M 1 i)) (omega (sumN (one :: L.map (bumpTerm M ρ i)))) := by
    rw [(hCN i hiN).2]; unfold vRhs
    rw [he1, he2, if_neg h1, if_neg h2, hV, hchN, List.map_congr_left hbL,
      sf_ot (isOT_add hVot (isOT_omega hSot))]
  rw [ev, ev']
  exact add_omega_succ_lhd hVot hSot

/-- **The lost upgrade**: `i` upgrades in `M` to a column `k` without children (row 2 of `k` nonzero), and
not in `N`; then `v_N(i) = V + 1 ◁ V + ω = v_M(i)`. -/
theorem v_upg_lost {M N : Mat} {ρ σ : Valn} {i k : Nat} (hZ2 : Z2 M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hkM : k < M.length)
    (hiN : i < N.length) (hu : upg M i = some k) (hkc : children M k = [])
    (he1 : entry N 1 i = entry M 1 i) (he2 : entry N 2 i = entry M 2 i)
    (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i)) (hun : upg N i = none) :
    Lhd z (σ.v i) (ρ.v i) := by
  obtain ⟨m, hm1, hmx, hcol, _⟩ := upg_spec hu
  obtain ⟨he1M, he2M⟩ := upg_e12 hu
  have he2z : entry M 2 i = 0 := by have := hZ2 i; omega
  set V := vOpt ρ (par M 1 i) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef, hm1]; exact hG.ot_v m (by have := par_lt M 1 _ m hm1; omega)
  have he1x : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact he1M
  have he2x : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
  have hV'ot : isOT (vOpt ρ (par M 1 k)) = true := by
    rw [hmx]; exact hG.ot_v m (by have := par_lt M 1 _ m hmx; omega)
  have hvx : ρ.v k = add (vOpt ρ (par M 1 k)) (omega one) := by
    rw [(hC _ hkM).2]; unfold vRhs
    rw [if_neg he1x, if_neg he2x, hkc]
    show sf (add _ (omega (sumN [one]))) = _
    rw [show sumN [one] = one from rfl, sf_ot (isOT_add hV'ot (isOT_omega isOT_one))]
  have hlast : last (ρ.v k) = omega one := by
    obtain ⟨s, y, h⟩ := (single_omega isOT_one).2
    rw [hvx, h, last_add_single]
  have ev : ρ.v i = add V (omega (succ z)) := by
    rw [(hC _ hiM).2]; unfold vRhs
    rw [if_neg he1M, if_pos he2z, hu]
    show sf (add V (last (ρ.v k))) = _
    rw [hlast, sf_ot (isOT_add hVot (isOT_omega isOT_one))]; rfl
  have ev' : σ.v i = add V (omega z) := by
    rw [(hCN _ hiN).2]; unfold vRhs
    rw [he1, he2, if_neg he1M, if_pos he2z, hun, hV]
    show sf (add V one) = _
    rw [omega_z, sf_ot (isOT_add hVot isOT_one)]
  rw [ev, ev']
  exact add_omega_succ_lhd hVot rfl

/-- `isUpg` before `x` is the same in `M.take x` when `x − 1` does not upgrade before `x`. -/
theorem isUpg_take_eq {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hu : ∀ c, c < x → upg M (x - 1) ≠ some c) {c : Nat} (hc : c < x) :
    isUpg (M.take x) c = isUpg M c := by
  apply Bool.eq_iff_iff.mpr
  rw [isUpg_take M (by omega) c]
  unfold isUpg
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hjc⟩
    exact ⟨j, List.mem_range.mpr (by omega), by simpa using hjc⟩
  · rintro ⟨j, hj, hjc⟩
    have hjc' : upg M j = some c := by simpa using hjc
    have hjl := List.mem_range.mp hj
    refine ⟨j, ?_, hjc'⟩
    by_contra h
    rcases (show j = x - 1 ∨ j = x by omega) with h' | h'
    · rw [h'] at hjc'; exact hu c hc hjc'
    · rw [h'] at hjc'
      unfold upg at hjc'; rw [if_pos (Or.inr (Or.inr (by omega)))] at hjc'; cases hjc'

section
variable {M : Mat} {r L qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
  (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
include hlen hL hA hp hqp hxb hBE

/-- **`t = 2`, `q ≠ r`, `n ≤ 1`** (`M[n] = M.take x`). -/
theorem t2_qn_take (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ []) (hun : upg M (r + L - 1) = none)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m)
    (hqL : ∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
      ¬ DepS M (SQ (r + qp) pq) true e)
    (hDvNil : ∀ c, c < r + L → DepS M (SQ (r + qp) pq) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ SQ (r + qp) pq true i → ¬ WQ (r + qp) true i →
      DepS M (SQ (r + qp) pq) true i → ¬ DepS M (SQ (r + qp) pq) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SQ (r + qp) pq) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SQ (r + qp) pq) true d))
    (hVSh : ∀ i, i < r + L → ¬ SQ (r + qp) pq false i → DepS M (SQ (r + qp) pq) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQ (r + qp) pq) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQ (r + qp) pq) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQ (r + qp) pq) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (M.take (r + L)) σ) (hGN : Good3 (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hVNN : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hseed : ∃ X K, σ.o pq = psi (ρ.v pq) X z ∧ Closed (ρ.v pq) X ∧
      psi (ρ.v pq) X z ≤ fs (ρ.o pq) (natT K)) :
    isOT (root (M.take (r + L)) σ) = true ∧ root (M.take (r + L)) σ < root M ρ := by
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hqx : r + qp < r + L := by omega
  have hqM : r + qp < M.length := by omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have hpqq : pq < r + qp := par_lt M 0 _ _ hpq
  have he2q := e2_q hlen hp hxb hBE
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0; have := e2_x hxb; omega
  have hcolN : ∀ i, i < r + L → col (M.take (r + L)) i = col M i := fun i hi => col_take M hi
  have hbumpN : ∀ i, i < r + L → bump (M.take (r + L)) i = bump M i := fun i hi => bump_take M hi
  have hchN : ∀ i, i < r + L → i ≠ r + qp → children (M.take (r + L)) i = children M i := by
    intro i _ hiq
    rw [children_take, children_filter_x hlen (fun h => hiq (by
      have h' := (mem_children_iff.mp h).2; rw [hp] at h'; exact (Option.some.inj h').symm))]
  have hupgN : ∀ i, i < r + L → upg (M.take (r + L)) i = upg M i := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
    · exact upg_take M h
    · rw [show i = r + L - 1 by omega, upg_take_last M (by omega) (by omega), hun]
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hcntS : ∀ i c, i < r + L → i ≠ pq → c ∈ children M i → c < r + L →
      (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hipq hc hcx
    by_contra h
    rcases cnt_change hlen hi hcx h with h' | h'
    · apply hipq
      have hc' := (mem_children_iff.mp h').2; rw [hp] at hc'
      have hcq : c = r + qp := (Option.some.inj hc').symm
      have h'' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h''; exact (Option.some.inj h'').symm
    · rw [hun] at h'; cases h'
  have hoff := t2_off_gen (S := SQ (r + qp) pq) (bnd := r + L) (p := r + qp) hC hCN hRN (by omega)
    (by rw [hlT]) (fun i hi hiq => hchN i hi hiq) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_take M y hi) (fun i hi => par_take M 1 i hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (DepS.seed (Or.inr ⟨rfl, h⟩))) hc hcx)
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    (fun i j hi hj hjx _ => by have := (mem_children hj).2; rw [hlT] at this; omega)
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
    apply v_bump_drop (L := (children M (r + qp)).filter (fun d => decide (d < r + L))) (j := r + L)
      hC hG hCN hqM (by rw [hlT]; omega) he1q (by omega)
      (entry_take M 1 hqx) (entry_take M 2 hqx)
    · rw [par_take M 1 _ hqx]
      cases hm : par M 1 (r + qp) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1q m hm)
    · exact hcqM
    · exact children_take M _ _
    · intro d hd
      have hdx : d < r + L := by have := (List.mem_filter.mp hd).2; simpa using this
      have hdM : d ∈ children M (r + qp) := (List.mem_filter.mp hd).1
      apply bumpTerm_eq_of
      · rw [hcolN d hdx, hbumpN _ hqx]
      · intro hb
        rw [hchN d hdx (by have := (mem_children hdM).1; omega)]
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
  -- the weak call `o(q)`
  have hWle : ∀ i, i < r + L → WQ (r + qp) true i → σ.o i ≤ ρ.o i := by
    intro i _ hw
    obtain ⟨-, hi⟩ := hw
    rw [hi]
    have hvot := hG.ot_v (r + qp) hqM
    rw [o_of_no_counted hC hqM hvot (no_cnt_of_cl_nil hCLq)]
    obtain ⟨y, hy⟩ := o_psi_sub hCN (show r + qp < (M.take (r + L)).length by rw [hlT]; omega)
    rw [hy, sf_ot (hGN.ot_v _ (by rw [hlT]; omega))]
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
  have hCLnil : ∀ c, c < r + L → ¬ WQ (r + qp) true c → CL M c = [] → CL (M.take (r + L)) c = [] := by
    intro c hc hw hcl
    by_cases hcpq : c = pq
    · exact (hpqCL (by rw [← hcpq]; exact hcl)).elim
    · have hcq : c ≠ r + qp := fun h => hw ⟨rfl, h⟩
      unfold CL at hcl ⊢
      rw [hchN c hc hcq, ← hcl]
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
  exact t2_assemble (S := SQ (r + qp) pq) (W := WQ (r + qp)) (bnd := r + L) (p := r + qp) hC hG hRM
    hCN hGN hRN hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlT]) (fun i hi hiq => hchN i hi hiq)
    (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_take M y hi) (fun i hi => par_take M 1 i hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (Or.inr ⟨rfl, h⟩)) hc hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inr ⟨rfl, rfl⟩)
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    (fun i j hi hj hjx _ => by have := (mem_children hj).2; rw [hlT] at this; omega)
    (fun i j hi hj hjx _ => by obtain ⟨_, rfl⟩ := hxc i j hj hjx; exact Or.inl ⟨rfl, rfl⟩)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
    (fun j hj0 hj => by rw [hlT] at hj; omega)
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


section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hu : upg M (r + L - 1) = some (r + L))
include hlen hL hp hu

/-- **`t = 2`, `q = r`, `x − 1` upgrades to `x`, `n ≤ 1`** (`M[n] = M.take x`). -/
theorem t2_sv_take (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) (he2r : entry M 2 r = 0)
    (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p) (hrCL : CL M r ≠ [])
    (hrU : isUpg M r = false)
    -- the shape of `D` in `M`
    (hP1 : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m)
    (hDvNil : ∀ c, c < r + L → DepS M (SV r (r + L - 1)) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ SV r (r + L - 1) true i →
      DepS M (SV r (r + L - 1)) true i → ¬ DepS M (SV r (r + L - 1)) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SV r (r + L - 1)) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SV r (r + L - 1)) true d))
    (hVSh : ∀ i, i < r + L → ¬ SV r (r + L - 1) false i → DepS M (SV r (r + L - 1)) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SV r (r + L - 1)) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SV r (r + L - 1)) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (M.take (r + L)) σ) (hGN : Good3 (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hVNN : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hseed : ∃ X K, σ.o r = psi (ρ.v r) X z ∧ Closed (ρ.v r) X ∧
      psi (ρ.v r) X z ≤ fs (ρ.o r) (natT K)) :
    isOT (root (M.take (r + L)) σ) = true ∧ root (M.take (r + L)) σ < root M ρ := by
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 0 r (r + L) hp
  have hxr := col_x_ne_bump_r hp hu
  have hcolN : ∀ i, i < r + L → col (M.take (r + L)) i = col M i := fun i hi => col_take M hi
  have hbumpN : ∀ i, i < r + L → bump (M.take (r + L)) i = bump M i := fun i hi => bump_take M hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hchN : ∀ i, i < r + L → i ≠ r → children (M.take (r + L)) i = children M i := by
    intro i _ hir
    rw [children_take, children_filter_x hlen (fun h => hir (hxc i (r + L) h (le_refl _)).2)]
  have hIU : ∀ c, c < r + L → isUpg (M.take (r + L)) c = isUpg M c := fun c hc =>
    isUpg_take_eq hlen (fun c' hc' h => by rw [hu] at h; cases h; omega) hc
  have hcnt : ∀ i c, i < r + L → c < r + L → (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hc
    by_cases hcr : c = r
    · subst hcr
      unfold Counted
      rw [col_take M hc, bump_take M hi, hIU _ hc, hrU]
      simp
    · by_contra h
      rcases cnt_change hlen hi hc h with h' | h'
      · exact hcr (hxc c (r + L) h' (le_refl _)).2
      · rw [hu] at h'; cases h'; omega
  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M (SV r (r + L - 1)) true R ∧ ¬ (fun _ _ => False : Bool → Nat → Prop) true R := by
    intro R hR hRA _
    have hRr : Anc0 M R r := anc0_par hRA (by omega) hp
    refine ⟨?_, id⟩
    apply path_upS hUAT hZ2 hR12 hBE (r - R) R r (le_refl _) (by omega) hRr (ne_of_e2z he2r)
      (DepS.seed (Or.inl ⟨rfl, rfl⟩))
    intro t _ htr
    have := htr.le
    exact ⟨r + L, by omega, hA, not_anc_out (by omega) (by omega)⟩
  have hCLnil : ∀ c, c < r + L → ¬ (fun _ _ => False : Bool → Nat → Prop) true c → CL M c = [] →
      CL (M.take (r + L)) c = [] := by
    intro c hc _ hcl
    by_cases hcr : c = r
    · exact (hrCL (by rw [← hcr]; exact hcl)).elim
    · unfold CL at hcl ⊢
      rw [hchN c hc hcr, ← hcl]
      apply List.filter_congr
      intro d hd
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h'
        exact hcr (hxc c d hd (by omega)).2
      simp only [hcnt c d hc hdx]
  have hSeed : ∀ b i, SV r (r + L - 1) b i → i < r + L → DepS M (SV r (r + L - 1)) b i →
      (∀ i, i < r + L → (¬ DepS M (SV r (r + L - 1)) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SV r (r + L - 1)) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SV r (r + L - 1)) b' i' → i' < r + L →
        ¬ (fun _ _ => False : Bool → Nat → Prop) b' i' → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i) := by
    rintro b i (⟨hb, hi'⟩ | ⟨hb, hi'⟩) _ _ hoff _
    · subst hb; rw [hi']
      show Lhd z (σ.o r) (ρ.o r)
      obtain ⟨X, K, hXo, hcl', hle⟩ := hseed
      have hrM : r < M.length := by omega
      have hor := o_cl_eq hC hG hrM
      have harg := arg_lt_of_cl hC hG hrM hrCL
      rw [hXo]
      rw [hor] at hle ⊢
      exact seed_closed (by rw [← hor]; exact hG.ot_o r hrM) (ne_of_gt harg) hcl' hle
    · subst hb; rw [hi']
      show Lhd z (σ.v (r + L - 1)) (ρ.v (r + L - 1))
      apply v_upg_lost hZ2 hC hG hCN (by omega) (by omega) (by rw [hlT]; omega) hu (children_last_nil hlen)
        (entry_take M 1 (by omega)) (entry_take M 2 (by omega)) _ (upg_take_last M (by omega) (by omega))
      rw [par_take M 1 _ (by omega)]
      cases hm : par M 1 (r + L - 1) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1 m hm)
  exact t2_assemble (S := SV r (r + L - 1)) (W := fun _ _ => False) (bnd := r + L) (p := r) hC hG hRM
    hCN hGN hRN hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlT]) (fun i hi hir => hchN i hi hir)
    (Or.inl (Or.inl ⟨rfl, rfl⟩)) (Or.inl he2r) (fun i hr hb => hrb i (mem_children_iff.mp hr).2 hb)
    (fun y i hi => entry_take M y hi) (fun i hi => par_take M 1 i hi)
    (fun i hi hs => by
      rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
      · exact upg_take M h
      · exact absurd (Or.inr ⟨rfl, by omega⟩) hs)
    (fun i c hi _ _ hcx => hcnt i c hi hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inl (Or.inl ⟨rfl, rfl⟩))
    (fun i k hi hk hkx => by
      obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
      exact Or.inr ⟨rfl, by rcases hcase with h | ⟨_, h⟩ <;> omega⟩)
    (fun i j hi hj hjx _ => by have := (mem_children hj).2; rw [hlT] at this; omega)
    (fun i j hi hj hjx hjb => by
      obtain ⟨hjx', hir⟩ := hxc i j hj hjx
      rw [hjx', hir] at hjb; exact absurd hjb hxr)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, hjr⟩ := hxc j k hk hkx
      rw [hjr] at hj hjb
      exact absurd hjb (hrb i (mem_children_iff.mp hj).2))
    (fun j hj0 hj => by rw [hlT] at hj; omega)
    (by have := anc0_e0_lt hA (by omega); omega)
    (fun i h => h.elim) (fun i h => h) (fun i c _ _ h => h.elim) (fun i j c _ _ _ _ _ h => h.elim)
    (fun c hc _ hd => hDvNil c hc hd)
    hCLnil (fun i hi hns _ hD hv => hOS i hi hns hD hv) hVSh hRD (fun i _ h => h.elim) hAbs hVNN hSeed

end

end Ytosk
