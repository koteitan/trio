/-
Weak-consumer route around T2UpgAbsW. Failure of strong absorption supplies
an old target and NBPar; qnu_take_of_drop uses the existing weak drop field
and PO/PV instead of strong absorption. No parent-coincidence theorem or
replacement residual is assumed. Only new lemmas are added in this file.
-/
import Ytosk.V3GroupA
import Ytosk.V3T2QNU
import Ytosk.V3T2QUBad

namespace Ytosk.T2UpgAbs
open T

/-- Right strict monotonicity makes addition injective in its right argument,
even for arbitrary raw terms. -/
theorem add_right_injective (V : T) {W W' : T}
    (h : add V W = add V W') : W = W' := by
  rcases lt_trichotomy W W' with hlt | heq | hgt
  · have := add_lt_add_left V hlt
    rw [h] at this
    exact False.elim ((lt_irrefl _) this)
  · exact heq
  · have := add_lt_add_left V hgt
    rw [h] at this
    exact False.elim ((lt_irrefl _) this)

/-- At a leaf upgrade target, the only possible nonzero W is omega. -/
theorem absorption_at_leaf {M : Mat} {ρ : Valn} {i k : Nat} {W : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hi : i < M.length)
    (hu : upg M i = some k) (hLeaf : children M k = [])
    (hW : ρ.v k = add (vOpt ρ (par M 1 i)) W) :
    ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W := by
  obtain ⟨m, hm, _, _, _⟩ := upg_spec hu
  have hV : isOT (vOpt ρ (par M 1 i)) = true := by
    rw [hm]
    exact hG.ot_v m (Nat.lt_trans (par_lt M 1 i m hm) hi)
  obtain ⟨_, _, _, _, hv, _⟩ := upg_target_val hC hG hi hu
  have hBW : bumpW M ρ k = omega one := by
    unfold bumpW
    rw [hLeaf]
    simp only [List.map_nil]
    rw [sumN_singleton (t := one) ⟨rfl, z, z, rfl⟩]
  rw [hBW] at hv
  have hEq : W = omega one := add_right_injective _ (hW.symm.trans hv)
  rw [hEq]
  intro r hr hlt
  exact lhd_lt_small (isOT_mem_summands hV hr) (by
    rw [omega_small one_lt_E0]
    exact lt_E0_iff.mpr ⟨rfl, by decide⟩) hlt

/-- Failure of strong absorption supplies an old upgrade target and NBPar.
The remaining parent-coincidence claim is not assumed in this reduction. -/
theorem old_target_of_failure {M : Mat} {ρ : Valn} {x : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW M x ρ) (hFail : ¬ UpgAbsX M x ρ) :
    ∃ k, upg M (x - 1) = some k ∧ k < x ∧ NBPar M (x - 1) := by
  classical
  unfold UpgAbsX at hFail
  push Not at hFail
  obtain ⟨i, k, W, hix, hu, hv, hW, r, hr, hrW, hnl⟩ := hFail
  have hi : i < M.length := by omega
  have hne : k ≠ x := by
    intro heq
    subst k
    exact hnl (absorption_at_leaf hC hG hi hu (children_last hx) hv r hr hrW)
  have hkx : k < x := by have := upg_le hu; omega
  have hnb : NBPar M i := by
    rcases hUA i k W hix hu hv hW with hs | hw
    · exact False.elim (hnl (hs r hr hrW))
    · exact hw.2.2.1
  have hie : i = x - 1 := by omega
  exact ⟨k, by simpa [hie] using hu, hkx, by simpa [hie] using hnb⟩

/-- Case split supplied by the existing weak drop field, without any t=2
parent-coincidence assumption. -/
theorem strong_or_old_target {M : Mat} {ρ : Valn} {x : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW M x ρ) :
    UpgAbsX M x ρ ∨ ∃ k, upg M (x - 1) = some k ∧ k < x ∧ NBPar M (x - 1) := by
  classical
  by_cases hs : UpgAbsX M x ρ
  · exact Or.inl hs
  · exact Or.inr (old_target_of_failure hx hC hG hUA hs)

theorem strong_of_no_upgrade {M : Mat} {ρ : Valn} {x : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW M x ρ) (hn : upg M (x - 1) = none) : UpgAbsX M x ρ := by
  rcases strong_or_old_target hx hC hG hUA with hs | ⟨k, hk, _⟩
  · exact hs
  · rw [hn] at hk
    cases hk

theorem strong_of_next_target {M : Mat} {ρ : Valn} {x : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW M x ρ) (hn : upg M (x - 1) = some x) : UpgAbsX M x ρ := by
  rcases strong_or_old_target hx hC hG hUA with hs | ⟨k, hk, hkx, _⟩
  · exact hs
  · rw [hn] at hk
    cases hk
    exact False.elim ((Nat.lt_irrefl _) hkx)

/-- At the already-common-parent frames, the weak drop field supplies the
exact body of T2UABad. The body is written out to keep this file below its
definition in V3T2Top and avoid an import cycle. -/
theorem strong_or_bad_of_common_parent {M : Mat} {ρ : Valn} {x r : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW M x ρ) (h0 : par M 0 x = some r) (h2 : par M 2 x = some r) :
    UpgAbsX M x ρ ∨
      ((∃ r, par M 0 x = some r ∧ par M 2 x = some r) ∧
        (∃ k, upg M (x - 1) = some k ∧ k < x) ∧ NBPar M (x - 1)) := by
  rcases strong_or_old_target hx hC hG hUA with hs | ⟨k,hk,hkx,hnb⟩
  · exact Or.inl hs
  · exact Or.inr ⟨⟨r,h0,h2⟩,⟨k,hk,hkx⟩,hnb⟩

/-- Strong o-seeds before x-1 need no global upgrade absorption. -/
theorem strong_seed_of_drop {M : Mat} {ρ σ : Valn} {x p : Nat}
    (hx : x + 1 = M.length) (hC : Cons M ρ) (hG : Good3 M ρ)
    (hp : p < x) (hne : p ≠ x - 1) (hCL : CL M p ≠ [])
    (hdrop : PO ρ σ p ∧ PV M ρ σ p) (ho : σ.o p ≠ ρ.o p) :
    Lhd z (σ.o p) (ρ.o p) := by
  rcases PO.zero_of_ne (show p + 2 ≠ M.length by omega) hC hG (by omega)
      hdrop.1 hdrop.2 with hE | ⟨_,w,hw⟩
  · rcases hE with heq | hl
    · exact False.elim (ho heq)
    · exact hl
  · have hor := o_cl_eq hC hG (show p < M.length by omega)
    have harg := arg_lt_of_cl hC hG (show p < M.length by omega) hCL
    rw [hw] at hor
    simp only [psi.injEq] at hor
    rw [← hor.2.1] at harg
    exact False.elim ((lt_irrefl _) harg)

section
variable {M : Mat} {r L qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
  (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
include hlen hL hA hp hqp hxb hBE

/-- **`t = 2`, `q ≠ r`, `x − 1` upgrades to `k`, `n ≤ 1`** (`M[n] = M.take x`). -/
theorem qnu_take_weak (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M)
    (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ []) {k : Nat} (hu : upg M (r + L - 1) = some k)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m)
    (hP1a : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m)
    (hqsh : ∃ Lb d Kb e, children M (r + qp) = Lb ++ [d, r + L] ∧ children M d = Kb ++ [e] ∧
      (∀ f ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true f) ∧
      (∀ d' ∈ Lb, ∀ e' ∈ children M d', ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e'))
    (hDvNil : ∀ c, c < r + L → DepS M (SQU (r + qp) pq (r + L - 1)) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ (SQU (r + qp) pq (r + L - 1)) true i →
      DepS M (SQU (r + qp) pq (r + L - 1)) true i → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SQU (r + qp) pq (r + L - 1)) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true d))
    (hVSh : ∀ i, i < r + L → ¬ (SQU (r + qp) pq (r + L - 1)) false i → DepS M (SQU (r + qp) pq (r + L - 1)) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (M.take (r + L)) σ) (hGN : Good3 (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hNB : NBPar M (r + L - 1))
    (hdrop : ∀ i, i < r + L → PO ρ σ i ∧ PV M ρ σ i)
    (hAbs : AbsWN M (M.take (r + L)) (r + L) ρ σ)
    (hseed : Lhd z (σ.o pq) (ρ.o pq)) :
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
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hchx : ∀ i c, c ∈ children M i → i ≠ r + qp → c < r + L := by
    intro i c hc hiq; by_contra h; exact hiq (hxc i c hc (by omega)).2
  -- the upgrade target `k`
  have hax : r + L - 1 < r + L := by omega
  have hkx : k < r + L := by
    by_contra h
    exact upg_not_x hlen hA hp hxb hBE hu (by omega) hax
  have hkT : topped M k = false := hUAT _ k hu (by omega)
  have hcqM : children M (r + qp) =
      (children M (r + qp)).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have hqT : topped M (r + qp) = true := by
    unfold topped; rw [hcqM]; simp [hxb]
  have hkq : k ≠ r + qp := by intro h; rw [h, hqT] at hkT; cases hkT
  have hupgN : ∀ i, i < r + L → i ≠ r + L - 1 → upg (M.take (r + L)) i = upg M i := by
    intro i hi hia; exact upg_take M (by omega)
  have hcntS : ∀ i c, i < r + L → i ≠ pq → c ∈ children M i → c < r + L →
      (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hipq hc hcx
    by_cases hck : c = k
    · rw [hck]
      unfold Counted
      rw [col_take M hkx, bump_take M hi,
        topped_take_eq hlen hkx (fun h => hkq (hxc k (r + L) h (le_refl _)).2), hkT]
      simp
    by_contra h
    rcases cnt_change hlen hi hcx h with h' | h'
    · apply hipq
      have hc' := (mem_children_iff.mp h').2; rw [hp] at hc'
      have hcq : c = r + qp := (Option.some.inj hc').symm
      have h'' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h''; exact (Option.some.inj h'').symm
    · rw [hu] at h'; exact hck (Option.some.inj h').symm
  have hCLnil : ∀ c, c < r + L → CL M c = [] → CL (M.take (r + L)) c = [] := by
    intro c hc hcl
    by_cases hcpq : c = pq
    · exact (hpqCL (by rw [← hcpq]; exact hcl)).elim
    · unfold CL at hcl ⊢
      rw [List.filter_eq_nil_iff] at hcl ⊢
      intro d hd hdc
      rw [children_take, List.mem_filter] at hd
      have hdx : d < r + L := by simpa using hd.2
      exact hcl d hd.1 (decide_eq_true ((hcntS c d hc hcpq hd.1 hdx).mp (of_decide_eq_true hdc)))
  -- the roots
  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M (SQU (r + qp) pq (r + L - 1)) true R ∧ ¬ (fun _ _ => False : Bool → Nat → Prop) true R := by
    intro R hR hRA hR0
    have he2R : entry M 2 R = 0 := e2_of_col hR0
    have hRq : R ≠ r + qp := by intro h; rw [h] at he2R; omega
    have hRq' : Anc0 M R (r + qp) := anc0_par hRA (by omega) hp
    have hRpq : Anc0 M R pq := anc0_par hRq' hRq hpq
    refine ⟨?_, id⟩
    apply path_upS hUAT hZ2 hR12 hBE (pq - R) R pq (le_refl _) (by omega) hRpq (ne_of_e2z he2pq)
      (DepS.seed (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    intro t _ htpq
    have := htpq.le
    exact ⟨r + L, by omega, Anc0.step hp (Anc0.step hpq (Anc0.refl pq)), not_anc_out (by omega) (by omega)⟩
  -- the seeds
  have hSeed : ∀ b i, (SQU (r + qp) pq (r + L - 1)) b i → i ≠ r + L - 1 → i < r + L → DepS M (SQU (r + qp) pq (r + L - 1)) b i →
      (∀ i, i < r + L → (¬ DepS M (SQU (r + qp) pq (r + L - 1)) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SQU (r + qp) pq (r + L - 1)) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SQU (r + qp) pq (r + L - 1)) b' i' → i' < r + L →
        i' ≠ r + L - 1 → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i) := by
    intro b i hs hnj _ _ hoff ih
    rcases hs with hiq | ⟨hb, hipq⟩ | ⟨hb, hia⟩
    · subst hiq
      cases b with
      | true =>
        show Lhd z (σ.o (r + qp)) (ρ.o (r + qp))
        have hv : Lhd z (σ.v (r + qp)) (ρ.v (r + qp)) :=
          ih false (r + qp) (hRM (r + qp) hqM).1 (DepS.seed (Or.inl rfl)) hqx hnj
        rw [o_of_no_counted hCN (by rw [hlT]; omega) (hGN.ot_v _ (by rw [hlT]; omega))
            (no_cnt_of_cl_nil (hCLnil _ hqx hCLq)),
          o_of_no_counted hC hqM (hG.ot_v _ hqM) (no_cnt_of_cl_nil hCLq)]
        exact lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hv)) (psi_lt_psi_z_iff.mpr (Or.inl hv.1))
      | false =>
        show Lhd z (σ.v (r + qp)) (ρ.v (r + qp))
        obtain ⟨Lb, d, Kb, e, hchq, hchd, hKnd, hLnd⟩ := hqsh
        have hs := children_sorted M (r + qp)
        rw [hchq] at hs
        have hp3 := List.pairwise_append.mp hs
        have hdx : d < r + L := (List.pairwise_cons.mp hp3.2.1).1 (r + L) (by simp)
        have hLd : ∀ d' ∈ Lb, d' < d := fun d' hd' => hp3.2.2 d' hd' d (by simp)
        have hdM : d ∈ children M (r + qp) := by rw [hchq]; simp
        have hdq : d ≠ r + qp := by have := (mem_children hdM).1; omega
        have hall := all_bump_of_last hR0 hZ2 hSD hZ1 he2q
          (show children M (r + qp) = (Lb ++ [d]) ++ [r + L] by rw [hchq]; simp) hxb
        have hdb : col M d = bump M (r + qp) := hall d hdM
        have heM : e ∈ children M d := by rw [hchd]; simp
        have hex : e < r + L := hchx d e heM hdq
        have hej : e ≠ r + L - 1 := by
          intro heq
          exact hNB d (r + qp) (by simpa [heq] using (mem_children_iff.mp heM).2)
            (mem_children_iff.mp hdM).2 hdb
        have heMl : e < M.length := (mem_children heM).2
        have heN : e < (M.take (r + L)).length := by rw [hlT]; exact hex
        have hcqN : children (M.take (r + L)) (r + qp) = Lb ++ [d] := by
          rw [children_take]
          have h := hcqM.symm.trans (show children M (r + qp) = (Lb ++ [d]) ++ [r + L] by rw [hchq]; simp)
          exact List.append_inj_left' h rfl
        have hV : vOpt σ (par (M.take (r + L)) 1 (r + qp)) = vOpt ρ (par M 1 (r + qp)) := by
          rw [par_take M 1 _ hqx]
          cases hm : par M 1 (r + qp) with
          | none => rfl
          | some m =>
            show σ.v m = ρ.v m
            exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1q m hm)
        have hbL : ∀ d' ∈ Lb, bumpTerm (M.take (r + L)) σ (r + qp) d' = bumpTerm M ρ (r + qp) d' := by
          intro d' hd'
          have hd'x : d' < r + L := by have := hLd d' hd'; omega
          have hd'M : d' ∈ children M (r + qp) := by rw [hchq]; simp [hd']
          have hd'q : d' ≠ r + qp := by have := (mem_children hd'M).1; omega
          apply bumpTerm_eq_of
          · rw [hcolN d' hd'x, hbumpN _ hqx]
          · intro _
            rw [hchN d' hd'x hd'q]
            apply List.map_congr_left
            intro e' he'
            exact (hoff e' (hchx d' e' he' hd'q)).1 (hLnd d' hd' e' he')
        have hKv : Kb.map σ.o = Kb.map ρ.o := List.map_congr_left (fun f hf => by
          have hfM : f ∈ children M d := by rw [hchd]; simp [hf]
          exact (hoff f (hchx d f hfM hdq)).1 (hKnd f hf))
        have hbdM : bumpTerm M ρ (r + qp) d = omega (sumN (Kb.map ρ.o ++ [ρ.o e])) := by
          unfold bumpTerm; rw [if_pos hdb, hchd, List.map_append, List.map_singleton]
        have hbdN : bumpTerm (M.take (r + L)) σ (r + qp) d = omega (sumN (Kb.map ρ.o ++ [σ.o e])) := by
          unfold bumpTerm
          rw [if_pos (by rw [hcolN d hdx, hbumpN _ hqx]; exact hdb), hchN d hdx hdq, hchd,
            List.map_append, List.map_singleton, hKv]
        have hbxM : bumpTerm M ρ (r + qp) (r + L) = one := by
          unfold bumpTerm; rw [if_pos hxb, children_last_nil hlen]; exact omega_z
        have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
          obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hu
          exact single_o hC hG (mem_children (show f ∈ children M d by rw [hchd]; simp [hf])).2
        have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o e])) = true := isOT_sumN _ (fun u hu => by
          rcases List.mem_append.mp hu with h | h
          · exact (hsK u h).1
          · simp at h; rw [h]; exact hG.ot_o e heMl)
        have hrel : (sumN (Kb.map ρ.o ++ [σ.o e]) = sumN (Kb.map ρ.o ++ [ρ.o e]) ∨
            BRelS (sumN (Kb.map ρ.o ++ [σ.o e])) (sumN (Kb.map ρ.o ++ [ρ.o e]))) ∧
            isOT (sumN (Kb.map ρ.o ++ [σ.o e])) = true := by
          by_cases hDe : DepS M (SQU (r + qp) pq (r + L - 1)) true e
          · have hrke : rkM true e < rkM false (r + qp) :=
              ((hRM (r + qp) hqM).2.2 he1q).2.2 (by omega) d hdM hdb e heM
            have hIH : Lhd z (σ.o e) (ρ.o e) := ih true e hrke hDe hex hej
            have hdec := hKD (r + qp) he1q (by omega) d hdM hdb
            rw [hchd, List.map_append, List.map_singleton] at hdec
            have hform : (∃ s y y', ρ.o e = psi s y z ∧ σ.o e = psi s y' z) ∨
                (∃ w' w Y, σ.o e = psi w' z z ∧ ρ.o e = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
              obtain ⟨y1, hy1⟩ := o_psi_sub hC heMl
              rw [sf_ot (hG.ot_v e heMl)] at hy1
              by_cases hve : σ.v e = ρ.v e
              · obtain ⟨y0, hy0⟩ := o_psi_sub hCN heN
                rw [sf_ot (hGN.ot_v e heN), hve] at hy0
                exact Or.inl ⟨_, _, _, hy1, hy0⟩
              · have hdv : DepS M (SQU (r + qp) pq (r + L - 1)) false e := by
                  by_contra hn'; exact hve ((hoff e hex).2 hn')
                have ho0 : σ.o e = psi (σ.v e) z z :=
                  o_of_no_counted hCN heN (hGN.ot_v e heN)
                    (no_cnt_of_cl_nil (hCLnil e hex (hDvNil e hex hdv)))
                have hvIH : Lhd z (σ.v e) (ρ.v e) :=
                  ih false e (by have := (hRM e heMl).1; omega) hdv hex hej
                have he1e : entry M 1 e ≠ 0 := by
                  intro he; apply hve
                  rw [v_z_of_e1 hC heMl he, v_z_of_e1 hCN heN (by rw [entry_take M 1 hex]; exact he)]
                have hv0 : σ.v e ≠ z := v_ne_z_of_e1 hCN heN (by rw [entry_take M 1 hex]; exact he1e)
                exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
            obtain ⟨hS, _, hG'ot⟩ := g_brel hsK hdec (single_o hC hG heMl) (single_o hCN hGN heN) hIH hform
            exact ⟨Or.inr hS, hG'ot⟩
          · rw [(hoff e hex).1 hDe]; exact ⟨Or.inl rfl, hGot⟩
        exact v_bump_drop_upg hC hG hCN hqM (by rw [hlT]; omega) he1q (by omega)
          (entry_take M 1 hqx) (entry_take M 2 hqx) hV hchq hcqN hbL hbdM hbdN hbxM hGot hrel.2 hrel.1
          hTD (hAbs _ hqx he1q (by omega))
    · subst hb; rw [hipq]; exact hseed
    · exact False.elim (hnj hia)
  set j := r + L - 1 with hj
  have hjx : j < r + L := by omega
  have hjM : j < M.length := by omega
  have he1j : entry M 1 j ≠ 0 := (upg_e12 hu).1
  have he2j : entry M 2 j = 0 := by have := hZ2 j; have := (upg_e12 hu).2; omega
  have hj0 : 0 < j := by
    by_contra h
    have hjz : j = 0 := by omega
    exact he1j (hR01 j (by rw [hjz]; exact h00))
  have he0j : 0 < entry M 0 j := by
    have hne : entry M 0 j ≠ 0 := fun h => he1j (hR01 j h)
    omega
  obtain ⟨pr, hpr⟩ := par0_some_of (M := M) hj0 (by omega)
  have hprj : pr < j := par_lt M 0 j pr hpr
  have hjch : j ∈ children M pr := mem_children_iff.mpr ⟨hjM, hpr⟩
  have hjcb : col M j ≠ bump M pr := by
    intro h
    have := e2_of_col h
    change entry M 2 j = 1 at this
    omega
  have hjU : ∀ t, upg M t ≠ some j := fun t h => by
    have := upg_target_e2 h
    omega
  have hjcu : ¬ (isUpg M j = true ∧ topped M j = true) := by
    rintro ⟨h, _⟩
    unfold isUpg at h
    obtain ⟨t, _, ht⟩ := List.any_eq_true.mp h
    exact hjU t (of_decide_eq_true ht)
  have hjCLp : j ∈ CL M pr := by
    unfold CL
    rw [List.mem_filter]
    exact ⟨hjch, by simpa using (show Counted M pr j from ⟨hjcb, hjcu⟩)⟩
  let Snew : Bool → Nat → Prop := fun b i => SQU (r + qp) pq j b i ∨ (b = true ∧ i = pr)
  have hmono : ∀ {b i}, DepS M (SQU (r + qp) pq j) b i → DepS M Snew b i :=
    fun h => DepS.mono (fun _ _ hs => Or.inl hs) h
  have hconv : ∀ {b i}, DepS M Snew b i → DepS M (SQU (r + qp) pq j) b i := by
    intro b i h
    induction h with
    | seed hs =>
      rcases hs with hs | ⟨rfl, rfl⟩
      · exact DepS.seed hs
      · exact DepS.ochild hjch hjcb hjcu
          (DepS.ov (DepS.seed (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    | ochild hc hcb hcu _ ih => exact DepS.ochild hc hcb hcu ih
    | ov _ ih => exact DepS.ov ih
    | vpar h1 hp _ ih => exact DepS.vpar h1 hp ih
    | vupg h1 h2 hu _ ih => exact DepS.vupg h1 h2 hu ih
    | vbump h1 h2 hc hb hk _ ih => exact DepS.vbump h1 h2 hc hb hk ih
  let Wj : Bool → Nat → Prop := fun _ i => i = j
  exact t2_assemble2 (S := Snew) (W := Wj) (bnd := r + L) (p := r + qp)
    hC hG hRM hCN hGN hRN hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlT])
    (fun i hi hiq => hchN i hi hiq)
    (Or.inl (Or.inl (Or.inl rfl))) (Or.inr (Or.inl (Or.inl rfl)))
    (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_take M y hi) (fun i hi => par_take M 1 i hi)
    (fun i hi hs => hupgN i hi (fun h => hs (Or.inl (Or.inr (Or.inr ⟨rfl, h⟩)))))
    (fun i c hi hs hc hcx => hcntS i c hi (fun h => hs (Or.inl (Or.inr (Or.inl ⟨rfl, h⟩)))) hc hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inl (Or.inl (Or.inl rfl)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    (fun i jj hi hc hcx _ => by have := (mem_children hc).2; rw [hlT] at this; omega)
    (fun i jj hi hc hcx _ => by obtain ⟨_, rfl⟩ := hxc i jj hc hcx; exact Or.inl (Or.inl rfl))
    (fun i jj k hi hc hcx hb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc jj k hk hkx
      have h' := (mem_children_iff.mp hc).2; rw [hpq] at h'; cases h'
      exact absurd hb hqb)
    (fun t ht hn => by rw [hlT] at hn; omega)
    (by have := anc0_e0_lt hA (by omega); omega)
    (fun i (hw : i = j) => by subst i; exact hmono (DepS.ov (DepS.seed (Or.inr (Or.inr ⟨rfl,rfl⟩)))))
    (fun i (hw : i = j) => by subst i; exact ⟨rfl, hjU⟩)
    (fun i c hc _ (hw : c = j) => by
      subst c
      have h1 := (mem_children_iff.mp hc).2; rw [hpr] at h1; cases h1
      exact Or.inr ⟨rfl,rfl⟩)
    (fun i jj c _ _ hc hb hcc (hw : c = j) => by
      subst c
      have h1 := (mem_children_iff.mp hcc).2; rw [hpr] at h1; cases h1
      exact absurd hb (hNB pr i hpr (mem_children_iff.mp hc).2))
    (fun c hc _ _ hd => hDvNil c hc (hconv hd))
    (fun c hc _ _ hd => hCLnil c hc (hDvNil c hc (hconv hd)))
    (fun c hc _ hcl => hCLnil c hc hcl)
    (fun i hi hs _ hd hv => by
      obtain ⟨Lp,c,R,h1,h2,h3,h4,h5⟩ :=
        hOS i hi (fun h => hs (Or.inl h)) (hconv hd) (fun h => hv (hmono h))
      exact ⟨Lp,c,R,h1,h2,hmono h3,h4,fun d hd hc hD => h5 d hd hc (hconv hD)⟩)
    (fun i hi hs hd => by
      obtain ⟨h1,h2⟩ := hVSh i hi (fun h => hs (Or.inl h)) (hconv hd)
      refine ⟨fun m hm hD => h1 m hm (hconv hD), fun he => ?_⟩
      obtain ⟨Lb,Kb,d,e,a1,a2,a3,a4,a5⟩ := h2 he
      exact ⟨Lb,Kb,d,e,a1,a2,a3,fun t ht hD => a4 t ht (hconv hD),
        fun t ht e he hD => a5 t ht e he (hconv hD)⟩)
    (fun R hR hRA hR0 => by
      refine ⟨hmono (hRD R hR hRA hR0).1, ?_⟩
      intro (hw : R = j)
      have he0R := e0_of_col hR0
      rw [hw] at he0R
      omega)
    (fun i hi _ => (hdrop i hi).1.le)
    hAbs
    (fun b i hs hnw hi hd hoff ih => by
      have hoffOld : ∀ t, t < r + L →
          (¬ DepS M (SQU (r + qp) pq j) true t → σ.o t = ρ.o t) ∧
          (¬ DepS M (SQU (r + qp) pq j) false t → σ.v t = ρ.v t) := by
        intro t ht
        exact ⟨fun h => (hoff t ht).1 (fun hd => h (hconv hd)),
          fun h => (hoff t ht).2 (fun hd => h (hconv hd))⟩
      rcases hs with hs | ⟨hb,hip⟩
      · exact hSeed b i hs hnw hi (hconv hd) hoffOld
          (fun b' i' hrk hD hi' hn => ih b' i' hrk (hmono hD) hi' hn)
      · subst b
        subst i
        have hjlt : σ.o j < ρ.o j := by
          have hvlt : σ.v j < ρ.v j := by
            apply v_upg_drop_lt hZ2 hC hG hCN hjM (by omega) (by rw [hlT]; exact hjx) hu
              (entry_take M 1 hjx) (entry_take M 2 hjx) _ (upg_take_last M (by omega) (by omega))
            rw [par_take M 1 _ hjx]
            cases hm : par M 1 j with
            | none => rfl
            | some m =>
              exact (hoffOld m (by have := par_lt M 1 j m hm; omega)).2 (hP1a m hm)
          have hclj : CL M j = [] := hDvNil j hjx (DepS.seed (Or.inr (Or.inr ⟨rfl,rfl⟩)))
          have hclT : CL (M.take (r + L)) j = [] := hCLnil j hjx hclj
          rw [o_of_no_counted hCN (by rw [hlT]; exact hjx) (hGN.ot_v j (by rw [hlT]; exact hjx))
              (no_cnt_of_cl_nil hclT),
            o_of_no_counted hC hjM (hG.ot_v j hjM) (no_cnt_of_cl_nil hclj)]
          exact psi_lt_psi_z_iff.mpr (Or.inl hvlt)
        have hlt : σ.o pr < ρ.o pr :=
          o_strict_frame hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hCN hRN hdrop
            (by omega) hjCLp (fun d hd => by
              have hdM := (mem_children (cl_mem_children hd)).2
              by_contra h
              have hdx : d = r + L := by omega
              have hpar := (mem_children_iff.mp (cl_mem_children hd)).2
              rw [hdx, hp] at hpar
              have hpqpr : pr = r + qp := (Option.some.inj hpar).symm
              rw [hpqpr] at hprj
              -- If q were pr, j would be a child of q, contradicting CL q=[] because j is counted.
              have hmem : j ∈ CL M (r + qp) := by simpa [hpqpr] using hjCLp
              rw [hCLq] at hmem
              simp at hmem)
            (fun _ => hjlt)
        rcases PO.zero_of_ne (show pr + 2 ≠ M.length by omega) hC hG (by omega)
            (hdrop pr (by omega)).1 (hdrop pr (by omega)).2 with h | ⟨_,w,hw⟩
        · rcases h with heq | h
          · exact False.elim (by rw [heq] at hlt; exact (lt_irrefl _) hlt)
          · exact h
        · have hne : CL M pr ≠ [] := List.ne_nil_of_mem hjCLp
          have harg := arg_lt_of_cl (σ := ρ) hC hG (by omega) hne
          rw [o_cl_eq hC hG (by omega)] at hw
          simp only [psi.injEq] at hw
          rw [hw.2.1] at harg
          exact False.elim ((lt_irrefl _) harg))

/-- Direct integration wrapper using only the weak drop absorption field. -/
theorem qnu_take_of_drop (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M)
    (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ []) {k : Nat} (hu : upg M (r + L - 1) = some k)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m)
    (hP1a : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m)
    (hqsh : ∃ Lb d Kb e, children M (r + qp) = Lb ++ [d, r + L] ∧ children M d = Kb ++ [e] ∧
      (∀ f ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true f) ∧
      (∀ d' ∈ Lb, ∀ e' ∈ children M d', ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e'))
    (hDvNil : ∀ c, c < r + L → DepS M (SQU (r + qp) pq (r + L - 1)) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ (SQU (r + qp) pq (r + L - 1)) true i →
      DepS M (SQU (r + qp) pq (r + L - 1)) true i → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SQU (r + qp) pq (r + L - 1)) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true d))
    (hVSh : ∀ i, i < r + L → ¬ (SQU (r + qp) pq (r + L - 1)) false i → DepS M (SQU (r + qp) pq (r + L - 1)) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (M.take (r + L)) σ) (hGN : Good3 (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hUA : UpgAbsXW M (r + L) ρ)
    (hdrop : ∀ i, i < r + L → PO ρ σ i ∧ PV M ρ σ i)
    (hAbs : AbsWN M (M.take (r + L)) (r + L) ρ σ)
    (hseed : Lhd z (σ.o pq) (ρ.o pq)) :
    isOT (root (M.take (r + L)) σ) = true ∧ root (M.take (r + L)) σ < root M ρ := by
  rcases strong_or_old_target hlen hC hG hUA with hs | ⟨k', hk', hkx', hnb⟩
  · exact t2_qnu_take hlen hL hA hp hqp hxb hBE hR0 hZ2 hSD hZ1 hUAT hR12 hR01
      h00 hpq hqb he2pq hCLq hpqCL hu hP1q hP1a hqsh hDvNil hOS hVSh hC hG hRM
      hCN hGN hRN hF hVS hTD hKD hs hAbs hseed
  · exact qnu_take_weak hlen hL hA hp hqp hxb hBE hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hR01
      h00 hpq hqb he2pq hCLq hpqCL hu hP1q hP1a hqsh hDvNil hOS hVSh hC hG hRM
      hCN hGN hRN hF hVS hTD hKD hnb hdrop hAbs hseed

end

#print axioms qnu_take_of_drop
#print axioms strong_or_bad_of_common_parent
#print axioms strong_or_old_target
#print axioms strong_of_no_upgrade
#print axioms strong_of_next_target
#print axioms strong_seed_of_drop
#print axioms qnu_take_weak
#print axioms absorption_at_leaf
#print axioms old_target_of_failure
end Ytosk.T2UpgAbs
