/-
**C の種の残り `T2SeedCRes.vqP` を `un` から（2026-10-17、t2）。**

C（q ≠ r、q は r で数えられない）で x − 1 が上げない（`T2SeedCRes.un`）なら、M.take x での v(q) は s′ = qnS。
- q の x より前の真の子孫は M.take x で値が変わらない（`chg_free_reg`: 領域は q の真の子孫で x より前。子で閉じ、
  出口は x − 1 だけで、x − 1 は上げない）。
- v(q) の式（行 2 = 1）: v(P_1 q) + ω^{1 + Σ bump 項}。P_1 q = r で v(r) は変わらない（r は topped でない）。
  M.take x の q の子は M の x より前の子で、bump 項は孫の値だけで決まるので M と同じ。これは qnS の定義そのもの。
-/
import Ytosk.V3T2ChgSub
import Ytosk.V3T2SeedRes

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`T2SeedCRes.vqP` from `T2SeedCRes.un`.** -/
theorem c_vqP_of_un {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hun : upg M (r + L - 1) = none) :
    ∀ τ, Cons (M.take (r + L)) τ → τ.v q = qnS M ρ r L q := by
  intro τ hτ
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set x := r + L with hxdef
  have hx : x + 1 = M.length := hlen
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < x := par_lt M 0 _ _ hq
  have hTlen : (M.take x).length = x := by rw [List.length_take]; omega
  -- the ranking of `M.take x`
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = x by omega] at hcnt
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) I.rank hcnt
  -- the region: the proper descendants of `q` before `x`
  have hAq : ∀ c, q ≤ c → c ≤ x → Anc0 M q c := fun c h1 h2 => t_anc_r hX hq h1 h2
  have hfree := chg_free_reg hx I.r0p I.z2 I.sd I.z1 I.uat I.uab (by rw [show x - 1 = r + L - 1 by rfl]; exact hun)
    (Reg := fun d => Anc0 M q d ∧ d ≠ q ∧ d < x)
    (fun d hd => hd.2.2)
    (fun i c hi hc => by
      have hpc := (mem_children_iff.mp hc).2
      have hic : i < c := par_lt M 0 c i hpc
      have hiq : q < i := by have := hi.1.le; have := hi.2.1; omega
      refine ⟨Anc0.trans hi.1 (anc0_of_par M 0 i c hpc), by omega, ?_⟩
      have hcM : c < M.length := (mem_children hc).2
      rcases Nat.lt_or_ge c x with h | h
      · exact h
      · exfalso
        have hcx : c = x := by omega
        rw [hcx, hq] at hpc; cases hpc; omega)
    (fun i hi hn => by
      intro hu
      have hiq : q < i := by have := hi.1.le; have := hi.2.1; omega
      rcases Nat.lt_or_ge (i + 1) x with h | h
      · exact hn ⟨hAq (i + 1) (by omega) (by omega), by omega, h⟩
      · have hix : i = x - 1 := by have := hi.2.2; omega
        rw [hix] at hu; rw [hun] at hu; cases hu)
  have hoff := chg_off hx I.cons I.good hτ hRk1
  have hsame : ∀ k, Anc0 M q k → k ≠ q → k < x → τ.o k = ρ.o k ∧ τ.v k = ρ.v k := by
    intro k h1 h2 h3
    exact ⟨(hoff k h3).1 (hfree true k · ⟨h1, h2, h3⟩), (hoff k h3).2 (hfree false k · ⟨h1, h2, h3⟩)⟩
  -- the value of `q` in `M.take x`
  have hxq : x ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have he2q : entry M 2 q = 1 := I.be q x hxq Txb
  have h1lt := (par2_facts I.z2 (show x < M.length by omega) hr).2
  have he1q : entry M 1 x = entry M 1 q :=
    e1_of_col (show col M x = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have hp1q : par M 1 q = some r := par1_of_child hpq (by omega)
  have hvr : τ.v r = ρ.v r :=
    v_take_of_untopped I hlen (by omega) (topP_C hM hS I hlen hr hq hqr) hτ
  have hv := (hτ q (by rw [hTlen]; exact hqx)).2
  unfold vRhs at hv
  rw [entry_take M 1 hqx, entry_take M 2 hqx, if_neg (by omega), if_neg (by omega),
    par_take M 1 q hqx, hp1q] at hv
  -- the children of `q` in `M.take x` and their bump terms
  have hch : children (M.take x) q = (children M q).filter (fun d => decide (d < x)) := children_take M x q
  have hbt : ∀ d ∈ (children M q).filter (fun d => decide (d < x)),
      bumpTerm (M.take x) τ q d = bumpTerm M ρ q d := by
    intro d hd
    obtain ⟨hdc, hdx⟩ := List.mem_filter.mp hd
    have hdx' : d < x := of_decide_eq_true hdx
    have hpd := (mem_children_iff.mp hdc).2
    have hqd : q < d := par_lt M 0 d q hpd
    have hAd : Anc0 M q d := anc0_of_par M 0 q d hpd
    unfold bumpTerm
    rw [col_take M hdx', bump_take M hqx]
    split_ifs with hb
    · congr 1
      -- the children of `d` lie before `x`
      have hcd : children (M.take x) d = children M d := by
        rw [children_take, List.filter_eq_self]
        intro k hk
        have hpk := (mem_children_iff.mp hk).2
        have hdk : d < k := par_lt M 0 k d hpk
        have hkM : k < M.length := (mem_children hk).2
        simp only [decide_eq_true_eq]
        rcases Nat.lt_or_ge k x with h | h
        · exact h
        · exfalso
          have hkx : k = x := by omega
          rw [hkx, hq] at hpk; cases hpk; omega
      rw [hcd]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hpk := (mem_children_iff.mp hk).2
      have hdk : d < k := par_lt M 0 k d hpk
      have hkM : k < M.length := (mem_children hk).2
      have hkx : k < x := by
        rcases Nat.lt_or_ge k x with h | h
        · exact h
        · exfalso
          have hkx : k = x := by omega
          rw [hkx, hq] at hpk; cases hpk; omega
      exact (hsame k (Anc0.trans hAd (anc0_of_par M 0 d k hpk)) (by omega) hkx).1
    · rfl
  rw [hch, List.map_congr_left hbt] at hv
  change τ.v q = sf (add (τ.v r) (omega (sumN (one ::
    ((children M q).filter (fun d => decide (d < x))).map (bumpTerm M ρ q))))) at hv
  rw [hv, hvr]
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hSot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < x))).map (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  rw [sf_ot (isOT_add hVot (isOT_omega hSot))]
  rfl

/-- **`T2SeedCRes` without `vqP`** (it follows from `un`). -/
structure T2SeedCResR (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  decP : ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
    ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s
  un : upg M (r + L - 1) = none
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
      (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z =
    sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)
  lhd : ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
    Lhd z (psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) z) (ρ.o r)

theorem t2SeedCRes_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (h : T2SeedCResR M ρ r L q) : T2SeedCRes M ρ r L q :=
  ⟨h.decP, h.un, c_vqP_of_un hM hS I hlen hr hq hqr h.un, h.rw, h.lhd⟩

end Ytosk

