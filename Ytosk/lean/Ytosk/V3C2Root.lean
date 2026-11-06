/-
**t = 2, q ≠ r: the root `r` in `M[n]` and in `M` (2026-11-06).**

The calls of `M` and `N = M[n]` before `x` have the same equations except `o(r)` (`q` counted in `N`), `o(q)` (`x′`
counted in `N`), `v(q)` (the bump term of `x` in `M`) and the column `x`.  Each of these depends on `v(r)`
(`P_1(q) = P_1(x) = r`), so with the exception set `E b i := rk(false, r) < rk(b, i)` of the ranking of `M`,
`agree_by_rank` gives `v_N(r) = v_M(r)` (`C_root_v`).  In the C configuration `q` is not counted at `r` in `M` and is
counted in `N`, so `CL_N(r) = CL_M(r) ++ [q]` (`C_root_cl`).  Neither uses the condition `un`.
-/
import Ytosk.V3TranslationRes

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem C_root {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) :
    σ.v r = ρ.v r ∧ ((¬ ∃ Lc, CL M r = Lc ++ [q]) →
      CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
        CL M r ++ [q]) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx0 : r < r + L := par_lt M 2 _ _ hr
  have hA0 : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrq0 : Anc0 M r q := anc0_par hA0 (by have := par_lt M 0 _ _ hq; omega) hq
  obtain ⟨pq, hpq0⟩ := par0_of_anc hrq0 (fun h => hqr h.symm)
  have hrq : r < q := by have := hrq0.le; omega
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  have hpq' := hpq0
  obtain ⟨Txb0, Tqb0, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq'
  have hpq : par M 0 (r + qp) = some r := by
    have he0lt' := anc0_e0_lt hA0 (by omega)
    obtain ⟨he2r', h1lt'⟩ := par2_facts hX.z2 (by omega) hr
    have hqb' : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
      intro i hi; rw [hpq0] at hi; cases hi; exact Tqb0
    exact qn_par0_q hlen (by omega) hA0 hq (d0 := entry M 0 (r + L) - entry M 0 r) (by omega) (le_refl 2)
      (d1 := entry M 1 (r + L) - entry M 1 r) (by omega) he2r' h1lt' hqb'
      (par1_x_r (by omega) I.z2 I.z1 hr) hqr Txb0 hJ hX.r0p I.be
  rw [hpq] at hpq0; cases hpq0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hqcntN : Counted N r (r + qp) := by
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact Tqb, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hrM : r < M.length := by omega
  have hxM : r + L < M.length := by omega
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have he1xq : entry M 1 (r + L) = entry M 1 (r + qp) :=
    e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from Txb)
  have he1q : entry M 1 (r + qp) ≠ 0 := by omega
  have he1x : entry M 1 (r + L) ≠ 0 := by omega
  have hp1q : par M 1 (r + qp) = some r := par1_of_child hpq (by omega)
  have hRq : rk false r < rk false (r + qp) := ((I.rank (r + qp) hqM).2.2 he1q).1 r hp1q
  have hRx : rk false r < rk false (r + L) := ((I.rank (r + L) hxM).2.2 he1x).1 r hr1
  have hoq := (I.rank (r + qp) hqM).1
  have hox := (I.rank (r + L) hxM).1
  have hor := (I.rank r hrM).1
  have hag := agree_by_rank (M' := M) (ρ := σ) (ρ' := ρ) (fun b i => rk false r < rk b i) I.rank
    (by
      intro i hi hE hvi hci
      have hE' : rk true i ≤ rk false r := not_lt.mp hE
      have hir : i ≠ r := fun e => by subst e; omega
      have hiq : i ≠ r + qp := fun e => by rw [e] at hE'; omega
      have hix : i ≠ r + L := fun e => by rw [e] at hE'; omega
      have hix' : i < r + L := by omega
      rw [(I.cons i hi).1, (hCN i (by omega)).1]
      unfold oRhs
      rw [hvi, hchN i hix']
      have hmap : (children M i).map (cnt M ρ i) = (children M i).map (cnt N σ i) := by
        apply List.map_congr_left
        intro c hc
        have hcx : c < r + L := by
          by_contra h'
          exact hiq (hxc i c hc (by omega)).2
        have hcq : c ≠ r + qp := by
          intro e; rw [e] at hc; rw [(mem_children_iff.mp hc).2] at hpq; cases hpq; exact hir rfl
        rw [cnt_eq_ite, cnt_eq_ite]
        by_cases hcnt : Counted M i c
        · rw [if_pos hcnt, if_pos ((hcntN i c hix' hcx hcq).mpr hcnt)]
          exact hci c hc hcnt
        · rw [if_neg hcnt, if_neg (fun h => hcnt ((hcntN i c hix' hcx hcq).mp h))]
      rw [hmap])
    (by
      intro i hi hE hp1 hup hbk
      have hE' : rk false i ≤ rk false r := not_lt.mp hE
      have hiq : i ≠ r + qp := fun e => by rw [e] at hE'; omega
      have hix : i ≠ r + L := fun e => by rw [e] at hE'; omega
      have hix' : i < r + L := by omega
      rw [(I.cons i hi).2, (hCN i (by omega)).2]
      unfold vRhs
      rw [entry_gexp_pre hlen hm1 1 hix', entry_gexp_pre hlen hm1 2 hix']
      have hpar : par N 1 i = par M 1 i := by rw [← par_take N 1 i hix', hT, par_take M 1 i hix']
      rw [hpar]
      by_cases h1 : entry M 1 i = 0
      · simp only [h1, if_true]
      rw [if_neg h1, if_neg h1]
      have hvo : vOpt ρ (par M 1 i) = vOpt σ (par M 1 i) := by
        cases hm : par M 1 i with
        | none => rfl
        | some m => exact hp1 m h1 hm
      by_cases h2' : entry M 2 i = 0
      · rw [if_pos h2', if_pos h2']
        have hupg : upg N i = upg M i := by
          rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
          · rw [← upg_take _ h, hT, upg_take M h]
          · have hi1 : i = r + L - 1 := by omega
            have hnu : upg M (r + L - 1) ≠ some (r + L) := by
              intro hu
              have := ((I.rank i hi).2.2 h1).2.1 h2' (r + L) (by rw [hi1]; exact hu)
              omega
            rw [hi1]
            exact upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu (by omega)
        rw [hupg, hvo]
        cases hk : upg M i with
        | none => rfl
        | some k =>
          show sf (add (vOpt σ (par M 1 i)) (last (ρ.v k))) = sf (add (vOpt σ (par M 1 i)) (last (σ.v k)))
          rw [hup k h1 h2' hk]
      · rw [if_neg h2', if_neg h2', hvo, hchN i hix']
        have hbt : (children M i).map (bumpTerm M ρ i) = (children M i).map (bumpTerm N σ i) := by
          apply List.map_congr_left
          intro j hj
          have hjx : j < r + L := by
            by_contra h'
            exact hiq (hxc i j hj (by omega)).2
          unfold bumpTerm
          rw [hcolN j hjx, hbN i hix']
          by_cases hjb : col M j = bump M i
          · rw [if_pos hjb, if_pos hjb, hchN j hjx]
            rw [List.map_congr_left (fun k hk => hbk j hj h1 h2' hjb k hk)]
          · rw [if_neg hjb, if_neg hjb]
        rw [hbt])
    (by
      intro i hi hE
      refine ⟨fun h => hE (lt_trans h (I.rank i hi).1), fun c hc hcnt h => hE (lt_trans h ?_)⟩
      exact (I.rank i hi).2.1 c hc hcnt.1 hcnt.2)
    (by
      intro i hi hE h1
      refine ⟨fun m hm h => hE (lt_trans h (((I.rank i hi).2.2 h1).1 m hm)),
        fun h2' k hk h => hE (lt_trans h (((I.rank i hi).2.2 h1).2.1 h2' k hk)),
        fun h2' j hj hjb k hk h => hE (lt_trans h (((I.rank i hi).2.2 h1).2.2 h2' j hj hjb k hk))⟩)
  refine ⟨((hag r hrM).2 (lt_irrefl _)).symm, fun hncl => ?_⟩
  -- the counted children of `r`
  have hqc : r + qp ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hqlast : children M r = (children M r).filter (fun d => decide (d < r + qp)) ++ [r + qp] := by
    apply split_last_max _ _ (children_sorted M r) hqc
    intro d hd
    by_contra hlt
    have hdx : d < r + L := by
      by_contra h'
      have := (hxc r d hd (by omega)).2; omega
    have hAq : Anc0 M (r + qp) (r + L) := Anc0.step hq (Anc0.refl _)
    have hAd : Anc0 M (r + qp) d := anc_between hAq d (by omega) (by omega)
    have hAr := anc0_par hAd (by omega) (mem_children_iff.mp hd).2
    have := hAr.le; omega
  have hnM : ¬ Counted M r (r + qp) := by
    intro hcnt
    apply hncl
    refine ⟨((children M r).filter (fun d => decide (d < r + qp))).filter (fun c => decide (Counted M r c)), ?_⟩
    unfold CL
    rw [hqlast, List.filter_append]
    simp [hcnt]
  unfold CL
  rw [hchN r (by omega)]
  conv_lhs => rw [hqlast, List.filter_append]
  conv_rhs => rw [hqlast, List.filter_append]
  rw [show List.filter (fun c => decide (Counted N r c)) [r + qp] = [r + qp] by simp [hqcntN],
    show List.filter (fun c => decide (Counted M r c)) [r + qp] = [] by simp [hnM], List.append_nil]
  congr 1
  apply List.filter_congr
  intro c hc
  have hc' := List.mem_filter.mp hc
  have hcq : c < r + qp := by simpa using hc'.2
  simp only [decide_eq_decide]
  exact hcntN r c (by omega) (by omega) (by omega)

#print axioms C_root

/-- **`cl_C` without `un`**: if `x − 1` upgrades to `q`, then `q ≠ x` and `UAT` makes `q` untopped, but `q` is topped
(it is an uncounted child of `r` that is not a bump child). -/
theorem cl_C_any {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) {r L q : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) :
    CL M r = CL (M.take (r + L)) r := by
  have hx : r + L + 1 = M.length := hlen
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hpq : par M 0 q = some r := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqM : q ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hxr : r + L ∉ children M r := fun h => by
    have := (mem_children_iff.mp h).2; rw [hq] at this; cases this; exact hqr rfl
  -- `q` is the largest child of `r`
  have hmax : ∀ d ∈ children M r, d ≤ q := by
    intro d hd
    by_contra hlt
    have hdl := (mem_children hd).2
    have hdx : d ≠ r + L := fun e => hxr (e ▸ hd)
    have hpd := (mem_children_iff.mp hd).2
    have h1 := ((par0_spec M).mp hpd).2.2 q (by omega) (by omega)
    have h2 := ((par0_spec M).mp hq).2.1
    have h3 := ((par0_spec M).mp hq).2.2 d (by omega) (by omega)
    omega
  have hsplit := split_last_max _ _ (children_sorted M r) hqM hmax
  have hnq : ¬ Counted M r q := by
    intro hc
    apply hncl
    refine ⟨((children M r).filter (fun d => decide (d < q))).filter (fun d => decide (Counted M r d)), ?_⟩
    unfold CL; rw [hsplit, List.filter_append]; simp [hc]
  -- `q` stays uncounted in `M.take x`
  have hnqT : ¬ Counted (M.take (r + L)) r q := by
    rintro ⟨hb, hu⟩
    rw [col_take M hqx, bump_take M (by omega)] at hb
    apply hnq
    refine ⟨hb, fun ⟨hU, hTp⟩ => hu ⟨?_, ?_⟩⟩
    · unfold isUpg at hU ⊢
      rw [List.any_eq_true] at hU ⊢
      obtain ⟨k, hk, hkq⟩ := hU
      have hkq' : upg M k = some q := by simpa using hkq
      have hk1 : k + 1 < r + L := by
        have hkl := List.mem_range.mp hk
        rcases Nat.lt_or_ge (k + 1) (r + L) with h | h
        · exact h
        · exfalso
          rcases Nat.lt_or_ge k (r + L) with h' | h'
          · rw [show k = r + L - 1 by omega] at hkq'
            have := I.uat (r + L - 1) q hkq' (by omega)
            rw [this] at hTp; cases hTp
          · rw [show k = r + L by omega, upg_last_none hx] at hkq'; cases hkq'
      exact ⟨k, List.mem_range.mpr (by rw [List.length_take]; omega), by rw [upg_take M hk1]; simp [hkq']⟩
    · -- all children of `q` are bump columns
      unfold isUpg at hU
      rw [List.any_eq_true] at hU
      obtain ⟨k, _, hkq⟩ := hU
      have he2 : entry M 2 q = 1 := by
        have := upg_target_e2 (show upg M k = some q by simpa using hkq); have := I.z2 q; omega
      have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
      have hchq := children_split_x hx hxq
      have hxb : col M (r + L) = bump M q := by
        unfold topped at hTp
        rw [hchq] at hTp
        simpa using hTp
      have hall := all_bump_of_last I.r0p I.z2 I.sd I.z1 he2 hchq hxb
      unfold topped
      rw [children_take]
      cases hl : ((children M q).filter (fun c => decide (c < r + L))).getLast? with
      | none => rfl
      | some ℓ =>
        have hℓ := List.mem_filter.mp (List.mem_of_getLast? hl)
        have hℓx : ℓ < r + L := by simpa using hℓ.2
        simp only [decide_eq_true_eq]
        rw [col_take M hℓx, bump_take M hqx]
        exact hall ℓ hℓ.1
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  unfold CL
  rw [children_take, children_filter_x hx hxr]
  apply List.filter_congr
  intro d hd
  have hdx : d < r + L := by
    have := (mem_children hd).2
    rcases Nat.lt_or_ge d (r + L) with h | h
    · exact h
    · exact absurd (show d = r + L by omega ▸ hd) hxr
  simp only [decide_eq_decide]
  by_cases hdq : d = q
  · subst hdq
    exact ⟨fun h => absurd h hnq, fun h => absurd h hnqT⟩
  · constructor
    · intro hM
      have h := counted_take_of (r := q) (L := r + L - q) (by omega) (by omega)
        (by rw [show q + (r + L - q) = r + L by omega]; exact hq) (show d < q + (r + L - q) by omega) hdq hM
        (show r < q + (r + L - q) by omega)
      rwa [show q + (r + L - q) = r + L by omega] at h
    · intro hT
      exact hcnt r d (by omega) (by rw [children_take]; exact List.mem_filter.mpr ⟨hd, by simpa using hdx⟩) hT

#print axioms cl_C_any

/-- **`T2C2Kids` without its structural fields** (`C_root`): only the relation of the children of `r`. -/
def T2C2Kids3 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ Lc0 c0, CL M r = Lc0 ++ [c0] → (∀ d ∈ Lc0, σ.o d = ρ.o d) ∧
      ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM

theorem t2C2Kids_of3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (h : T2C2Kids3 M ρ r L q) : T2C2Kids M ρ r L q := fun n hn σ hCN hGN =>
  ⟨(C_root hM hS I hz h2 hlen hr hq hqr hn hCN).2 hncl, (C_root hM hS I hz h2 hlen hr hq hqr hn hCN).1,
    h n hn σ hCN hGN⟩

def C2Kids3 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2Kids3 M ρ r L q

theorem c2Kids_of3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (h : C2Kids3 M ρ) : C2Kids M ρ := fun r L q k hlen hr hq hqr hncl hu =>
  t2C2Kids_of3 hM hS I hz h2 hlen hr hq hqr hncl (h r L q k hlen hr hq hqr hncl hu)

/-- **`T2C2RootRel` without its structural fields** (`cl_C_any`, `C_root`): only the relation of the states. -/
def T2C2RootRel3 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ,
    Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    ∀ j, j ≤ (CL M r).length →
      spArg (ρ.v r) z (sumN (((CL M r).take j).map σ.o)) =
        spArg (ρ.v r) z (sumN (((CL M r).take j).map ρ.o)) ∨
      Lhd z (spArg (ρ.v r) z (sumN (((CL M r).take j).map σ.o)))
        (spArg (ρ.v r) z (sumN (((CL M r).take j).map ρ.o)))

theorem t2C2RootRel_of3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (h : T2C2RootRel3 M ρ r L q) : SeedFO.T2C2RootRel M ρ r L q :=
  ⟨cl_C_any hM hS I hlen hr hq hqr hncl, fun n hn σ hCN hGN =>
    ⟨(C_root hM hS I hz h2 hlen hr hq hqr hn hCN).2 hncl, (C_root hM hS I hz h2 hlen hr hq hqr hn hCN).1,
      h n hn σ hCN hGN⟩⟩

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU : T2AtV3 T2BelowAtV3U)
    (hCan : HCanon)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK3 : T2AtV3 (fun M ρ => C2Kids3 M ρ))
    (hC2R3 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2RootRel3 M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG

theorem desc3_res2 : Desc3 :=
  desc3_res hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF
    (fun M ρ rk C hz h2 => c2Kids_of3 C.std C.ne (coreW C.S C.I) hz h2 (hK3 M ρ rk C hz h2))
    (fun M ρ rk C hz h2 r L q k hlen hr hq hqr hncl hu => t2C2RootRel_of3 C.std C.ne (coreW C.S C.I) hz h2
      hlen hr hq hqr hncl (hC2R3 M ρ rk C hz h2 r L q k hlen hr hq hqr hncl hu))
    hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (C2 structure proved). -/
theorem translation_order_res2
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_res2 hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG)
    hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res2 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ (desc3_res2 hDI hF hAbsU hSeeds hQR hQN hBXU hCan hVF hK3 hC2R3 hFD hQNd hSC hCopy hVD hAG)
    hFS hot hvN hlt

end

#print axioms translation_order_res2
#print axioms translation_surj_res2

end Ytosk.V3Main.SeedPF
