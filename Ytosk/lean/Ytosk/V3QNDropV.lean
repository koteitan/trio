/-
**3 行・t = 2・qn: 落とした後の q の v（x − 1 が上げない場合）。**

`t2_qn_take`（V3T2T）の中の種 v(q) の部分だけを取り出した（`t2_qn_take_vq`）: q の最後の子 x は bump 子で子を持たず、
M.take x ではその bump 項 1 が消える。q の bump 子の子は DepS に入らない（`qn_shapes`）ので o は変わらず、
`v_bump_drop` で v_T(q) ◁ v_M(q)。
x − 1 が上げる場合は n ≤ 1 の展開の `T2UpgAbs.qnu_take_of_drop_full`（列ごとの ◁ を返す形にした）から出す（`qn_drop_v_upg`）。
これで T2SeedPResRC2 の qn の欄はすべて証明でき、残りは qr・sv・C の `T2SeedPResRC5` になる。
-/
import Ytosk.V3QNTakeL
import Ytosk.V3T2Top
import Ytosk.V3T2UpgAbs

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **`v_T(q) ◁ v_M(q)`** at `t = 2`, `q ≠ r`, when `x − 1` does not upgrade (the seed `v(q)` of `t2_qn_take`). -/
theorem t2_qn_take_vq {M : Mat} {r L qp pq : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
    (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
    (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M)
    (hpq : par M 0 (r + qp) = some pq) (hqb : col M (r + qp) ≠ bump M pq) (hun : upg M (r + L - 1) = none)
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m)
    (hqL : ∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
      ¬ DepS M (SQ (r + qp) pq) true e)
    {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN) :
    Lhd z (σ.v (r + qp)) (ρ.v (r + qp)) := by
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
  exact hvq

/-- **The qn drop at `q`** when `x − 1` does not upgrade: `v_T(q) ⊴ v_M(q)`. -/
theorem qn_drop_v_noupg {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hun : upg M (r + L - 1) = none) :
    ∀ τ, Cons (M.take (r + L)) τ → LhdE (τ.v q) (ρ.v q) := by
  intro τ hτ
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, -⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  obtain ⟨Tp1, TqL, -⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
    I.uat I.uab I.r12 hpq' Tqb
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have h := t2_qn_take_vq hlen (by omega) hA hq' (by omega) Txb I.be I.z2 I.uat I.r12 hpq' Tqb hun Tp1 TqL
    I.cons I.good hC1 hRk1
  rw [show r + (q - r) = q by omega] at h
  have hag := agree_of_cons hτ hC1 hRk1
  have hqT : q < (M.take (r + L)).length := by rw [List.length_take]; omega
  rw [(hag q hqT).2]
  exact Or.inr h

/-- **The qn drop at `q`** when `x − 1` upgrades: `v_T(q) ◁ v_M(q)` from the `n ≤ 1` engine
(`T2UpgAbs.qnu_take_of_drop_full`). Its seed `o(r)` changes because `t₁ < v(q)` (`qn_take_t1L`, `leaf_M_side`). -/
theorem qn_drop_v_upg {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hNB : ¬ Bad2 M)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    {k : Nat} (hux : upg M (r + L - 1) = some k) :
    ∀ τ, Cons (M.take (r + L)) τ → LhdE (τ.v q) (ρ.v q) := by
  intro τ hτ
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  obtain ⟨Up1, Up1a, Uqsh, Udv, Uos, Uvsh⟩ := qnu_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd
    I.z1 I.uat I.uab I.r12 hpq' Tqb hux
  -- the drop
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := R.hdrop
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  have hab := (R.old hNB).ab
  have hua := (R.old hNB).ua
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hdrop hG1 hab hua
  have hAbs := absWN_of_absC hab hC1 hq' (fun i h => by rw [hpq'] at h; cases h; exact Tqb)
  -- the seed `o(r)` changes
  obtain ⟨ωT, hsp, -, -, -, hωT, hvqM⟩ := qn_take_t1L hM hS I R hlen hr hq hqr hCL hC1
  have hSot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  have ht1lt : add (ρ.v r) ωT < ρ.v q := by
    rw [hvqM]
    exact add_lt_add_left _ (lt_of_le_of_lt hωT (omega_lt_omega hSot (isOT_succ hSot) (lt_succ_self _)))
  have hTclq : CL M q = [] := by rw [show q = r + (q - r) by omega]; exact Tclq
  have hoqM : ρ.o q = psi (ρ.v q) z z := by
    rw [o_cl_eq I.cons I.good (show q < M.length by omega), hTclq]; rfl
  have hrM := (leaf_M_side I (show r < M.length by omega) hCL hoqM).2.2
  have hne : (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)).o r ≠ ρ.o r := by
    intro h
    rw [o_cl_eq hC1 hG1 (by rw [List.length_take]; omega), hsp, hrM] at h
    simp only [psi.injEq] at h
    have h2 := app_left_cancel h.2.1
    simp only [psi.injEq] at h2
    rw [h2.1] at ht1lt
    exact lt_irrefl' _ ht1lt
  have hs1 := T2UpgAbs.strong_seed_of_drop hlen I.cons I.good (p := r) (by omega) (by omega) Tclpq
    (hdrop r (by omega)) hne (R.old hNB).ws.2.2
  have H := T2UpgAbs.qnu_take_of_drop_full hlen (by omega) hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
    I.uat I.uab I.r12 I.r01 I.e00 hpq' Tqb Te2pq Tclq Tclpq hux Up1 Up1a Uqsh Udv Uos Uvsh
    I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hua (R.old hNB).ws.2.2 hdrop hAbs hs1
  have h := H.2
  rw [show r + (q - r) = q by omega] at h
  have hag := agree_of_cons hτ hC1 hRk1
  have hqT : q < (M.take (r + L)).length := by rw [List.length_take]; omega
  rw [(hag q hqT).2]
  exact Or.inr h

/-- **The seed residuals with the qn field only when `x − 1` upgrades** (`v_T(q) ⊴ v_M(q)`). -/
structure T2SeedPResRC4 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SVStrict M ρ r L ∧
      ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
        Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → upg M (r + L - 1) ≠ none →
      ∀ τ, Cons (M.take (r + L)) τ → Lhd z (tqN (ρ.v r) (qnS M ρ r L q) (τ.v q) 1) (ρ.v q)
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCResR2 M ρ r L q

/-- **Residual (t2): the seed residuals with the qn field only when `x − 1` upgrades.** -/
def T2SeedPResRCV2D : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC4 M ρ

theorem t2SeedPResRCV2C_of_D (h : T2SeedPResRCV2D) : T2SeedPResRCV2C := fun M ρ rk C hz h2 =>
  have H := h M ρ rk C hz h2
  ⟨H.qr, H.sv, fun r L q hlen hr hq hqr Lc hCL τ hτ => by
    cases hu : upg M (r + L - 1) with
    | none =>
      exact qn1_of_lhdE C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hlen hr hq hqr hCL
        (fun τ' hτ' => qn_drop_v_noupg C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr hu τ' hτ') τ hτ
    | some k => exact H.qn r L q hlen hr hq hqr Lc hCL (by rw [hu]; simp) τ hτ, H.C⟩

/-- **The seed residuals without the qn field** (qn is proved: `qn_drop_v_noupg`・`qn_drop_v_upg`). -/
structure T2SeedPResRC5 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SVStrict M ρ r L ∧
      ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
        Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCResR2 M ρ r L q

/-- **Residual (t2): the seed residuals of qr, sv and C** (the qn field is proved). -/
def T2SeedPResRCV2E : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC5 M ρ

/-- **Residual (t2, `Bad2`): the first qn subscript** `t_1 ◁ v_M(q)` (`t_0 = v_T(q)`, 2026-10-25). Outside `Bad2` it
follows from the drop at `q` (`qn_drop_v_upg`・`qn1_of_lhdE`); on `Bad2` (where `x − 1` always upgrades) the drop
`v_T(q) ⊴ v_M(q)` is false (b2grow1: 319 of 587) but `t_1 ◁ v_M(q)` holds (b2grow1・b2grow2・graftBb2St, 4119 cases;
`t_2`, `t_3` too). -/
def T2QN1Bad : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → ∀ τ, Cons (M.take (r + L)) τ →
        Lhd z (tqN (ρ.v r) (qnS M ρ r L q) (τ.v q) 1) (ρ.v q)

theorem t2SeedPResRCV2D_of_E (hQB : T2QN1Bad) (h : T2SeedPResRCV2E) : T2SeedPResRCV2D := fun M ρ rk C hz h2 =>
  have H := h M ρ rk C hz h2
  ⟨H.qr, H.sv, fun r L q hlen hr hq hqr Lc hCL hu τ hτ => by
    by_cases hB2 : Bad2 M
    · exact hQB M ρ rk C hB2 hz h2 r L q hlen hr hq hqr Lc hCL τ hτ
    cases hk : upg M (r + L - 1) with
    | none => exact absurd hk hu
    | some k =>
      exact qn1_of_lhdE C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hlen hr hq hqr hCL
        (qn_drop_v_upg C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hB2 hlen hr hq hqr hCL hk) τ hτ,
    H.C⟩

end Ytosk
